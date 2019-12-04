/*-------------------------------------------------------------------------
 *
 * execProcnode.c
 *	 contains dispatch functions which call the appropriate "initialize",
 *	 "get a tuple", and "cleanup" routines for the given node type.
 *	 If the node has children, then it will presumably call ExecInitNode,
 *	 ExecProcNode, or ExecEndNode on its subnodes and do the appropriate
 *	 processing.
 *
 * Portions Copyright (c) 2005-2008, Greenplum inc
 * Portions Copyright (c) 2012-Present Pivotal Software, Inc.
 * Portions Copyright (c) 1996-2016, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execProcnode.c
 *
 *-------------------------------------------------------------------------
 */
/*
 *	 INTERFACE ROUTINES
 *		ExecInitNode	-		initialize a plan node and its subplans
 *		ExecProcNode	-		get a tuple by executing the plan node
 *		ExecEndNode		-		shut down a plan node and its subplans
 *
 *	 NOTES
 *		This used to be three files.  It is now all combined into
 *		one file so that it is easier to keep ExecInitNode, ExecProcNode,
 *		and ExecEndNode in sync when new nodes are added.
 *
 *	 EXAMPLE
 *		Suppose we want the age of the manager of the shoe department and
 *		the number of employees in that department.  So we have the query:
 *
 *				select DEPT.no_emps, EMP.age
 *				from DEPT, EMP
 *				where EMP.name = DEPT.mgr and
 *					  DEPT.name = "shoe"
 *
 *		Suppose the planner gives us the following plan:
 *
 *						Nest Loop (DEPT.mgr = EMP.name)
 *						/		\
 *					   /		 \
 *				   Seq Scan		Seq Scan
 *					DEPT		  EMP
 *				(name = "shoe")
 *
 *		ExecutorStart() is called first.
 *		It calls InitPlan() which calls ExecInitNode() on
 *		the root of the plan -- the nest loop node.
 *
 *	  * ExecInitNode() notices that it is looking at a nest loop and
 *		as the code below demonstrates, it calls ExecInitNestLoop().
 *		Eventually this calls ExecInitNode() on the right and left subplans
 *		and so forth until the entire plan is initialized.  The result
 *		of ExecInitNode() is a plan state tree built with the same structure
 *		as the underlying plan tree.
 *
 *	  * Then when ExecutorRun() is called, it calls ExecutePlan() which calls
 *		ExecProcNode() repeatedly on the top node of the plan state tree.
 *		Each time this happens, ExecProcNode() will end up calling
 *		ExecNestLoop(), which calls ExecProcNode() on its subplans.
 *		Each of these subplans is a sequential scan so ExecSeqScan() is
 *		called.  The slots returned by ExecSeqScan() may contain
 *		tuples which contain the attributes ExecNestLoop() uses to
 *		form the tuples it returns.
 *
 *	  * Eventually ExecSeqScan() stops returning tuples and the nest
 *		loop join ends.  Lastly, ExecutorEnd() calls ExecEndNode() which
 *		calls ExecEndNestLoop() which in turn calls ExecEndNode() on
 *		its subplans which result in ExecEndSeqScan().
 *
 *		This should show how the executor works by having
 *		ExecInitNode(), ExecProcNode() and ExecEndNode() dispatch
 *		their work to the appropriate node support routines which may
 *		in turn call these routines themselves on their subplans.
 */
#include "postgres.h"

#include "executor/executor.h"
#include "executor/nodeAgg.h"
#include "executor/nodeAppend.h"
#include "executor/nodeBitmapAnd.h"
#include "executor/nodeBitmapHeapscan.h"
#include "executor/nodeBitmapIndexscan.h"
#include "executor/nodeDynamicBitmapHeapscan.h"
#include "executor/nodeDynamicBitmapIndexscan.h"
#include "executor/nodeBitmapOr.h"
#include "executor/nodeCtescan.h"
#include "executor/nodeCustom.h"
#include "executor/nodeForeignscan.h"
#include "executor/nodeFunctionscan.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "executor/nodeIndexonlyscan.h"
#include "executor/nodeIndexscan.h"
#include "executor/nodeLimit.h"
#include "executor/nodeLockRows.h"
#include "executor/nodeMaterial.h"
#include "executor/nodeMergeAppend.h"
#include "executor/nodeMergejoin.h"
#include "executor/nodeModifyTable.h"
#include "executor/nodeNestloop.h"
#include "executor/nodeGather.h"
#include "executor/nodeRecursiveunion.h"
#include "executor/nodeResult.h"
#include "executor/nodeSamplescan.h"
#include "executor/nodeSeqscan.h"
#include "executor/nodeSetOp.h"
#include "executor/nodeSort.h"
#include "executor/nodeSubplan.h"
#include "executor/nodeSubqueryscan.h"
#include "executor/nodeTidscan.h"
#include "executor/nodeUnique.h"
#include "executor/nodeValuesscan.h"
#include "executor/nodeWindowAgg.h"
#include "executor/nodeWorktablescan.h"
#include "nodes/nodeFuncs.h"
#include "miscadmin.h"

#include "cdb/cdbvars.h"
#include "cdb/ml_ipc.h"			/* interconnect context */
#include "executor/nodeAssertOp.h"
#include "executor/nodeDML.h"
#include "executor/nodeDynamicIndexscan.h"
#include "executor/nodeDynamicSeqscan.h"
#include "executor/nodeExternalscan.h"
#include "executor/nodeMotion.h"
#include "executor/nodePartitionSelector.h"
#include "executor/nodeRepeat.h"
#include "executor/nodeRowTrigger.h"
#include "executor/nodeSequence.h"
#include "executor/nodeShareInputScan.h"
#include "executor/nodeSplitUpdate.h"
#include "executor/nodeTableFunction.h"
#include "pg_trace.h"
#include "tcop/tcopprot.h"
#include "utils/metrics_utils.h"

 /* flags bits for planstate walker */
#define PSW_IGNORE_INITPLAN    0x01

 /**
  * Forward declarations of static functions
  */
static CdbVisitOpt planstate_walk_node_extended(PlanState *planstate,
				 CdbVisitOpt (*walker) (PlanState *planstate, void *context),
							 void *context,
							 int flags);

static CdbVisitOpt planstate_walk_array(PlanState **planstates,
					 int nplanstate,
				 CdbVisitOpt (*walker) (PlanState *planstate, void *context),
					 void *context,
					 int flags);

static CdbVisitOpt planstate_walk_kids(PlanState *planstate,
				 CdbVisitOpt (*walker) (PlanState *planstate, void *context),
					void *context,
					int flags);

/*
 * saveExecutorMemoryAccount saves an operator specific memory account
 * into the PlanState of that operator
 */
static inline void
saveExecutorMemoryAccount(PlanState *execState,
						  MemoryAccountIdType curMemoryAccountId)
{
	Assert(curMemoryAccountId != MEMORY_OWNER_TYPE_Undefined);
	Assert(MEMORY_OWNER_TYPE_Undefined == execState->memoryAccountId);
	execState->memoryAccountId = curMemoryAccountId;
}


/*
 * CREATE_EXECUTOR_MEMORY_ACCOUNT is a convenience macro to create a new
 * operator specific memory account *if* the operator will be executed in
 * the current slice, i.e., it is not part of some other slice (alien
 * plan node). We assign a shared AlienExecutorMemoryAccount for plan nodes
 * that will not be executed in current slice
 *
 * If the operator is a child of an 'X_NestedExecutor' account, the operator
 * is also assigned to the 'X_NestedExecutor' account, unless the
 * explain_memory_verbosity guc is set to 'debug' or above.
 */
#define CREATE_EXECUTOR_MEMORY_ACCOUNT(isAlienPlanNode, planNode, NodeType)    \
	MemoryAccounting_CreateExecutorAccountWithType(                            \
		(isAlienPlanNode), (planNode), MEMORY_OWNER_TYPE_Exec_##NodeType)


/* ----------------------------------------------------------------
 *		ExecProcNode
 *
 *		Execute the given node to return a(nother) tuple.
 * ----------------------------------------------------------------
 */
void ExecProcNodeBatch(PlanState *node,TupleTableSlots *resultSlots)
{
	TupleTableSlot *result = NULL;
	Assert(resultSlots);
	START_MEMORY_ACCOUNT(node->memoryAccountId);
	{

		CHECK_FOR_INTERRUPTS();

		/*
		* Even if we are requested to finish query, Motion has to do its work
		* to tell End of Stream message to upper slice.  He will probably get
		* NULL tuple from underlying operator by calling another ExecProcNode,
		* so one additional operator execution should not be a big hit.
		*/
		if (QueryFinishPending && !IsA(node, MotionState))
			return;

		if (node->plan)
			TRACE_POSTGRESQL_EXECPROCNODE_ENTER(GpIdentity.segindex, currentSliceId, nodeTag(node), node->plan->plan_node_id);

		if (node->chgParam != NULL) /* something changed */
			ExecReScan(node);		/* let ReScan handle this */

		if (node->squelched)
			elog(ERROR, "cannot execute squelched plan node of type: %d",
				(int) nodeTag(node));

		if (node->instrument)
			InstrStartNode(node->instrument);

		if(!node->fHadSentGpmon)
			CheckSendPlanStateGpmonPkt(node);

		if(!node->fHadSentNodeStart)
		{
			/* GPDB hook for collecting query info */
			if (query_info_collect_hook)
				(*query_info_collect_hook)(METRICS_PLAN_NODE_EXECUTING, node);
			node->fHadSentNodeStart = true;
		}

		switch (nodeTag(node))
		{
				/*
				* control nodes
				*/
			case T_ResultState:
				result = ExecResult((ResultState *) node);
				break;

			case T_ModifyTableState:
				result = ExecModifyTable((ModifyTableState *) node);
				break;

			case T_AppendState:
				result = ExecAppend((AppendState *) node);
				break;

			case T_MergeAppendState:
				result = ExecMergeAppend((MergeAppendState *) node);
				break;

			case T_RecursiveUnionState:
				result = ExecRecursiveUnion((RecursiveUnionState *) node);
				break;

			case T_SequenceState:
				result = ExecSequence((SequenceState *) node);
				break;

				/* BitmapAndState does not yield tuples */

				/* BitmapOrState does not yield tuples */

				/*
				* scan nodes
				*/
			case T_SeqScanState:
				//result = ExecSeqScan((SeqScanState *)node);
				ExecScanBatch((ScanState *) node,resultSlots);
				break;

				/*GPDB_95_MERGE_FIXME: Do we need DynamicSampleScan here?*/
			case T_DynamicSeqScanState:
				result = ExecDynamicSeqScan((DynamicSeqScanState *) node);
				break;

			case T_ExternalScanState:
				result = ExecExternalScan((ExternalScanState *) node);
				break;

			case T_SampleScanState:
				result = ExecSampleScan((SampleScanState *) node);
				break;

			case T_IndexScanState:
				result = ExecIndexScan((IndexScanState *) node);
				break;

			case T_DynamicIndexScanState:
				result = ExecDynamicIndexScan((DynamicIndexScanState *) node);
				break;

			case T_IndexOnlyScanState:
				result = ExecIndexOnlyScan((IndexOnlyScanState *) node);
				break;

				/* BitmapIndexScanState does not yield tuples */

			case T_BitmapHeapScanState:
				result = ExecBitmapHeapScan((BitmapHeapScanState *) node);
				break;

			case T_DynamicBitmapHeapScanState:
				result = ExecDynamicBitmapHeapScan((DynamicBitmapHeapScanState *) node);
				break;

			case T_TidScanState:
				result = ExecTidScan((TidScanState *) node);
				break;

			case T_SubqueryScanState:
				result = ExecSubqueryScan((SubqueryScanState *) node);
				break;

			case T_FunctionScanState:
				result = ExecFunctionScan((FunctionScanState *) node);
				break;

			case T_TableFunctionState:
				result = ExecTableFunction((TableFunctionState *) node);
				break;

			case T_ValuesScanState:
				result = ExecValuesScan((ValuesScanState *) node);
				break;

			case T_CteScanState:
				result = ExecCteScan((CteScanState *) node);
				break;

			case T_WorkTableScanState:
				result = ExecWorkTableScan((WorkTableScanState *) node);
				break;

			case T_ForeignScanState:
				result = ExecForeignScan((ForeignScanState *) node);
				break;

			case T_CustomScanState:
				result = ExecCustomScan((CustomScanState *) node);
				break;

				/*
				* join nodes
				*/
			case T_NestLoopState:
				result = ExecNestLoop((NestLoopState *) node);
				break;

			case T_MergeJoinState:
				result = ExecMergeJoin((MergeJoinState *) node);
				break;

			case T_HashJoinState:
				result = ExecHashJoin((HashJoinState *) node);
				break;

				/*
				* materialization nodes
				*/
			case T_MaterialState:
				result = ExecMaterial((MaterialState *) node);
				break;

			case T_SortState:
				//result = ExecSort((SortState *) node);
				ExecSortBatch((SortState *) node,resultSlots);
				break;

			case T_AggState:
				result = ExecAgg((AggState *) node);
				break;

			case T_WindowAggState:
				result = ExecWindowAgg((WindowAggState *) node);
				break;

			case T_UniqueState:
				result = ExecUnique((UniqueState *) node);
				break;

			case T_GatherState:
				result = ExecGather((GatherState *) node);
				break;

			case T_HashState:
				result = ExecHash((HashState *) node);
				break;

			case T_SetOpState:
				result = ExecSetOp((SetOpState *) node);
				break;

			case T_LockRowsState:
				result = ExecLockRows((LockRowsState *) node);
				break;

			case T_LimitState:
				result = ExecLimit((LimitState *) node);
				break;

			case T_MotionState:
				result = ExecMotion((MotionState *) node);
				break;

			case T_ShareInputScanState:
				result = ExecShareInputScan((ShareInputScanState *) node);
				break;

			case T_RepeatState:
				result = ExecRepeat((RepeatState *) node);
				break;

			case T_DMLState:
				result = ExecDML((DMLState *) node);
				break;

			case T_SplitUpdateState:
				result = ExecSplitUpdate((SplitUpdateState *) node);
				break;

			case T_RowTriggerState:
				result = ExecRowTrigger((RowTriggerState *) node);
				break;

			case T_AssertOpState:
				result = ExecAssertOp((AssertOpState *) node);
				break;

			case T_PartitionSelectorState:
				result = ExecPartitionSelector((PartitionSelectorState *) node);
				break;

			default:
				elog(ERROR, "unrecognized node type: %d", (int) nodeTag(node));
				result = NULL;
				break;
		}

		if(nodeTag(node) == T_SeqScanState
			 || nodeTag(node)==T_SortState)
		{
			if(resultSlots->slotNum>0){
				if(!TupIsNull(resultSlots->slots[resultSlots->slotNum-1])){
					node->gpmon_pkt.u.qexec.rowsout += resultSlots->slotNum;
				}else{
					node->gpmon_pkt.u.qexec.rowsout += resultSlots->slotNum-1;
				}
			}
	
			if (node->instrument){
				for(int i=0;i<resultSlots->slotNum;++i){
					result = resultSlots->slots[i];
					InstrStopNode(node->instrument, TupIsNull(result) ? 0 : 1);
				}
			}
			CheckSendPlanStateGpmonPkt(node);
		}else{
			resultSlots->slots[0] = result;
			resultSlots->slotNum = 1;
			if (!TupIsNull(result))
			{
				Gpmon_Incr_Rows_Out(&node->gpmon_pkt);
				CheckSendPlanStateGpmonPkt(node);
			}
			if (node->instrument)
				InstrStopNode(node->instrument, TupIsNull(result) ? 0 : 1);
		}
		if (node->plan)
			TRACE_POSTGRESQL_EXECPROCNODE_EXIT(GpIdentity.segindex, currentSliceId, nodeTag(node), node->plan->plan_node_id);
	}
	END_MEMORY_ACCOUNT();
	return;
}
