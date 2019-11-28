/*-------------------------------------------------------------------------
 *
 * execScan.c
 *	  This code provides support for generalized relation scans. ExecScan
 *	  is passed a node and a pointer to a function to "do the right thing"
 *	  and return a tuple from the relation. ExecScan then does the tedious
 *	  stuff - checking the qualification and projecting the tuple
 *	  appropriately.
 *
 * Portions Copyright (c) 2006 - present, EMC/Greenplum
 * Portions Copyright (c) 2012-Present Pivotal Software, Inc.
 * Portions Copyright (c) 1996-2016, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execScan.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "executor/executor.h"
#include "miscadmin.h"
#include "utils/memutils.h"

#include "utils/snapmgr.h"
#include "cdb/cdbappendonlyam.h"
#include "cdb/cdbaocsam.h"

static void
InitAOCSScanOpaque(SeqScanState *scanstate, Relation currentRelation);

/* ----------------------------------------------------------------
 *		ExecScan
 *
 *		Scans the relation using the 'access method' indicated and
 *		returns the next qualifying tuple in the direction specified
 *		in the global variable ExecDirection.
 *		The access method returns the next tuple and ExecScan() is
 *		responsible for checking the tuple returned against the qual-clause.
 *
 *		A 'recheck method' must also be provided that can check an
 *		arbitrary tuple of the relation against any qual conditions
 *		that are implemented internal to the access method.
 *
 *		Conditions:
 *		  -- the "cursor" maintained by the AMI is positioned at the tuple
 *			 returned previously.
 *
 *		Initial States:
 *		  -- the relation indicated is opened for scanning so that the
 *			 "cursor" is positioned before the first qualifying tuple.
 * ----------------------------------------------------------------
 */

/*
 * ExecScanFetch -- fetch next potential tuple
 *
 * This routine is concerned with substituting a test tuple if we are
 * inside an EvalPlanQual recheck.  If we aren't, just execute
 * the access method's next-tuple routine.
 */
static inline 
void ExecScanFetchBatch(ScanState *node,
			  ExecScanAccessMtd accessMtd,
			  ExecScanRecheckMtd recheckMtd
			  )
{
	EState	   *estate = node->ps.state;

	if (estate->es_epqTuple != NULL)
	{
		/*
		 * We are inside an EvalPlanQual recheck.  Return the test tuple if
		 * one is available, after rechecking any access-method-specific
		 * conditions.
		 */
		Index		scanrelid = ((Scan *) node->ps.plan)->scanrelid;

		if (scanrelid == 0)
		{
			TupleTableSlot *slot = node->ss_ScanTupleSlot;

			/*
			 * This is a ForeignScan or CustomScan which has pushed down a
			 * join to the remote side.  The recheck method is responsible not
			 * only for rechecking the scan/join quals but also for storing
			 * the correct tuple in the slot.
			 */
			if (!(*recheckMtd) (node, slot)){
				ExecClearTuple(slot);	/* would not be returned by scan */
				node->ss_resultSlots.slots[0] = slot;
				node->ss_resultSlots.slotNum = 1;
				return;
			}
		}
		else if (estate->es_epqTupleSet[scanrelid - 1])
		{
			TupleTableSlot *slot = node->ss_ScanTupleSlot;

			/* Return empty slot if we already returned a tuple */
			if (estate->es_epqScanDone[scanrelid - 1]){
				ExecClearTuple(slot);
				node->ss_resultSlots.slots[0] = slot;
				node->ss_resultSlots.slotNum = 1;
				return;
			}
			/* Else mark to remember that we shouldn't return more */
			estate->es_epqScanDone[scanrelid - 1] = true;

			/* Return empty slot if we haven't got a test tuple */
			if (estate->es_epqTuple[scanrelid - 1] == NULL){
				ExecClearTuple(slot);
				node->ss_resultSlots.slots[0] = slot;
				node->ss_resultSlots.slotNum = 1;
				return;
			}
				

			/* Store test tuple in the plan node's scan slot */
			ExecStoreHeapTuple(estate->es_epqTuple[scanrelid - 1],
						   slot, InvalidBuffer, false);

			/* Check if it meets the access-method conditions */
			if (!(*recheckMtd) (node, slot)){
				ExecClearTuple(slot);	/* would not be returned by scan */
				node->ss_resultSlots.slots[0] = slot;
				node->ss_resultSlots.slotNum = 1;
				return;
			}
		}
	}

	/*
	 * Run the node-type-specific access method function to get the next tuple
	 */
	return (*accessMtd) (node);
}

void
ExecSeqScanBatch(ScanState *node,
		 ExecScanAccessMtd accessMtd,	/* function returning a tuple */
		 ExecScanRecheckMtd recheckMtd,
		 TupleTableSlots *resultSlots)
{
	ExprContext *econtext;
	List	   *qual;
	ProjectionInfo *projInfo;
	int batchSize = 0;
	int resultRows = 0 ;

	/*
	*	重置slot数据量
	*/
	Assert(resultSlots);
	resultSlots->slotNum = 0;
	batchSize = sizeof(resultSlots->slots)/sizeof(TupleTableSlot*);
	
	/*
	 * Fetch data from node
	 */
	qual = node->ps.qual;
	projInfo = node->ps.ps_ProjInfo;
	econtext = node->ps.ps_ExprContext;

	/*
	 * If we have neither a qual to check nor a projection to do, just skip
	 * all the overhead and return the raw scan tuple.
	 */
	if (!qual && !projInfo)
	{
		TupleTableSlot *slot;
		ExecScanFetchBatch(node, accessMtd, recheckMtd);
		*resultSlots = node->ss_resultSlots;
		return;
	}

	/*
	* Reset per-tuple memory context to free any expression evaluation
	* storage allocated in the previous tuple cycle.
	*/
	ResetExprContext(econtext);

	CHECK_FOR_INTERRUPTS();

	if (QueryFinishPending)
		return ;

	/*
	 * get a tuple from the access method.  Loop until we obtain a tuple that
	 * passes the qualification.
	 */

	for (;;)
	{
		TupleTableSlot *slot;

		//上个批次处理完毕
		if(node->ss_resultSlots.handledCnt == node->ss_resultSlots.slotNum){
			ResetExprContext(econtext);
			ExecScanFetchBatch(node, accessMtd, recheckMtd);
			node->ss_resultSlots.handledCnt = 0;
		}


		for(int i=node->ss_resultSlots.handledCnt;i<node->ss_resultSlots.slotNum;++i){

			slot = node->ss_resultSlots.slots[i];
			/*
			* if the slot returned by the accessMtd contains NULL, then it means
			* there is nothing more to scan so we just return an empty slot,
			* being careful to use the projection result slot so it has correct
			* tupleDesc.
			*/
			if (TupIsNull(slot))
			{
				if (projInfo){
					slot = ExecClearTuple(projInfo->pi_slot);
				}
				//所有结果处理完毕
				resultSlots->slots[resultRows] = slot;
				resultSlots->slotNum += 1;
				resultRows += 1;
				node->ss_resultSlots.slotNum = 0;
				node->ss_resultSlots.handledCnt = 0;
				return;
			}

			/*
			* place the current tuple into the expr context
			*/
			econtext->ecxt_scantuple = slot;
			/*
			* check that the current tuple satisfies the qual-clause
			*
			* check for non-nil qual here to avoid a function call to ExecQual()
			* when the qual is nil ... saves only a few cycles, but they add up
			* ...
			*/
			if (!qual || ExecQual(qual, econtext, false))
			{
				/*
				* Found a satisfactory scan tuple.
				*/
				if (projInfo)
				{
					/*
					* Form a projection tuple, store it in the result tuple slot
					* and return it.
					*/
					TupleTableSlot* newSlot;
					HeapTuple	tuple;
					slot = ExecProject(projInfo, NULL);
					newSlot = ExecInitExtraTupleSlot(((SeqScanState*)node)->ss.ps.state);
					ExecSetSlotDescriptor(newSlot, ((SeqScanState*)node)->ss.ss_ScanTupleSlot->tts_tupleDescriptor);
					{
						Datum *slotvalues = slot_get_values(slot);
						bool  *slotnulls = slot_get_isnull(slot);
						Datum *newslotvalues = slot_get_values(newSlot);
						bool *newslotnulls = slot_get_isnull(newSlot);
						int nv = slot->PRIVATE_tts_nvalid;
						memcpy(newslotvalues, slotvalues, sizeof(Datum) * nv);
						memcpy(newslotnulls, slotnulls, sizeof(bool) * nv);
						TupSetVirtualTupleNValid(newSlot, nv);
						newSlot->tts_tupleDescriptor = slot->tts_tupleDescriptor;
					}
					resultSlots->slots[resultRows] = newSlot;
					resultSlots->slotNum += 1;
					node->ss_resultSlots.handledCnt ++;
					resultRows += 1;
					if(resultRows == batchSize){
						return;
					}
				}
				else
				{
					/*
					* Here, we aren't projecting, so just return scan tuple.
					*/
					resultSlots->slots[resultRows] = slot;
					resultSlots->slotNum += 1;
					node->ss_resultSlots.handledCnt ++;
					resultRows += 1;
					if(resultRows == batchSize){
						return;
					}
				}
			} else {
				InstrCountFiltered1(node, 1);
			}
		}
	}
}


/* ----------------------------------------------------------------
 *						Scan Support
 * ----------------------------------------------------------------
 */

/* ----------------------------------------------------------------
 *		SeqNext
 *
 *		This is a workhorse for ExecSeqScan
 * ----------------------------------------------------------------
 */
static void SeqNextBatch(SeqScanState *node)
{
	HeapTuple	tuple;
	EState	   *estate;
	ScanDirection direction;
	TupleTableSlot *slot;
	int batchSize = 0;

	batchSize = sizeof(node->ss.ss_resultSlots.slots)/sizeof(TupleTableSlot*);
	node->ss.ss_resultSlots.slotNum = 0;

	/*
	 * get information from the estate and scan state
	 */
	estate = node->ss.ps.state;
	direction = estate->es_direction;
	slot = node->ss.ss_ScanTupleSlot;

	if (node->ss_currentScanDesc_ao == NULL &&
		node->ss_currentScanDesc_aocs == NULL &&
		node->ss_currentScanDesc_heap == NULL)
	{
		/*
		 * We reach here if the scan is not parallel, or if we're executing a
		 * scan that was intended to be parallel serially.
		 */
		Relation currentRelation = node->ss.ss_currentRelation;

		if (RelationIsAoRows(currentRelation))
		{
			Snapshot appendOnlyMetaDataSnapshot;

			appendOnlyMetaDataSnapshot = node->ss.ps.state->es_snapshot;
			if (appendOnlyMetaDataSnapshot == SnapshotAny)
			{
				/*
				 * the append-only meta data should never be fetched with
				 * SnapshotAny as bogus results are returned.
				 */
				appendOnlyMetaDataSnapshot = GetTransactionSnapshot();
			}

			node->ss_currentScanDesc_ao = appendonly_beginscan(
				currentRelation,
				node->ss.ps.state->es_snapshot,
				appendOnlyMetaDataSnapshot,
				0, NULL);
		}
		else if (RelationIsAoCols(currentRelation))
		{
			Snapshot appendOnlyMetaDataSnapshot;

			InitAOCSScanOpaque(node, currentRelation);

			appendOnlyMetaDataSnapshot = node->ss.ps.state->es_snapshot;
			if (appendOnlyMetaDataSnapshot == SnapshotAny)
			{
				/*
				 * the append-only meta data should never be fetched with
				 * SnapshotAny as bogus results are returned.
				 */
				appendOnlyMetaDataSnapshot = GetTransactionSnapshot();
			}

			node->ss_currentScanDesc_aocs =
				aocs_beginscan(currentRelation,
							   node->ss.ps.state->es_snapshot,
							   appendOnlyMetaDataSnapshot,
							   NULL /* relationTupleDesc */,
							   node->ss_aocs_proj);
		}
		else
		{
			node->ss_currentScanDesc_heap = heap_beginscan(currentRelation,
														   estate->es_snapshot,
														   0, NULL);
		}
	}

	/*
	* get the next tuple from the table
	*/
	if (node->ss_currentScanDesc_ao)
	{
		for(int i=0;i<batchSize;++i){
			slot = node->ss.ss_resultSlots.slots[i];
			if(slot!=NULL){
				slot = ExecClearTuple(slot);
			}else{
				slot = ExecInitExtraTupleSlot(estate);
				ExecSetSlotDescriptor(slot, node->ss.ss_ScanTupleSlot->tts_tupleDescriptor);
			}
			appendonly_getnext(node->ss_currentScanDesc_ao, direction, slot);

			node->ss.ss_resultSlots.slots[i] = slot;

			node->ss.ss_resultSlots.slotNum += 1;
			if(TupIsNull(slot)){
				break;
			}
		}
	}
	else if (node->ss_currentScanDesc_aocs)
	{
		for(int i=0;i<batchSize;++i){
			slot = node->ss.ss_resultSlots.slots[i];
			if(slot!=NULL){
				slot = ExecClearTuple(slot);
			}else{
				slot = ExecInitExtraTupleSlot(estate);
				ExecSetSlotDescriptor(slot, node->ss.ss_ScanTupleSlot->tts_tupleDescriptor);
			}
			
			aocs_getnext(node->ss_currentScanDesc_aocs, direction, slot);
			
			node->ss.ss_resultSlots.slots[i] = slot;
			node->ss.ss_resultSlots.slotNum += 1;
			if(TupIsNull(slot)){
				break;
			}
		}
	}
	else
	{

		HeapScanDesc scandesc = node->ss_currentScanDesc_heap;

		for(int i=0;i<batchSize;++i){
			tuple = heap_getnext(scandesc, direction);
			slot = node->ss.ss_resultSlots.slots[i];
			if(slot != NULL){
				slot = ExecClearTuple(slot);
			}else{
				slot = ExecInitExtraTupleSlot(estate);
				ExecSetSlotDescriptor(slot, node->ss.ss_ScanTupleSlot->tts_tupleDescriptor);
			}
			heap_copytuple_with_tuple(tuple,node->ss.ss_resultSlots.htups+i);
			/*
			* save the tuple and the buffer returned to us by the access methods in
			* our scan tuple slot and return the slot.  Note: we pass 'false' because
			* tuples returned by heap_getnext() are pointers onto disk pages and were
			* not created with palloc() and so should not be pfree()'d.  Note also
			* that ExecStoreTuple will increment the refcount of the buffer; the
			* refcount will not be dropped until the tuple table slot is cleared.
			*/
			if (tuple){
				slot = ExecStoreHeapTuple( node->ss.ss_resultSlots.htups+i,	/* tuple to store */
									slot,	/* slot to store in */
									scandesc->rs_cbuf,		/* buffer associated with this
																* tuple */
									false);	/* don't pfree this pointer */
				node->ss.ss_resultSlots.slots[i] = slot;
				node->ss.ss_resultSlots.slotNum += 1;
			} else {
				ExecClearTuple(slot);
				node->ss.ss_resultSlots.slots[i] = slot;
				node->ss.ss_resultSlots.slotNum += 1;
				break;
			}
				
		}
	}
	return;
}


static void
InitAOCSScanOpaque(SeqScanState *scanstate, Relation currentRelation)
{
	/* Initialize AOCS projection info */
	bool	   *proj;
	int			ncol;
	int			i;

	Assert(currentRelation != NULL);

	ncol = currentRelation->rd_att->natts;
	proj = palloc0(ncol * sizeof(bool));
	GetNeededColumnsForScan((Node *) scanstate->ss.ps.plan->targetlist, proj, ncol);
	GetNeededColumnsForScan((Node *) scanstate->ss.ps.plan->qual, proj, ncol);

	for (i = 0; i < ncol; i++)
	{
		if (proj[i])
			break;
	}

	/*
	 * In some cases (for example, count(*)), no columns are specified.
	 * We always scan the first column.
	 */
	if (i == ncol)
		proj[0] = true;

	scanstate->ss_aocs_ncol = ncol;
	scanstate->ss_aocs_proj = proj;
}

/*
 * SeqRecheck -- access method routine to recheck a tuple in EvalPlanQual
 */
static bool
SeqRecheck(SeqScanState *node, TupleTableSlot *slot)
{
	/*
	 * Note that unlike IndexScan, SeqScan never use keys in heap_beginscan
	 * (and this is very bad) - so, here we do not check are keys ok or not.
	 */
	return true;
}

void ExecScanBatch(ScanState *node,TupleTableSlots *resultSlots){
	ExecSeqScanBatch(node,
					(ExecScanAccessMtd) SeqNextBatch,
					(ExecScanRecheckMtd) SeqRecheck,
					resultSlots);
}