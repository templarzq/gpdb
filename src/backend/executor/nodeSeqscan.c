/*-------------------------------------------------------------------------
 *
 * nodeSeqscan.c
 *	  Support routines for sequential scans of relations.
 *
 * In GPDB, this also deals with AppendOnly and AOCS tables.
 *
 * Portions Copyright (c) 1996-2016, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/nodeSeqscan.c
 *
 *-------------------------------------------------------------------------
 */
/*
 * INTERFACE ROUTINES
 *		ExecSeqScan				sequentially scans a relation.
 *		ExecSeqNext				retrieve next tuple in sequential order.
 *		ExecInitSeqScan			creates and initializes a seqscan node.
 *		ExecEndSeqScan			releases any storage allocated.
 *		ExecReScanSeqScan		rescans the relation
 *
 *		ExecSeqScanEstimate		estimates DSM space needed for parallel scan
 *		ExecSeqScanInitializeDSM initialize DSM for parallel scan
 *		ExecSeqScanInitializeWorker attach to DSM info in parallel worker
 */
#include "postgres.h"

#include "access/relscan.h"
#include "executor/execdebug.h"
#include "executor/nodeSeqscan.h"
#include "utils/rel.h"

#include "cdb/cdbappendonlyam.h"
#include "cdb/cdbaocsam.h"
#include "utils/snapmgr.h"

static void InitScanRelation(SeqScanState *node, EState *estate, int eflags, Relation currentRelation);
static TupleTableSlot *SeqNext(SeqScanState *node);

static void InitAOCSScanOpaque(SeqScanState *scanState, Relation currentRelation);

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
static TupleTableSlot *
SeqNext(SeqScanState *node)
{
	HeapTuple	tuple;
	EState	   *estate;
	ScanDirection direction;
	TupleTableSlot *slot;

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
		appendonly_getnext(node->ss_currentScanDesc_ao, direction, slot);
	}
	else if (node->ss_currentScanDesc_aocs)
	{
		aocs_getnext(node->ss_currentScanDesc_aocs, direction, slot);
	}
	else
	{
		HeapScanDesc scandesc = node->ss_currentScanDesc_heap;

		tuple = heap_getnext(scandesc, direction);

		/*
		 * save the tuple and the buffer returned to us by the access methods in
		 * our scan tuple slot and return the slot.  Note: we pass 'false' because
		 * tuples returned by heap_getnext() are pointers onto disk pages and were
		 * not created with palloc() and so should not be pfree()'d.  Note also
		 * that ExecStoreTuple will increment the refcount of the buffer; the
		 * refcount will not be dropped until the tuple table slot is cleared.
		 */
		if (tuple)
			ExecStoreHeapTuple(tuple,	/* tuple to store */
						   slot,	/* slot to store in */
						   scandesc->rs_cbuf,		/* buffer associated with this
													 * tuple */
						   false);	/* don't pfree this pointer */
		else
			ExecClearTuple(slot);
	}

	return slot;
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

/* ----------------------------------------------------------------
 *		ExecSeqScan(node)
 *
 *		Scans the relation sequentially and returns the next qualifying
 *		tuple.
 *		We call the ExecScan() routine and pass it the appropriate
 *		access method functions.
 * ----------------------------------------------------------------
 */
TupleTableSlot *
ExecSeqScan(SeqScanState *node)
{
	return ExecScan((ScanState *) node,
					(ExecScanAccessMtd) SeqNext,
					(ExecScanRecheckMtd) SeqRecheck);
}

/* ----------------------------------------------------------------
 *		InitScanRelation
 *
 *		Set up to access the scan relation.
 * ----------------------------------------------------------------
 */
static void
InitScanRelation(SeqScanState *node, EState *estate, int eflags, Relation currentRelation)
{
	node->ss.ss_currentRelation = currentRelation;

	/* and report the scan tuple slot's rowtype */
	ExecAssignScanType(&node->ss, RelationGetDescr(currentRelation));
}


/* ----------------------------------------------------------------
 *		ExecInitSeqScan
 * ----------------------------------------------------------------
 */
SeqScanState *
ExecInitSeqScan(SeqScan *node, EState *estate, int eflags)
{
	Relation	currentRelation;

	/*
	 * get the relation object id from the relid'th entry in the range table,
	 * open that relation and acquire appropriate lock on it.
	 */
	currentRelation = ExecOpenScanRelation(estate, node->scanrelid, eflags);

	return ExecInitSeqScanForPartition(node, estate, eflags, currentRelation);
}

SeqScanState *
ExecInitSeqScanForPartition(SeqScan *node, EState *estate, int eflags,
							Relation currentRelation)
{
	SeqScanState *scanstate;

	/*
	 * Once upon a time it was possible to have an outerPlan of a SeqScan, but
	 * not any more.
	 */
	Assert(outerPlan(node) == NULL);
	Assert(innerPlan(node) == NULL);

	/*
	 * create state structure
	 */
	scanstate = makeNode(SeqScanState);
	scanstate->ss.ps.plan = (Plan *) node;
	scanstate->ss.ps.state = estate;

	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &scanstate->ss.ps);

	/*
	 * initialize child expressions
	 */
	scanstate->ss.ps.targetlist = (List *)
		ExecInitExpr((Expr *) node->plan.targetlist,
					 (PlanState *) scanstate);
	scanstate->ss.ps.qual = (List *)
		ExecInitExpr((Expr *) node->plan.qual,
					 (PlanState *) scanstate);

	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &scanstate->ss.ps);
	ExecInitScanTupleSlot(estate, &scanstate->ss);

	/*
	 * initialize scan relation
	 */
	InitScanRelation(scanstate, estate, eflags, currentRelation);

	/*
	 * Initialize result tuple type and projection info.
	 */
	ExecAssignResultTypeFromTL(&scanstate->ss.ps);
	ExecAssignScanProjectionInfo(&scanstate->ss);
	memset(scanstate->ss.ss_resultSlots.slots,0,sizeof(scanstate->ss.ss_resultSlots.slots));
	return scanstate;
}

/* ----------------------------------------------------------------
 *		ExecEndSeqScan
 *
 *		frees any storage allocated through C routines.
 * ----------------------------------------------------------------
 */
void
ExecEndSeqScan(SeqScanState *node)
{
	Relation	relation;

	/*
	 * get information from node
	 */
	relation = node->ss.ss_currentRelation;

	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->ss.ps);

	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->ss.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->ss.ss_ScanTupleSlot);

	/*
	 * close heap scan
	 */
	if (node->ss_currentScanDesc_heap)
	{
		heap_endscan(node->ss_currentScanDesc_heap);
		node->ss_currentScanDesc_heap = NULL;
	}
	if (node->ss_currentScanDesc_ao)
	{
		appendonly_endscan(node->ss_currentScanDesc_ao);
		node->ss_currentScanDesc_ao = NULL;
	}
	if (node->ss_currentScanDesc_aocs)
	{
		aocs_endscan(node->ss_currentScanDesc_aocs);
		node->ss_currentScanDesc_aocs = NULL;
	}

	/*
	 * close the heap relation.
	 */
	ExecCloseScanRelation(relation);
}

/* ----------------------------------------------------------------
 *						Join Support
 * ----------------------------------------------------------------
 */

/* ----------------------------------------------------------------
 *		ExecReScanSeqScan
 *
 *		Rescans the relation.
 * ----------------------------------------------------------------
 */
void
ExecReScanSeqScan(SeqScanState *node)
{
	if (node->ss_currentScanDesc_ao)
	{
		appendonly_rescan(node->ss_currentScanDesc_ao,
						  NULL);			/* new scan keys */
	}
	else if (node->ss_currentScanDesc_aocs)
	{
		aocs_rescan(node->ss_currentScanDesc_aocs);
	}
	else if (node->ss_currentScanDesc_heap)
	{
		heap_rescan(node->ss_currentScanDesc_heap, /* scan desc */
					NULL);		/* new scan keys */
	}
	else
	{
		/* scan not started yet, nothing to do. */
	}

	ExecScanReScan((ScanState *) node);
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

/* ----------------------------------------------------------------
 *						Parallel Scan Support
 * ----------------------------------------------------------------
 */

/* ----------------------------------------------------------------
 *		ExecSeqScanEstimate
 *
 *		estimates the space required to serialize seqscan node.
 * ----------------------------------------------------------------
 */
void
ExecSeqScanEstimate(SeqScanState *node,
					ParallelContext *pcxt)
{
	EState	   *estate = node->ss.ps.state;

	node->pscan_len = heap_parallelscan_estimate(estate->es_snapshot);
	shm_toc_estimate_chunk(&pcxt->estimator, node->pscan_len);
	shm_toc_estimate_keys(&pcxt->estimator, 1);
}

/* ----------------------------------------------------------------
 *		ExecSeqScanInitializeDSM
 *
 *		Set up a parallel heap scan descriptor.
 * ----------------------------------------------------------------
 */
void
ExecSeqScanInitializeDSM(SeqScanState *node,
						 ParallelContext *pcxt)
{
	EState	   *estate = node->ss.ps.state;
	ParallelHeapScanDesc pscan;

	if (!RelationIsHeap(node->ss.ss_currentRelation))
		elog(ERROR, "parallel SeqScan not implemented for AO or AOCO tables");

	pscan = shm_toc_allocate(pcxt->toc, node->pscan_len);
	heap_parallelscan_initialize(pscan,
								 node->ss.ss_currentRelation,
								 estate->es_snapshot);
	shm_toc_insert(pcxt->toc, node->ss.ps.plan->plan_node_id, pscan);
	node->ss_currentScanDesc_heap =
		heap_beginscan_parallel(node->ss.ss_currentRelation, pscan);
}

/* ----------------------------------------------------------------
 *		ExecSeqScanInitializeWorker
 *
 *		Copy relevant information from TOC into planstate.
 * ----------------------------------------------------------------
 */
void
ExecSeqScanInitializeWorker(SeqScanState *node, shm_toc *toc)
{
	ParallelHeapScanDesc pscan;

	if (!RelationIsHeap(node->ss.ss_currentRelation))
		elog(ERROR, "parallel SeqScan not implemented for AO or AOCO tables");

	pscan = shm_toc_lookup(toc, node->ss.ps.plan->plan_node_id);
	node->ss_currentScanDesc_heap =
		heap_beginscan_parallel(node->ss.ss_currentRelation, pscan);
}
