/*-------------------------------------------------------------------------
 *
 * predicate_internals.h
 *	  POSTGRES internal predicate locking definitions.
 *
 *
 * Portions Copyright (c) 1996-2011, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/storage/predicate_internals.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef PREDICATE_INTERNALS_H
#define PREDICATE_INTERNALS_H

#include "storage/lock.h"

/*
 * Commit number.
 */
typedef uint64 SerCommitSeqNo;

/*
 * Reserved commit sequence numbers:
 *	- 0 is reserved to indicate a non-existent SLRU entry; it cannot be
 *	  used as a SerCommitSeqNo, even an invalid one
 *	- InvalidSerCommitSeqNo is used to indicate a transaction that
 *	  hasn't committed yet, so use a number greater than all valid
 *	  ones to make comparison do the expected thing
 *	- RecoverySerCommitSeqNo is used to refer to transactions that
 *	  happened before a crash/recovery, since we restart the sequence
 *	  at that point.  It's earlier than all normal sequence numbers,
 *	  and is only used by recovered prepared transactions
 */
#define InvalidSerCommitSeqNo		((SerCommitSeqNo) UINT64CONST(0xFFFFFFFFFFFFFFFF))
#define RecoverySerCommitSeqNo		((SerCommitSeqNo) 1)
#define FirstNormalSerCommitSeqNo	((SerCommitSeqNo) 2)

/*
 * The SERIALIZABLEXACT struct contains information needed for each
 * serializable database transaction to support SSI techniques.
 *
 * A home-grown list is maintained in shared memory to manage these.
 * An entry is used when the serializable transaction acquires a snapshot.
 * Unless the transaction is rolled back, this entry must generally remain
 * until all concurrent transactions have completed.  (There are special
 * optimizations for READ ONLY transactions which often allow them to be
 * cleaned up earlier.)  A transaction which is rolled back is cleaned up
 * as soon as possible.
 *
 * Eligibility for cleanup of committed transactions is generally determined
 * by comparing the transaction's finishedBefore field to
 * SerializableGlobalXmin.
 */
typedef struct SERIALIZABLEXACT
{
	VirtualTransactionId vxid;	/* The executing process always has one of
								 * these. */
	SerCommitSeqNo commitSeqNo;
	union						/* these values are not both interesting at
								 * the same time */
	{
		SerCommitSeqNo earliestOutConflictCommit;		/* when committed with
														 * conflict out */
		SerCommitSeqNo lastCommitBeforeSnapshot;		/* when not committed or
														 * no conflict out */
	}			SeqNo;
	SHM_QUEUE	outConflicts;	/* list of write transactions whose data we
								 * couldn't read. */
	SHM_QUEUE	inConflicts;	/* list of read transactions which couldn't
								 * see our write. */
	SHM_QUEUE	predicateLocks; /* list of associated PREDICATELOCK objects */
	SHM_QUEUE	finishedLink;	/* list link in
								 * FinishedSerializableTransactions */

	/*
	 * for r/o transactions: list of concurrent r/w transactions that we could
	 * potentially have conflicts with, and vice versa for r/w transactions
	 */
	SHM_QUEUE	possibleUnsafeConflicts;

	TransactionId topXid;		/* top level xid for the transaction, if one
								 * exists; else invalid */
	TransactionId finishedBefore;		/* invalid means still running; else
										 * the struct expires when no
										 * serializable xids are before this. */
	TransactionId xmin;			/* the transaction's snapshot xmin */
	uint32		flags;			/* OR'd combination of values defined below */
	int			pid;			/* pid of associated process */
} SERIALIZABLEXACT;

#define SXACT_FLAG_ROLLED_BACK				0x00000001
#define SXACT_FLAG_COMMITTED				0x00000002
#define SXACT_FLAG_CONFLICT_OUT				0x00000004
#define SXACT_FLAG_READ_ONLY				0x00000008
#define SXACT_FLAG_DID_WRITE				0x00000010
#define SXACT_FLAG_MARKED_FOR_DEATH			0x00000020
#define SXACT_FLAG_DEFERRABLE_WAITING		0x00000040
#define SXACT_FLAG_RO_SAFE					0x00000080
#define SXACT_FLAG_RO_UNSAFE				0x00000100
#define SXACT_FLAG_SUMMARY_CONFLICT_IN		0x00000200
#define SXACT_FLAG_SUMMARY_CONFLICT_OUT		0x00000400
#define SXACT_FLAG_PREPARED					0x00000800

/*
 * The following types are used to provide an ad hoc list for holding
 * SERIALIZABLEXACT objects.  An HTAB is overkill, since there is no need to
 * access these by key -- there are direct pointers to these objects where
 * needed.	If a shared memory list is created, these types can probably be
 * eliminated in favor of using the general solution.
 */
typedef struct PredXactListElementData
{
	SHM_QUEUE	link;
	SERIALIZABLEXACT sxact;
} PredXactListElementData;

typedef struct PredXactListElementData *PredXactListElement;

#define PredXactListElementDataSize \
		((Size)MAXALIGN(sizeof(PredXactListElementData)))

typedef struct PredXactListData
{
	SHM_QUEUE	availableList;
	SHM_QUEUE	activeList;

	/*
	 * These global variables are maintained when registering and cleaning up
	 * serializable transactions.  They must be global across all backends,
	 * but are not needed outside the predicate.c source file.
	 */
	TransactionId SxactGlobalXmin;		/* global xmin for active serializable
										 * transactions */
	int			SxactGlobalXminCount;	/* how many active serializable
										 * transactions have this xmin */
	int			WritableSxactCount;		/* how many non-read-only serializable
										 * transactions are active */
	SerCommitSeqNo LastSxactCommitSeqNo;		/* a strictly monotonically
												 * increasing number for
												 * commits of serializable
												 * transactions */
	/* Protected by SerializableXactHashLock. */
	SerCommitSeqNo CanPartialClearThrough;		/* can clear predicate locks
												 * and inConflicts for
												 * committed transactions
												 * through this seq no */
	/* Protected by SerializableFinishedListLock. */
	SerCommitSeqNo HavePartialClearedThrough;	/* have cleared through this
												 * seq no */
	SERIALIZABLEXACT *OldCommittedSxact;		/* shared copy of dummy sxact */
	bool		NeedTargetLinkCleanup;	/* to save cleanup effort for rare
										 * case */

	PredXactListElement element;
} PredXactListData;

typedef struct PredXactListData *PredXactList;

#define PredXactListDataSize \
		((Size)MAXALIGN(sizeof(PredXactListData)))


/*
 * The following types are used to provide lists of rw-conflicts between
 * pairs of transactions.  Since exactly the same information is needed,
 * they are also used to record possible unsafe transaction relationships
 * for purposes of identifying safe snapshots for read-only transactions.
 *
 * When a RWConflictData is not in use to record either type of relationship
 * between a pair of transactions, it is kept on an "available" list.  The
 * outLink field is used for maintaining that list.
 */
typedef struct RWConflictData
{
	SHM_QUEUE	outLink;		/* link for list of conflicts out from a sxact */
	SHM_QUEUE	inLink;			/* link for list of conflicts in to a sxact */
	SERIALIZABLEXACT *sxactOut;
	SERIALIZABLEXACT *sxactIn;
} RWConflictData;

typedef struct RWConflictData *RWConflict;

#define RWConflictDataSize \
		((Size)MAXALIGN(sizeof(RWConflictData)))

typedef struct RWConflictPoolHeaderData
{
	SHM_QUEUE	availableList;
	RWConflict	element;
} RWConflictPoolHeaderData;

typedef struct RWConflictPoolHeaderData *RWConflictPoolHeader;

#define RWConflictPoolHeaderDataSize \
		((Size)MAXALIGN(sizeof(RWConflictPoolHeaderData)))


/*
 * The SERIALIZABLEXIDTAG struct identifies an xid assigned to a serializable
 * transaction or any of its subtransactions.
 */
typedef struct SERIALIZABLEXIDTAG
{
	TransactionId xid;
} SERIALIZABLEXIDTAG;

/*
 * The SERIALIZABLEXID struct provides a link from a TransactionId for a
 * serializable transaction to the related SERIALIZABLEXACT record, even if
 * the transaction has completed and its connection has been closed.
 *
 * These are created as new top level transaction IDs are first assigned to
 * transactions which are participating in predicate locking.  This may
 * never happen for a particular transaction if it doesn't write anything.
 * They are removed with their related serializable transaction objects.
 *
 * The SubTransGetTopmostTransaction method is used where necessary to get
 * from an XID which might be from a subtransaction to the top level XID.
 */
typedef struct SERIALIZABLEXID
{
	/* hash key */
	SERIALIZABLEXIDTAG tag;

	/* data */
	SERIALIZABLEXACT *myXact;	/* pointer to the top level transaction data */
} SERIALIZABLEXID;


/*
 * The PREDICATELOCKTARGETTAG struct identifies a database object which can
 * be the target of predicate locks.  It is designed to fit into 16 bytes
 * with no padding.  Note that this would need adjustment if we widen Oid or
 * BlockNumber to more than 32 bits.
 *
 * TODO SSI: If we always use the same fields for the same type of value, we
 * should rename these.  Holding off until it's clear there are no exceptions.
 * Since indexes are relations with blocks and tuples, it's looking likely that
 * the rename will be possible.  If not, we may need to divide the last field
 * and use part of it for a target type, so that we know how to interpret the
 * data..
 */
typedef struct PREDICATELOCKTARGETTAG
{
	uint32		locktag_field1; /* a 32-bit ID field */
	uint32		locktag_field2; /* a 32-bit ID field */
	uint32		locktag_field3; /* a 32-bit ID field */
	uint16		locktag_field4; /* a 16-bit ID field */
	uint16		locktag_field5; /* a 16-bit ID field */
} PREDICATELOCKTARGETTAG;

/*
 * The PREDICATELOCKTARGET struct represents a database object on which there
 * are predicate locks.
 *
 * A hash list of these objects is maintained in shared memory.  An entry is
 * added when a predicate lock is requested on an object which doesn't
 * already have one.  An entry is removed when the last lock is removed from
 * its list.
 *
 * Because a check for predicate locks on a tuple target should also find
 * locks on previous versions of the same row, if there are any created by
 * overlapping transactions, we keep a pointer to the target for the prior
 * version of the row.	We also keep a pointer to the next version of the
 * row, so that when we no longer have any predicate locks and the back
 * pointer is clear, we can clean up the prior pointer for the next version.
 */
typedef struct PREDICATELOCKTARGET PREDICATELOCKTARGET;

struct PREDICATELOCKTARGET
{
	/* hash key */
	PREDICATELOCKTARGETTAG tag; /* unique identifier of lockable object */

	/* data */
	SHM_QUEUE	predicateLocks; /* list of PREDICATELOCK objects assoc. with
								 * predicate lock target */

	/*
	 * The following two pointers are only used for tuple locks, and are only
	 * consulted for conflict detection and cleanup; not for granularity
	 * promotion.
	 */
	PREDICATELOCKTARGET *priorVersionOfRow;		/* what other locks to check */
	PREDICATELOCKTARGET *nextVersionOfRow;		/* who has pointer here for
												 * more targets */
};


/*
 * The PREDICATELOCKTAG struct identifies an individual predicate lock.
 *
 * It is the combination of predicate lock target (which is a lockable
 * object) and a serializable transaction which has acquired a lock on that
 * target.
 */
typedef struct PREDICATELOCKTAG
{
	PREDICATELOCKTARGET *myTarget;
	SERIALIZABLEXACT *myXact;
} PREDICATELOCKTAG;

/*
 * The PREDICATELOCK struct represents an individual lock.
 *
 * An entry can be created here when the related database object is read, or
 * by promotion of multiple finer-grained targets.	All entries related to a
 * serializable transaction are removed when that serializable transaction is
 * cleaned up.	Entries can also be removed when they are combined into a
 * single coarser-grained lock entry.
 */
typedef struct PREDICATELOCK
{
	/* hash key */
	PREDICATELOCKTAG tag;		/* unique identifier of lock */

	/* data */
	SHM_QUEUE	targetLink;		/* list link in PREDICATELOCKTARGET's list of
								 * predicate locks */
	SHM_QUEUE	xactLink;		/* list link in SERIALIZABLEXACT's list of
								 * predicate locks */
	SerCommitSeqNo commitSeqNo; /* only used for summarized predicate locks */
} PREDICATELOCK;


/*
 * The LOCALPREDICATELOCK struct represents a local copy of data which is
 * also present in the PREDICATELOCK table, organized for fast access without
 * needing to acquire a LWLock.  It is strictly for optimization.
 *
 * Each serializable transaction creates its own local hash table to hold a
 * collection of these.  This information is used to determine when a number
 * of fine-grained locks should be promoted to a single coarser-grained lock.
 * The information is maintained more-or-less in parallel to the
 * PREDICATELOCK data, but because this data is not protected by locks and is
 * only used in an optimization heuristic, it is allowed to drift in a few
 * corner cases where maintaining exact data would be expensive.
 *
 * The hash table is created when the serializable transaction acquires its
 * snapshot, and its memory is released upon completion of the transaction.
 */
typedef struct LOCALPREDICATELOCK
{
	/* hash key */
	PREDICATELOCKTARGETTAG tag; /* unique identifier of lockable object */

	/* data */
	bool		held;			/* is lock held, or just its children?	*/
	int			childLocks;		/* number of child locks currently held */
} LOCALPREDICATELOCK;


/*
 * The types of predicate locks which can be acquired.
 */
typedef enum PredicateLockTargetType
{
	PREDLOCKTAG_RELATION,
	PREDLOCKTAG_PAGE,
	PREDLOCKTAG_TUPLE
	/* TODO SSI: Other types may be needed for index locking */
}	PredicateLockTargetType;


/*
 * This structure is used to quickly capture a copy of all predicate
 * locks.  This is currently used only by the pg_lock_status function,
 * which in turn is used by the pg_locks view.
 */
typedef struct PredicateLockData
{
	int			nelements;
	PREDICATELOCKTARGETTAG *locktags;
	SERIALIZABLEXACT *xacts;
} PredicateLockData;


/*
 * These macros define how we map logical IDs of lockable objects into the
 * physical fields of PREDICATELOCKTARGETTAG.	Use these to set up values,
 * rather than accessing the fields directly.  Note multiple eval of target!
 */
#define SET_PREDICATELOCKTARGETTAG_RELATION(locktag,dboid,reloid) \
	((locktag).locktag_field1 = (dboid), \
	 (locktag).locktag_field2 = (reloid), \
	 (locktag).locktag_field3 = InvalidBlockNumber, \
	 (locktag).locktag_field4 = InvalidOffsetNumber, \
	 (locktag).locktag_field5 = 0)

#define SET_PREDICATELOCKTARGETTAG_PAGE(locktag,dboid,reloid,blocknum) \
	((locktag).locktag_field1 = (dboid), \
	 (locktag).locktag_field2 = (reloid), \
	 (locktag).locktag_field3 = (blocknum), \
	 (locktag).locktag_field4 = InvalidOffsetNumber, \
	 (locktag).locktag_field5 = 0)

#define SET_PREDICATELOCKTARGETTAG_TUPLE(locktag,dboid,reloid,blocknum,offnum) \
	((locktag).locktag_field1 = (dboid), \
	 (locktag).locktag_field2 = (reloid), \
	 (locktag).locktag_field3 = (blocknum), \
	 (locktag).locktag_field4 = (offnum), \
	 (locktag).locktag_field5 = 0)

#define GET_PREDICATELOCKTARGETTAG_DB(locktag) \
	((locktag).locktag_field1)
#define GET_PREDICATELOCKTARGETTAG_RELATION(locktag) \
	((locktag).locktag_field2)
#define GET_PREDICATELOCKTARGETTAG_PAGE(locktag) \
	((locktag).locktag_field3)
#define GET_PREDICATELOCKTARGETTAG_OFFSET(locktag) \
	((locktag).locktag_field4)
#define GET_PREDICATELOCKTARGETTAG_TYPE(locktag)							 \
	(((locktag).locktag_field4 != InvalidOffsetNumber) ? PREDLOCKTAG_TUPLE : \
	 (((locktag).locktag_field3 != InvalidBlockNumber) ? PREDLOCKTAG_PAGE :   \
	  PREDLOCKTAG_RELATION))

/*
 * Two-phase commit statefile records. There are two types: for each
 * transaction, we generate one per-transaction record and a variable
 * number of per-predicate-lock records.
 */
typedef enum TwoPhasePredicateRecordType
{
	TWOPHASEPREDICATERECORD_XACT,
	TWOPHASEPREDICATERECORD_LOCK
}	TwoPhasePredicateRecordType;

/*
 * Per-transaction information to reconstruct a SERIALIZABLEXACT. Not
 * much is needed because most of it not meaningful for a recovered
 * prepared transaction.
 *
 * In particular, we do not record the in and out conflict lists for a
 * prepared transaction because the associated SERIALIZABLEXACTs will
 * not be available after recovery. Instead, we simply record the
 * existence of each type of conflict by setting the transaction's
 * summary conflict in/out flag.
 */
typedef struct TwoPhasePredicateXactRecord
{
	TransactionId xmin;
	uint32		flags;
} TwoPhasePredicateXactRecord;

/* Per-lock state */
typedef struct TwoPhasePredicateLockRecord
{
	PREDICATELOCKTARGETTAG target;
} TwoPhasePredicateLockRecord;

typedef struct TwoPhasePredicateRecord
{
	TwoPhasePredicateRecordType type;
	union
	{
		TwoPhasePredicateXactRecord xactRecord;
		TwoPhasePredicateLockRecord lockRecord;
	}			data;
} TwoPhasePredicateRecord;

/*
 * Define a macro to use for an "empty" SERIALIZABLEXACT reference.
 */
#define InvalidSerializableXact ((SERIALIZABLEXACT *) NULL)


/*
 * Function definitions for functions needing awareness of predicate
 * locking internals.
 */
extern PredicateLockData *GetPredicateLockStatusData(void);


#endif   /* PREDICATE_INTERNALS_H */
