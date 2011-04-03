/*-------------------------------------------------------------------------
 *
 * miscinit.c
 *	  miscellaneous initialization support stuff
 *
 * Portions Copyright (c) 1996-2011, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/utils/init/miscinit.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <sys/param.h>
#include <signal.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <fcntl.h>
#include <unistd.h>
#include <grp.h>
#include <pwd.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#ifdef HAVE_UTIME_H
#include <utime.h>
#endif

#include "catalog/pg_authid.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "postmaster/autovacuum.h"
#include "postmaster/postmaster.h"
#include "storage/fd.h"
#include "storage/ipc.h"
#include "storage/pg_shmem.h"
#include "storage/proc.h"
#include "storage/procarray.h"
#include "utils/builtins.h"
#include "utils/guc.h"
#include "utils/memutils.h"
#include "utils/syscache.h"

/* Note: we rely on this to initialize as zeroes */
static char socketLockFile[MAXPGPATH];

#define DIRECTORY_LOCK_FILE		"postmaster.pid"
static pid_t GetPIDHoldingLock(int fileDescriptor,bool exclusiveLockFlag);
static int AcquireLock(int fileDescriptor,bool exclusiveLockFlag,bool waitForLock);
static int ReleaseLock(int fileDescriptor);
void AcquireDataDirLock();
pid_t GetPIDHoldingDataDirLock();
static void WriteLockFileContents(char *lockFilePath,int lockFileFD,bool isPostmasterFlag,pid_t processPid,char *dataDirectoryPath,long startTime,int portNumber,char * socketDirectory);

/* enum used by CreateLockFile to report its success or error condition */
typedef enum
  {
    /* positive numbers refer to the PID of a conflicting lock-holding process, but not necessarily a postmaster */
    CreateLockFileNoError=0, 
    CreateLockFileFileError=-1, /*advises the caller to check the errno for the error */
    CreateLockFileSharedLockAcquisitionError=-2,
    CreateLockFileExclusiveLockCheckError=-3,
  } CreateLockFileValue;


static CreateLockFileValue CreateLockFile(char *lockFilePath,bool amPostmaster,int *lockFileRetDescriptor,bool blockOnLockFlag);

ProcessingMode Mode = InitProcessing;


/* ----------------------------------------------------------------
 *		ignoring system indexes support stuff
 *
 * NOTE: "ignoring system indexes" means we do not use the system indexes
 * for lookups (either in hardwired catalog accesses or in planner-generated
 * plans).	We do, however, still update the indexes when a catalog
 * modification is made.
 * ----------------------------------------------------------------
 */

bool		IgnoreSystemIndexes = false;


/* ----------------------------------------------------------------
 *				database path / name support stuff
 * ----------------------------------------------------------------
 */

void
SetDatabasePath(const char *path)
{
	/* This should happen only once per process */
	Assert(!DatabasePath);
	DatabasePath = MemoryContextStrdup(TopMemoryContext, path);
}

/*
 * Set data directory, but make sure it's an absolute path.  Use this,
 * never set DataDir directly.
 */
void
SetDataDir(const char *dir)
{
	char	   *new;

	AssertArg(dir);

	/* If presented path is relative, convert to absolute */
	new = make_absolute_path(dir);

	if (DataDir)
		free(DataDir);
	DataDir = new;
}

/*
 * Change working directory to DataDir.  Most of the postmaster and backend
 * code assumes that we are in DataDir so it can use relative paths to access
 * stuff in and under the data directory.  For convenience during path
 * setup, however, we don't force the chdir to occur during SetDataDir.
 */
void
ChangeToDataDir(void)
{
	AssertState(DataDir);

	if (chdir(DataDir) < 0)
		ereport(FATAL,
				(errcode_for_file_access(),
				 errmsg("could not change directory to \"%s\": %m",
						DataDir)));
}

/*
 * If the given pathname isn't already absolute, make it so, interpreting
 * it relative to the current working directory.
 *
 * Also canonicalizes the path.  The result is always a malloc'd copy.
 *
 * Note: interpretation of relative-path arguments during postmaster startup
 * should happen before doing ChangeToDataDir(), else the user will probably
 * not like the results.
 */
char *
make_absolute_path(const char *path)
{
	char	   *new;

	/* Returning null for null input is convenient for some callers */
	if (path == NULL)
		return NULL;

	if (!is_absolute_path(path))
	{
		char	   *buf;
		size_t		buflen;

		buflen = MAXPGPATH;
		for (;;)
		{
			buf = malloc(buflen);
			if (!buf)
				ereport(FATAL,
						(errcode(ERRCODE_OUT_OF_MEMORY),
						 errmsg("out of memory")));

			if (getcwd(buf, buflen))
				break;
			else if (errno == ERANGE)
			{
				free(buf);
				buflen *= 2;
				continue;
			}
			else
			{
				free(buf);
				elog(FATAL, "could not get current working directory: %m");
			}
		}

		new = malloc(strlen(buf) + strlen(path) + 2);
		if (!new)
			ereport(FATAL,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of memory")));
		sprintf(new, "%s/%s", buf, path);
		free(buf);
	}
	else
	{
		new = strdup(path);
		if (!new)
			ereport(FATAL,
					(errcode(ERRCODE_OUT_OF_MEMORY),
					 errmsg("out of memory")));
	}

	/* Make sure punctuation is canonical, too */
	canonicalize_path(new);

	return new;
}


/* ----------------------------------------------------------------
 *	User ID state
 *
 * We have to track several different values associated with the concept
 * of "user ID".
 *
 * AuthenticatedUserId is determined at connection start and never changes.
 *
 * SessionUserId is initially the same as AuthenticatedUserId, but can be
 * changed by SET SESSION AUTHORIZATION (if AuthenticatedUserIsSuperuser).
 * This is the ID reported by the SESSION_USER SQL function.
 *
 * OuterUserId is the current user ID in effect at the "outer level" (outside
 * any transaction or function).  This is initially the same as SessionUserId,
 * but can be changed by SET ROLE to any role that SessionUserId is a
 * member of.  (XXX rename to something like CurrentRoleId?)
 *
 * CurrentUserId is the current effective user ID; this is the one to use
 * for all normal permissions-checking purposes.  At outer level this will
 * be the same as OuterUserId, but it changes during calls to SECURITY
 * DEFINER functions, as well as locally in some specialized commands.
 *
 * SecurityRestrictionContext holds flags indicating reason(s) for changing
 * CurrentUserId.  In some cases we need to lock down operations that are
 * not directly controlled by privilege settings, and this provides a
 * convenient way to do it.
 * ----------------------------------------------------------------
 */
static Oid	AuthenticatedUserId = InvalidOid;
static Oid	SessionUserId = InvalidOid;
static Oid	OuterUserId = InvalidOid;
static Oid	CurrentUserId = InvalidOid;

/* We also have to remember the superuser state of some of these levels */
static bool AuthenticatedUserIsSuperuser = false;
static bool SessionUserIsSuperuser = false;

static int	SecurityRestrictionContext = 0;

/* We also remember if a SET ROLE is currently active */
static bool SetRoleIsActive = false;


/*
 * GetUserId - get the current effective user ID.
 *
 * Note: there's no SetUserId() anymore; use SetUserIdAndSecContext().
 */
Oid
GetUserId(void)
{
	AssertState(OidIsValid(CurrentUserId));
	return CurrentUserId;
}


/*
 * GetOuterUserId/SetOuterUserId - get/set the outer-level user ID.
 */
Oid
GetOuterUserId(void)
{
	AssertState(OidIsValid(OuterUserId));
	return OuterUserId;
}


static void
SetOuterUserId(Oid userid)
{
	AssertState(SecurityRestrictionContext == 0);
	AssertArg(OidIsValid(userid));
	OuterUserId = userid;

	/* We force the effective user ID to match, too */
	CurrentUserId = userid;
}


/*
 * GetSessionUserId/SetSessionUserId - get/set the session user ID.
 */
Oid
GetSessionUserId(void)
{
	AssertState(OidIsValid(SessionUserId));
	return SessionUserId;
}


static void
SetSessionUserId(Oid userid, bool is_superuser)
{
	AssertState(SecurityRestrictionContext == 0);
	AssertArg(OidIsValid(userid));
	SessionUserId = userid;
	SessionUserIsSuperuser = is_superuser;
	SetRoleIsActive = false;

	/* We force the effective user IDs to match, too */
	OuterUserId = userid;
	CurrentUserId = userid;
}


/*
 * GetUserIdAndSecContext/SetUserIdAndSecContext - get/set the current user ID
 * and the SecurityRestrictionContext flags.
 *
 * Currently there are two valid bits in SecurityRestrictionContext:
 *
 * SECURITY_LOCAL_USERID_CHANGE indicates that we are inside an operation
 * that is temporarily changing CurrentUserId via these functions.	This is
 * needed to indicate that the actual value of CurrentUserId is not in sync
 * with guc.c's internal state, so SET ROLE has to be disallowed.
 *
 * SECURITY_RESTRICTED_OPERATION indicates that we are inside an operation
 * that does not wish to trust called user-defined functions at all.  This
 * bit prevents not only SET ROLE, but various other changes of session state
 * that normally is unprotected but might possibly be used to subvert the
 * calling session later.  An example is replacing an existing prepared
 * statement with new code, which will then be executed with the outer
 * session's permissions when the prepared statement is next used.  Since
 * these restrictions are fairly draconian, we apply them only in contexts
 * where the called functions are really supposed to be side-effect-free
 * anyway, such as VACUUM/ANALYZE/REINDEX.
 *
 * Unlike GetUserId, GetUserIdAndSecContext does *not* Assert that the current
 * value of CurrentUserId is valid; nor does SetUserIdAndSecContext require
 * the new value to be valid.  In fact, these routines had better not
 * ever throw any kind of error.  This is because they are used by
 * StartTransaction and AbortTransaction to save/restore the settings,
 * and during the first transaction within a backend, the value to be saved
 * and perhaps restored is indeed invalid.	We have to be able to get
 * through AbortTransaction without asserting in case InitPostgres fails.
 */
void
GetUserIdAndSecContext(Oid *userid, int *sec_context)
{
	*userid = CurrentUserId;
	*sec_context = SecurityRestrictionContext;
}

void
SetUserIdAndSecContext(Oid userid, int sec_context)
{
	CurrentUserId = userid;
	SecurityRestrictionContext = sec_context;
}


/*
 * InLocalUserIdChange - are we inside a local change of CurrentUserId?
 */
bool
InLocalUserIdChange(void)
{
	return (SecurityRestrictionContext & SECURITY_LOCAL_USERID_CHANGE) != 0;
}

/*
 * InSecurityRestrictedOperation - are we inside a security-restricted command?
 */
bool
InSecurityRestrictedOperation(void)
{
	return (SecurityRestrictionContext & SECURITY_RESTRICTED_OPERATION) != 0;
}


/*
 * These are obsolete versions of Get/SetUserIdAndSecContext that are
 * only provided for bug-compatibility with some rather dubious code in
 * pljava.	We allow the userid to be set, but only when not inside a
 * security restriction context.
 */
void
GetUserIdAndContext(Oid *userid, bool *sec_def_context)
{
	*userid = CurrentUserId;
	*sec_def_context = InLocalUserIdChange();
}

void
SetUserIdAndContext(Oid userid, bool sec_def_context)
{
	/* We throw the same error SET ROLE would. */
	if (InSecurityRestrictedOperation())
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("cannot set parameter \"%s\" within security-restricted operation",
						"role")));
	CurrentUserId = userid;
	if (sec_def_context)
		SecurityRestrictionContext |= SECURITY_LOCAL_USERID_CHANGE;
	else
		SecurityRestrictionContext &= ~SECURITY_LOCAL_USERID_CHANGE;
}


/*
 * Check if the authenticated user is a replication role
 */
bool
is_authenticated_user_replication_role(void)
{
	bool            result = false;
	HeapTuple       utup;

	utup = SearchSysCache1(AUTHOID, ObjectIdGetDatum(AuthenticatedUserId));
	if (HeapTupleIsValid(utup))
	{
		result = ((Form_pg_authid) GETSTRUCT(utup))->rolreplication;
		ReleaseSysCache(utup);
	}
	return result;
}

/*
 * Initialize user identity during normal backend startup
 */
void
InitializeSessionUserId(const char *rolename)
{
	HeapTuple	roleTup;
	Form_pg_authid rform;
	Oid			roleid;

	/*
	 * Don't do scans if we're bootstrapping, none of the system catalogs
	 * exist yet, and they should be owned by postgres anyway.
	 */
	AssertState(!IsBootstrapProcessingMode());

	/* call only once */
	AssertState(!OidIsValid(AuthenticatedUserId));

	roleTup = SearchSysCache1(AUTHNAME, PointerGetDatum(rolename));
	if (!HeapTupleIsValid(roleTup))
		ereport(FATAL,
				(errcode(ERRCODE_INVALID_AUTHORIZATION_SPECIFICATION),
				 errmsg("role \"%s\" does not exist", rolename)));

	rform = (Form_pg_authid) GETSTRUCT(roleTup);
	roleid = HeapTupleGetOid(roleTup);

	AuthenticatedUserId = roleid;
	AuthenticatedUserIsSuperuser = rform->rolsuper;

	/* This sets OuterUserId/CurrentUserId too */
	SetSessionUserId(roleid, AuthenticatedUserIsSuperuser);

	/* Also mark our PGPROC entry with the authenticated user id */
	/* (We assume this is an atomic store so no lock is needed) */
	MyProc->roleId = roleid;

	/*
	 * These next checks are not enforced when in standalone mode, so that
	 * there is a way to recover from sillinesses like "UPDATE pg_authid SET
	 * rolcanlogin = false;".
	 */
	if (IsUnderPostmaster)
	{
		/*
		 * Is role allowed to login at all?
		 */
		if (!rform->rolcanlogin)
			ereport(FATAL,
					(errcode(ERRCODE_INVALID_AUTHORIZATION_SPECIFICATION),
					 errmsg("role \"%s\" is not permitted to log in",
							rolename)));

		/*
		 * Check connection limit for this role.
		 *
		 * There is a race condition here --- we create our PGPROC before
		 * checking for other PGPROCs.	If two backends did this at about the
		 * same time, they might both think they were over the limit, while
		 * ideally one should succeed and one fail.  Getting that to work
		 * exactly seems more trouble than it is worth, however; instead we
		 * just document that the connection limit is approximate.
		 */
		if (rform->rolconnlimit >= 0 &&
			!AuthenticatedUserIsSuperuser &&
			CountUserBackends(roleid) > rform->rolconnlimit)
			ereport(FATAL,
					(errcode(ERRCODE_TOO_MANY_CONNECTIONS),
					 errmsg("too many connections for role \"%s\"",
							rolename)));
	}

	/* Record username and superuser status as GUC settings too */
	SetConfigOption("session_authorization", rolename,
					PGC_BACKEND, PGC_S_OVERRIDE);
	SetConfigOption("is_superuser",
					AuthenticatedUserIsSuperuser ? "on" : "off",
					PGC_INTERNAL, PGC_S_OVERRIDE);

	ReleaseSysCache(roleTup);
}


/*
 * Initialize user identity during special backend startup
 */
void
InitializeSessionUserIdStandalone(void)
{
	/*
	 * This function should only be called in single-user mode and in
	 * autovacuum workers.
	 */
	AssertState(!IsUnderPostmaster || IsAutoVacuumWorkerProcess());

	/* call only once */
	AssertState(!OidIsValid(AuthenticatedUserId));

	AuthenticatedUserId = BOOTSTRAP_SUPERUSERID;
	AuthenticatedUserIsSuperuser = true;

	SetSessionUserId(BOOTSTRAP_SUPERUSERID, true);
}


/*
 * Change session auth ID while running
 *
 * Only a superuser may set auth ID to something other than himself.  Note
 * that in case of multiple SETs in a single session, the original userid's
 * superuserness is what matters.  But we set the GUC variable is_superuser
 * to indicate whether the *current* session userid is a superuser.
 *
 * Note: this is not an especially clean place to do the permission check.
 * It's OK because the check does not require catalog access and can't
 * fail during an end-of-transaction GUC reversion, but we may someday
 * have to push it up into assign_session_authorization.
 */
void
SetSessionAuthorization(Oid userid, bool is_superuser)
{
	/* Must have authenticated already, else can't make permission check */
	AssertState(OidIsValid(AuthenticatedUserId));

	if (userid != AuthenticatedUserId &&
		!AuthenticatedUserIsSuperuser)
		ereport(ERROR,
				(errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
				 errmsg("permission denied to set session authorization")));

	SetSessionUserId(userid, is_superuser);

	SetConfigOption("is_superuser",
					is_superuser ? "on" : "off",
					PGC_INTERNAL, PGC_S_OVERRIDE);
}

/*
 * Report current role id
 *		This follows the semantics of SET ROLE, ie return the outer-level ID
 *		not the current effective ID, and return InvalidOid when the setting
 *		is logically SET ROLE NONE.
 */
Oid
GetCurrentRoleId(void)
{
	if (SetRoleIsActive)
		return OuterUserId;
	else
		return InvalidOid;
}

/*
 * Change Role ID while running (SET ROLE)
 *
 * If roleid is InvalidOid, we are doing SET ROLE NONE: revert to the
 * session user authorization.	In this case the is_superuser argument
 * is ignored.
 *
 * When roleid is not InvalidOid, the caller must have checked whether
 * the session user has permission to become that role.  (We cannot check
 * here because this routine must be able to execute in a failed transaction
 * to restore a prior value of the ROLE GUC variable.)
 */
void
SetCurrentRoleId(Oid roleid, bool is_superuser)
{
	/*
	 * Get correct info if it's SET ROLE NONE
	 *
	 * If SessionUserId hasn't been set yet, just do nothing --- the eventual
	 * SetSessionUserId call will fix everything.  This is needed since we
	 * will get called during GUC initialization.
	 */
	if (!OidIsValid(roleid))
	{
		if (!OidIsValid(SessionUserId))
			return;

		roleid = SessionUserId;
		is_superuser = SessionUserIsSuperuser;

		SetRoleIsActive = false;
	}
	else
		SetRoleIsActive = true;

	SetOuterUserId(roleid);

	SetConfigOption("is_superuser",
					is_superuser ? "on" : "off",
					PGC_INTERNAL, PGC_S_OVERRIDE);
}


/*
 * Get user name from user oid
 */
char *
GetUserNameFromId(Oid roleid)
{
	HeapTuple	tuple;
	char	   *result;

	tuple = SearchSysCache1(AUTHOID, ObjectIdGetDatum(roleid));
	if (!HeapTupleIsValid(tuple))
		ereport(ERROR,
				(errcode(ERRCODE_UNDEFINED_OBJECT),
				 errmsg("invalid role OID: %u", roleid)));

	result = pstrdup(NameStr(((Form_pg_authid) GETSTRUCT(tuple))->rolname));

	ReleaseSysCache(tuple);
	return result;
}


/*-------------------------------------------------------------------------
 *				Interlock-file support
 *
 * These routines are used to create a data-directory lockfile
 * ($DATADIR/postmaster.pid).
 * The file contains the info:
 *
 *		Owning process' PID
 *		Data directory path
 *
 * By convention, the owning process' PID is negated if it is a standalone
 * backend rather than a postmaster.  This is just for informational purposes.
 * The path is also just for informational purposes (so that a socket lockfile
 * can be more easily traced to the associated postmaster).
 *
 * A data-directory lockfile can optionally contain a third line, containing
 * the key and ID for the shared memory block used by this postmaster.
 *
 *-------------------------------------------------------------------------
 */

/* We hold onto the lockFile for the life of the process to hold onto the advisory locks. */
static int DataDirLockFileFD = 0;

/*
 * Create the data directory lockfile.
 *
 * When this is called, we must have already switched the working
 * directory to DataDir, so we can just use a relative path.  This
 * helps ensure that we are locking the directory we should be.
 */
void
CreateDataDirLockFile(bool amPostmaster,bool blockOptionFlag)
{
  char *lockFilePath=DIRECTORY_LOCK_FILE;
  CreateLockFileValue error = CreateLockFile(lockFilePath,amPostmaster,&DataDirLockFileFD,blockOptionFlag);
  if(error==CreateLockFileNoError)
    {
      return;
    }
  else if(error==CreateLockFileFileError)
    {
      ereport(FATAL,
              (errmsg("failed operation on lock file at \"%s\": %m",lockFilePath)));
    }
  else if(error==CreateLockFileSharedLockAcquisitionError)
    {
      ereport(FATAL,
              (errmsg("failed to acquire shared lock on file \"%s\": %m",lockFilePath)));
    }
  else if(error==CreateLockFileExclusiveLockCheckError)
    {
      ereport(FATAL,
              (errmsg("failed to check for exclusive lock on file \"%s\": %m", lockFilePath)));

    }
  else if(error>0)
    {
      /* error holds the pid of the conflicting process */
      ereport(FATAL,
              (errmsg("another postgresql process is running in the data directory \"%s\" with pid %d",DataDir,error),
               errhint("kill the other server processes to start a new postgresql server")));
    }
  else
    {
      ereport(FATAL,
              (errmsg("an unhandled locking error occurred")));
    }
}

static CreateLockFileValue
CreateLockFile(char *lockFilePath,bool amPostmaster,int *lockFileRetDescriptor,bool blockOnLockFlag)
{
  int success = 0;
  pid_t pidHoldingLock;
  int lockFileFD = 0;

  /* open the directory lock file- whether or not it already exists is irrelevant because we will check for file locks */
  lockFileFD = open(lockFilePath, O_RDWR | O_CREAT, 0600);
  if(lockFileFD<0)
    {
      return CreateLockFileFileError;
    }

  if(!blockOnLockFlag)
    {
      /* Acquire the shared advisory lock without blocking*/
      
      success = AcquireLock(lockFileFD,false,false); 
      if(success < 0)
        {
          /* We failed to acquire the read lock, which is unlikely because we no one should be holding an exclusive lock on it. */
          return CreateLockFileSharedLockAcquisitionError;
        }
    }
  else 
    {
      /* loop until we get the exclusive lock and the subsequent shared lock- waiting until the data directory is not being serviced is data directory postgresql hot standy mode*/
      while(1)
        {
          success = AcquireLock(lockFileFD,true,true);
          if(success < 0)
            return CreateLockFileExclusiveLockCheckError;
          
          /* now we hold the exclusive lock, so demote to read lock, but be wary of the race condition whereby a different postmaster could also be waiting to grab the read lock too */
          success = ReleaseLock(lockFileFD);
          if(success < 0)
            return CreateLockFileExclusiveLockCheckError;
          
          success = AcquireLock(lockFileFD,false,false);
          if(success < 0)
            {
              /* d'oh- some other postmaster grabbed the exclusive lock in the meantime, so try again later */
              pg_usleep(500L);
              continue;
            }
          else
            break;
        }
    }

  
  /* Determine if acquiring an exclusive (write) lock would be denied. If so, there is another postmaster or postgres child process running, so abort. */
  pidHoldingLock = GetPIDHoldingLock(lockFileFD,true);
  if(pidHoldingLock < 0)
    {
      /* checking for a lock failed */
      return CreateLockFileExclusiveLockCheckError;
    }
  else if(pidHoldingLock > 0)
    {
      /* there is another process holding the lock, so we must abort starting a new postmaster */
      return pidHoldingLock;
    }
  /*no process would block the lock, so we are cleared for starting a new postmaster*/
  WriteLockFileContents(lockFilePath,lockFileFD,
                        true,
                        getpid(),
                        DataDir,
                        (long)MyStartTime,
                        PostPortNumber,
#ifdef HAVE_UNIX_SOCKETS
                        (*UnixSocketDir != '\0') ? UnixSocketDir : DEFAULT_PGSOCKET_DIR
#else
                         ""
#endif
                        );
  /* There is no need to remove the lock file because the locks synchronize access, not the existence of the file. */

  if(lockFileRetDescriptor != NULL)
    *lockFileRetDescriptor = lockFileFD;
  return CreateLockFileNoError;
}

static void WriteLockFileContents(char *lockFilePath,int lockFileFD,bool isPostmasterFlag,pid_t processPid,char *dataDirectoryPath,long startTime,int portNumber,char * socketDirectoryPath)
{
  char writeBuffer[MAXPGPATH * 2 + 256];  
  snprintf(writeBuffer,sizeof(writeBuffer),"%d\n%s\n%ld\n%d\n%s\n",
           isPostmasterFlag ? (int) processPid : -((int) processPid),
           dataDirectoryPath,
           startTime,
           portNumber,
           socketDirectoryPath
           );
  errno = 0;
  if (write(lockFileFD, writeBuffer, strlen(writeBuffer)) != strlen(writeBuffer))
    {
      int                     save_errno = errno;
      unlink(lockFilePath);
      /* if write didn't set errno, assume problem is no disk space */
      errno = save_errno ? save_errno : ENOSPC;
      ereport(FATAL,
              (errcode_for_file_access(),
               errmsg("could not write lock file \"%s\": %m", lockFilePath)));
    }
  if (pg_fsync(lockFileFD) != 0)
    {
      int                     save_errno = errno;

      unlink(lockFilePath);
      errno = save_errno;
      ereport(FATAL,
              (errcode_for_file_access(),
               errmsg("could not write lock file \"%s\": %m", lockFilePath)));
    }
  return;
}

/* Called by pg_ctl to determine when the postmaster is shutdown. */
pid_t GetPIDHoldingDataDirLock(void)
{
	return GetPIDHoldingLock(DataDirLockFileFD,true);
}


/*
 * Called by backends when they startup to signify that the data directory is in use
 */
void AcquireDataDirLock(void)
{
  int success;
  int exclusiveLockViolatingPID = 0;
  /* get the read lock */
  success = AcquireLock(DataDirLockFileFD,false,false); 
  if(success < 0)
    {
      /* Failed to acquire read lock, bomb out */
      ereport(FATAL,
              (errmsg("failed to acquire lock on \"%s\": %m",DIRECTORY_LOCK_FILE)));

    }
  /* verify that grabbing an exclusive lock would complain that the parent or PROC_ARRAY sibling process would cause exclusive lock acquisition to fail- otherwise a separate postmaster is holding the lock (eliminates a possible race condition when the postmaster spawns a backend, immediately dies and new postmaster takes over) */
  exclusiveLockViolatingPID = GetPIDHoldingLock(DataDirLockFileFD,true);
  if(exclusiveLockViolatingPID < 0)
    {
      /* error testing for the lock, very unlikely, but fatal */
      ereport(FATAL,
              (errmsg("failed to test for lock on \"%s\": %m",DIRECTORY_LOCK_FILE)));
    }
  else if(exclusiveLockViolatingPID == 0)
    {
      /* the postmaster should be holding the lock- in this case it is not (and this is the only backend running), so don't bother running the backend because the postmaster just died */
      ereport(FATAL,
              (errmsg("failed to initialize backend because the postmaster exited")));
    }
  else
    {
      /* the PID is valid, so we should check that the PID refers either to the postmaster or its children */
      /* NOTE TO REVIEWER: is this too early to call BackendPidGetProc? */ 
      PGPROC *violatingProc = NULL;
      violatingProc = BackendPidGetProc(exclusiveLockViolatingPID);

      if(exclusiveLockViolatingPID != getppid() && 
         violatingProc == NULL)
        {
          /* the violating lock is neither the postmaster nor a sibling child- data directory conflict detected! */
          ereport(FATAL,
                  (errmsg("backend startup race condition detected- another postmaster is running in this data directory")));
        }
    }
  return;
}

/*
 * Create a lockfile for the specified Unix socket file.
 */
void
CreateSocketLockFile(const char *socketfile, bool amPostmaster)
{
  char lockFilePath[MAXPGPATH];
  CreateLockFileValue error;

  snprintf(lockFilePath, sizeof(lockFilePath), "%s.lock", socketfile);

  /* This intentionally leaks the socket file descriptor- we hold onto it so that the lock is held until the process is exited */
  error = CreateLockFile(lockFilePath, amPostmaster,NULL,false);
  
  if(error==CreateLockFileNoError)
    {
      return;
    }
  else if(error==CreateLockFileFileError)
    {
      ereport(FATAL,
              (errmsg("failed operation on lock file at \"%s\": %m",lockFilePath)));
    }
  else if(error==CreateLockFileSharedLockAcquisitionError)
    {
      ereport(FATAL,
              (errmsg("failed to acquire shared lock on file \"%s\": %m",lockFilePath)));
    }
  else if(error==CreateLockFileExclusiveLockCheckError)
    {
      ereport(FATAL,
              (errmsg("failed to check for exclusive lock on file \"%s\": %m", lockFilePath)));
      
    }
  else if(error>0)
    {
      /* error holds the pid of the conflicting process */
      ereport(FATAL,
              (errmsg("another postgresql process with pid %d is bound to the socket file at \"%s\"",error,lockFilePath),
               errhint("configure a different socket file path in postgresql.conf or kill the conflicting postgresql server")));
    }
  else
    {
      ereport(FATAL,
              (errmsg("an unhandled locking error occurred")));
    }
  
  /* Save name of lockfile for TouchSocketLockFile */
  strcpy(socketLockFile, lockFilePath);
}

/*
 * TouchSocketLockFile -- mark socket lock file as recently accessed
 *
 * This routine should be called every so often to ensure that the lock file
 * has a recent mod or access date.  That saves it
 * from being removed by overenthusiastic /tmp-directory-cleaner daemons.
 * (Another reason we should never have put the socket file in /tmp...)
 */
void
TouchSocketLockFile(void)
{
  /* Do nothing if we did not create a socket... */
  if (socketLockFile[0] != '\0')
    {
      /*
       * utime() is POSIX standard, utimes() is a common alternative; if we
       * have neither, fall back to actually reading the file (which only
       * sets the access time not mod time, but that should be enough in
       * most cases).  In all paths, we ignore errors.
       */
#ifdef HAVE_UTIME
      utime(socketLockFile, NULL);
#else/* !HAVE_UTIME */
#ifdef HAVE_UTIMES
      utimes(socketLockFile, NULL);
#else/* !HAVE_UTIMES */
      intfd;
      charbuffer[1];

      fd = open(socketLockFile, O_RDONLY | PG_BINARY, 0);
      if (fd >= 0)
        {
          read(fd, buffer, sizeof(buffer));
        }
#endif   /* HAVE_UTIMES */
#endif   /* HAVE_UTIME */
    }
}

/*
 * Add (or replace) a line in the data directory lock file.
 * The given string should not include a trailing newline.
 *
 * Caution: this erases all following lines.  In current usage that is OK
 * because lines are added in order.  We could improve it if needed.
 */
void
AddToDataDirLockFile(int target_line, const char *str)
{
	int			fd;
	int			len;
	int			lineno;
	char	   *ptr;
	char		buffer[BLCKSZ];
        int success;

	fd = DataDirLockFileFD;
        /* rewind the file handle to rewrite it */
        success = lseek(fd,0,SEEK_SET);
	if (success < 0)
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not seek lock file \"%s\": %m",
                                        DIRECTORY_LOCK_FILE)));
		return;
	}
	len = read(fd, buffer, sizeof(buffer) - 1);
	if (len < 0)
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not read from file \"%s\": %m",
						DIRECTORY_LOCK_FILE)));
		return;
	}
	buffer[len] = '\0';

	/*
	 * Skip over lines we are not supposed to rewrite.
	 */
	ptr = buffer;
	for (lineno = 1; lineno < target_line; lineno++)
	{
		if ((ptr = strchr(ptr, '\n')) == NULL)
		{
			elog(LOG, "bogus data in \"%s\"", DIRECTORY_LOCK_FILE);
			return;
		}
		ptr++;
	}

	/*
	 * Write or rewrite the target line.
	 */
	snprintf(ptr, buffer + sizeof(buffer) - ptr, "%s\n", str);

	/*
	 * And rewrite the data.  Since we write in a single kernel call, this
	 * update should appear atomic to onlookers.
	 */
	len = strlen(buffer);
	errno = 0;
	if (lseek(fd, (off_t) 0, SEEK_SET) != 0 ||
		(int) write(fd, buffer, len) != len)
	{
		/* if write didn't set errno, assume problem is no disk space */
		if (errno == 0)
			errno = ENOSPC;
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not write to file \"%s\": %m",
						DIRECTORY_LOCK_FILE)));
		return;
	}
	if (pg_fsync(fd) != 0)
	{
		ereport(LOG,
				(errcode_for_file_access(),
				 errmsg("could not write to file \"%s\": %m",
						DIRECTORY_LOCK_FILE)));
	}
}


/*-------------------------------------------------------------------------
 *				Version checking support
 *-------------------------------------------------------------------------
 */

/*
 * Determine whether the PG_VERSION file in directory `path' indicates
 * a data version compatible with the version of this program.
 *
 * If compatible, return. Otherwise, ereport(FATAL).
 */
void
ValidatePgVersion(const char *path)
{
	char		full_path[MAXPGPATH];
	FILE	   *file;
	int			ret;
	long		file_major,
				file_minor;
	long		my_major = 0,
				my_minor = 0;
	char	   *endptr;
	const char *version_string = PG_VERSION;

	my_major = strtol(version_string, &endptr, 10);
	if (*endptr == '.')
		my_minor = strtol(endptr + 1, NULL, 10);

	snprintf(full_path, sizeof(full_path), "%s/PG_VERSION", path);

	file = AllocateFile(full_path, "r");
	if (!file)
	{
		if (errno == ENOENT)
			ereport(FATAL,
					(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
					 errmsg("\"%s\" is not a valid data directory",
							path),
					 errdetail("File \"%s\" is missing.", full_path)));
		else
			ereport(FATAL,
					(errcode_for_file_access(),
					 errmsg("could not open file \"%s\": %m", full_path)));
	}

	ret = fscanf(file, "%ld.%ld", &file_major, &file_minor);
	if (ret != 2)
		ereport(FATAL,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("\"%s\" is not a valid data directory",
						path),
				 errdetail("File \"%s\" does not contain valid data.",
						   full_path),
				 errhint("You might need to initdb.")));

	FreeFile(file);

	if (my_major != file_major || my_minor != file_minor)
		ereport(FATAL,
				(errcode(ERRCODE_INVALID_PARAMETER_VALUE),
				 errmsg("database files are incompatible with server"),
				 errdetail("The data directory was initialized by PostgreSQL version %ld.%ld, "
						   "which is not compatible with this version %s.",
						   file_major, file_minor, version_string)));
}

/*-------------------------------------------------------------------------
 *				Library preload support
 *-------------------------------------------------------------------------
 */

/*
 * GUC variables: lists of library names to be preloaded at postmaster
 * start and at backend start
 */
char	   *shared_preload_libraries_string = NULL;
char	   *local_preload_libraries_string = NULL;

/* Flag telling that we are loading shared_preload_libraries */
bool		process_shared_preload_libraries_in_progress = false;

/*
 * load the shared libraries listed in 'libraries'
 *
 * 'gucname': name of GUC variable, for error reports
 * 'restricted': if true, force libraries to be in $libdir/plugins/
 */
static void
load_libraries(const char *libraries, const char *gucname, bool restricted)
{
	char	   *rawstring;
	List	   *elemlist;
	int			elevel;
	ListCell   *l;

	if (libraries == NULL || libraries[0] == '\0')
		return;					/* nothing to do */

	/* Need a modifiable copy of string */
	rawstring = pstrdup(libraries);

	/* Parse string into list of identifiers */
	if (!SplitIdentifierString(rawstring, ',', &elemlist))
	{
		/* syntax error in list */
		pfree(rawstring);
		list_free(elemlist);
		ereport(LOG,
				(errcode(ERRCODE_SYNTAX_ERROR),
				 errmsg("invalid list syntax in parameter \"%s\"",
						gucname)));
		return;
	}

	/*
	 * Choose notice level: avoid repeat messages when re-loading a library
	 * that was preloaded into the postmaster.	(Only possible in EXEC_BACKEND
	 * configurations)
	 */
#ifdef EXEC_BACKEND
	if (IsUnderPostmaster && process_shared_preload_libraries_in_progress)
		elevel = DEBUG2;
	else
#endif
		elevel = LOG;

	foreach(l, elemlist)
	{
		char	   *tok = (char *) lfirst(l);
		char	   *filename;

		filename = pstrdup(tok);
		canonicalize_path(filename);
		/* If restricting, insert $libdir/plugins if not mentioned already */
		if (restricted && first_dir_separator(filename) == NULL)
		{
			char	   *expanded;

			expanded = palloc(strlen("$libdir/plugins/") + strlen(filename) + 1);
			strcpy(expanded, "$libdir/plugins/");
			strcat(expanded, filename);
			pfree(filename);
			filename = expanded;
		}
		load_file(filename, restricted);
		ereport(elevel,
				(errmsg("loaded library \"%s\"", filename)));
		pfree(filename);
	}

	pfree(rawstring);
	list_free(elemlist);
}

/*
 * process any libraries that should be preloaded at postmaster start
 */
void
process_shared_preload_libraries(void)
{
	process_shared_preload_libraries_in_progress = true;
	load_libraries(shared_preload_libraries_string,
				   "shared_preload_libraries",
				   false);
	process_shared_preload_libraries_in_progress = false;
}

/*
 * process any libraries that should be preloaded at backend start
 */
void
process_local_preload_libraries(void)
{
	load_libraries(local_preload_libraries_string,
				   "local_preload_libraries",
				   true);
}

void
pg_bindtextdomain(const char *domain)
{
#ifdef ENABLE_NLS
	if (my_exec_path[0] != '\0')
	{
		char		locale_path[MAXPGPATH];

		get_locale_path(my_exec_path, locale_path);
		bindtextdomain(domain, locale_path);
		pg_bind_textdomain_codeset(domain);
	}
#endif
}

/* We can also offer the option to block until the other postmaster is cleared away using F_SETLKW */
static int AcquireLock(int fileDescriptor,bool exclusiveLockFlag,bool waitForLock)
{
  struct flock lock = { 
    .l_type = exclusiveLockFlag ? F_WRLCK : F_RDLCK,
    .l_start = 0,
    .l_whence = SEEK_SET,
    .l_len = 100 
  };
  return fcntl(fileDescriptor , waitForLock ? F_SETLKW : F_SETLK, &lock);
}

static int ReleaseLock(int fileDescriptor)
{
  struct flock lock = {
    .l_type = F_UNLCK,
    .l_start = 0,
    .l_whence = SEEK_SET,
    .l_len = 100
  };
  return fcntl(fileDescriptor, F_SETLK, &lock);
}

static pid_t GetPIDHoldingLock(int fileDescriptor,bool exclusiveLockFlag)
{
  struct flock lock = {
    .l_type = exclusiveLockFlag ? F_WRLCK : F_RDLCK,
    .l_start = 0,
    .l_whence = SEEK_SET,
    .l_len = 100,
    .l_pid = 0
  };
  int success;

  success = fcntl(fileDescriptor,F_GETLK,&lock);
  if(success < 0)
    {
      return (pid_t)success;
    }
  if(lock.l_whence == SEEK_SET)
    return lock.l_pid;
  else
    return -1;
}
