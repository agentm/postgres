/*-------------------------------------------------------------------------
 *
 * posix_shmem.c
 *	  Implement shared memory using POSIX facilities
 *
 * These routines represent a fairly thin layer on top of POSIX shared
 * memory functionality.
 *
 * Portions Copyright (c) 1996-2006, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <signal.h>
#include <unistd.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <sys/types.h>
#ifdef HAVE_KERNEL_OS_H
#include <kernel/OS.h>
#endif

#include "miscadmin.h"
#include "libpq/md5.h"
#include "storage/ipc.h"
#include "storage/pg_shmem.h"


#define IPCProtection	(0600)	/* access/modify by user only */
#define IPCNameLength		31  /* Darwin requires max 30 + '\0' */

uint8	UsedShmemInstanceId = 0;
void	*UsedShmemSegAddr = NULL;

static void GenerateIPCName(uint8 instanceId, char destIPCName[IPCNameLength]);
static void *InternalIpcMemoryCreate(const char ipcName[IPCNameLength],
									 uint8 instanceId, Size size);
static void IpcMemoryDetach(int status, Datum shmaddr);
static void IpcMemoryDelete(int status, Datum instanceId);
static PGShmemHeader *PGSharedMemoryAttach(uint8 instanceId);
static int POSIXSharedMemoryFD=-1;


/*
 *	GenerateIPCName(instanceId, destIPCName)
 *
 * Generate a shared memory object key name using the implicit argument
 * DataDir's pathname and the current instance id. A hash of the
 * canonicalized directory path is used to construct the key name.
 * Store the result in destIPCName, which must be IPCNameLength bytes.
 */
static void
GenerateIPCName(uint8 instanceId, char destIPCName[IPCNameLength])
{
  
  /* This must be 30 characters or less for portability (i.e. Darwin).
   * POSIX requires shared memory names to begin with a single slash. It 
   * should not have any others slashes or any non-alphanumerics as the
   * that is the broadest assumption of what is permitted in a filename.
   * Also, case sensitivity should not be presumed.
   *
   * Collisions are averted by the fact that the shared memory region is 
   * immediately unlinked.
   * 
   * The string is formed starting with a slash, then the identifier 'PG.',
   * then the pid of the current process.
   */
  snprintf(destIPCName, IPCNameLength, "/PG.%6ld", getpid());
}

/*
 *	InternalIpcMemoryCreate(ipcName, size)
 *
 * Attempt to create a new shared memory segment with the specified IPC name.
 * Will fail (return NULL) if such a segment already exists.  If successful,
 * attach the segment to the current process and return its attached address.
 * On success, callbacks are registered with on_shmem_exit to detach and
 * delete the segment when on_shmem_exit is called.
 *
 * If we fail with a failure code other than collision-with-existing-segment,
 * print out an error and abort.  Other types of errors are not recoverable.
 */
static void *
InternalIpcMemoryCreate(const char ipcName[IPCNameLength], uint8 instanceId, Size size)
{
	int			fd;
	void	   *shmaddr;
	struct		stat statbuf;
	
	fd = shm_open(ipcName, O_RDWR | O_CREAT | O_EXCL, IPCProtection);

	if (fd < 0)
	{
		/*
		 * Fail quietly if error indicates a collision with existing segment.
		 * One would expect EEXIST, given that we said O_EXCL.
		 */
		if (errno == EEXIST || errno == EACCES || errno == EINTR)
			return NULL;

		/*
		 * Else complain and abort
		 */
		ereport(FATAL,
				(errmsg("could not create shared memory segment: %m"),
				 errdetail("Failed system call was shm_open(name=%s, oflag=%lu, mode=%lu).",
						   ipcName, (unsigned long) O_CREAT | O_EXCL,
						   (unsigned long) IPCProtection),
				 (errno == EMFILE) ?
				 errhint("This error means that the process has reached its limit "
						 "for open file descriptors.") : 0,
				 (errno == ENOSPC) ?
				 errhint("This error means the process has ran out of address "
						 "space.") : 0));
	}
	/* the race between creation and unlinking is protected by the shared memory pid file */

	int unlink_status = shm_unlink(ipcName);
	if(unlink_status<0)
	  {
	    /* It would be virtually impossible for us to fail to unlink a shared memory region we just created, but we need to handle this anyway- refuse to use this shared memory segment. */
	    char * hint = NULL;
	    if(errno==EACCESS)
	      {
		hint = "This error means that unlink access was denied on a shared memory segment that the process created.";
	      }
	    else if(errno==ENAMETOOLONG)
	      {
		hint = "This error means that the shared memory region could be unlinked because its name was too long.";
	      }
	    else if(errno==ENOENT)
	      {
		hint = "This error means that the shared memory segment was deleted by another process.";
	      }
	    ereport(FATAL,
		    (errmsg("could not unlink shared memory segment : %m"),
		     errdetail("Failed system call was shm_unlink(name=%s).",ipcName),
		     errhint(hint)));
	    return NULL;
	  }
	
	/* Increase the size of the file descriptor to the desired length.
	 * If this fails so will mmap since it can't map size bytes. */
	fstat(fd, &statbuf);
	if (statbuf.st_size < size)
	  ftruncate(fd, size);
	
	/* OK, should be able to attach to the segment */
	shmaddr = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);

	if (shmaddr == MAP_FAILED)
	  elog(FATAL, "mmap with size=%ul and fd=%d failed: %m", (unsigned int) size, fd);

	/* Register on-exit routine to detach new segment before deleting */
	on_shmem_exit(IpcMemoryDetach, PointerGetDatum(shmaddr));

	/* Record instance ID in lockfile for data directory. */
	RecordSharedMemoryInLockFile((unsigned long) instanceId, 0);
	
	POSIXSharedMemoryFD = fd;
	return shmaddr;
}

/****************************************************************************/
/*	IpcMemoryDetach(status, shmaddr)	removes a shared memory segment		*/
/*										from process' address space		*/
/*	(called as an on_shmem_exit callback, hence funny argument list)		*/
/****************************************************************************/
static void
IpcMemoryDetach(int status, Datum shmaddr)
{
	PGShmemHeader  *hdr;
	hdr = (PGShmemHeader *) DatumGetPointer(shmaddr);
	
	if (munmap(DatumGetPointer(shmaddr), hdr->totalsize) < 0)
		elog(LOG, "munmap(%p, ...) failed: %m", DatumGetPointer(shmaddr));
}

/****************************************************************************/
/*	IpcMemoryDelete(status, fd)		deletes a shared memory segment		*/
/*	(called as an on_shmem_exit callback, hence funny argument list)		*/
/****************************************************************************/
static void
IpcMemoryDelete(int status, Datum instanceId)
{
  /*nothing to do- last close on the shm file descriptor deletes it*/
}

/*
 * PGSharedMemoryIsInUse
 *
 * Is a previously-existing shmem segment still existing and in use?
 *
 * The point of this exercise is to detect the case where a prior postmaster
 * crashed, but it left child backends that are still running.	Therefore
 * we only care about shmem segments that are associated with the intended
 * DataDir.  This is an important consideration since accidental matches of
 * shmem segment IDs are reasonably common.
 */
bool
PGSharedMemoryIsInUse(unsigned long id1, unsigned long id2)
{
	char		ipcName[IPCNameLength];
	PGShmemHeader  *hdr;
	int			fd, isValidHeader;
	
#ifndef WIN32
	struct stat statbuf;
#endif
	
	/*
	 * We detect whether a shared memory segment is in use by seeing whether
	 * we can open it. If so, 
	 */
	GenerateIPCName((uint8) id1, ipcName);
	fd = shm_open(ipcName, O_RDWR, 0);
	if (fd < 0)
	{
		/*
		 * ENOENT means the segment no longer exists.
		 */
		if (errno == ENOENT)
			return false;

		/*
		 * EACCES implies that the segment belongs to some other userid, which
		 * means that there is an different account with the same database open.
		 */
		if (errno == EACCES)
			return true;
	}

	/*
	 * Try to attach to the segment and see if it matches our data directory,
	 * just as a sanity check. Note that this is not absolutely necessary
	 * since the data directory is encoded in the IPC shared memory key name.
	 * 
	 * On Windows, which doesn't have useful inode numbers, we can't do this
	 * so we punt and assume that the shared memory is valid (which in all
	 * likelihood it is).
	 */
#ifdef WIN32
	close(fd);
	return true;
#else
	if (stat(DataDir, &statbuf) < 0)
	{
		close(fd);
		return true;			/* if can't stat, be conservative */
	}

	hdr = (PGShmemHeader *) mmap(NULL, sizeof(PGShmemHeader), PROT_READ, MAP_SHARED, fd, 0);
	close(fd);

	if (hdr == (PGShmemHeader *) -1)
		return true;			/* if can't attach, be conservative */

	isValidHeader = hdr->magic == PGShmemMagic &&
		hdr->device == statbuf.st_dev &&
		hdr->inode == statbuf.st_ino;
	munmap((void *) hdr, sizeof(PGShmemHeader));
	
	/*
	 * If true, it's either not a Postgres segment, or not one for my data
	 * directory.  In either case it poses no threat.
	 * If false, trouble -- looks a lot like there are still live backends
	 */
	
	return isValidHeader;
#endif
}


/*
 * PGSharedMemoryCreate
 *
 * Create a shared memory segment of the given size and initialize its
 * standard header.  Also, register an on_shmem_exit callback to release
 * the storage.
 *
 * Dead Postgres segments are released when found, but we do not fail upon
 * collision with non-Postgres shmem segments, although this is astronomically
 * unlikely.
 *
 * makePrivate means to always create a new segment, rather than attach to
 * or recycle any existing segment. Currently, this value is ignored as
 * all segments are newly created (the dead ones are simply released).
 *
 * Port is ignored. (It is leftover from the SysV shared memory routines.)
 */
PGShmemHeader *
PGSharedMemoryCreate(Size size, bool makePrivate, int port)
{
	uint8			instanceId;
	void		   *shmaddr;
	PGShmemHeader  *hdr;
	char			ipcName[IPCNameLength];
	
#ifndef WIN32
	struct stat		statbuf;
#endif

	/* Room for a header? */
	Assert(size > MAXALIGN(sizeof(PGShmemHeader)));

	/* Make sure PGSharedMemoryAttach doesn't fail without need */
	UsedShmemSegAddr = NULL;

	/* Loop till we find a free IPC key */
	for (instanceId = 0; true; instanceId++)
	{
		/*
		 * Try to create new segment. InternalIpcMemoryCreate encodes the data
		 * directory path name into the IPC key name, so if this fails
		 * one of three things has happened:
		 * 1) there is another postmaster still running with the same data directory
		 * 2) the postmaster in this directory crashed or was kill -9'd
		 *		and there are backends still running.
		 * 3) the postmaster in this directory crashed or was kill -9'd and there 
		 *		are no backends still running, just an orpaned shmem segment
		 *
		 * Case 1 is handled by the postmaster.pid file and doesn't concern us here.
		 * For case 2 & 3 we now should unlink the shmem segment so that it is
		 * cleaned up, either now (case 3) or when the backends terminate (case 2). 
		 * Then we should try the next instanceId to create a new segment so this
		 * process can be up and running quickly.  
		 */
		GenerateIPCName(instanceId, ipcName);
		shmaddr = InternalIpcMemoryCreate(ipcName, instanceId, size);
		if (shmaddr)
			break;				/* successful create and attach */

		/*
		 * The segment appears to be from a dead Postgres process, or from a
		 * previous cycle of life in this same process.  Zap it, if possible.
		 * This shouldn't fail, but if it does, assume the segment
		 * belongs to someone else after all, and continue quietly.
		 */
		shm_unlink(ipcName);
	}

	/* OK, we created a new segment.  Mark it as created by this process. */
	hdr = (PGShmemHeader *) shmaddr;
	hdr->creatorPID = getpid();
	hdr->magic = PGShmemMagic;

#ifndef WIN32
	/* Fill in the data directory ID info, too */
	if (stat(DataDir, &statbuf) < 0)
		ereport(FATAL,
				(errcode_for_file_access(),
				 errmsg("could not stat data directory \"%s\": %m",
						DataDir)));
	hdr->device = statbuf.st_dev;
	hdr->inode = statbuf.st_ino;
#endif

	/* Initialize space allocation status for segment. */
	hdr->totalsize = size;
	hdr->freeoffset = MAXALIGN(sizeof(PGShmemHeader));

	/* Save info for possible future use */
	UsedShmemInstanceId = instanceId;
	UsedShmemSegAddr = shmaddr;

	return hdr;
}

#ifdef EXEC_BACKEND

/*
 * PGSharedMemoryReAttach
 *
 * Re-attach to an already existing shared memory segment.	In the non
 * EXEC_BACKEND case this is not used, because postmaster children inherit
 * the shared memory segment attachment via fork().
 *
 * UsedShmemInstanceId and UsedShmemSegAddr are implicit parameters to this
 * routine.  The caller must have already restored them to the postmaster's
 * values.
 */
void
PGSharedMemoryReAttach(void)
{
	int		fd;
	void   *hdr;
	void   *origUsedShmemSegAddr = UsedShmemSegAddr;

	Assert(UsedShmemSegAddr != NULL);
	Assert(IsUnderPostmaster);

#ifdef __CYGWIN__
	/* cygipc (currently) appears to not detach on exec. */
	PGSharedMemoryDetach();
	UsedShmemSegAddr = origUsedShmemSegAddr;
#endif

	elog(DEBUG3, "attaching to %p", UsedShmemSegAddr);
	hdr = (void *) PGSharedMemoryAttach(UsedShmemInstanceId);
	if (hdr == NULL)
		elog(FATAL, "could not reattach to shared memory (instanceId=%d, addr=%p): %m",
			 (int) UsedShmemInstanceId, UsedShmemSegAddr);
	if (hdr != origUsedShmemSegAddr)
		elog(FATAL, "reattaching to shared memory returned unexpected address (got %p, expected %p)",
			 hdr, origUsedShmemSegAddr);

	UsedShmemSegAddr = hdr;		/* probably redundant */
}


/*
 * Attach to shared memory and make sure it has a Postgres header
 *
 * Returns attach address if OK, else NULL
 */
static PGShmemHeader *
PGSharedMemoryAttach(uint8 instanceId)
{
	PGShmemHeader *hdr;
	char		ipcName[IPCNameLength];
	Size		size;
	int fd;

	fd = POSIXSharedMemoryFD;

	if (fd < 0)
		return NULL;

	hdr = (PGShmemHeader *) mmap(UsedShmemSegAddr, sizeof(PGShmemHeader),
								 PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);

	if (hdr == MMAP_FAILED)
	{
		return NULL;			/* failed to mmap- unlikely */
	}

	if (hdr->magic != PGShmemMagic)
	{
		munmap((void *) hdr, sizeof(PGShmemHeader));
		return NULL;			/* segment belongs to a non-Postgres app */
	}
	
	/* Since the segment has a valid Postgres header, unmap and re-map it with the proper size */
	size = hdr->totalsize;
	munmap((void *) hdr, sizeof(PGShmemHeader));
	hdr = (PGShmemHeader *) mmap(UsedShmemSegAddr, size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
	
	if (hdr == MMAP_FAILED)   /* this shouldn't happen */
		return NULL;
	
	return hdr;
}
#endif   /* EXEC_BACKEND */

/*
 * PGSharedMemoryDetach
 *
 * Detach from the shared memory segment, if still attached.  This is not
 * intended for use by the process that originally created the segment
 * (it will have an on_shmem_exit callback registered to do that).	Rather,
 * this is for subprocesses that have inherited an attachment and want to
 * get rid of it.
 */
void
PGSharedMemoryDetach(void)
{
	PGShmemHeader  *hdr;
	if (UsedShmemSegAddr != NULL)
	{
		hdr = (PGShmemHeader *) UsedShmemSegAddr;
		if (munmap(UsedShmemSegAddr, hdr->totalsize) < 0)
			elog(LOG, "munmap(%p) failed: %m", UsedShmemSegAddr);
		UsedShmemSegAddr = NULL;
	}
}
