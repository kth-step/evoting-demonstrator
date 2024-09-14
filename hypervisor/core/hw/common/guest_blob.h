#ifndef _GUEST_BLOB_H_
#define _GUEST_BLOB_H_

/*
 * Guest "blob" definitions
 */

/* C and Assembler stuff */
#define GUESTS_MAGIC 0xfa7ec0de
#define MAX_GUESTS 8

/* C stuff */
#ifndef __ASSEMBLER__

struct guest_binary {	//Initialized by arm_guest_blob.S by reading guest_data.S
	addr_t pstart;		//Physical start address of guest = 0x8100_0000 for Linux.
	addr_t vstart;		//Virtual start address of guest = 0xC000_0000 for Linux.
	size_t psize;		//Physical memory size allocated to guest = 0x0700_0000 = 112MB for Linux.
	size_t fwsize;		//Byte size of guest image, few MBs for Linux.
	size_t offset;		//0x0001_0000 = 64kB. Not used for Linux.
};

struct guests_database {
	uint32_t count;
	uint32_t pstart, pend;
	struct guest_binary guests[MAX_GUESTS];

};

extern struct guests_database guests_db;
extern struct guest_binary *get_guest(int index);

#endif				/* __ASSEMBLER__ */

#endif				/* _GUEST_BLOB_H_ */
