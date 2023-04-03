/*
 * mm.c
 *
 * Name: Youssef Shoala
 *
 * General:
 * Each block has a header and footer with the size and the alloc bit
 * HEAP***PrologueHDR  PrologueFTR  Epilogue
 *                   ^            ^
 *                   |            |
 *               hepalistp    new blks here
 * 
 * Malloc:
 * My solution uses 14 free lists to track a variety of sizes that can be changed in the find_freelist() function. 
 * The idea is that we search through the appropriate sized freelist to find a free blk, the lists are sorted by increasing size and the first block that has enough size is returned when looking for a block. Keeping track of only freeblks increases throughput drastically. Multiple freelists help with both throughput and util
 * If no free blk is found then the heap is extended using sbrk and the new blk that's made is the freeblk that is used for the alloc
 * 
 * Free:
 * Will only change the hdr and ftr alloc bit to 0 to display it is free
 * Coalescing is implemented and the freelist will update after it has coalesced if the new coalesced block belongs in a different freelist
 * For internal fragmentation, the place funtion will never leave unused space in a block, instead it will turn that remaining space into a new freeblk
 * 
 * Realloc:
 * Assuming both parameters are valid, realloc will either:
 * 		return the same blkp with a new size smaller than the original size of the blk
 * 		call malloc to get a freeblk that can fit the specified size, then free the old ptr
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>
#include "mm.h"
#include "memlib.h"

#include <time.h>

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */





#define DEBUG



#ifdef DEBUG
// When debugging is enabled, the underlying functions get called
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
// When debugging is disabled, no code gets generated
#define dbg_printf(...)
#define dbg_assert(...)
#endif // DEBUG

// do not change the following!
#ifdef DRIVER
// create aliases for driver tests
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mm_memset
#define memcpy mm_memcpy
#endif // DRIVER

#define ALIGNMENT 16
#define WSIZE 8
#define DSIZE 16
#define CHINKSIZE (1<<12)


/*Function declaration*/
bool remove_freeblk(void *bp); 
bool place_freeblk(void *bp); 
static bool in_heap(const void* p); 
void *coalesce(void *bp);
char **find_free_list(size_t asize);
uint64_t GET_SIZE(char *p); 
char *HDRP(void *bp);


/*Private global vairables */
static char *heap_listp = 0; 		//Points to the first block in the heap
static char *freeblk_listp = 0;     //Points to the first free blk in the heap
static char *freeblk_listp1 = 0;	
static char *freeblk_listp2 = 0;	
static char *freeblk_listp3 = 0;	
static char *freeblk_listp4 = 0;	
static char *freeblk_listp5 = 0;	
static char *freeblk_listp6 = 0;	
static char *freeblk_listp7 = 0;	
static char *freeblk_listp8 = 0;	
static char *freeblk_listp9 = 0;	
static char *freeblk_listp10 = 0;
static char *freeblk_listp11 = 0;
static char *freeblk_listp12 = 0;
static char *freeblk_listp13 = 0;
static char **curr_freelist = &freeblk_listp; 		//Points to the correct list given block size

uint64_t MAX(int x, int y)
{
	return (x > y ? x : y); 
}

/*Pack a size and allocated bit into a word*/
size_t PACK(size_t size, size_t alloc)
{
	return (size | alloc); 
}

/*Read and write a word at address p*/ 
uint64_t GET(char *p)
{
	return (*(uint64_t *)(p));
}
void PUT(char *p, uint64_t val)
{
	(*(uint64_t *)(p) = (val));
}


/*Read the next and prev free block pointers*/
char *GET_NEXT_FREEBLK(char *p)
{
	curr_freelist = find_free_list(GET_SIZE(HDRP((void *)p))); 
	if(heap_listp == *curr_freelist)
	{
		return NULL; 
	}
	char *next_free = NULL; 
	memcpy(&next_free, p, 8); 
	return next_free;
}
char *GET_PREV_FREEBLK(char *p)
{
	curr_freelist = find_free_list(GET_SIZE(HDRP((void *)p))); 
	if(heap_listp == *curr_freelist)
	{
		return NULL; 
	}
	char *prev_free = NULL;
	memcpy(&prev_free, p+8, 8); 
	return (char *)prev_free;
}

/*Write the next and prev free block pointers*/
void SET_NEXT_FREEBLK(char *p, uint64_t val)
{
	//*p = val; 
	//memset(p, (int)val, 8); 
	PUT(p, val); 
}
void SET_PREV_FREEBLK(char *p, uint64_t val)
{
	//*(p+8) = val; 
	//memset(p+8, (int)val, 8);
	PUT(p+8, val); 
}

/*Read the size ald allocated fields from address p*/ 
uint64_t GET_SIZE(char *p)
{
	return (GET(p) & ~(DSIZE-1));
}
uint64_t GET_ALLOC(char *p)
{
	return (GET(p) & 0x1);
}

/*Given block pointer bp, compute address of its header and footer*/
char *HDRP(void *bp)
{
	return((char *)(bp) - WSIZE);
}
char *FTRP(void *bp)
{
	return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

/*Given block ptr bp, compute address of its header and footer*/
char *NEXT_BLKP(void *bp)
{
	return((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE));
}
char *PREV_BLKP(void *bp) 
{
	return((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE));
}

/*Rounds up to the nearest multiple of ALIGNMENT*/
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

/*Chooses which free list to use depending on size*/
char **find_free_list(size_t asize)
{
	// listXmin <= asize < listXmax
	//
	//unsigned long long int sizes[14] = {0, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65636, 131072}; //strictly pow 2
	//unsigned long long int sizes[14] = {0, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224}; //strictly +16
	//unsigned long long int sizes[14] = {0, 32, 48, 64, 80, 96, 128, 256, 512, 1024, 2048, 4096, 8192, 16384}; //5 +16 last rest pow2
	unsigned long long int sizes[14] = {0, 32, 48, 64, 80, 96, 112, 128, 512, 2048, 8192, 32768, 131072, 524288};  //half +16 half pow4
	//
	// list 0 will take any size less than list0max
	size_t list0min = sizes[0];
	size_t list0max = sizes[1];

	size_t list1min = sizes[1];
	size_t list1max = sizes[2];

	size_t list2min = sizes[2];
	size_t list2max = sizes[3];
	
	size_t list3min = sizes[3];
	size_t list3max = sizes[4]; 

	size_t list4min = sizes[4];
	size_t list4max = sizes[5];

	size_t list5min = sizes[5];
	size_t list5max = sizes[6];

	size_t list6min = sizes[6];
	size_t list6max = sizes[7];

	size_t list7min = sizes[7];
	size_t list7max = sizes[8];

	size_t list8min = sizes[8];
	size_t list8max = sizes[9];

	size_t list9min = sizes[9];
	size_t list9max = sizes[10];

	size_t list10min =sizes[10];
	size_t list10max =sizes[11];

	size_t list11min = sizes[11];
	size_t list11max = sizes[12];

	size_t list12min = sizes[12];
	size_t list12max = sizes[13];

	//list 13 takes all larger than list12max

	if(asize == 0)
	{
		return NULL; 
	}
	else if(list0min <= asize && asize < list0max)
	{
		curr_freelist = &freeblk_listp;
	}
	else if(list1min <= asize && asize < list1max)
	{
		curr_freelist = &freeblk_listp1;
	}
	else if(list2min <= asize && asize < list2max)
	{
		curr_freelist = &freeblk_listp2;
	}
	else if(list3min <= asize && asize < list3max)
	{
		curr_freelist = &freeblk_listp3;
	}
	else if(list4min <= asize && asize < list4max)
	{
		curr_freelist = &freeblk_listp4;
	}
	else if(list5min <= asize && asize < list5max)
	{
		curr_freelist = &freeblk_listp5;
	}
	else if(list6min <= asize && asize < list6max)
	{
		curr_freelist = &freeblk_listp6;
	}
	else if(list7min <= asize && asize < list7max)
	{
		curr_freelist = &freeblk_listp7;
	}
	else if(list8min <= asize && asize < list8max)
	{
		curr_freelist = &freeblk_listp8;
	}
	else if(list9min <= asize && asize < list9max)
	{
		curr_freelist = &freeblk_listp9;
	}
	else if(list10min <= asize && asize < list10max)
	{
		curr_freelist = &freeblk_listp10;
	}
	else if(list11min <= asize && asize < list11max)
	{
		curr_freelist = &freeblk_listp11;
	}
	else if(list12min <= asize && asize < list12max)
	{
		curr_freelist = &freeblk_listp12;
	}
	else
	{
		curr_freelist = &freeblk_listp13;
	}


	return curr_freelist;
}

/*search through all blocks in heap looking for a free block of adequate size, returns NULL if no fit*/
/*NOT IN USE*/
void *find_fit(size_t asize)
{
	void *bp; 

	/*
	if(asize > CHUNKSIZE)
	{
		return NULL; 
	}
	*/
	
	for (bp = heap_listp + DSIZE; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
		//mm_checkheap(7);
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
		{
			return bp; 
		}
	}
	return NULL; 
}

/*checks to see if two free blocks are in the same free list*/
bool in_same_freelist(void *bp1, void*bp2)
{
	char **bp1_freelst = find_free_list(GET_SIZE(HDRP(bp1))); 
	char **bp2_freelst = find_free_list(GET_SIZE(HDRP(bp2)));
	return *bp1_freelst == *bp2_freelst;
}

/*loops through the appropriate freeblk list and returns the first free block of appropriate size, else null*/
/*MAYBE: Use binary search for added throughput*/
void *find_fit_given_free_list(size_t asize)
{
	curr_freelist = find_free_list(asize);

	if(*curr_freelist == heap_listp)
	{
		return NULL; 
	}
	/*
	 * MAYBE: if i need more space util, make this a for loop and search all 
	 * freelists with greater size than current block, this will take 
	 * longer and decrease throughput a bit
	 */
	char *bp; 
	for(bp = *curr_freelist; GET_NEXT_FREEBLK(bp) != 0; bp = GET_NEXT_FREEBLK(bp))
	{
		if(asize<=GET_SIZE(HDRP(bp)))
		{
			return bp; 
		}
	}
	if(asize<=GET_SIZE(HDRP(bp)))
	{
		return bp; 
	}

	return NULL; 
}

/*allocates the given free block for size asize*/
void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp)); 

	/*if the block we are placing is smaller than the free block its going into,
	  split it so that the free space is a new free block*/ 
	PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));
	remove_freeblk(bp); 
	if ((csize - asize) >= (2*DSIZE))
	{
		PUT(HDRP(bp), PACK(asize, 1)); 
		//TOREM: 
		PUT(FTRP(bp), PACK(asize, 1)); 
		char *newbp = NEXT_BLKP(bp); 
		PUT(HDRP(newbp), PACK(csize-asize, 0)); 
		PUT(FTRP(newbp), PACK(csize-asize, 0)); 
		coalesce(newbp);
	}

	/*if its the perfect size, simply change the free block to allocated*/
	else
	{
		PUT(HDRP(bp), PACK(csize, 1));
		//TOREM:
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

/*places a free block into the proper freeblk list*/
bool place_freeblk(void *new_freeblk)
{
	
	//dbg code
//	clock_t start, end; 
//	double CPUtime; 
//	start = clock();
	//end dbg

	curr_freelist = find_free_list(GET_SIZE(HDRP(new_freeblk)));

	//returns false if passed block is not free
	if(GET_ALLOC(HDRP(new_freeblk)))
	{
		return false; 
	}
	

	//initialises list to first free blk if currenlty empty
	if(*curr_freelist == heap_listp)
	{
		*curr_freelist = new_freeblk; 
		SET_NEXT_FREEBLK(*curr_freelist, 0x00000000);
		SET_PREV_FREEBLK(*curr_freelist, 0x00000000);

		//dbg code
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("PlaceFreBlk EMPTY took: %f s\n", CPUtime);
		//end dbg

		return true; 
	}

	//otherwise placed the new freeblk in its sorted position by increasing size
	else
	{
		// nb cb next
		char *comp_block = *curr_freelist; 
		{
			*curr_freelist = new_freeblk; 
			SET_PREV_FREEBLK(new_freeblk, (uint64_t)0x00000000); 
			SET_NEXT_FREEBLK(new_freeblk, (uint64_t)comp_block); 
			SET_PREV_FREEBLK(comp_block, (uint64_t)new_freeblk);

			//dbg code
		//	end = clock();
		//	CPUtime = (double)((end - start));
		//	dbg_printf("PlaceFreBlk FIRST took: %f s\n", CPUtime);
			//end dbg

			return true; 
		}
		// prev nb cb next
		while(in_heap(GET_NEXT_FREEBLK(comp_block)))
		{
			if(GET_SIZE(HDRP(comp_block)) >=  GET_SIZE(HDRP(new_freeblk)))
			{	
				SET_NEXT_FREEBLK(new_freeblk, (uint64_t)comp_block); 
				SET_PREV_FREEBLK(new_freeblk, (uint64_t)GET_PREV_FREEBLK(comp_block)); 	
				SET_NEXT_FREEBLK(GET_PREV_FREEBLK(comp_block), (uint64_t)new_freeblk); 
				SET_PREV_FREEBLK(comp_block, (uint64_t)new_freeblk); 

				//dbg code
			//	end = clock();
			//	CPUtime = (double)((end - start));
			//	dbg_printf("PlaceFreBlk MID took: %f s\n", CPUtime);
				//end dbg

				return true; 
			}
			comp_block = GET_NEXT_FREEBLK(comp_block); 
		}
		// prev nb cb 
		if(GET_SIZE(HDRP(comp_block)) >= GET_SIZE(HDRP(new_freeblk)))
		{
			SET_NEXT_FREEBLK(new_freeblk, (uint64_t)comp_block); 
			SET_PREV_FREEBLK(new_freeblk, (uint64_t)GET_PREV_FREEBLK(comp_block)); 	
			SET_NEXT_FREEBLK(GET_PREV_FREEBLK(comp_block), (uint64_t)new_freeblk); 
			SET_PREV_FREEBLK(comp_block, (uint64_t)new_freeblk); 

			//dbg code
		//	end = clock();
		//	CPUtime = (double)((end - start));
		//	dbg_printf("PlaceFreBlk B4LAST took: %f s\n", CPUtime);
			//end dbg

			return true; 
		}
		// prev cb nb
		else
		{
			SET_NEXT_FREEBLK(comp_block, (uint64_t)new_freeblk);
			SET_PREV_FREEBLK(new_freeblk, (uint64_t)comp_block); 
			SET_NEXT_FREEBLK(new_freeblk, (uint64_t)0x00000000);

			//dbg code
		//	end = clock();
		//	CPUtime = (double)((end - start));
		//	dbg_printf("PlaceFreBlk LAST took: %f s\n", CPUtime);
			//end dbg

			return true; 
		}

		/*
		//otherwise sets the next free blk of the last free blk to the new freeblk
		char *bp = *curr_freelist; 
		while(GET_NEXT_FREEBLK(bp) != 0)
		{
			bp = GET_NEXT_FREEBLK(bp); 
		}
		SET_NEXT_FREEBLK(bp, (uint64_t)new_freeblk); 
		SET_PREV_FREEBLK(new_freeblk, (uint64_t)bp); 
		SET_NEXT_FREEBLK(new_freeblk, 0); 

		return true; 
		*/
	}
	return false; 
} 


/*remove a free block from the freeblk list*/ 
bool remove_freeblk(void *block_to_remove)
{
	
	//dbg code
//	clock_t start, end; 
//	double CPUtime; 
//	start = clock();
	//end dbg

	curr_freelist = find_free_list(GET_SIZE(HDRP(block_to_remove)));

	//returns false if freelist is uninitialised
	if(*curr_freelist == heap_listp)    
	{
		return false;
	}
	//returns false if block is currently free
	if(!GET_ALLOC(HDRP(block_to_remove)))
	{
		return false; 
	}
	if(block_to_remove == *curr_freelist)
	{
		//if we are removing the first and only block of the list, set the list back to uninitialised
		if(GET_NEXT_FREEBLK(*curr_freelist) == 0)
		{
			*curr_freelist = heap_listp; 
		}
		//if we are removing the first block of the list and there are still blocks left, 
		//set the head of the list to the second element in the list
		else
		{
			SET_PREV_FREEBLK(GET_NEXT_FREEBLK(*curr_freelist), 0); 
			*curr_freelist = GET_NEXT_FREEBLK(*curr_freelist); 	

		}

		//dbg code
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("RemFreBlk FIRST took: %f s\n", CPUtime);
		//end dbg

		return true; 
	}
	//loop through the rest of the freelist and extract the block to remove if found
	void *bp; 
	for(bp = *curr_freelist; GET_NEXT_FREEBLK(bp) != 0; bp = GET_NEXT_FREEBLK(bp))
	{
		if(bp == block_to_remove)
		{
			SET_NEXT_FREEBLK(GET_PREV_FREEBLK(bp), (uint64_t)GET_NEXT_FREEBLK(bp)); 
			
			SET_PREV_FREEBLK(GET_NEXT_FREEBLK(bp), (uint64_t)GET_PREV_FREEBLK(bp)); 

			//dbg code
		//	end = clock();
		//	CPUtime = (double)((end - start));
		//	dbg_printf("RemFreBlk MID took: %f s\n", CPUtime);
			//end dbg		

			return true; 
		}
	}
	//this is an extra iteration incase the block to remove is the last block in the list
	if(bp == block_to_remove)
	{
		SET_NEXT_FREEBLK(GET_PREV_FREEBLK(bp), 0); 

		//dbg code
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("RemFreBlk LAST took: %f s\n", CPUtime);
		//end dbg	

		return true; 
	}
	
	return false; 
}

/*combines adjacent free blocks then places it in the appropriate free list*/
void *coalesce(void *bp)
{
	//dbg code
//	clock_t start, end; 
//	double CPUtime; 
//	start = clock();
	//end dbg

	size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp)); 

	/*Case 1: Neither blocks free*/
	if((prev_alloc && next_alloc))
	{
		place_freeblk(bp); 

		//dbg code
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("Coalesce NONE took: %f s\n", CPUtime);
		//end dbg
	
		return bp;  
	}

	/*Case 2: Only next block free*/ 
	else if(prev_alloc && !next_alloc)
	{
		char *blk_to_remove = NEXT_BLKP(bp);

		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		
		PUT(HDRP(blk_to_remove), PACK(GET_SIZE(HDRP(blk_to_remove)), 1)); 
		remove_freeblk(blk_to_remove); 

		PUT(HDRP(bp), PACK(size, 0)); 
		PUT(FTRP(bp), PACK(size, 0)); 


		place_freeblk(bp); 

		//dbg code
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("Coalesce NEXT took: %f s\n", CPUtime);
		//end dbg
		
		return bp; 
	}

	/*Case 3: Only prev block free*/
	else if(!prev_alloc && next_alloc)
	{	
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		if(find_free_list(GET_SIZE(HDRP(PREV_BLKP(bp)))) == find_free_list(size))
		{
			PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
			PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
			bp = PREV_BLKP(bp);
		}
		else
		{
			PUT(HDRP(PREV_BLKP(bp)), PACK(GET_SIZE(HDRP(PREV_BLKP(bp))), 1)); 
			remove_freeblk(PREV_BLKP(bp));
			PUT(HDRP(PREV_BLKP(bp)), PACK(GET_SIZE(HDRP(PREV_BLKP(bp))), 0)); 
			PUT(FTRP(bp), PACK(size, 0));
			PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
			bp = PREV_BLKP(bp);
			place_freeblk(bp);
		}
		//dbg code
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("Coalesce PREV took: %f s\n", CPUtime);
		//end dbg
	}

	/*Case 4: Both prev and next free*/
	else if(!prev_alloc && !next_alloc)
	{
		PUT(HDRP(NEXT_BLKP(bp)), PACK(GET_SIZE(HDRP(NEXT_BLKP(bp))), 1)); 
		remove_freeblk(NEXT_BLKP(bp));

		size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)))); 
		if(find_free_list(GET_SIZE(HDRP(bp))) == find_free_list(size))
		{
			PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
			PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0)); 
			bp = PREV_BLKP(bp); 
	
			//SET_NEXT_FREEBLK(bp, (uint64_t)GET_NEXT_FREEBLK(GET_NEXT_FREEBLK(bp)));
			//SET_PREV_FREEBLK(GET_NEXT_FREEBLK(bp), (uint64_t)bp);
		}
		else 
		{
			PUT(HDRP(PREV_BLKP(bp)), PACK(GET_SIZE(HDRP(PREV_BLKP(bp))), 1)); 
			remove_freeblk(PREV_BLKP(bp));
			PUT(HDRP(PREV_BLKP(bp)), PACK(GET_SIZE(HDRP(PREV_BLKP(bp))), 0)); 
			
			PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
			PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0)); 
			bp = PREV_BLKP(bp); 
	
			//SET_NEXT_FREEBLK(bp, (uint64_t)GET_NEXT_FREEBLK(GET_NEXT_FREEBLK(bp)));
			//SET_PREV_FREEBLK(GET_NEXT_FREEBLK(bp), (uint64_t)bp);
			place_freeblk(bp);
		}
		
		//dbg code
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("Coalesce PREV&NEXT took: %f s\n", CPUtime);
		//end dbg
	}

	else
	{
		return NULL; 
	}
	return bp; 
}

/*extends heap by n bytes*/ 
void *extend_heap(size_t bytes)
{
	char *bp; 
	size_t size = bytes; 

	/*Allocate an even number of words to maintain alignment*/
	size = align(size);

	//extends heap returning null if it fails
	if((long)(bp = mm_sbrk(size)) == -1)
	{
		return NULL; 
	}


	/*Initialize free block header/footer and the epilogue header*/
	PUT(HDRP(bp), PACK(size, 0));			//Free block header
	PUT(FTRP(bp), PACK(size, 0));			//Free block footer 
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));	//New epilogue header 

	return coalesce(bp); 
}

/*
 * mm_init: returns false on error, true on success.
 */
bool mm_init(void)
{
	/*Create initial empty heap*/
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
	{
		return false; 
	}
	PUT(heap_listp, 0); 							//Alighment header
	PUT(heap_listp + (WSIZE), PACK(DSIZE, 1));		//Prologue header
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); 	//Prologue footer
	PUT(heap_listp + (3*WSIZE), PACK(0, 1)); 		//Epilogue header

	//Initialise all the list pointers, these will ALWAYS point to the beginning of the specified list
	heap_listp += (2*WSIZE); //points inbetween the prologue header and footer 
	freeblk_listp = heap_listp; 
	freeblk_listp1 = heap_listp; 
	freeblk_listp2 = heap_listp; 
	freeblk_listp3 = heap_listp; 
	freeblk_listp4 = heap_listp; 
	freeblk_listp5 = heap_listp; 
	freeblk_listp6 = heap_listp; 
	freeblk_listp7 = heap_listp; 
	freeblk_listp8 = heap_listp; 
	freeblk_listp9 = heap_listp; 
	freeblk_listp10 = heap_listp; 
	freeblk_listp11 = heap_listp; 
	freeblk_listp12 = heap_listp; 
	freeblk_listp13 = heap_listp; 

	return true;
}

/*
 * malloc 
 */
void* malloc(size_t size)
{
	//dbg code
	//mm_checkheap(15);
	dbg_printf("calling malloc with size = %zu\n", size);
	//end dbg

	size_t asize; 		//adjusted block size
	char *bp; 			//block pointer

	/*Ignore spurious requests*/
	if (size == 0)
	{
		return NULL; 
	}

	/*Adjust block size to include overhead and alignment reqs*/
	if (size <= DSIZE)
	{
		asize = 2*DSIZE; 
	}
	else
	{
		asize = align(size+DSIZE); 
	}

	//dbg code	
//	clock_t start, end; 
//	double CPUtime; 
//	start = clock(); 
	//end dbg


	/*Search free list for a fit if found place it in returned block*/
	if ((bp = find_fit_given_free_list(asize)) != NULL) 
	{
		place(bp, asize); 

		//dbg code
	//	end = clock(); 
	//	CPUtime = (double)((end - start));
	//	dbg_printf("Malloc size %ld find fit took: %f s\n", size, CPUtime);
	//	mm_checkheap(16);
		//end dbg

		return bp; 
	}


	//dbg code	
//	start = clock(); 
	//end dbg

	/*No fit, increase heap size to get a fit*/
	if ((bp = extend_heap(asize)) == NULL)
	{
		return NULL; 
	}
	/*place in returned freeblock form extendheap()*/
	place(bp, asize); 

	//dbg code
//	end = clock();
//	CPUtime = (double)((end - start));
//	dbg_printf("Malloc size %ld extend heap took: %f s\n", size, CPUtime);
//	mm_checkheap(16);
	//end dbg

	return bp; 
}

/*
 * free
 */
void free(void* ptr)
{
	//dbg code
//	clock_t start, end; 
//	double CPUtime; 
//	start = clock();
	//mm_checkheap(15);
	dbg_printf("calling free on blk %p w/ size = %zu\n", ptr, GET_SIZE(HDRP(ptr)));
	//end dbg

	/*change block header to portray that it is now free*/
	size_t size = GET_SIZE(HDRP(ptr)); 
	PUT(HDRP(ptr), PACK(size, 0)); 
	PUT(FTRP(ptr), PACK(size, 0)); 
	
	coalesce(ptr); 

	//dbg code
//	end = clock();
//	CPUtime = (double)((end - start));
//	dbg_printf("Free blk %p took: %f s\n", ptr, CPUtime);
//	mm_checkheap(16);
	//end dbg
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
	//dbg code
//	clock_t start, end; 
//	double CPUtime; 
//	start = clock();
	//mm_checkheap(15);
	dbg_printf("Calling realloc w size = %ld; oldp = %p\n", size, oldptr); 
	//end dbg

	if (oldptr == NULL) 
	{
		return malloc(size); 
	}

	else if(size == 0) 
	{
		free(oldptr); 
		return NULL; 
	}
	
	/*if block the oldptr points to is large enough, place block and return the same pointer*/ 
	size_t asize = align(size + DSIZE); 
	if (GET_SIZE(HDRP(oldptr)) >= asize)
	{
		//free(oldptr) --could cause problem when coalescing
		place(oldptr, asize); 

		//dbg code 
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("Realloc IS large enough size %ld ptr %p took: %f s\n", size, oldptr, CPUtime);
	//	mm_checkheap(16);
		//end dbg

		return oldptr; 
	}

	/*if the oldpointer does not have enough room, 
	 * return the address of another block with enough space, 
	 * copy the content from the oldptr to the new block and free the old block*/
	else
	{
		void *newptr = malloc(size); 
	    memcpy(newptr, oldptr, GET_SIZE(HDRP(oldptr))-DSIZE);	
		free(oldptr);
		
		//dbg code 
	//	end = clock();
	//	CPUtime = (double)((end - start));
	//	dbg_printf("Realloc NOT large enough size %ld ptr %p took: %f s\n", size, oldptr, CPUtime);
	//	mm_checkheap(16);
		//end dbg

		return newptr; 
	} 
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mm_heap_hi() && p >= mm_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}
/*
 *Checks if given block is in given freelist
 */
static bool blk_in_freelist(char *blkp, char *curr_freelist_dbg)
{
	if(curr_freelist_dbg == heap_listp)
	{
		return false; 
	}
	char *bp; 
	for(bp = curr_freelist_dbg; in_heap(GET_NEXT_FREEBLK(bp)); bp = GET_NEXT_FREEBLK(bp))
	{
		if(blkp == bp)
		{
			return true; 
		}
	}
	if(blkp == bp)
	{
		return true; 
	}
	return false; 


}

/*
 * mm_checkheap
 * Lineno: 
 * 0-14  ---->  display freeblk_listp(0-6)
 * 15    ---->  display current state of heap
 * 16   ---->  crosscheck freelist and heap (assert)
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    // Write code to check heap invariants here
	
	if(lineno == 15)
	{		
			int i = 0; 
			long size = 0; 
			dbg_printf("Heap Begins Here _________-----------------_____________--------\n");
			for(void *bp = heap_listp + DSIZE; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
			{

				if(GET_ALLOC(HDRP(bp)))
				{
					size += (long)GET_SIZE(HDRP(bp));
				}		
				
				dbg_assert(in_heap(bp));
				dbg_assert(aligned(bp));
				
				dbg_printf("-->Block %d = %p\n", i, bp);
				i++;
				dbg_printf("A=%ld         SZE=%ld\n\n", GET_ALLOC(HDRP(bp)), GET_SIZE(HDRP(bp)));	
			}
			dbg_printf("End Heap!!>>>>>>>>!!>>>>>>>>>>>!!\n\n");
			dbg_printf("---heapsize                 = %ld\n", mm_heapsize()); 
			dbg_printf("---total alloced blockspace = %ld\n\n\n ", size); 
	}
					
	if(lineno >= 0 && lineno<15)
	{
			char **curr_freelist_dbg; 
			dbg_printf("CURR FREELIST: %p\n", curr_freelist); 
			if(lineno == 0)
			{
				curr_freelist_dbg = &freeblk_listp;
				dbg_printf("FREE LIST 0: %p\n", &freeblk_listp); 
			}
			else if(lineno == 1)
			{
				curr_freelist_dbg = &freeblk_listp1;
				dbg_printf("FREE LIST 1: %p\n", &freeblk_listp1); 
			}	
			else if(lineno == 2)
			{
				curr_freelist_dbg = &freeblk_listp2;
				dbg_printf("FREE LIST 2: %p\n", &freeblk_listp2); 
			}
			else if(lineno == 3)
			{
				curr_freelist_dbg = &freeblk_listp3;
				dbg_printf("FREE LIST 3: %p\n", &freeblk_listp3); 
			}
			else if(lineno == 4)
			{	
				curr_freelist_dbg = &freeblk_listp4;
				dbg_printf("FREE LIST 4: %p\n", &freeblk_listp4); 
			}
			else if(lineno == 5)
			{
				curr_freelist_dbg = &freeblk_listp5;
				dbg_printf("FREE LIST 5: %p\n", &freeblk_listp5); 
			}
			else if(lineno == 6)
			{
				curr_freelist_dbg = &freeblk_listp6;
				dbg_printf("FREE LIST 6: %p\n", &freeblk_listp6); 
			}
			else if(lineno == 7)
			{
				curr_freelist_dbg = &freeblk_listp7;
				dbg_printf("FREE LIST 7: %p\n", &freeblk_listp7); 
			}
			else if(lineno == 8)
			{
				curr_freelist_dbg = &freeblk_listp8;
				dbg_printf("FREE LIST 8: %p\n", &freeblk_listp8); 
			}
			else if(lineno == 9)
			{
				curr_freelist_dbg = &freeblk_listp9;
				dbg_printf("FREE LIST 9: %p\n", &freeblk_listp9); 
			}
			else if(lineno == 10)
			{
				curr_freelist_dbg = &freeblk_listp10;
				dbg_printf("FREE LIST 10: %p\n", &freeblk_listp10); 
			}
			else if(lineno == 11)
			{
				curr_freelist_dbg = &freeblk_listp11;
				dbg_printf("FREE LIST 11: %p\n", &freeblk_listp11); 
			}
			else if(lineno == 12)
			{
				curr_freelist_dbg = &freeblk_listp12;
				dbg_printf("FREE LIST 12: %p\n", &freeblk_listp12); 
			}
			else if(lineno == 13)
			{
				curr_freelist_dbg = &freeblk_listp13;
				dbg_printf("FREE LIST 13: %p\n", &freeblk_listp13); 
			}
			else
			{
				dbg_printf("somethings gone wrong w the freelists\n");
				return false; 
			}
			dbg_printf("\n"); 
	
			
			if(*curr_freelist_dbg == heap_listp)
			{
				dbg_printf("heap_listp = %p\n", heap_listp); 
				dbg_printf("*curr_freelist = %p\n\n", *curr_freelist_dbg); 
				dbg_printf("FREE LIST CURRENTLY EMPTY!!!!!!!!!!!!!!!!!!!\n\n");
				return false; 
			}

			dbg_printf("FREE LIST -------------->>>>>>>>>>>---------------->>>>>>>>>>>>>>-----------\n");
			dbg_printf("heap_listp = %p\n", heap_listp); 
			dbg_printf("*curr_freelist = %p\n\n", *curr_freelist_dbg); 
			int i = 0; 
			char *bp; 
			for(bp = *curr_freelist_dbg; in_heap(GET_NEXT_FREEBLK(bp)); bp = GET_NEXT_FREEBLK(bp))
			{
				dbg_printf("-->free blk %d\n", i); 
				i++; 
				dbg_printf("prev = %p\n", GET_PREV_FREEBLK(bp));
				dbg_printf("curr = %p\n", bp);
				dbg_printf("next = %p\n\n", GET_NEXT_FREEBLK(bp));
			}

			dbg_printf("-->free blk LAST\n"); 
			dbg_printf("prev = %p\n", GET_PREV_FREEBLK(bp));
			dbg_printf("curr = %p\n", bp);
			dbg_printf("next = %p\n\n", GET_NEXT_FREEBLK(bp));

			dbg_printf("END FREE LST-------------------<<<<<<<<<<<<--------------\n\n\n\n\n");
	}

	//Assert: block in heap, block size appropriate for curr freelist, block is free, prev and next valid
	if(lineno == 16)
	{
		unsigned long long int sizes[15] = {1, 32, 48, 64, 80, 96, 112, 128, 512, 2048, 8192, 32768, 131072, 524288, 1000000000000000000};  //half +16 half pow4
		for(int i = 0; i<14; i++)
		{	
			char **curr_freelist_dbg = find_free_list(sizes[i]); 
			dbg_printf("Cheking FreeList: %d: %p\n", i, *curr_freelist_dbg); 
			if(*curr_freelist_dbg == heap_listp)
			{
				dbg_printf("List empty, checking if freelist is initialised properly\n\n");
				dbg_assert(GET_NEXT_FREEBLK(*curr_freelist_dbg) == NULL);
				dbg_assert(GET_PREV_FREEBLK(*curr_freelist_dbg) == NULL); 
				continue; 
			}

			char *bp = *curr_freelist_dbg; 
			char *prev_bp = NULL; 
			int freeblks_in_freelist = 1;
			for(bp = *curr_freelist_dbg; in_heap(GET_NEXT_FREEBLK(bp)); bp = GET_NEXT_FREEBLK(bp))
			{
				dbg_printf("Checking freeblk size and alloc of block %p\n", bp); 
				dbg_assert(sizes[i] <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) < sizes[i+1]); 
				dbg_assert(!GET_ALLOC(HDRP(bp)));

				dbg_printf("Checking prev freeblk = %p of curr freeblk equals actual prev blk = %p\n", GET_PREV_FREEBLK(bp), prev_bp); 
				dbg_assert(GET_PREV_FREEBLK(bp) == prev_bp); 
				prev_bp = bp; 
				freeblks_in_freelist ++;
			}
			dbg_printf("Checking last block of freelist\n"); 

			dbg_printf("Checking freeblk size and alloc of block %p\n", bp); 
			dbg_assert(GET_PREV_FREEBLK(bp) == prev_bp);
			dbg_assert(!GET_ALLOC(HDRP(bp)));
			
			dbg_printf("Checking prev freeblk = %p of curr freeblk equals actual prev blk = %p\n", GET_PREV_FREEBLK(bp), prev_bp); 
			dbg_assert(sizes[i] <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) < sizes[i+1]); 

			dbg_printf("Checking nextblk of last block: %p is NULL\n", bp); 
			dbg_assert(GET_NEXT_FREEBLK(bp) == NULL); 
			
			dbg_printf("\n");
			
			//for loop to check if any free blks in heap of appropriate size are not accounted for 
			int freeblks_in_heap = 0;
			for(bp = heap_listp; in_heap(NEXT_BLKP(bp)); bp = NEXT_BLKP(bp))
			{
				if(!GET_ALLOC(HDRP(bp)) && sizes[i] <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) < sizes[i+1])
				{
					dbg_printf("Checking freeblk %p is in freelist %i, %p\n", bp, i, *curr_freelist_dbg); 
					dbg_assert(blk_in_freelist(bp, *curr_freelist_dbg));
					freeblks_in_heap ++;
				}
			}
			if(!GET_ALLOC(HDRP(bp)) && sizes[i] <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) < sizes[i+1])
			{
				dbg_printf("Checking freeblk %p is in freelist %i, %p\n", bp, i, *curr_freelist_dbg); 
				dbg_assert(blk_in_freelist(bp, *curr_freelist_dbg));
				freeblks_in_heap ++;
			}
			dbg_printf("Ensuring same num freeblks in heap as in freelist\n");
			dbg_assert(freeblks_in_heap == freeblks_in_freelist);
			dbg_printf("\n");
		}
		return true; 
	}
	
#endif // DEBUG
    return true;
	
}
