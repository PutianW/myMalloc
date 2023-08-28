#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation

  if ((int) raw_size == 0) {
    return NULL;
  }

  int size8 = ((raw_size + 7) / 8) * 8;
  if (size8 < ALLOC_HEADER_SIZE) {
    size8 = ALLOC_HEADER_SIZE;
  }

  int i = (size8 / 8) - 1;

  for (; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    if (freelist->next != freelist) {
      break;
    }
  }

  if (i >= N_LISTS) {
    i = N_LISTS - 1;
  }

  header * freelist = &freelistSentinels[i];
  header * p = freelist->next;
  size_t whole_size = size8 + ALLOC_HEADER_SIZE;

  // search in the last freelist
  while (p != freelist && get_size(p) < whole_size) {
    p = p->next;
  }

  // when it needs to allocate new chunk(s)
  if (p == freelist) {

    header * last_header = get_left_header(lastFencePost);
    header * big_block;
    size_t big_size;

    header * hdr = allocate_chunk(ARENA_SIZE);
    if (((char *) hdr - (char *) lastFencePost) > 2 * ALLOC_HEADER_SIZE) {

      big_block = hdr;
      big_size = get_size(hdr);
      insert_os_chunk(get_left_header(hdr));
      lastFencePost = get_right_header(big_block);
      lastFencePost->left_size = big_size;
      last_header = big_block;

    } else {
      if (get_state(last_header) == ALLOCATED) {

        big_block = lastFencePost;
        big_size = ARENA_SIZE;
        set_state(big_block, UNALLOCATED);
        set_size(big_block, big_size);
        lastFencePost = get_right_header(big_block);
        lastFencePost->left_size = big_size;
        last_header = big_block;

      } else {

        last_header->prev->next = last_header->next;
        last_header->next->prev = last_header->prev;
        big_block = last_header;
        big_size = get_size(big_block) + ARENA_SIZE;
        set_size(big_block, big_size);
        lastFencePost = get_right_header(big_block);
        lastFencePost->left_size = big_size;
        last_header = big_block;

      }
    }

    while (big_size < whole_size) {
      header * hdr = allocate_chunk(ARENA_SIZE);
      
      big_size = get_size(big_block) + ARENA_SIZE;
      set_size(big_block, big_size);
      lastFencePost = get_right_header(big_block);
      lastFencePost->left_size = big_size;
    }

    p = big_block;

    // put the new chunk "p" into the last freelist
    header * q = &freelistSentinels[N_LISTS - 1];
    p->next = q->next;
    p->prev = q;
    q->next->prev = p;
    q->next = p;
  }

  // when we don't need to split the block
  size_t remainder = get_size(p) - whole_size;
  if (remainder < 2 * ALLOC_HEADER_SIZE) {
    p->prev->next = p->next;
    p->next->prev = p->prev;
    char * data = p->data;
    set_state(p, ALLOCATED);
    return (header *) data;
  }

  // split the block when we need to
  header * right_hdr = get_right_header(p);
  set_size(p, remainder);
  
  // create new allocated header called split_hdr
  header * split_hdr = (header *) ((char *) (right_hdr) - whole_size);
  set_size(split_hdr, whole_size);
  set_state(split_hdr, ALLOCATED);
  split_hdr->left_size = remainder;

  // reset the left size of the right_hdr
  right_hdr->left_size = whole_size;

  // modified the position of remainder block "p" in the freelistsentinels (if needed)
  int pos = (int) ((remainder - ALLOC_HEADER_SIZE - 1) / 8);
  if (pos < N_LISTS - 2) {

    p->prev->next = p->next;
    p->next->prev = p->prev;

    header * q = &freelistSentinels[pos];

    p->next = q->next;
    p->prev = q;
    q->next->prev = p;
    q->next = p;
  }

  // return split_hdr's data pointer
  char * split_data = split_hdr->data;
  return (header *) split_data;

}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation

  if (p == NULL) {
    return;
  }

  header * hdr = (header *) ((char *) p - ALLOC_HEADER_SIZE);

  // check double-free error
  if (get_state(hdr) == UNALLOCATED) {
    printf("Double Free Detected\n");
    printf("Assertion Failed!\n");
    exit(1);
  }

  header * right_hdr = get_right_header(hdr);
  header * left_hdr = get_left_header(hdr);
  set_state(hdr, UNALLOCATED);
  size_t block_size = get_size(hdr);
  size_t data_size = block_size - ALLOC_HEADER_SIZE;
  size_t right_block_size = get_size(right_hdr);
  size_t left_block_size = get_size(left_hdr);
  int size8 = ((data_size + 7) / 8) * 8;
  if (size8 < ALLOC_HEADER_SIZE) {
    size8 = ALLOC_HEADER_SIZE;
  }

  int i = (size8 / 8) - 1;
  if (i > N_LISTS - 1) {
    i = N_LISTS - 1;
  }


  // A U A
  if (get_state(right_hdr) != UNALLOCATED && get_state(left_hdr) != UNALLOCATED) {
    header * q = &freelistSentinels[i];
    hdr->next = q->next;
    hdr->prev = q;
    q->next->prev = hdr;
    q->next = hdr;
  }
    

  // A U U
  if (get_state(right_hdr) == UNALLOCATED && get_state(left_hdr) != UNALLOCATED) {
    header * right_right_hdr = get_right_header(right_hdr);
    size_t updated_size = block_size + right_block_size;
    right_right_hdr->left_size = updated_size;

    set_size(hdr, updated_size);

    if (get_size(right_hdr) - ALLOC_HEADER_SIZE >= 8 * (N_LISTS)) {
      hdr->next = right_hdr->next;
      hdr->prev = right_hdr->prev;
      right_hdr->prev->next = hdr;
      right_hdr->next->prev = hdr;
    } else {
      right_hdr->prev->next = right_hdr->next;
      right_hdr->next->prev = right_hdr->prev;
      int i = ((updated_size - ALLOC_HEADER_SIZE) / 8) - 1;
      if (i > N_LISTS - 1) {
        i = N_LISTS - 1;
      }

      header * q = &freelistSentinels[i];
      hdr->next = q->next;
      hdr->prev = q;
      q->next->prev = hdr;
      q->next = hdr;
    }
      
  }


  // U U A
  if (get_state(right_hdr) != UNALLOCATED && get_state(left_hdr) == UNALLOCATED) {
    size_t updated_size = block_size + left_block_size;
    right_hdr->left_size = updated_size;

    set_size(left_hdr, updated_size);

    if (get_size(left_hdr) - ALLOC_HEADER_SIZE < 8 * (N_LISTS)) {
        
      left_hdr->prev->next = left_hdr->next;
      left_hdr->next->prev = left_hdr->prev;
      int i = ((updated_size - ALLOC_HEADER_SIZE) / 8) - 1;
      if (i > N_LISTS - 1) {
        i = N_LISTS - 1;
      }

      header * q = &freelistSentinels[i];
      left_hdr->next = q->next;
      left_hdr->prev = q;
      q->next->prev = left_hdr;
      q->next = left_hdr;
    }
      
  }


  // U U U
  if (get_state(right_hdr) == UNALLOCATED && get_state(left_hdr) == UNALLOCATED) {
    header * right_right_hdr = get_right_header(right_hdr);
    size_t updated_size = left_block_size + block_size + right_block_size;
    right_right_hdr->left_size = updated_size;

    right_hdr->prev->next = right_hdr->next;
    right_hdr->next->prev = right_hdr->prev;

    set_size(left_hdr, updated_size);

    if (get_size(left_hdr) - ALLOC_HEADER_SIZE < 8 * (N_LISTS)) {

      left_hdr->prev->next = left_hdr->next;
      left_hdr->next->prev = left_hdr->prev;
      int i = ((updated_size - ALLOC_HEADER_SIZE) / 8) - 1;
      if (i > N_LISTS - 1) {
        i = N_LISTS - 1;
      }

      header * q = &freelistSentinels[i];
      left_hdr->next = q->next;
      left_hdr->prev = q;
      q->next->prev = left_hdr;
      q->next = left_hdr;
    }

  }

}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size);
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
