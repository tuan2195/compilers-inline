#include <stdio.h>
#include "gc.h"

static int *old_start = NULL;
static int *old_end   = NULL;
static int *new_start = NULL;

void naive_print_heap(int* heap, int size) {
  for(int i = 0; i < size; ++i)
    printf("  %p: %p (%d)\n", (heap + i), (int*)(*(heap + i)), *(heap + i));
}

// Implement the functions below

static void implement_print_heap(FILE* out, int* cur, int* end)
{
    while(cur < end)
    {
        fprintf(out, "%p: ", cur);
        printHelp(out, *cur);
        fprintf(out, "\n");
        if ((*cur & BIT3_MASK) == FUNC_TAG)
        {
            int* addr = (int*)(*cur - FUNC_TAG);
            cur += addr[2];
        }
        else if ((*cur & BIT3_MASK) == TUPLE_TAG)
        {
            int* addr = (int*)(*cur - TUPLE_TAG);
            cur += (*addr) + (((*addr) % 2) ? 1 : 2);
        }
        else ++cur;
    }
}
void smarter_print_heap(int* from_start, int* from_end, int* to_start, int* to_end)
{
    // Print out the entire heap (both semispaces), and
    // try to print values readably when possible
    printf("Old heap: [%p-%p]\n", from_start, from_end);
    implement_print_heap(stdout, from_start, from_end);
    printf("New heap: [%p-%p]\n", to_start, to_end);
    implement_print_heap(stdout, to_start, to_end);
    fflush(stdout);
}

/*
  Copies a Garter value from the given address to the new heap,
  but only if the value is heap-allocated and needs copying.

  Arguments:
    garter_val_addr: the *address* of some Garter value, which contains a Garter value,
                     i.e. a tagged word.
                     It may or may not be a pointer to a heap-allocated value...
    heap_top: the location at which to begin copying, if any copying is needed

  Return value:
    The new top of the heap, at which to continue allocations

  Side effects:
    If the data needed to be copied, then this replaces the value at its old location
    with a forwarding pointer to its new location
 */

int* copy_if_needed(int* garter_val_addr, int* heap_top)
{
    int val = *garter_val_addr;
    int* addr = NULL;
    int size = 0;
    int TAG = 0;
    int offset = 0;
    int* old_top = heap_top;

    if(((val & NUM_TAG_MASK) == 0) || (val == BOOL_TRUE) || (val == BOOL_FALSE))
    {
        return heap_top;
    }
    else if ((val & BIT3_MASK) == FUNC_TAG)
    {
        TAG = FUNC_TAG;
        addr = (int*)(val - TAG);
        size = addr[2];
        offset = 3;
    }
    else if ((val & BIT3_MASK) == TUPLE_TAG)
    {
        TAG = TUPLE_TAG;
        addr = (int*)(val - TAG);
        size = (*addr) + (((*addr) % 2) ? 1 : 2);
        offset = 1;
    }
    else return heap_top;

    if ((int*)*addr > new_start && ((int*)*addr < old_start || (int*)*addr > old_end))
    {
        // If a forwarding pointer is found
        *garter_val_addr = *addr;
        return heap_top;
    }

    for(int i = 0; i < size; ++i)
    {
        // Copy data from old heap to new
        heap_top[i] = addr[i];
    }

    *garter_val_addr = (int)((void*)heap_top + TAG);
    *addr = *garter_val_addr;
    heap_top += size;

    for(int i = offset; i < size; ++i)
    {
        // Skip the tag infos of tuples/lambdas
        heap_top = copy_if_needed(&old_top[i], heap_top);
    }

    return heap_top;
}

/*
  Implements Cheney's garbage collection algorithm.

  Arguments:
    bottom_frame: the base pointer of our_code_starts_here, i.e. the bottommost Garter frame
    top_frame: the base pointer of the topmost Garter stack frame
    top_stack: the current stack pointer of the topmost Garter stack frame
    from_start and from_end: bookend the from-space of memory that is being compacted
    to_start: the beginning of the to-space of memory

  Returns:
    The new location within to_start at which to allocate new data
 */

static int* _gc_(int* bottom_frame, int* top_frame, int* top_stack, int* to_start)
{
    for (int* cur_word = top_stack; cur_word < top_frame; cur_word++)
    {
        to_start = copy_if_needed(cur_word, to_start);
    }

    if (top_frame < bottom_frame)
    {
        to_start = _gc_(bottom_frame,
                       (int*)(*top_frame), // [top_frame] points to the saved EBP, which is the next stack frame
                                           // [top_frame+4] points to the return address
                       top_frame + 2,      // [top_frame+8] is the next frame's stack-top
                       to_start);          // to_start has been changed to include any newly copied data
    }

    return to_start;
}

// Entry point for garbage collection
int* gc(int* bottom_frame, int* top_frame, int* top_stack, int* from_start, int* from_end, int* to_start)
{
    old_start = from_start;
    old_end   = from_end;
    new_start = to_start;

    return _gc_(bottom_frame, top_frame, top_stack, to_start);
}


void printHelp(FILE *out, int val) {
  static int tupleCounter = 0;

  if((val & NUM_TAG_MASK) == 0) {
    fprintf(out, "%d", val >> 1);
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if ((val & BIT3_MASK) == FUNC_TAG) {
    fprintf(out, "<function>");
  }
  else if ((val & BIT3_MASK) != 0) {
    int* addr = (int*)(val - 1);
    // Check whether we've visited this tuple already
    if ((*addr & 0x80000000) != 0) {
      fprintf(out, "<cyclic tuple %p>", (int)(*addr & 0x7FFFFFFE));
      /*return;*/
    }
    // Mark this tuple: save its length locally, then mark it
    int len = addr[0];
    *(addr) = 0x80000000 | (++tupleCounter);
    fprintf(out, "(");
    for (int i = 1; i <= len; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len;
  }
  else {
    fprintf(out, "Unknown value: %#010x", val);
  }
}

