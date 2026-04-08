#include "stdint.h"
#define CLWB 1
/* ------------------------ CACHE OPS ---------------------------
 borrowed from https://github.com/utsaslab/RECIPE
*/

static unsigned long write_latency_in_ns = 0;
static unsigned long cpu_freq_mhz = 2100;
static unsigned long cache_line_size = 64;

static inline void my_cpu_pause()
{
    __asm__ volatile ("pause" ::: "memory");
}

static inline unsigned long my_read_tsc(void)
{
    unsigned long var;
    unsigned int hi, lo;

    __asm__ volatile ("rdtsc" : "=a" (lo), "=d" (hi));
    var = ((unsigned long long int) hi << 32) | lo;

    return var;
}

__attribute__((used))
__attribute__ ((annotate("preprocess_ignore")))
__attribute__ ((annotate("myflush:addr|size")))
static inline void my_clflush(char *data, int len)
{
    volatile char *ptr = (char *)((unsigned long)data & ~(cache_line_size - 1));
    for (; ptr < data+len; ptr += cache_line_size){
        unsigned long etsc = my_read_tsc() +
            (unsigned long)(write_latency_in_ns * cpu_freq_mhz/1000);
#ifdef CLFLUSH
        __asm__ volatile("clflush %0" : "+m" (*(volatile char *)ptr));
#elif CLFLUSH_OPT
        __asm__ volatile(".byte 0x66; clflush %0" : "+m" (*(volatile char *)(ptr)));
#elif CLWB
        __asm__ volatile(".byte 0x66; xsaveopt %0" : "+m" (*(volatile char *)(ptr)));
#endif
        while (my_read_tsc() < etsc) my_cpu_pause();
    }
}

/* ------------------------ FliT ----------------------------
  borrowed from https://github.com/cmuparlay/flit
*/

struct flit_counter_t {
	uint64_t count;
};
typedef struct flit_counter_t flit_counter;

#define NUM_FLUSH_COUNTERS ((1ull<<16)/sizeof(flit_counter))
static const uint64_t FLUSH_COUNTER_MASK = NUM_FLUSH_COUNTERS-1ull;
static const uint64_t CACHE_LINE_MASK = ~((1ull<<6)-1ull);

static flit_counter flit_counters[NUM_FLUSH_COUNTERS] __attribute__((aligned(64)));

static inline uint64_t hash64(uint64_t x) {
  x = (x ^ (x >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  x = (x ^ (x >> 27)) * UINT64_C(0x94d049bb133111eb);
  x = x ^ (x >> 31);
  return x;
}

__attribute__((used))
static inline uint64_t *get_flit_counter(const void* ptr) {
  int index = hash64(((uint64_t) ptr) & CACHE_LINE_MASK) & FLUSH_COUNTER_MASK;
  return &flit_counters[index].count;
}

