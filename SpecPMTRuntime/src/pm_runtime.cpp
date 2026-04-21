#include "pm_runtime.h"

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>

#define MAX_LOG_ENTRIES 1024
#define MAGIC 0xC0FFEE

static char* pmem_base = NULL;
static size_t pmem_size = 0;

static superblock* sb = NULL;
static log_entry* log_entries = NULL;

static log_entry spec_log[MAX_LOG_ENTRIES];
static size_t spec_log_size = 0;

static uint64_t current_tx_id = 0;
static uint64_t global_tx_id = 0;
static uint64_t committed_tx_id = 0;

static size_t alloc_ptr = 0;

static inline void pmem_flush(void* addr, size_t len) {
    __builtin___clear_cache((char*)addr, (char*)addr + len);
}

void pmem_init(const char* path, size_t size) {
    printf("[INIT] Mapping PMEM file: %s\n", path);

    int fd = open(path, O_CREAT | O_RDWR, 0666);
    if (fd < 0) {
        perror("open");
        exit(1);
    }

    if (ftruncate(fd, size) != 0) {
        perror("ftruncate");
        exit(1);
    }

    pmem_base = (char*) mmap(
        NULL,
        size,
        PROT_READ | PROT_WRITE,
        MAP_SHARED,
        fd,
        0
    );

    if (pmem_base == MAP_FAILED) {
        perror("mmap");
        exit(1);
    }

    pmem_size = size;

    sb = (superblock*) pmem_base;

    if (sb->magic != MAGIC) {
        printf("[INIT] First-time initialization\n");
        sb->magic = MAGIC;
        sb->log_offset = sizeof(superblock);
        pmem_flush(sb, sizeof(superblock));
    } else {
        printf("[INIT] Existing image detected\n");
    }

    log_entries = (log_entry*)(pmem_base + sb->log_offset);

    printf("[INIT] PMEM ready\n");
}

void* pmem_alloc(size_t size) {
    void* ptr = pmem_base + alloc_ptr;
    alloc_ptr += size;
    return ptr;
}

void pmem_tx_begin() {
    printf("[TX BEGIN]\n");

    current_tx_id = ++global_tx_id;
    spec_log_size = 0;
}

void pmem_spec_write(void* addr, const void* data, size_t len) {
    printf("[SPEC WRITE] addr=%p len=%lu\n", addr, len);

    // apply write immediately (speculative)
    memcpy(addr, data, len);

    if (spec_log_size >= MAX_LOG_ENTRIES) {
        printf("Log overflow!\n");
        exit(1);
    }

    log_entry* e = &spec_log[spec_log_size++];

    e->tx_id = current_tx_id;
    e->offset = (char*)addr - pmem_base;
    e->len = len;

    if (len > sizeof(e->data)) len = sizeof(e->data);
    memcpy(e->data, data, len);
}

void pmem_commit() {
    printf("[COMMIT]\n");

    if (spec_log_size == 0) return;

    assert(spec_log_size < MAX_LOG_ENTRIES);

    for (size_t i = 0; i < spec_log_size; i++) {
        log_entries[i] = spec_log[i];
    }

    pmem_flush(log_entries, spec_log_size * sizeof(log_entry));

    committed_tx_id = current_tx_id;
    pmem_flush(&committed_tx_id, sizeof(uint64_t));

    spec_log_size = 0;
}

void pmem_recover() {
    printf("[RECOVER]\n");

    uint64_t last = committed_tx_id;

    if (last == 0) return;

    for (size_t i = 0; i < MAX_LOG_ENTRIES; i++) {
        log_entry* e = &log_entries[i];

        if (e->tx_id == 0) continue;
        if (e->tx_id <= last) {
            void* addr = pmem_base + e->offset;
            memcpy(addr, e->data, e->len);
            pmem_flush(addr, e->len);
        }
    }
}