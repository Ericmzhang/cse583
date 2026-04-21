#pragma once
#include <cstddef>
#include <cstdint>

#ifdef __cplusplus
extern "C" {
#endif

// Persistent structures

struct log_entry {
    uint64_t tx_id;
    size_t offset;
    size_t len;
    char data[64];
};

struct superblock {
    uint64_t magic;
    size_t log_offset;
};

// API

void pmem_init(const char* path, size_t size);
void pmem_recover();

void pmem_tx_begin();
void pmem_spec_write(void* addr, const void* data, size_t len);
void pmem_commit();

void* pmem_alloc(size_t size);

#ifdef __cplusplus
}
#endif