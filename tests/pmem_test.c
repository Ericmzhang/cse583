#include <stdio.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

// This mimics a persistent data structure
struct PersistentData {
    int id;
    long value;
};

int main() {
    // 1. Open a file on the DAX mount
    int fd = open("/pmem/test_data", O_RDWR | O_CREAT, 0666);
    if (fd < 0) return 1;

    // 2. Map it into the process address space
    // The Taint Analysis should mark 'ptr' as a Persistent Memory address
    struct PersistentData *ptr = (struct PersistentData *)mmap(
        NULL, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);

    if (ptr == MAP_FAILED) return 1;

    // 3. Perform a Store
    // Because 'ptr' is tainted, PMRobustness should insert a clflush here
    ptr->id = 101; 
    ptr->value = 5000L;

    munmap(ptr, 4096);
    close(fd);
    return 0;
}