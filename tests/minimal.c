#include <stdio.h>

int main() {
    int x = 10;
    int y = 20;
    int z = x + y;
    printf("Result: %d\n", z); // The printf prevents the compiler from deleting the math
    return 0;
}