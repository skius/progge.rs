#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>

char** argv;
int64_t program(int64_t argc);

int64_t print_int(int64_t i) {
    printf("%" PRId64 "\n", i);
    return i;
}

int64_t* alloc_array(int64_t size) {
    int64_t* array = malloc((size + 1) * sizeof(int64_t));
    if (array == NULL) {
        printf("Array allocation failed!\n");
        exit(1);
    }
    array[0] = size;
    return array;
}

int64_t* alloc_array_default(int64_t size, int64_t value) {
    int64_t* array = malloc((size + 1) * sizeof(int64_t));
    if (array == NULL) {
        printf("Array allocation failed!\n");
        exit(1);
    }
    array[0] = size;
    for (int i = 1; i <= size; i++) {
        array[i] = value;
    }
    return array;
}

int64_t int_arg(int64_t i) {
    char* arg = argv[i];
    int64_t result = 0;
    sscanf(arg, "%" SCNd64, &result);
    return result;
}

int main(int argc, char** _argv) {
    argv = _argv;
    return program(argc);
}