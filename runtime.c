#include <stdio.h>
#include <inttypes.h>

char** argv;
int64_t program(int64_t argc);

int64_t print_int(int64_t i) {
    printf("%" PRId64 "\n", i);
    return i;
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