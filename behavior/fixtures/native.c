#include <stddef.h>
// An intentionally small native extraction fixture. It is not a verified lift.
int bounded_copy(unsigned char *dst, size_t capacity,
                 const unsigned char *src, size_t length) {
    if (length > capacity) return -1;
    for (size_t i = 0; i < length; ++i) dst[i] = src[i];
    return 0;
}
int main(void) { unsigned char dst[4]; const unsigned char src[2] = {1, 2};
    return bounded_copy(dst, 4, src, 2); }
