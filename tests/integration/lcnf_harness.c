#include <stdint.h>

extern uint64_t l_captureAdd(uint64_t, uint64_t);
extern uint64_t l_captureSelect(uint8_t, uint64_t, uint64_t);

int main(void) {
    if (l_captureAdd(UINT64_C(40), UINT64_C(2)) != UINT64_C(42)) {
        return 1;
    }
    if (l_captureSelect(UINT8_C(0), UINT64_C(11), UINT64_C(22)) != UINT64_C(22)) {
        return 2;
    }
    if (l_captureSelect(UINT8_C(1), UINT64_C(11), UINT64_C(22)) != UINT64_C(11)) {
        return 3;
    }
    return 0;
}
