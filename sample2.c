#include <stdio.h>

int main() {
    int i = 0;
    int sum = 0;
    int temp = 100;

    while (i < 3) {
        sum = sum + i;
        i = i + 1;
    }

    return sum;
}
