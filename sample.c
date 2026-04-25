#include <stdio.h>

int main() {
    int x = 3 + 5;    
    int y = x;         
    int z = 10;        
    int w = z + 2;     

    if (y > 5) {
        int a = y + 1;
        printf("%d\n", a);
    } else {
        int b = 0;
    }

    return y;
}
