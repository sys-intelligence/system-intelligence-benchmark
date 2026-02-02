int main(void)
{
    // Please tweak the iteration counts to make this calculation run long enough
    volatile long long unsigned int sum = 0;
    for (int i = 0; i < 100000000; i++) {
        volatile long long unsigned int fac = 1;
        for (int j = 1; j <= 50; j++) {
            fac *= j;
        }
        sum += fac;
    }
    return 0;
}
