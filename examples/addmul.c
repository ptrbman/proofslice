void main() {
    int sum = 0;
    int prod = 1;

    for (int i = 1; i <= 5; i++) {
        sum = sum + i;
        prod = prod * i;
    }

    assert(sum == 15);
}