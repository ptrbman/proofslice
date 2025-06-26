void main() {
    int x = 10;
    int y = 5;
    int z;
    z = x * y + 3;

    int result;

    if (z > 50) {
        result = z - 20;
    } else {
        result = z + 10;
    }

    assert(result >= -1);
}
