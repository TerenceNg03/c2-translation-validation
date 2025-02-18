public class Arithmetic{
    public static void main(String[] args) {
       arithmetic(1, 2);
    }

    static int arithmetic (int i, int j) {
        i = 127 - i;
        j++;
        i *= 10;
        i = i / j;
        i = i + j % 21;
        i--;
        return i - j + -143;
    }
}