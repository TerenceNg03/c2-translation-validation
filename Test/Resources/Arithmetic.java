public class Arithmetic{
    public static void main(String[] args) {
       arithmetic(1, 2, 10, 1.3f, 4.23d);
    }

    static double arithmetic (int i, int j, long l, float f, double d) {
        i += j;
        i *= j;
        i /= j;
        i -= j;
        l += j;
        l -= j;
        l *= j;
        l /= l + 1;
        f += f;
        f -= f;
        f *= d;
        f /= d;
        d += i;
        d /= 5.23;
        d -= 2.34;
        d *= f;
        return i + f;
    }
}