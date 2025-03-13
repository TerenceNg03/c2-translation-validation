public class LShift{
    public static void main(String[] args) {
        lshift(10);
    }

    static long lshift(long i){
        return (i + i) << 63;
    }
}