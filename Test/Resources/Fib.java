public class Fib {
    public static void main(String[] args) {
        System.out.println("Fib(10): " + fib(10));
    }

    static int fib(int n) {
        if (n <= 1) {
            return n;
        }else{
            return 2*fib(n-1) + 1;
        }
    }
}
