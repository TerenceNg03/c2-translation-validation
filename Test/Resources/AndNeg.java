public class AndNeg{
    public static void main(String[] args) {
        int x = andneg(0xfffffffe, 0xfffffffe);
        System.out.println(x);
    }

    static int andneg(int x, int y){
        return (-x) & (-y);
    }
}