

class Test{
    public static void main(String[] args) {
        float pattern = 2^128;//Float.intBitsToFloat(0x0f400000);
        // var x = test(pattern);
        // var l = Double.doubleToLongBits(pattern);
        // var s = Long.toBinaryString(l);
        var i = Float.floatToIntBits(pattern);
        var s = Integer.toBinaryString(i);
        System.out.println(test(123,2,3,4));
    }

    static int test(int i, int j, int k, int n){
        return (j << 5) >> 5;
    }
}