public class Call {
    public static void main(String[] args) {
        call(0,0,0,0,0);
    }

    static void call (int i, int j, int k, int f, int g){
        if (i > 10) {
           return; 
        }
        call(i+1, j+2, k, f+3, g);
    }
}