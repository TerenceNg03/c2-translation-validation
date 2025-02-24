class Pair {
    public int i = 0;
    public int j = 2;
}

public class Memory {
    public static void main(String[] args) {
        memory(new Pair());
    }

    static Pair memory (Pair i) {
        i.i = 10;
        return i;
    }
}