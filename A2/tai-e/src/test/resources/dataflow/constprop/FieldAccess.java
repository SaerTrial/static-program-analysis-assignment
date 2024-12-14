public class ClassA {
    public int field;

    public ClassA(int field) {
        this.field = field;
    }

}

public class FieldAccess {
    public int field;

     void invoke(){
        int i = 2;
        ClassA a = new ClassA(1);
        a.field = 2;
    }

    void complicated(int x, float y, ClassA z){
         z.field = 123;
    }
}
