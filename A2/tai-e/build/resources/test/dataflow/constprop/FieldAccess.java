class FieldAccess {
    public String field = "field";
}

class Accesser {
    void invoke() {
        FieldAccess fieldAccess = new FieldAccess();
        String receiver = fieldAccess.field;
    }
}