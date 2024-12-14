interface Iterator {
    Object next();
}

class TwoObject {
    public static void main(String[] args) {
        m();
    }

    static void m() {
        List l1 = new List(); //o11
        l1.add(new Object()); //o12
        List l2 = new List(); //o13
        l2.add(new Object()); //o14

        Iterator i1 = l1.iterator(); // i1 -> [o11]:o31
        Object o1 = i1.next();
        Iterator i2 = l2.iterator();
        Object o2 = i2.next();
    }
}

class List {

    Object element;

    void add(Object e) {
        this.element = e;
    }

    Iterator iterator() {
        return new ListIterator();
    }

    class ListIterator implements Iterator {

        public Object next() {
            return element;
        }
    }
}
