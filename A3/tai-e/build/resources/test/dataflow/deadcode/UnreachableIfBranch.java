class UnreachableIfBranch {

//    int branch() {
//        int x = 10;
//        int y = 1;
//        int z;
//        if (x > y) {
//            z = 100;
//        } else {
//            z = 200; // unreachable branch
//        }
//        return z;
//    }
//
//    int branch2() {
//        int x = 10;
//        int y = 1;
//        int z;
//        if (y > x) {
//            z = 100; // unreachable branch
//        } else {
//            z = 200;
//        }
//        return z;
//    }
//
//
//    void nestedIfBranch() {
//        int x = 10;
//        int k = 1;
//        int z = 2;
//        if (k > x) {
//           // unreachable if stmt
//           if( x > z)
//               z = 3;
//           else
//               z = 4;
//           x = 11;
//        } else {
//            use();
//        }
//    }
//
//    void nestedWhileBranch() {
//            int x = 10;
//            int k = 1;
//            int z = 2;
//            if (k > x) {
//               // unreachable if stmt
//               while (x > z){
//                   k = 9;
//               }
//            } else {
//                use();
//            }
//    }

    void heavyNestedBranch() {
        int x = 10;
        int k = 1;
        int z = 2;
        if (k > x) {
            // unreachable if stmt
            while (x > z){
                if(k > z) z = 2;
                else z = 3;
                k = 9;
            }
        } else {
            use();
        }
    }

        void use(){}
}
