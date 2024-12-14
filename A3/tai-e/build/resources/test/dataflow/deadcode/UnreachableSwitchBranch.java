class UnreachableSwitchBranch {

    void lookupSwitch() {
        int x = 1;
        int y = x << 3;
        switch (y) {
            case 2:
                use(2);
                break;  // unreachable case
            case 4:
                use(4);
                break; // unreachable case
            case 8:
                use(8);
                break;
            default:
                use(666);
                break; // unreachable case
        }
    }

    void lookupNestedSwitch() {
        int x = 1;
        int y = x << 3;
        switch (y) {
            case 2:
                use(2);
                break;  // unreachable case
            case 4:
                switch (x) {
                    case 1:
                        use(1);
                        break;
                    case 2:
                        use(2);
                        break;
                    default:
                        use(6);
                        break;
                }
                use(4);
                break;  // unreachable case
            case 8:
                use(8);
                break;
            default:
                use(666);
                break; // unreachable case
        }

    }

    void lookupNestedIfSwitch() {
        int x = 1;
        int y = x << 3;
        switch (y) {
            case 2:
                use(2);
                break;  // unreachable case
            case 4:
                if (x == 1) use(1);
                else use(6);
                break;
            case 8:
                use(8);
                break; // unreachable case
            default:
                use(666);
                break; // unreachable case
        }

    }

//    void lookupOpSwitch() {
//        int x = 1;
//        int y = x << 3;
//        switch (cal(x, y)) {
//            case 2:
//                use(2);
//                break;  // unreachable case
//            case 4:
//                use(4);
//                break; // unreachable case
//            case 8:
//                use(8);
//                break; // unreachable case
//            default:
//                use(666);
//                break;
//        }
//    }

    int cal(int x, int y) {return x * y;}

    void lookupNoBreakSwitch() {
    int x = 1;
    int y = x << 3;
    switch (y) {
        case 2:
            use(2);
            break; // unreachable case
        case 4:
            use(4);
            break; // unreachable case
        case 8:
            use(8);
        default:
            use(666);
            break;
        }
    }

//    void lookupDefaultSwitch() {
//        int x = 1;
//        int y = x << 4;
//        switch (y) {
//            case 2:
//                use(2);
//                break; // unreachable case
//            case 4:
//                use(4);
//                break; // unreachable case
//            case 8:
//                use(8);
//                break; // unreachable case
//            default:
//                use(666);
//                break;
//        }
//    }

    void lookupSideEffectSwitch() {
        int x = 1;
        int y = x << 3;
        int[] intArray = {1,2,3};
        switch (y) {
            case 2:
                use(2);
                break;  // unreachable case
            case 4:
                use(4);
                break; // unreachable case
            case 8:
                x = intArray[0]; // side effect, can't be deleted
                use(8);
                break;
            default:
                use(666);
                break; // unreachable case
        }
    }


    void use(int x) {
    }
}
