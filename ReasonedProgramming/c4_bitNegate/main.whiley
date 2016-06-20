function bitNegate(int x) -> (int b)
requires x == 1 || x == 0
ensures (x == 0 && b == 1) || (x == 1 && b == 0):
    //
    if x == 1:
        return 0
    else:
        return 1
    