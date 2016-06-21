function pred(int x) -> (int r)
requires x >= 0
ensures (r == 0 && x == 0) || (x > 0 && r == x-1):
    //
    if x == 0:
        return 0
    else:
        return x-1