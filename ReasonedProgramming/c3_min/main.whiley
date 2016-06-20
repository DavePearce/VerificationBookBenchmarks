function min(int x, int y) -> (int r)
ensures r == x || r == y
ensures r <= x && r <= y:
    //
    if x <= y:
        return x
    else:
        return y
