import abs from whiley.lang.Math

function pdifference(int x, int y) -> (int r)
ensures r == abs(x-y):
    //
    if x >= y:
        return x - y
    else:
        return y - x