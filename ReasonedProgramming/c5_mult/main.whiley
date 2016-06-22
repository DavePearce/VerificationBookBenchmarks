type nat is (int x) where x >= 0

function mult(int x, nat n) -> (int r)
ensures r == x * n:
    if n == 0:
        return 0
    else:
        int y = 2 * mult(x,n/2)
        //
        if n > 0 && n % 2 == 0:
            return y
        else:
            return y + x