type nat is (int x) where x >= 0

function sum(nat n) -> (nat r):
    //
    if n == 0:
        return n
    else:
        return sum(n-1) + n