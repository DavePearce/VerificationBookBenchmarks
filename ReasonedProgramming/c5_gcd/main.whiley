type nat is (int x) where x >= 0

function gcd(nat x, nat y) -> (nat z)
ensures x%z == 0 && y%z == 0:
    //
    if y == 0:
        return x
    else:
        return gcd(y,x % y)