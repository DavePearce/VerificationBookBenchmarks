type Num is {
    int dividend,
    int remainder
}

function divide(int x, int y) -> (Num|null r)
ensures y != 0 ==> (r is Num && (r.dividend*y) + r.remainder == x)
ensures y == 0 <==> r is null:
    //
    if y == 0:
        return null
    else:
        return {
            dividend: x / y,
            remainder: x % y
        }