function and(bool x, bool y) -> (bool r)
ensures r == (x && y):
    //
    if x:
        return y
    else:
        return false

function or(bool x, bool y) -> (bool r)
ensures r == (x || y):
    //
    if x:
        return true
    else:
        return y

function not(bool x) -> (bool r)
ensures r == !x:
    //
    if x:
        return false
    else:
        return true
