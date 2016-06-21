function sign(int n) -> (int sign)
ensures (n == 0 && sign == 0) || (n > 0 && sign == 1) || (n < 0 && sign == -1):
    //
    if n == 0:
        return 0
    else if n > 0:
        return 1
    else:
        return -1
        