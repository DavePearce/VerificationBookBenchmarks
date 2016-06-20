function hasSolutions(int a, int b, int c) -> (bool r)
ensures r <==> some { x in 0..100 | (a*x*x) + (b*x) + c == 0 }:
    //
    ???