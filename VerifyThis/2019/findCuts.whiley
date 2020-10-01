type uint is (int x) where x >= 0
type pos is (int x) where x > 0

function findCutPoints(int[] s) -> (int[] rs, int rl):
    final int n = |s|
    //
    int[] cuts = [0; n]
    uint l = 0
    (uint x, pos y) = (0,1)
    //
    while y < n 
    where x < y 
    where l <= x
    where |cuts| == n:
        bool increasing = s[x] < s[y]
        uint z = (uint) y
        while z < n && (s[z-1] < s[z]) == increasing
        where y <= z && z <= n:
            z = z + 1
        cuts[l] = z
        l = l + 1
        x = (uint) z
        y = x + 1
    //
    if x < n:
        cuts[l] = n
    //
    return cuts,l
