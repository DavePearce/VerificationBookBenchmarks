property present(int[] A, int i, int val) where
  some { k in 0..i | A[k] == val } 

function invert(int[] A) -> (int[] B)
// A must be injection
requires 
  all { i in 0..|A|, j in 0..|A| | i != j ==> A[i] != A[j] }
// all elements of A must be within bounds
requires all { i in 0..|A| | A[i] >= 0 && A[i] < |A| }
// A and B have same size
ensures |A| == |B|
// all elements of B are within bounds
ensures all { i in 0..|B| | 0 <= B[i] && B[i] < |B| }
// B is really inversion of A
ensures all { i in 0..|B| | B[A[i]] == i }
// B is injective
ensures 
  all { i in 0..|B|, j in 0..|B| | i != j ==> B[i] != B[j] }:
    //
    int[] C = [-1; |A|]
    assert all { k in 0..|A| | C[k] == -1 }
    int i = 0
    //
    while i < |A|
        // i must be positive
        where 0 <= i && i <= |A| && |C| == |A|
        // C is inversion so far
        //where all { k in 0..i | C[A[k]] == k }
        // and a stronger form of the inversion
        where all { j in 0..|C| | 
            (C[j] == -1 && !present(A, i, j)) ||
            (0 <= C[j] && C[j] < |A| && A[C[j]]==j) }:
        C[A[i]] = i
        i = i + 1
    //
    // we assume this property of injective functions, since this is well-known mathematical result, but requires induction to prove.
    assume all { j in 0..|A| | present(A, |A|, j) }
    
    // Now prove that C is complete (no holes).
    assert all { j in 0..|C| | C[j] != -1 }
    
    // Other ideas / invariants that we tried (but subsumed by above inv):
    //assert all { j in 0..|C| | C[j] != -1 ==> A[C[j]]==j }
    //assert all { k in 0..|A| | some { j in 0..|A| | (C[j]==k) == (A[k] == j) } }
    //assert all { k in 0..|A|, j in 0..|A| | A[k] != A[j]  ==> C[A[k]] != C[A[j]] }
    return C
