import whiley.lang.*

function invert(int[] A) -> (int[] B)
// A must be injection
requires 
  all { i in 0..|A|, j in 0..|A| | i != j ==> A[i] != A[j] }
// all elements of A must be within bounds
requires all { i in 0..|A| | A[i] >= 0 && A[i] < |A| }
// A and B have same size
ensures |A| == |B|
// all elements of B are withing bounds
ensures all { i in 0..|B| | 0 <= B[i] && B[i] < |B| }
// B is really inversion of A
ensures all { i in 0..|B| | B[A[i]] == i }
// B is injective
ensures 
  all { i in 0..|B|, j in 0..|B| | i != j ==> B[i] != B[j] }:
    //
    int[] C = A
    int i = 0
    //
    while i < |A|
        // i must be positive
        where i >= 0 && |C| == |A| && i <= |A|
        // is inversion so far
        where all { k in 0..i | C[A[k]] == k }:
        C[A[i]] = i
        i = i + 1
    //
    return C

method main(System.Console console):
    int[] A = [9,3,8,2,7,4,0,1,5,6]
    int[] B = invert(A)
    console.out.println(Any.toString(A))    
    console.out.println(Any.toString(B))
