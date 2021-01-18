These are some of the challenge problems from VSCOMP10:

Klebanov V. et al. (2011) The 1st Verified Software Competition: Experience Report. 
In: Butler M., Schulte W. (eds) FM 2011: Formal Methods. FM 2011. 
Lecture Notes in Computer Science, vol 6664. Springer, Berlin, Heidelberg.
https://doi.org/10.1007/978-3-642-21437-0_14


Problem 1: SUM&MAX. 
Given an N-element array of natural numbers, write a program to
compute the sum and the maximum of the elements in the array.
Prove the postcondition that sum <= N * max.

Problem 2: Inverting an Injection.
Invert an injective (and thus surjective)
array A of N elements in the subrange from 0 to N-1. 
Prove that the output array B is injective and that 
B[A[i]] = i for 0 <= i < N.

Problem 3: Searching a LinkedList.
Given a linked-list representation of a list of integers, 
find the index of the first element that is equal to zero.
Show that the program returns a number i equal to the length of
the list if there is no such element. Otherwise, the element at
index i must be equal to zero, and all the preceding elements must be non-zero.

Problem 4: N Queens. 
Write and verify a program to place N queens on an N*N chess board
so that no queen can capture another one with a legal move.
If there is no solution, the algorithm should indicate that.

Problem 5: Amortized Queue.
An applicative queue with a good amortized
complexity can be implemented using a pair of linked lists, such that the front
list joined to the reverse of the rear list gives the abstract queue. The queue
offers the operations Enqueue(item: T) to place an element at the rear of the
queue, Tail() to return the queue without the first element, and Front() to
return the first element of the queue. The implementation must maintain the
invariant queue.rear.length <= queue.front.length (prove this). Also, show
that a client invoking the above operations observes an abstract queue given by
a sequence.
