// First, define the type of linked lists
type LinkedList is null | {LinkedList next, int item}

// A recursive property capturing the concept of n'th item in a List
property nth_item(LinkedList head, int n, int value)
    where (n == 0 && ! (head is null)) ==> head.item == value
    where (n > 0 && ! (head is null)) ==> nth_item(head.next, n - 1, value)

// A recursive property capturing the concept of n'th tail of a List
property nth_tail(LinkedList head, int n, LinkedList tail)
    where n == 0 ==> head == tail
    where (n > 0 && ! (head is null)) ==> nth_tail(head.next, n - 1, tail)

// not used yet.
function cons(int head, LinkedList tail) -> LinkedList:
    return { next: tail, item: head }

// Should return index in list of item, or size of list otherwise.
// NOTE: AT THE MOMENT IT JUST RETURNS LENGTH
function search(LinkedList list0, int item) -> (int result)
ensures 
  //nth_item(list0, result, item) || 
  nth_tail(list0, result, null):
    //
    LinkedList list = list0
    int i = 0
    assert nth_tail(list0, i, list)
    //
    while !(list is null)  // but this does not work: list != null
        where 0 <= i
        where i == 0 ==> list0 == list
        where !(list0 is null)
        where nth_tail(list0, i, list):
        //where all { j in 0..i | !at_pos(list0, j, item) }:
        //
        //if list.item == item:
        //    return i
        assert nth_tail(list0, i+1, list.next)
        list = list.next
        i = i + 1
    //
    return i
