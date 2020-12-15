import whiley.lang.*

// First, define the type of linked lists
type LinkedList is null | {LinkedList next, int item}

function cons(int head, LinkedList tail) -> LinkedList:
    return { next: tail, item: head }

// Should return index in list of item, or size of list otherwise.
function search(LinkedList list, int item) -> (int result):
    //
    int i = 0
    //
    while list != null:
        if list.item == item:
            return i
        list = list.next
        i = i + 1
    //
    return i

method main(System.Console console):
    LinkedList list = cons(0,cons(5,cons(3,null)))
    console.out.println_s(Any.toString(search(list,0)))
    console.out.println_s(Any.toString(search(list,5)))
    console.out.println_s(Any.toString(search(list,3)))
    console.out.println_s(Any.toString(search(list,4)))
    console.out.println_s(Any.toString(search(list,7)))                