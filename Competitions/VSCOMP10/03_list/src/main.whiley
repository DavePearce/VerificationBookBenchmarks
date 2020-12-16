// First, define the type of linked lists
type LinkedList is null | {LinkedList next, int item}

function cons(int head, LinkedList tail) -> LinkedList:
    return { next: tail, item: head }

// Should return index in list of item, or size of list otherwise.
function search(LinkedList list, int item) -> (int result):
    //
    int i = 0
    //
    while !(list is null):
        if list.item == item:
            return i
        list = list.next
        i = i + 1
    //
    return i
