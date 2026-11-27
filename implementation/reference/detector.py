"""The twenty-coordinate finite tree algebra in UniformS.Certified."""
from typing import NamedTuple
from verify_selected_s import S


class State(NamedTuple):
    leaf: bool = False
    unary: bool = False
    box: bool = False
    frame_head: bool = False
    header: bool = False
    tag: int | None = None
    reader: int | None = None
    right_tag: int | None = None
    word: int | None = None
    unary_word: int | None = None
    box_word: int | None = None
    unary_box_word: int | None = None
    arm: int | None = None
    slot: int | None = None
    unary_slot: int | None = None
    row: int | None = None
    box_row: int | None = None
    rows: int | None = None
    rail: int | None = None
    root: int | None = None


LEAF = State(leaf=True, tag=0)


def first(left, right):
    return right if left is None else left


def combine(u, v):
    box = u.tag == 1
    return State(
        unary=u.leaf, box=box, frame_head=u.box, header=u.leaf and v.box,
        tag=1 if u.leaf and v.leaf else None,
        reader=v.tag if box else None, right_tag=u.tag,
        word=first(u.reader, u.unary_word if v.right_tag is not None else None),
        unary_word=v.word if u.leaf else None, box_word=v.word if box else None,
        unary_box_word=v.box_word if u.leaf else None, arm=u.unary_box_word,
        slot=v.arm if u.unary else None, unary_slot=v.slot if u.leaf else None,
        row=first(u.unary_slot, v.row) if u.unary else None,
        box_row=v.row if box else None, rows=u.box_row if u.box else None,
        rail=first(u.rows, v.rail) if u.frame_head else None,
        root=first(u.unary_box_word, v.rail) if u.header else None)


def observe(term):
    """Exact bottom-up algebra on any tree, using two temporary O(height) stacks."""
    todo = [(term, False)]
    values = []
    while todo:
        node, closing = todo.pop()
        if node is S:
            values.append(LEAF)
        elif closing:
            right = values.pop()
            values.append(combine(values.pop(), right))
        else:
            todo.extend(((node, True), (node[1], False), (node[0], False)))
    return values.pop().root
