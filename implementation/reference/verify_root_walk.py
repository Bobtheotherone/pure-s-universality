"""A root-restarted two-pass implementation of the paper's binary selector.

A cursor carries one occurrence zipper. Its other selection state is finite.
Paths returned to the regression harness are instrumentation. Off the grammar
the walker chooses the first native redex in preorder, or returns None.
"""
from itertools import product
from functools import cache
from random import Random
import verify_selected_s as ref

S = ref.S


class BadShape(Exception):
    pass


def require(ok):
    if not ok:
        raise BadShape()


def pair_shape(t):
    return t is not S and t[0] is not S and t[0][0] is S


def box_shape(t):
    return pair_shape(t) and t[0][1] is S


def degree(t):
    k = 0
    while t is not S and k < 5:
        k += 1
        t = t[0]
    return k


class Cursor:
    def __init__(self, term):
        self.term = term
        self.zip = []

    def down(self, sides):
        for side in sides:
            require(self.term is not S)
            i = int(side)
            self.zip.append((self.term, i))
            self.term = self.term[i]

    def up(self, n=1):
        for _ in range(n):
            require(bool(self.zip))
            self.term, _ = self.zip.pop()

    def root(self):
        while self.zip:
            self.up()

    def address(self):
        return "".join(str(i) for _, i in self.zip)


class Summary:
    def __init__(self):
        self.spent = self.committed = 0
        self.last = None
        self.has_live = self.has_free = False


def bit(t):
    if t is S:
        return 0
    require(t == (S, S))
    return 1


def status(t):
    if t is not S and t[0] == ref.pair(S, S):
        return "fresh"
    require(pair_shape(t))
    return "fired"


def read_box(c, summary, mode):
    require(box_shape(c.term))
    c.down("1")
    while c.term is not S:
        t = c.term
        require(t[0] is not S)
        if t[0][0] == (S, S):
            bit(t[0][1])
            if mode == "pop":
                return True
            summary.has_live = True
            c.down("1")
        else:
            require(t[0][0] is S and t[1] is not S and not summary.has_live)
            summary.spent ^= 1
            summary.last = bit(t[1][0])
            c.down("01")
    while True:
        c.up()
        level = degree(c.term)
        if level == 2:
            return False
        if level == 1:
            c.up()
        else:
            require(level == 3)


def sweep(c, mode, chosen_bit=None):
    summary = Summary()
    require(pair_shape(c.term))
    c.down("01")
    if read_box(c, summary, mode):
        return summary
    c.up(2)
    c.down("1")
    while degree(c.term) == 4:
        c.down("00")
        require(box_shape(c.term))
        c.down("1")
        require(c.term is not S)
        while c.term is not S:
            require(pair_shape(c.term))
            c.down("01")
            require(pair_shape(c.term))
            zero, one = status(c.term[0][1]), status(c.term[1])
            if (zero, one) == ("fresh", "fresh"):
                if mode == "commit":
                    c.down("01" if chosen_bit == 0 else "1")
                    return summary
                summary.has_free = True
            else:
                require(not summary.has_free and (zero == "fired") != (one == "fired"))
                summary.committed ^= 1
                if one == "fired":
                    c.down("101")
                    if read_box(c, summary, mode):
                        return summary
                    c.up(3)
            c.up(2)
            c.down("1")
        c.up()
        while not box_shape(c.term):
            require(pair_shape(c.term))
            c.up()
        c.up(2)
        c.down("1")
    require(degree(c.term) == 3)
    if mode in ("pop", "commit"):
        raise BadShape()
    return summary


def fallback(c):
    c.root()
    while True:
        if degree(c.term) == 3:
            return c.address()
        if c.term is not S:
            c.down("0")
            continue
        while c.zip and c.zip[-1][1] == 1:
            c.up()
        if not c.zip:
            return None
        c.up()
        c.down("1")


def select(term):
    c = Cursor(term)
    try:
        flags = sweep(c, "read")
        if flags.spent == flags.committed:
            mode = "pop" if flags.has_live else "frontier"
        else:
            mode = "commit" if flags.has_free else "frontier"
            if mode == "commit":
                require(flags.last is not None)
        c.root()
        sweep(c, mode, flags.last)
        require(degree(c.term) == 3)
        return c.address()
    except BadShape:
        return fallback(c)


@cache
def ground_terms(n):
    if n == 1:
        return (S,)
    return tuple((l, r) for i in range(1, n)
                 for l in ground_terms(i) for r in ground_terms(n-i))


def check():
    checked = off = 0
    # This parsed tree lies outside the simulation invariant. Its only slot was
    # fired before any bit was consumed. Allocation needs no remembered bit.
    arbitrary = ref.cyclic_seed(((1,),), (1,))
    for _ in range(2):
        arbitrary = ref.contract_at(arbitrary, ref.inspect(arbitrary).frontier)
    arbitrary = ref.contract_at(arbitrary, ref.inspect(arbitrary).free[0])
    assert select(arbitrary) == ref.inspect(arbitrary).frontier
    words = [t for n in range(3) for t in product((0, 1), repeat=n)]
    seeds = [t for n in range(4) for t in product((0, 1), repeat=n)]
    examples = [(p, s) for d in (1, 2) for p in product(words, repeat=d) for s in seeds]
    rng = Random(20261126)
    for _ in range(75):
        p = tuple(tuple(rng.randrange(2) for _ in range(rng.randrange(6)))
                  for _ in range(rng.randrange(1, 8)))
        s = tuple(rng.randrange(2) for _ in range(rng.randrange(1, 9)))
        examples.append((p, s))
    examples.append((((1,),), (1,)))
    for p, s in examples:
        t = ref.cyclic_seed(p, s)
        for _ in range(30):
            expected, _ = ref.select(ref.inspect(t))
            actual = select(t)
            assert actual == expected
            t = ref.contract_at(t, actual)
            checked += 1
    for n in range(1, 10):
        for t in ground_terms(n):
            addr = select(t)
            if addr is None:
                assert not any(degree(u) == 3 for u in walk(t))
            else:
                ref.contract_at(t, addr)
            off += 1
    print(f"Fresh-root agreement: {checked} native selections on {len(examples)} seeds")
    print(f"All bare trees with at most nine leaves: {off}")


def walk(t):
    yield t
    if t is not S:
        yield from walk(t[0])
        yield from walk(t[1])


if __name__ == "__main__":
    check()
