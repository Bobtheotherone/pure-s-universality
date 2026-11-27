#!/usr/bin/env python3
"""Literal native-S replay for the cyclic tag and finite queue constructions.

Run with Python 3.10+. All mutation goes through contract_at. Immutable tuples
can share memory; rebuilding a path replaces exactly one tree occurrence.
Selector scans below implement the paper's rules on the reachable grammar.
The differential tests use a separate ordinary queue only as the reference.
"""
from collections import Counter
from dataclasses import dataclass, field
from functools import cache
from itertools import product
from random import Random

S = None
LEFT_FIELD = "01"
RIGHT_FIELD = "1"


def pair(x, y):
    return ((S, x), y)


def box(w):
    return pair(S, w)


def pack_list(items):
    result = S
    for item in reversed(items):
        result = pair(item, result)
    return result


@cache
def tag(number):
    result = S
    for _ in range(number):
        result = (S, result)
    return result


def tag_number(term):
    result = 0
    while term is not S:
        assert term[0] is S
        result += 1
        term = term[1]
    return result


def word(letters):
    tail = S
    for a in reversed(letters):
        tail = (pair(S, tag(a)), tail)
    return tail


def arm(payload):
    return (pair(S, S), payload)


def make_seed(letters, block):
    template = pair(S, pack_list(block))
    a = (S, template)
    x0 = pair(a, a)
    return pair(box(word(letters)), (x0, x0))


def cyclic_seed(program, letters):
    assert program
    return make_seed(letters, [pair(arm(S), arm(box(word(v)))) for v in program])


def menu_tree(leaves):
    """Full binary menu. Tagged leaves and branches have disjoint shapes."""
    level = [pair(tag(1), leaf) for leaf in leaves]
    capacity = 1 << (len(level) - 1).bit_length()
    level.extend([level[-1]] * (capacity - len(level)))
    while len(level) > 1:
        level = [pair(S, pair(level[i], level[i+1])) for i in range(0, len(level), 2)]
    return level[0]


def state_seed(table, letters):
    # One menu per block. Row-major order is state, then input symbol.
    menu = [arm(pair(tag(q), box(word(v)))) for row in table for q, v in row]
    return make_seed(letters, [menu_tree(menu)])


def menu_address(tree, rank):
    # Reconstruct the leaf address from the fixed-width binary slot number.
    depth = 0
    probe = tree
    while probe[0][1] is S:
        depth += 1
        probe = probe[1][0][1]
    assert 0 <= rank < (1 << depth)
    bits = format(rank, f"0{depth}b") if depth else ""
    return "".join("101" if b == "0" else "11" for b in bits) + "1"


class MenuFacts:
    """Optional cache on immutable subtrees only. Clearing it changes no result.
    Each entry is the unique fired leaf address, or None for a pristine subtree.
    Keeping the object alongside the key prevents identity recycling.
    """
    def __init__(self):
        self.cache = {}
        self.state_tags = {}
        self.payloads = {}

    def opened_payload(self, menu, address):
        key = id(menu)
        saved = self.payloads.get(key)
        if saved is not None:
            return saved[1], saved[2]
        payload = at(menu, address)[0][1]
        state_tag = payload[0][1]
        entry = self.state_tags.get(id(state_tag))
        if entry is None:
            entry = state_tag, tag_number(state_tag)
            self.state_tags[id(state_tag)] = entry
        self.payloads[key] = menu, entry[1], payload[1]
        return entry[1], payload[1]

    def fired(self, t):
        saved = self.cache.get(id(t))
        if saved is not None:
            return saved[1]
        if t[0][1] is not S:
            assert t[0][1] == (S, S)
            shape = arity(t[1])
            assert shape in (2, 3)
            addr = "1" if shape == 2 else None
        else:
            left = self.fired(t[1][0][1])
            right = self.fired(t[1][1])
            assert left is None or right is None
            addr = "101" + left if left is not None else None
            if right is not None:
                addr = "11" + right
        self.cache[id(t)] = t, addr
        return addr


def arity(t):
    n = 0
    while t is not S:
        n += 1
        t = t[0]
    return n


def at(t, p):
    for side in p:
        t = t[int(side)]
    return t


def contract_at(t, p):
    spine = []
    for side in p:
        side = int(side)
        spine.append((side, t[1 - side]))
        t = t[side]
    assert t is not S and t[0] is not S and t[0][0] is not S
    (((head, x), y), z) = t
    assert head is S, "selected occurrence is not a native S redex"
    out = ((x, z), (y, z))
    for side, sibling in reversed(spine):
        out = (sibling, out) if side else (out, sibling)
    return out


def entries(t, p):
    while t is not S:
        assert t[0][0] is S
        yield t[0][1], p + LEFT_FIELD
        t, p = t[1], p + RIGHT_FIELD


@dataclass
class View:
    spent: int = 0
    committed: int = 0
    last: int | None = None
    front: str | None = None
    live: list = field(default_factory=list)
    free: list | None = None
    menu: tuple | None = None
    menu_path: str = ""
    frontier: str = ""
    state: int = 0


def read_word(t, p, result):
    while t is not S:
        shape = arity(t[0])
        if shape == 1:
            # The right historical copy stays opaque.
            assert not result.live
            result.spent += 1
            result.last = tag_number(t[1][0])
            t, p = t[0][1], p + LEFT_FIELD
        else:
            assert shape == 2 and t[0][0] == (S, S)
            if result.front is None:
                result.front = p
            result.live.append(tag_number(t[0][1]))
            t, p = t[1], p + RIGHT_FIELD


def inspect(t, state_mode=False, facts=None):
    result = View()
    if state_mode and facts is None:
        facts = MenuFacts()
    read_word(t[0][1][1], LEFT_FIELD + RIGHT_FIELD, result)
    rail, path = t[1], RIGHT_FIELD
    while arity(rail) == 4:
        block = rail[0][0][1]
        for slot, sp in entries(block, path + "001"):
            if state_mode:
                address = facts.fired(slot)
                if address is None:
                    if result.menu is None:
                        result.menu, result.menu_path = slot, sp
                else:
                    assert result.menu is None
                    result.committed += 1
                    result.state, exposed_word = facts.opened_payload(slot, address)
                    read_word(exposed_word[1], sp + address + LEFT_FIELD + '11', result)
                continue
            arms = [(slot[0][1], sp + LEFT_FIELD), (slot[1], sp + RIGHT_FIELD)]
            fired = [(i, p) for i, (a, p) in enumerate(arms) if arity(a) == 2]
            if not fired:
                if result.free is None:
                    result.free = [p for _, p in arms]
                continue
            assert result.free is None and len(fired) == 1
            result.committed += 1
            i, p = fired[0]
            payload = arms[i][0][0][1]
            if i == 1:
                read_word(payload[1], p + LEFT_FIELD + RIGHT_FIELD, result)
        rail, path = rail[1], path + RIGHT_FIELD
    assert arity(rail) == 3
    result.frontier = path
    return result


def select(v, alphabet_size=None, halt_state=None):
    stable = (v.spent - v.committed) % 2 == 0
    if stable:
        if v.front is None or v.state == halt_state:
            return v.frontier, "halt allocation"
        return v.front, "pop"
    if alphabet_size is not None:
        if v.menu is None:
            return v.frontier, "allocation"
        key = v.state * alphabet_size + v.last
        return v.menu_path + menu_address(v.menu, key), "commit"
    if v.free is None:
        return v.frontier, "allocation"
    return v.free[v.last], "commit"


def cycle_test(program, seed, fuel, counts):
    term = cyclic_seed(program, seed)
    expected = tuple(seed)
    phase = 0
    counts["cyclic seeds"] += 1
    for _ in range(fuel):
        v = inspect(term)
        assert tuple(v.live) == expected and v.spent == v.committed
        assert v.committed % len(program) == phase
        if not expected:
            for _ in range(4):
                p, op = select(v)
                assert op == "halt allocation"
                term = contract_at(term, p)
                v = inspect(term)
                assert not v.live and v.spent == v.committed
                counts["native contractions"] += 1
            return
        head, remainder = expected[0], expected[1:]
        expected = remainder + (program[phase] if head == 1 else ())
        phase = (phase + 1) % len(program)
        for steps in range(1, 5):
            p, op = select(v)
            term = contract_at(term, p)
            counts["native contractions"] += 1
            v = inspect(term)
            if op == "commit":
                break
            assert v.spent == v.committed + 1
        assert op == "commit" and steps >= 2
        assert tuple(v.live) == expected and v.spent == v.committed
        counts[f"cyclic steps of length {steps}"] += 1


def register_table(program, nr):
    """Compile register sweeps into finite FIFO table. Symbols 2*i and 2*i+1
    are respectively one unary unit and the delimiter of register i."""
    size = 2 * nr
    table = []
    for q, ins in enumerate(program):
        for seen in (0, 1):
            row = []
            for a in range(size):
                nxt, flag, out = q, seen, (a,)
                op = ins[0]
                if op == "I" and a == 2 * ins[1] + 1:
                    out = (a - 1, a)
                if op == "B" and a == 2 * ins[1] and not flag:
                    flag, out = 1, ()
                if a == size - 1:
                    if op == "I":
                        nxt = ins[2]
                    elif op == "B":
                        nxt = ins[2 + flag]
                    elif op == "J":
                        nxt = ins[1]
                    flag = 0
                row.append((2 * nxt + flag, out))
            table.append(row)
    return table


def row_word(values):
    return tuple(a for i, n in enumerate(values) for a in ([2*i] * n + [2*i+1]))


def state_test(program, values, horizon, counts):
    nreg = len(values)
    table = register_table(program, nreg)
    halt_state = 2 * next(q for q, ins in enumerate(program) if ins[0] == "H")
    state, queue = 0, row_word(values)
    term = state_seed(table, queue)
    counts["register seeds"] += 1
    for _ in range(horizon):
        v = inspect(term, True)
        assert (v.state, tuple(v.live)) == (state, queue)
        assert v.spent == v.committed
        if state == halt_state:
            for _ in range(3):
                addr, op = select(v, 2*nreg, halt_state)
                assert op == "halt allocation"
                term = contract_at(term, addr)
                counts["native contractions"] += 1
                v = inspect(term, True)
                assert v.state == halt_state and tuple(v.live) == queue
            return
        # The expected register instruction is executed independently of the table.
        ins = program[state // 2]
        prior_values = values[:]
        if ins[0] == "I":
            values[ins[1]] += 1
            next_instruction = ins[2]
        elif ins[0] == "B":
            pos = values[ins[1]] > 0
            values[ins[1]] -= int(pos)
            next_instruction = ins[2 + int(pos)]
        else:
            next_instruction = ins[1]
        for _ in row_word(prior_values):
            letter, rest = queue[0], queue[1:]
            state, emitted = table[state][letter]
            queue = rest + tuple(emitted)
            for steps in range(1, 5):
                addr, op = select(v, 2*nreg, halt_state)
                term = contract_at(term, addr)
                counts["native contractions"] += 1
                v = inspect(term, True)
                if op == "commit":
                    break
                assert v.spent == v.committed + 1
            assert op == "commit" and steps >= 2
            assert (v.state, tuple(v.live)) == (state, queue)
            assert v.spent == v.committed
            counts["finite-queue transitions"] += 1
        assert queue == row_word(values) and state == 2 * next_instruction
        counts["register instructions"] += 1


def universal_endpoint(e, x):
    """Build the numeric theorem's actual seed and readout parameters.

    The large fixed table is included in the source archive. This explicit
    occurrence model is intended for correctness, not large-run performance.
    The same table is used on every input.
    """
    import json
    from pathlib import Path
    assert isinstance(e, int) and isinstance(x, int) and min(e, x) >= 0
    meta = json.loads(Path(__file__).with_name("universal_register_program.json").read_text())
    source = meta["instructions"]
    names = meta["registers"]
    registers = [{"E": e, "program": e, "X": x, "argument": x}.get(n, 0) for n in names]
    compiled = register_table(source, len(names))
    term = state_seed(compiled, row_word(registers))
    halt = 2 * next(q for q, ins in enumerate(source) if ins[0] == "H")
    return term, 2 * len(names), halt, 2 * meta["output_register"]


def numeric_observe(v, halt, out_letter):
    if (v.spent - v.committed) % 2 or v.state != halt:
        return None
    return v.live.count(out_letter)


def run():
    counts = Counter()
    words = [bits for n in range(3) for bits in product((0, 1), repeat=n)]
    seeds = [bits for n in range(4) for bits in product((0, 1), repeat=n)]
    for p in (1, 2):
        for program in product(words, repeat=p):
            for seed in seeds:
                cycle_test(program, seed, 12, counts)
    rng = Random(20261126)
    for _ in range(75):
        program = tuple(tuple(rng.randrange(2) for _ in range(rng.randrange(6)))
                        for _ in range(rng.randrange(1, 8)))
        seed = tuple(rng.randrange(2) for _ in range(rng.randrange(1, 9)))
        cycle_test(program, seed, 32, counts)
    cycle_test(((1,),), (1,), 128, counts)
    # Move register 1 into register 0, then jump to halt.
    p = (("B", 1, 2, 1), ("I", 0, 0), ("J", 3), ("H",))
    for x in range(5):
        for y in range(5):
            state_test(p, [x, y], 2*y + 4, counts)
    # Decrement last/first registers, increment last, handle zero, and loop.
    for x in range(3):
        state_test((("B", 0, 2, 1), ("I", 1, 0), ("H",)), [x, 2], 10, counts)
    state_test((("J", 0), ("H",)), [0], 12, counts)
    state_test((("H",),), [3], 1, counts)
    for k in sorted(counts):
        print(f"{k}: {counts[k]}")


def universal_run(e, x, budget):
    term, alphabet, halt, out_letter = universal_endpoint(e, x)
    facts = MenuFacts()
    for index in range(budget + 1):
        view = inspect(term, True, facts)
        output = numeric_observe(view, halt, out_letter)
        if output is not None:
            print(f"U({e}, {x}) = {output}; native contractions {index}; "
                  f"FIFO transitions {view.committed}")
            return output
        if index < budget:
            address, _ = select(view, alphabet, halt)
            term = contract_at(term, address)
    print(f"No terminal sample within {budget} contractions")
    return None


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--universal", nargs=3, type=int, metavar=("E", "X", "LIMIT"))
    args = parser.parse_args()
    if args.universal:
        universal_run(*args.universal)
    else:
        run()
