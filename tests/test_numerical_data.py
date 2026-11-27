"""Compare actual physical word slices with an independent FIFO oracle. The
menu tests exercise the separate 446-interpreter calling convention on small
programs and read the numerical result from actual live ground-term letters."""
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "implementation/reference"))
import bare_macro as macro
import verify_selected_s as s


def physical_bits(term):
    for word, _ in macro.word_roots(term):
        while word is not s.S:
            if s.arity(word[0]) == 1:
                yield s.tag_number(word[1][0])
                word = word[0][1]
            else:
                yield s.tag_number(word[0][1])
                word = word[1]


def physical_windows(program, width, bits):
    phase = 0
    for pos, bit in enumerate(bits):
        yield phase, bits[pos:pos + width]
        width = width - 1 + (len(program[phase]) if bit else 0)
        phase = (phase + 1) % len(program)
    yield phase, ()


def compare_fifo(program, initial):
    term = s.cyclic_seed(program, initial)
    phase, queue, oracle = 0, initial, []
    for _ in range(40):
        oracle.append((phase, queue))
        if not queue:
            assert macro.action(term) is None
            bits = tuple(physical_bits(term))
            assert tuple(b for _, word in oracle if word for b in [word[0]]) == bits
            assert list(physical_windows(program, len(initial), bits)) == oracle
            return True
        addresses, term = macro.action(term)
        assert 2 <= len(addresses) <= 4
        queue = queue[1:] + (program[phase] if queue[0] else ())
        phase = (phase + 1) % len(program)
    return False


def menu(program, initial, output_index, limit):
    compiled = s.register_table(program, len(initial))
    halt = 2 * next(i for i, ins in enumerate(program) if ins[0] == "H")
    t = s.state_seed(compiled, s.row_word(initial))
    facts = s.MenuFacts()
    for n in range(limit + 1):
        v = s.inspect(t, True, facts)
        result = s.numeric_observe(v, halt, 2 * output_index)
        if result is not None:
            assert result == v.live.count(2 * output_index)
            return result
        if n != limit:
            addr, _ = s.select(v, 2 * len(initial), halt)
            t = s.contract_at(t, addr)
    return None


if __name__ == "__main__":
    words = ((), (0,), (1,), (1, 0))
    seeds = [w for n in range(4) for w in itertools.product((0, 1), repeat=n)]
    finished = sum(compare_fifo(p, w) for size in (1, 2) for p in itertools.product(words, repeat=size)
                   for w in seeds)
    add = (("B",1,2,1),("I",0,0),("H",))
    zero = (("B",0,1,0),("H",))
    inc = (("I",0,1),("I",0,2),("H",))
    forever = (("J",0),("H",))
    values = [menu(add, [2,3],0,2500), menu(add,[0,4],0,2500),
              menu(zero,[4],0,1500), menu(inc,[5],0,1000), menu(forever,[2],0,120)]
    assert values == [5,4,0,7,None], values
    print(f"{finished} completed physical FIFO archives; native menu results {values}")
