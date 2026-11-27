"""Check the primitive action, its guard, and the physical equality of boundary outputs."""
import sys
from functools import cache
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "implementation/reference"))
from bare_macro import action
from micro import Mode, accepting, observe, step
from verify_root_walk import Cursor, fallback
from verify_selected_s import S, contract_at, cyclic_seed


@cache
def trees(n):
    if n == 1:
        return (S,)
    return tuple((l, r) for k in range(1, n) for l in trees(k) for r in trees(n-k))


checks = 0
for size in range(1, 10):
    for term in trees(size):
        preorder = fallback(Cursor(term))
        for mode in Mode:
            out = step(mode, term)
            assert (out is None) == (preorder is None)
            if out is not None:
                _, site, result = out
                assert result == contract_at(term, site)
            checks += 1

macro_count = native_count = 0
words = [(), (0,), (1,), (1,0), (1,1)]
for program in [(v,) for v in words] + list(product(words, repeat=2)):
    for queue in [(), (0,), (1,), (1,0,1)]:
        term = cyclic_seed(program, queue)
        mode = Mode.BOUNDARY
        for phase in range(7):
            assert accepting(mode, term) == (not queue)
            assert observe(term) == (queue[0] if queue else None)
            if not queue:
                break
            marks, expected = action(term)
            for j, mark in enumerate(marks):
                mode, site, term = step(mode, term)
                assert site == mark
                if j+1 < len(marks):
                    assert mode is not Mode.BOUNDARY and not accepting(mode, term)
            assert mode is Mode.BOUNDARY and term == expected
            queue = queue[1:] + (program[phase % len(program)] if queue[0] else ())
            macro_count += 1
            native_count += len(marks)
print(f"PASS {checks} mode/tree cases; {macro_count} blocks; {native_count} monitored contractions")
