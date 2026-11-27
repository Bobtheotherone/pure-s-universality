from itertools import product
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"implementation/reference"))
from bare_macro import action,head
from verify_selected_s import cyclic_seed,contract_at
from verify_root_walk import select
words=[(),(0,),(1,),(1,0),(1,1)]
count=steps=sites=0
for program in [(v,) for v in words]+list(product(words,repeat=2)):
    for seed in [(),(0,),(1,),(1,0,1)]:
        term=cyclic_seed(program,seed)
        que=seed
        count+=1
        for n in range(7):
            assert head(term)==(que[0] if que else None)
            ans=action(term)
            if not que:
                assert ans is None
                break
            marks,new=ans
            assert 2<=len(marks)<=4
            for mark in marks:
                expected=select(term)
                assert expected==mark,(expected,mark)
                term=contract_at(term,mark)
            assert term==new
            que=que[1:]+(program[n%len(program)] if que[0] else ())
            steps+=1
            sites+=len(marks)
print(f"PASS {count} seeds; {steps} complete bare macros; {sites} exact primitive addresses")
