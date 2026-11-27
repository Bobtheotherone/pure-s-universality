"""Cross-check canonical source semantics independently of selection and mutation."""
from pathlib import Path
from itertools import product
import json
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"implementation/reference"))
import evaluator as ev
import verify_selected_s as ref
import verify_root_walk as walker


def binary_cases():
    cases=selections=0
    for phase in range(1,5):
        for seed in ((),(0,),(1,),(1,0,1),(1,1,0,0)):
            p=tuple(tuple((i+j)%2 for j in range(i%3)) for i in range(phase))
            t=ev.binary_seed(p,seed)
            queue=seed
            source_index=0
            for _ in range(24):
                r=ev.binary_read(t)
                if r["stable"]:
                    assert r["queue"]==queue and r["halt"]==(not queue)
                    if queue:
                        q=queue[0]
                        queue=queue[1:]+(p[source_index] if q else ())
                        source_index=(source_index+1)%phase
                address=walker.select(t)
                assert address is not None
                t=ref.contract_at(t,address)
                selections+=1
            cases+=1
    # Normal or malformed inputs must select a legal redex or report normality.
    raw_trees=0
    for n in range(1,10):
        for t in walker.ground_terms(n):
            v=ev.numeric_read(t,6,4)
            addr=walker.fallback(walker.Cursor(t))
            actual=ev.numeric_step(t,6,4,4)
            if v is None:
                assert actual==(ref.contract_at(t,addr) if addr is not None else t)
            else:
                assert addr is not None
                candidates=[]
                todo=[(t,"")]
                while todo:
                    node,path=todo.pop()
                    if walker.degree(node)==3:
                        candidates.append(ref.contract_at(t,path))
                    if node is not None:
                        todo.extend(((node[0],path+"0"),(node[1],path+"1")))
                assert actual in candidates
            raw_trees+=1
    return dict(program_seed_pairs=cases,selections=selections,arbitrary_numeric_trees=raw_trees)


def numerical_cases():
    # Move register 1 to register 0 and halt. The test interpreter runs on
    # ordinary integers. It supplies expected outputs only.
    code=(("B",1,2,1),("I",0,0),("J",3),("H",))
    table=ref.register_table(code,2)
    states,letters,terminal=len(table),4,6
    total=0
    for x,y in product(range(3),repeat=2):
        t=ref.state_seed(table,ref.row_word([x,y]))
        while True:
            a=ev.numeric_read(t,states,letters)
            assert a is not None
            v=ref.inspect(t,True)
            assert v.live==a.live and v.state==a.state
            assert (v.spent%2,v.committed%2)==(a.pop_parity,a.fire_parity)
            actual=ev.numeric_output(a,terminal,0)
            if actual is not None:
                assert actual==x+y
                break
            p,_=ref.select(v,letters,terminal)
            expected=ref.contract_at(t,p)
            t=ev.numeric_step(t,states,letters,terminal)
            assert t==expected
            total+=1
            assert total<100000
    return dict(program_inputs=9,compared_native_contractions=total)


if __name__=="__main__":
    print(json.dumps(dict(binary=binary_cases(),numeric=numerical_cases()),sort_keys=True))
