"""Sizes are for ordinary unfolded occurrence trees and for identity-shared immutable DAGs."""
from pathlib import Path
import json
import platform
import resource
import sys
from time import perf_counter,process_time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"implementation/reference"))
import verify_selected_s as ref
import verify_root_walk as walker


def sizes(t):
    memo = {id(None):(1,0)}
    stack = [(t,False)]
    while stack:
        v,ready = stack.pop()
        if id(v) in memo:
            continue
        if not ready:
            stack.extend(((v,True),(v[1],False),(v[0],False)))
        else:
            a,b = memo[id(v[0])],memo[id(v[1])]
            memo[id(v)] = (1+a[0]+b[0],1+max(a[1],b[1]))
    nodes,height=memo[id(t)]
    return {"expanded_nodes":nodes,"height":height,"identity_DAG_nodes":len(memo)}


def profile(p,w,steps):
    start=perf_counter()
    cpu=process_time()
    t=ref.cyclic_seed(p,w)
    init=perf_counter()-start
    rows=[dict(k=0,step=0,word=w,**sizes(t))]
    k=0
    for i in range(1,steps+1):
        if not ref.inspect(t).live:
            break
        while True:
            address=walker.select(t)
            t=ref.contract_at(t,address)
            k+=1
            v=ref.inspect(t)
            if v.spent==v.committed:
                rows.append(dict(k=k,step=i,word=v.live,**sizes(t)))
                break
    return {"program":p,"input":w,"initialization_seconds":init,"elapsed_seconds":perf_counter()-start,
            "CPU_seconds":process_time()-cpu,"samples":rows}

if __name__=="__main__":
    reports=[profile(((1,),()),(1,0,1),2),profile(((1,),),(1,),48),profile(((),(1,0)),(0,1,0),12)]
    print(json.dumps({"Python":platform.python_version(),"platform":platform.machine(),
                      "RSS_KiB_process_peak":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                      "profiles":reports},indent=2))
