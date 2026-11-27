"""Execute finite checks. Captures actual statuses, output, wall times and CPU times."""
from pathlib import Path
import argparse,json,os,platform,resource,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[1]

def run(label,args,expected,logs):
    start=time.perf_counter()
    before=resource.getrusage(resource.RUSAGE_CHILDREN)
    cp=subprocess.run(args,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    result={"label":label,"argv":args,"exit":cp.returncode,"seconds":time.perf_counter()-start,
            "child_cpu_seconds":(after.ru_utime+after.ru_stime)-(before.ru_utime+before.ru_stime),
            "stdout":cp.stdout,"expected_fragments":expected}
    result["passed"]=cp.returncode==0 and all(s in cp.stdout for s in expected)
    logs.append(result)
    print(f"{label}: {result['passed']} ({result['seconds']:.2f} seconds)",flush=True)
    if not result["passed"]:raise RuntimeError(cp.stdout[-2100:])

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--quick",action="store_true")
    p.add_argument("--mathics",help="optional Mathics executable")
    p.add_argument("--out",default="verification/test_results.json")
    args=p.parse_args()
    logs=[]
    try:
        py="python3"
        base="implementation/reference/"
        run("micro-controller",[py,"tests/test_micro.py"],["16448 mode/tree cases; 331 blocks; 1066 monitored contractions"],logs)
        run("bare-macro",[py,"tests/compare_bare_macro.py"],["120 seeds;"],logs)
        run("assembler",[py,base+"interpreter_assembly.py"],["446 assembled instructions; 29 register names"],logs)
        run("native-differential",[py,base+"verify_selected_s.py"],["cyclic seeds: 916","native contractions: 25763","register instructions: 171"],logs)
        run("walker",[py,base+"verify_root_walk.py"],["27480 native selections","2056"],logs)
        run("arbitrary-and-menu",[py,"tests/adversarial.py"],['"compared_native_contractions": 489'],logs)
        run("public-binary",[py,base+"evaluator.py","1,","101","--limit","6"],['"contractions": 6, "word": "11"'],logs)
        run("physical-numerical",[py,"tests/test_numerical_data.py"],["native menu results [5, 4, 0, 7, None]"],logs)
        if not args.quick:
            run("U(1,0)",[py,base+"verify_selected_s.py","--universal","1","0","9000"],["U(1, 0) = 0; native contractions 6552; FIFO transitions 2162"],logs)
            run("U(1,1)",[py,base+"verify_selected_s.py","--universal","1","1","15000"],["U(1, 1) = 1; native contractions 11668; FIFO transitions 3860"],logs)
        if args.mathics:
            run("wolfram-language",[args.mathics,"-q","-f","examples/CheckWolfram.wl"],["PASS cyclic samples and initially empty input"],logs)
    finally:
        report={"python":platform.python_version(),"architecture":platform.machine(),"quick":args.quick,"checks":logs}
        f=Path(args.out)
        if not f.is_absolute(): f=ROOT/f
        f.parent.mkdir(parents=True,exist_ok=True)
        f.write_text(json.dumps(report,indent=2)+"\n")
if __name__=="__main__":main()
