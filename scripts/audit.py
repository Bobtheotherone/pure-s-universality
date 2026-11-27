"""Read statements, direct project constants and transitive axiom sets from the compiled environment."""
from pathlib import Path
import json
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
def run():
    p=subprocess.run(["lake","env","lean","Audit.lean"],cwd=ROOT/"formal",text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if p.returncode:
        print(p.stdout[-5000:]);raise SystemExit(p.returncode)
    rows=[json.loads(s[5:]) for s in p.stdout.splitlines() if s.startswith("DECL ")]
    reports=[s for s in p.stdout.splitlines() if s.startswith("'")]
    allowed={"propext","Quot.sound","Classical.choice"}
    assert rows and reports
    assert all(set(r["axioms"])<=allowed for r in rows)
    written={}
    for f in sorted((ROOT/"formal/PureS").glob("*.lean")):
        for kind,short in re.findall(r"^(?:@\[simp\]\s+)?(?:private\s+)?(theorem|def|inductive|structure|abbrev)\s+([\w.]+)",f.read_text(),re.M):
            candidates=[r for r in rows if r["module"]=="PureS."+f.stem and
                        (r["name"]=="UniformS."+short or r["name"].endswith("."+short))]
            if not candidates:continue
            row=min(candidates,key=lambda x:len(x["name"]))
            row=dict(row,source_declaration=kind,verified=True)
            written[row["name"]]=row
    assert "UniformS.Bridge.tape_halts_iff_native_samples" in written
    assert "UniformS.Certified.universal_selected_halting" in written
    assert "UniformS.Separation.combined_cutoff" in written
    for name in ("universal_natural_io","universal_single_natural_io","all_machine_tables","decode_completed","physical_outputs","accepted_tree_origin","sigma_native","size_exact","unique_output"):
        assert "UniformS.Numerical."+name in written
    assert "UniformS.Separation.first_numeric_cutoff" in written
    for row in written.values():
        if row["module"] in {"PureS.Numerical","PureS.NumericalPrimitive","PureS.FifoArchive"}:
            row["paper_labels"]=["certnumeric","sym:numerical"]
            if row["module"]=="PureS.FifoArchive":
                row["paper_labels"]=["fifoexact","sym:windnum","sym:physnum"]
        if row["name"]=="UniformS.Separation.first_numeric_cutoff":
            row["paper_labels"]=["numericv2 (Numerical separation)","final bounded equivalence in Symbolic_Numerical.tex"]
    recs=sorted(written.values(),key=lambda r:(r["module"],r["name"]))
    totals={"authored_library_modules":len(list((ROOT/"formal/PureS").glob("*.lean"))),
            "authored_library_source_lines":sum(len(f.read_text().splitlines()) for f in (ROOT/"formal/PureS").glob("*.lean")),
            "explicit_theorems":sum(r["source_declaration"]=="theorem" for r in recs),
            "explicit_definitions_and_types":sum(r["source_declaration"]!="theorem" for r in recs),
            "indexed_authored_declarations":len(recs),"environment_declarations_examined":len(rows),
            "vendored_source_modules":len(list((ROOT/"third_party/cinematic-strawberry-compiler/PureSFormal").rglob("*.lean")))}
    (ROOT/"verification").mkdir(exist_ok=True)
    ledger={"counts":totals,"declared_scope":"Arbitrary unary numerical output for every deterministic tape table on ground pure-S trees. Certified at bare macro boundaries and after individual contractions. Direct project dependencies and transitive foundation axioms come from the compiled environment.",
            "proved":recs,
            "open":[{"claim":"unbounded correspondence for the original separately restarted single-contraction walker and marked automaton; the bounded bare macro is fully proved","status":"written_proof_only"},
                    {"claim":"historical register-program numbering, full 446-label finite-menu path and literal a4 count; the tape-coded numerical theorem is fully certified","status":"written_proof_only"},
                    {"claim":"all-input physical two-pass walker move bound and stack/parent-pointer implementation equivalence","status":"written_proof_only"},
                    {"claim":"guarded pushdown replacement separation","status":"written_proof_only"}]}
    (ROOT/"verification/theorem_ledger.json").write_text(json.dumps(ledger,indent=2)+"\n")
    (ROOT/"verification/axioms_report.txt").write_text("\n".join(reports)+"\n")
    print(json.dumps(totals,sort_keys=True))
if __name__=="__main__":run()
