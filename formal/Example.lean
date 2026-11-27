import PureS.Certified
import PureS.Simulation
import PureS.WordAudit
open UniformS

def proveByReplay (p : Program) (w : Word) (horizon : Nat) : IO Nat := do
  let mut state := seed w
  let mut ground := state.tree p
  let mut contractions := 0
  for _ in [:horizon] do
    if (Automaton.halt ground != state.queue.isEmpty) then
      throw (IO.userError "different empty-queue tests")
    if (Certified.halt ground != state.queue.isEmpty) then
      throw (IO.userError "different boundary regular halt tests")
    match advance p state with
    | none => break
    | some (k,next) =>
      if Certified.action ground != some (k,next.tree p) then
        throw (IO.userError "different entire bare macro result")
      for _ in [:k] do
        let some nextTerm := Automaton.oneStep ground | throw (IO.userError "missing redex")
        ground := nextTerm
        contractions := contractions+1
      if ground != next.tree p then throw (IO.userError "bare and annotated terms differ")
      state := next
  return contractions

def main : IO Unit := do
  let mut count := 0
  for p in [Program.mk [true] [[]],⟨[],[]⟩,⟨[false],[]⟩,⟨[true],[]⟩] do
    for w in [[],[true],[false],[true,false,true]] do
      count := count + (← proveByReplay p w 3)
  IO.println s!"PASS: 16 seeds; {count} independently nominated native contractions"
