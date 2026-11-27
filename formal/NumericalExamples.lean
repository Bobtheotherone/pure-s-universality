import PureS

open UniformS UniformS.Numerical
open PureSFormal.Research.ProtectedTrieDeterministicCompiler
open PureSFormal.Computation

/-- Erase the first unit and move right; halt immediately on a blank. -/
def predMachine : DeterministicTape.Machine := ⟨[⟨none,some ⟨false,.right,1⟩⟩]⟩
/-- Scan across the numeral, append a unit, return left to the blank, then
    move onto the first unit. Handles the initially empty numeral as well. -/
def succMachine : DeterministicTape.Machine :=
  ⟨[⟨some ⟨true,.left,1⟩,some ⟨true,.right,0⟩⟩,
    ⟨some ⟨false,.right,2⟩,some ⟨true,.left,1⟩⟩]⟩
def divergeMachine : DeterministicTape.Machine :=
  ⟨[⟨some ⟨false,.stay,0⟩,some ⟨true,.stay,0⟩⟩]⟩

def evaluateSource (m : DeterministicTape.Machine) (x fuel : Nat) : Option Nat := do
  let r ← DeterministicTape.runFor? m (DeterministicTape.initialRow ⟨m,0,List.replicate x true⟩) fuel
  if (DeterministicTape.step? m r).isNone then some (numeral r) else none

theorem sourceTest_to_ground (m : DeterministicTape.Machine) (x fuel y)
    (h : evaluateSource m x fuel = some y) :
    ∃ k, H (iter k (E (DeterministicTapeCode.machineCode m) x)) = true ∧
      D (iter k (E (DeterministicTapeCode.machineCode m) x)) = some y := by
  apply (universal_natural_io _ _ _).mp
  let s : Source := ⟨m,0,List.replicate x true⟩
  have hs : Numerical.source (DeterministicTapeCode.machineCode m) x = s := by
    simp [Numerical.source,s]
  change Returns (Numerical.source _ x) y
  rw [hs]
  change ((DeterministicTape.runFor? m (DeterministicTape.initialRow s) fuel).bind
    (fun r => if (DeterministicTape.step? m r).isNone then some (numeral r) else none)) = some y at h
  cases he : DeterministicTape.runFor? m (DeterministicTape.initialRow s) fuel with
  | none => simp [he] at h
  | some r =>
    cases hr : DeterministicTape.step? m r with
    | none => exact ⟨r,⟨⟨fuel,he⟩,hr⟩,by simpa [he,hr] using h⟩
    | some t => simp [he,hr] at h

example : evaluateSource predMachine 0 0 = some 0 := by decide
example : evaluateSource predMachine 6 1 = some 5 := by decide
example : evaluateSource succMachine 0 2 = some 1 := by decide
example : evaluateSource succMachine 4 10 = some 5 := by decide
example : evaluateSource succMachine 8 18 = some 9 := by decide
example : evaluateSource divergeMachine 3 20 = none := by decide

def main : IO Unit := do
  for (m,x,k) in [(predMachine,0,0),(predMachine,6,1),(succMachine,0,2),
      (succMachine,4,10),(succMachine,8,18),(divergeMachine,3,20)] do
    IO.println (x,k,evaluateSource m x k)
