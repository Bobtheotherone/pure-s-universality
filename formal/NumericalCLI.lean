import PureS

open UniformS UniformS.Numerical

/-- Fuel bounds the demonstration only. The certified interface has no fuel.
    Compiled universal Cook inputs can exceed available physical memory. -/
def boundedRead (fuel : Nat) (t : Term) : Option Nat :=
  if H t then D t else
    match fuel with
    | 0 => none
    | n+1 => boundedRead n (sigma t)

def main (args : List String) : IO UInt32 := do
  match args.map String.toNat? with
  | [some e,some x,some fuel] =>
    IO.println (repr (boundedRead fuel (E e x)))
    return 0
  | _ =>
    IO.eprintln "Supply a machine code, unary input value and macro budget as decimal naturals."
    return 2
