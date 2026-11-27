import PureS.Observer
import PureS.Board

namespace UniformS.Automaton

theorem parse_live (b) (w : Term) :
    (run (readCell b w)).word = joinR (some (liveToken false)) (run w).word := by cases b <;> rfl
theorem parse_spent (b) (w g : Term) :
    (run (spent b w g)).word = joinR (some (spentToken b)) (run w).word := by cases b <;> rfl

def parity : List α → Bool
  | [] => false | _::xs => !parity xs
def segmentInfo (h : Word) (t : Word) : Report :=
  {pops := parity h, last := h.getLast?, live := !t.isEmpty}

theorem parse_emitted (w : Word) : (run (emit w)).word = some (segmentInfo [] w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [emit,parse_live,ih]
    simp [joinR,combine,liveToken,segmentInfo,parity]

theorem parse_history (h : List (Bool × Term)) (w : Word) :
    (run (Segment.term ⟨h,w⟩)).word = some (segmentInfo (h.map Prod.fst) w) := by
  induction h with
  | nil => exact parse_emitted w
  | cons a h ih =>
    obtain ⟨b,g⟩ := a
    change (run (spent b (Segment.term ⟨h,w⟩) g)).word = _
    rw [parse_spent,ih]
    cases h with
    | nil => simp [joinR,combine,spentToken,segmentInfo,parity]
    | cons a h =>
      simp [joinR,combine,spentToken,segmentInfo,parity,List.getLast?_cons,Option.orElse]

theorem seed_detector (p : Program) (w : Word) : halt ((seed w).tree p) = w.isEmpty := by
  rw [seed_tree]
  change (match joinR (run (emit w)).word (some {markedEnd := false}) with
    | some v => v.pops == v.commits && !v.live | none => false) = w.isEmpty
  rw [parse_emitted]
  cases w <;> rfl

end UniformS.Automaton
