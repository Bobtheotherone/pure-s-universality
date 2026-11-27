import PureS.Policy
namespace UniformS.Certified
open UniformS Readback BareMacro
abbrev Bit := Option Bool
def first (x y : Bit) := x.orElse (fun _ => y)
structure State where
  leaf : Bool := false
  unary : Bool := false
  box : Bool := false
  frameHead : Bool := false
  header : Bool := false
  tag : Bit := none
  reader : Bit := none
  rightTag : Bit := none
  word : Bit := none
  unaryWord : Bit := none
  boxWord : Bit := none
  unaryBoxWord : Bit := none
  arm : Bit := none
  slot : Bit := none
  unarySlot : Bit := none
  row : Bit := none
  boxRow : Bit := none
  rows : Bit := none
  rail : Bit := none
  root : Bit := none
  deriving DecidableEq, Inhabited, Repr

def delta (u v : State) : State :=
  let bx := u.tag == some true
  { unary := u.leaf, box := bx, frameHead := u.box, header := u.leaf && v.box,
    tag := if u.leaf && v.leaf then some true else none,
    reader := if bx then v.tag else none, rightTag := u.tag,
    word := if u.reader.isSome then u.reader else if v.rightTag.isSome then u.unaryWord else none,
    unaryWord := if u.leaf then v.word else none,
    boxWord := if bx then v.word else none,
    unaryBoxWord := if u.leaf then v.boxWord else none,
    arm := u.unaryBoxWord, slot := if u.unary then v.arm else none,
    unarySlot := if u.leaf then v.slot else none,
    row := if u.unary then first u.unarySlot v.row else none,
    boxRow := if bx then v.row else none,
    rows := if u.box then u.boxRow else none,
    rail := if u.frameHead then first u.rows v.rail else none,
    root := if u.header then first u.unaryBoxWord v.rail else none }
def fold : Term → State
  | .s => {leaf := true,tag := some false}
  | .app l r => delta (fold l) (fold r)

-- A concrete injection into five two-state and fifteen three-state coordinates.
def code (s : State) : List Bit :=
  [s.leaf,s.unary,s.box,s.frameHead,s.header,s.tag,s.reader,s.rightTag,s.word,s.unaryWord,
   s.boxWord,s.unaryBoxWord,s.arm,s.slot,s.unarySlot,s.row,s.boxRow,s.rows,s.rail,s.root]
theorem code_inj (s t : State) (h : code s = code t) : s = t := by
  cases s; cases t; simp [code] at h; obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ := h; congr
theorem code_length (s) : (code s).length = 20 := rfl
theorem head_append (x y : Word) : (x ++ y).head? = first x.head? y.head? := by cases x <;> rfl

theorem folded_word (w : Segment) : (fold w.term).word = w.todo.head? := by
  have fresh (v : Word) : (fold (emit v)).word = v.head? := by
    cases v with | nil => rfl | cons b v => cases b <;> rfl
  rcases w with ⟨h,v⟩
  induction h with
  | nil => exact fresh v
  | cons entry h ih =>
    obtain ⟨b,g⟩ := entry
    cases b <;> exact ih

theorem folded_slot (r : Region) (ok : SlotOK r) (t : Term) :
    (fold (r.term ⋆ t)).row = first r.live.head? (fold t).row := by
  cases ok with
  | zero v => rfl
  | one w g =>
    change first (fold w.term).word (fold t).row = _
    rw [folded_word]; simp [rightR,Region.live,freshBox]
theorem folded_row (a : Sleeve) (ha : SlotsOK a) (t : Term) :
    (fold (plug a t)).row = first (visible a).head? (fold t).row := by
  induction a with
  | nil => rfl
  | cons r rs ih =>
    have hh : SlotsOK rs := fun u hu => ha u (by simp [hu])
    rw [plug,folded_slot r (ha r (by simp)),ih hh]
    change first r.live.head? (first (visible rs).head? (fold t).row) =
      first (r.live ++ visible rs).head? (fold t).row
    rw [head_append]; cases r.live.head? <;> rfl
theorem folded_fresh (vs : List Word) : (fold (slots vs)).row = none := by
  induction vs with | nil => rfl | cons v vs ih => exact ih
theorem folded_front (p) (r j) : (fold (X (template p) r ⋆ X (template p) j)).rail = none := by
  cases r <;> rfl
theorem folded_frame (p) (r) (ok : FrameOK p r) (t) :
    (fold (r.term ⋆ t)).rail = first r.live.head? (fold t).rail := by
  cases ok with
  | made a ha j =>
    change first (fold (pack a (.raw S)).term).row (fold t).rail = _
    rw [pack_term,folded_row a ha]
    change first (first (visible a).head? none) (fold t).rail = _
    simp [finished,Region.live,pack_live,first]
theorem folded_frames (p) (rs : Sleeve) (hr : ∀ r ∈ rs, FrameOK p r) (t) :
    (fold (plug rs t)).rail = first (visible rs).head? (fold t).rail := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hh : ∀ z ∈ rs, FrameOK p z := fun z hz => hr z (by simp [hz])
    rw [plug,folded_frame p r (hr r (by simp)),ih hh]
    change first r.live.head? (first (visible rs).head? (fold t).rail) =
      first (r.live ++ visible rs).head? (fold t).rail
    rw [head_append]; cases r.live.head? <;> rfl
theorem folded_outer (p) {u} (ok : OuterOK p u) (t) :
    (fold (plug u t)).root = first (visible u).head? (fold t).rail := by
  obtain ⟨w,rs,rfl,hr⟩ := ok
  change first (fold w.term).word (fold (plug rs t)).rail = _
  rw [folded_word,folded_frames p rs hr]
  change first w.todo.head? (first (visible rs).head? (fold t).rail) = _
  simp [visible,headR,freshBox,Region.live,head_append]
  cases w.todo.head? <;> rfl

theorem head_correct (p s) (hs : Valid p s) : (fold (s.tree p)).root = s.queue.head? := by
  cases s with
  | frontier u r j =>
    rw [Board.tree,folded_outer p hs,folded_front]
    simp [first,Board.queue]
  | period u a v vs f r j =>
    obtain ⟨hu,ha⟩ := hs
    rw [Board.tree,folded_outer p hu]
    change first (visible u).head? (first (fold (plug a (slots (v::vs)))).row
        (fold (X (template p) r ⋆ X (template p) j)).rail) = _
    rw [folded_row a ha,folded_front,folded_fresh]
    simp [first,Board.queue,head_append]

def halt (t : Term) := (fold t).root.isNone
def action (t : Term) : Option (Nat × Term) := do
  let b ← (fold t).root
  let v ← pop t
  let (j,z) ← finish b v
  return (j+1,z)
def nextTerm (t : Term) := ((action t).map Prod.snd).getD t
def orbit : Nat → Term → Term
  | 0,t => t
  | n+1,t => nextTerm (orbit n t)

theorem action_valid (p s) (h : Valid p s) :
    action (s.tree p) = (advance p s).map (fun (k,t) => (k,t.tree p)) := by
  rw [← selected_spec p s h]
  simp only [action,selected,head_correct p s h,live_valid p s h]

theorem all_terms_native (t u k) (h : action t = some (k,u)) :
    2 ≤ k ∧ k ≤ 4 ∧ Steps k t u := by
  cases hb : (fold t).root with
  | none => simp [action,hb] at h
  | some b =>
    cases hp : pop t with
    | none => simp [action,hb,hp] at h
    | some v =>
      cases hf : finish b v with
      | none => simp [action,hb,hp,hf] at h
      | some x =>
        obtain ⟨j,z⟩ := x
        simp [action,hb,hp,hf] at h; obtain ⟨rfl,rfl⟩ := h
        obtain ⟨lo,hi,hn⟩ := finish_legal _ _ _ _ hf
        exact ⟨by omega,by omega,.cons (pop_legal _ _ hp) hn⟩

theorem orbit_literal (p : Program) (w : Word) (n) :
    orbit n ((seed w).tree p) = (Bridge.sample p n (seed w)).tree p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orbit,ih,nextTerm,action_valid p _ (valid_sample p w n)]
    cases e : advance p (Bridge.sample p n (seed w)) with
    | none => simp [Bridge.sample,Bridge.tick,e]
    | some x => cases x; simp [Bridge.sample,Bridge.tick,e]

theorem all_program_queues (p : PureSFormal.CTS.Program) (w : Word) (n) :
    live (orbit n ((seed w).tree (Bridge.compile p))) =
      (PureSFormal.CTS.iterate p n (PureSFormal.CTS.initial p w)).data := by
  rw [orbit_literal,complete_readback]
  exact (Bridge.sample_agrees p w n).1

open PureSFormal.Research.ProtectedTrieDeterministicCompiler in
/-- A fixed ground-term-only macro, a fixed finite tree algebra and a fixed
    program. No decomposed board or source configuration occurs in the assertion. -/
theorem universal_selected_halting (m : DeterministicTape.Instance) :
    DeterministicTape.Halts m ↔
      ∃ n, halt (orbit n ((Bridge.input m).tree Bridge.fixed)) = true := by
  rw [BareMacro.tape_halts_iff_selected]
  apply exists_congr
  intro n
  simp only [Bridge.input,all_bare_samples,orbit_literal,halt,head_correct _ _ (valid_sample _ _ _),complete_readback]
  cases (Bridge.sample Bridge.fixed n (seed (PureSFormal.Computation.DeterministicTapeCook.encodeBits m))).queue <;> simp
end UniformS.Certified
