import PureS.BareMacro
namespace UniformS.BareMacro
open UniformS Readback

def finish (b : Bool) (t : Term) : Option (Nat × Term) := do
  if let some u := fire b t then return (1,u)
  let a ← alloc t
  if let some u := fire b a then return (2,u)
  let a' ← alloc a
  let u ← fire b a'
  return (3,u)

/-- A literal bounded algorithm on the bare tree. Between macro invocations
    its entire persistent state is the ground S-term. -/
def selected (t : Term) : Option (Nat × Term) := do
  let b ← (live t).head?
  let u ← pop t
  let (k,v) ← finish b u
  return (k+1,v)

theorem fire_port (p) (s : Port) (b : Bool) (ok : Valid p s.board) :
    fire b (s.board.tree p) = some ((s.fire p b).tree p) := by
  rcases s with ⟨u,a,v,vs,f,r,j⟩
  obtain ⟨hu,ha⟩ := ok
  change boardAction skip (fireY b) skip (plug u (frame (plug a (slots (v::vs)))
    (X (template p) f) (X (template p) r ⋆ X (template p) j))) = _
  rw [outer_closed_spec p u hu _ _ _ (Or.inl ⟨b,rfl⟩)]
  simp only [frame,box,pair,railAction,row_closed (fireY b) a ha _ (Or.inl ⟨b,rfl⟩),fresh_fire,
    Option.map_some]
  cases vs <;> simp [Port.fire,Board.tree,plug_append,plug,finished,Region.term,added,
    frame,pair,box,pack_term,slots]

theorem fire_front (p u r j) (hu : OuterOK p u) (b) :
    fire b ((Board.frontier u r j).tree p) = none := by
  rw [fire,Board.tree,outer_closed_spec p u hu _ _ _ (Or.inl ⟨b,rfl⟩),front_skip]; rfl

theorem alloc_zero (p u j) (hu : OuterOK p u) :
    alloc ((Board.frontier u 0 j).tree p) =
      some ((Board.frontier u (j+1) (j+1)).tree p) := by
  rw [alloc,Board.tree,outer_closed_spec p u hu _ _ _ (Or.inr rfl),front_red]; rfl

theorem alloc_succ (p u r j) (hu : OuterOK p u) :
    alloc ((Board.frontier u (r+1) j).tree p) =
      some ((Port.mk u [] p.first p.rest j r j).board.tree p) := by
  rw [alloc,Board.tree,outer_closed_spec p u hu _ _ _ (Or.inr rfl),front_red]; rfl

theorem finish_spec (p s b) (ok : Valid p s) :
    finish b (s.tree p) =
      some ((prepare p s).1+1,((prepare p s).2.fire p b).tree p) := by
  cases s with
  | period u a v vs f r j =>
    let port : Port := ⟨u,a,v,vs,f,r,j⟩
    have hv := fire_port p port b ok
    change fire b ((Board.period u a v vs f r j).tree p) = _ at hv
    simp [finish,hv,prepare,port]
  | frontier u r j =>
    cases r with
    | zero =>
      let a : Port := ⟨u,[],p.first,p.rest,j+1,j,j+1⟩
      have ha : Valid p a.board := ⟨ok,by simp [a,SlotsOK]⟩
      simp [finish,fire_front p u _ _ ok,alloc_zero p u _ ok,alloc_succ p u _ _ ok,
        fire_port p a b ha,a,prepare]
    | succ r =>
      let a : Port := ⟨u,[],p.first,p.rest,j,r,j⟩
      have ha : Valid p a.board := ⟨ok,by simp [a,SlotsOK]⟩
      simp [finish,fire_front p u _ _ ok,alloc_succ p u _ _ ok,fire_port p a b ha,a,prepare]

theorem live_valid (p s) (h : Valid p s) : live (s.tree p) = s.queue := by
  rw [live,bare_marks p s h]
  cases s <;> simp [Board.marks,Board.queue,sleeve_remaining]

theorem selected_spec (p s) (hs : Valid p s) :
    selected (s.tree p) = (advance p s).map (fun (k,t) => (k,t.tree p)) := by
  simp only [selected,live_valid p s hs,pop_spec p s hs,advance]
  cases e : s.pop with
  | none => simp [(Board.pop_none s).mp e]
  | some x =>
    obtain ⟨b,t⟩ := x
    have ht := valid_pop p hs e
    have eqn := (Board.pop_sound p e).1
    simp [eqn,finish_spec p t b ht,Nat.add_assoc]

def next (t : Term) := ((selected t).map Prod.snd).getD t
def run : Nat → Term → Term
  | 0,t => t
  | n+1,t => next (run n t)

theorem all_bare_samples (p : Program) (w : Word) (n) :
    run n ((seed w).tree p) = (Bridge.sample p n (seed w)).tree p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run,ih,next,selected_spec p _ (valid_sample p w n)]
    cases e : advance p (Bridge.sample p n (seed w)) with
    | none => simp [Bridge.sample,Bridge.tick,e]
    | some x => cases x; simp [Bridge.sample,Bridge.tick,e]

theorem registered_source (p : PureSFormal.CTS.Program) (w : Word) (n) :
    live (run n ((seed w).tree (Bridge.compile p))) =
      (PureSFormal.CTS.iterate p n (PureSFormal.CTS.initial p w)).data := by
  rw [all_bare_samples,complete_readback]
  exact (Bridge.sample_agrees p w n).1

open PureSFormal.Research.ProtectedTrieDeterministicCompiler in
theorem tape_halts_iff_selected (m : DeterministicTape.Instance) :
    DeterministicTape.Halts m ↔
      ∃ n, live (run n ((Bridge.input m).tree Bridge.fixed)) = [] := by
  rw [Readback.tape_halts_iff_empty_bare_sample]
  constructor
  · rintro ⟨n,k,_,_,ha⟩
    exact ⟨n,by simpa [Bridge.input,all_bare_samples] using ha⟩
  · rintro ⟨n,ha⟩
    obtain ⟨k,hk,hpath⟩ := Bridge.sample_native Bridge.fixed (Bridge.input m) n
    exact ⟨n,k,hk,hpath,by simpa [Bridge.input,all_bare_samples] using ha⟩
end UniformS.BareMacro
