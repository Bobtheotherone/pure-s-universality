import PureS.Board

namespace UniformS
structure Port where
  outer : Sleeve
  inner : Sleeve
  current : Word
  rest : List Word
  stamp : Nat
  leftIndex : Nat
  rightIndex : Nat
  deriving Repr, Inhabited

def Port.board (s : Port) := Board.period s.outer s.inner s.current s.rest s.stamp s.leftIndex s.rightIndex

def prepare (p : Program) : Board → Nat × Port
  | .period u a v vs f r j => (0,⟨u,a,v,vs,f,r,j⟩)
  | .frontier u 0 j => (2,⟨u,[],p.first,p.rest,j+1,j,j+1⟩)
  | .frontier u (r+1) j => (1,⟨u,[],p.first,p.rest,j,r,j⟩)

def phaseList (p : Program) (s : Board) := if s.pending.isEmpty then p.period else s.pending

theorem prepare_spec (p s) :
    let (n,k) := prepare p s
    n ≤ 2 ∧ Steps n (s.tree p) (k.board.tree p) ∧
      k.board.queue = s.queue ∧ (k.current :: k.rest) = phaseList p s := by
  cases s with
  | period u a v vs f r j => exact ⟨by decide, .refl _, rfl, rfl⟩
  | frontier u r j =>
    cases r with
    | zero =>
      exact ⟨by decide, plug_steps u (.cons (reset _ j) (.one (allocate _ j (j+1)))),
             by simp [Port.board,Board.queue,visible],rfl⟩
    | succ r =>
      exact ⟨by decide, plug_steps u (.one (allocate _ r j)),
             by simp [Port.board,Board.queue,visible],rfl⟩

def added (b : Bool) (v : Word) : Region := .join (.raw S) (released b v)
def finished (p : Program) (a : Sleeve) (stamp : Nat) : Region :=
  .join (.join (.raw (S ⋆ S)) (pack a (.raw S))) (.raw (X (template p) stamp))

def Port.fire (p : Program) (s : Port) (b : Bool) : Board :=
  let a := s.inner ++ [added b s.current]
  match s.rest with
  | [] => .frontier (s.outer ++ [finished p a s.stamp]) s.leftIndex s.rightIndex
  | v::vs => .period s.outer a v vs s.stamp s.leftIndex s.rightIndex

theorem fire_spec (p) (s : Port) (b : Bool) :
    (s.fire p b).queue = s.board.queue ++ payload b s.current ∧
    (s.fire p b).pending = s.rest ∧ Native (s.board.tree p) ((s.fire p b).tree p) := by
  rcases s with ⟨u,a,v,vs,f,r,j⟩
  cases vs with
  | nil =>
    constructor
    · simp [Port.fire,Port.board,Board.queue,visible,finished,Region.live,added,List.append_assoc]
    · refine ⟨rfl,?_⟩
      simp only [Port.board,Port.fire,Board.tree,plug_append,plug,finished,
                 Region.term,pack_term,added,frame,slots]
      exact plug_native u (.left _ (.left _ (.right _ (plug_native a (.left _ (.right _ (fire_slot b v)))))))
  | cons w ws =>
    constructor
    · simp [Port.fire,Port.board,Board.queue,visible,Region.live,added,List.append_assoc]
    · refine ⟨rfl,?_⟩
      simp only [Port.board,Port.fire,Board.tree,plug_append,plug,added,Region.term,slots,frame]
      exact plug_native u (.left _ (.left _ (.right _ (plug_native a (.left _ (.right _ (fire_slot b v)))))))

/-- A conventional CTS phase cursor. An empty remaining period restarts at its
    first appendant on the next step. The empty data queue has no successor. -/
structure Config where
  queue : Word
  remaining : List Word
  deriving DecidableEq, Repr, Inhabited
def observe (s : Board) : Config := ⟨s.queue,s.pending⟩
def source (p : Program) (c : Config) : Option Config :=
  match c.queue with
  | [] => none
  | b::z =>
    let next := if c.remaining.isEmpty then p.period else c.remaining
    match next with
    | [] => none
    | v::vs => some ⟨z ++ payload b v,vs⟩

def advance (p : Program) (s : Board) : Option (Nat × Board) := do
  let (b,t) ← s.pop
  let (k,a) := prepare p t
  return (k+2,a.fire p b)

theorem macro_none (p s) : advance p s = none ↔ s.queue = [] := by
  unfold advance
  cases e : s.pop with
  | none => simp [(Board.pop_none s).mp e]
  | some z =>
    have hn : s.queue ≠ [] := fun h => by have := (Board.pop_none s).mpr h; simp [e] at this
    rcases z with ⟨b,t⟩; cases prepare p t; simp [hn]

theorem macro_exact (p) {s t : Board} {n} (h : advance p s = some (n,t)) :
    2 ≤ n ∧ n ≤ 4 ∧ Steps n (s.tree p) (t.tree p) ∧ source p (observe s) = some (observe t) := by
  unfold advance at h
  cases hp : s.pop with
  | none => simp [hp] at h
  | some z =>
    obtain ⟨b,s'⟩ := z
    cases hk : prepare p s' with
    | mk k a =>
      simp [hp,hk] at h
      obtain ⟨rfl,rfl⟩ := h
      obtain ⟨hq,he,hr⟩ := Board.pop_sound p hp
      have hprep := prepare_spec p s'
      rw [hk] at hprep
      obtain ⟨hb,hn,ha,hw⟩ := hprep
      obtain ⟨hf,hs,hstep⟩ := fire_spec p a b
      refine ⟨by omega,by omega,?_,?_⟩
      · have hpath := Steps.cons hr (hn.trans (Steps.one hstep))
        simpa [Nat.add_assoc] using hpath
      · change (a.current :: a.rest) = (if s'.pending.isEmpty then p.period else s'.pending) at hw
        rw [he] at hw
        simp only [source,observe,hq,← hw,hf,ha,hs]

inductive Run (p : Program) : Nat → Config → Config → Prop
  | zero (s) : Run p 0 s s
  | next {n s t u} : source p s = some t → Run p n t u → Run p (n+1) s u

theorem lift_step (p) (s : Board) {c} (h : source p (observe s) = some c) :
    ∃ n t, advance p s = some (n,t) ∧ observe t = c := by
  cases e : advance p s with
  | none => have hz := (macro_none p s).mp e; simp [source,observe,hz] at h
  | some z =>
    obtain ⟨n,t⟩ := z
    exact ⟨n,t,rfl,Option.some.inj ((macro_exact p e).2.2.2.symm.trans h)⟩

theorem run_refines (p) {n a b} (h : Run p n a b) (s : Board) (hs : observe s = a) :
    ∃ k t, 2*n ≤ k ∧ k ≤ 4*n ∧ Steps k (s.tree p) (t.tree p) ∧ observe t = b := by
  induction h generalizing s with
  | zero => exact ⟨0,s,by omega,by omega,.refl _,hs⟩
  | next first _ ih =>
    obtain ⟨k,t,hm,he⟩ := lift_step p s (hs ▸ first)
    obtain ⟨lo,hi,hn,_⟩ := macro_exact p hm
    obtain ⟨j,u,jlo,jhi,jh,hu⟩ := ih t he
    exact ⟨k+j,u,by omega,by omega,hn.trans jh,hu⟩

theorem ground_trace (p : Program) (w : Word) {n c} (h : Run p n ⟨w,[]⟩ c) :
    ∃ k t, 2*n ≤ k ∧ k ≤ 4*n ∧ Steps k ((seed w).tree p) (t.tree p) ∧ observe t = c :=
  run_refines p h (seed w) (by simp [observe,seed_queue]; rfl)

end UniformS
