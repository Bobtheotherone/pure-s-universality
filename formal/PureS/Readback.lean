import PureS.Dataflow
import PureS.Tape
namespace UniformS.Readback
open UniformS

/-- A permissive structural readout on bare trees. Malformed branches contribute
    no tokens. Histories in nondesignated fields are never traversed. -/
def word : Term → List Mark
  | .app (.app (.app .s .s) t) w =>
    match t with
    | .s => (false,false)::word w
    | .app .s .s => (false,true)::word w
    | _ => []
  | .app (.app .s w) (.app t _) =>
    match t with
    | .s => (true,false)::word w
    | .app .s .s => (true,true)::word w
    | _ => []
  | _ => []

theorem word_emit (w : Word) : word (emit w) = marked false w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [emit,word,readCell,tag,marked] at ih ⊢ <;> exact ih

theorem word_segment (w : Segment) : word w.term = (Region.word w).marks := by
  rcases w with ⟨h,w⟩
  induction h with
  | nil => exact word_emit w
  | cons a h ih =>
    obtain ⟨b,g⟩ := a
    change word (spent b (Segment.term ⟨h,w⟩) g) = _
    cases b <;> simp [spent,tag,word,Region.marks,Segment.history,marked] at ih ⊢ <;> exact ih

def openPayload : Term → List Mark
  | .app (.app .s (.app (.app .s .s) w)) _ => word w
  | _ => []
def isOpen : Term → Bool
  | .app (.app .s _) _ => true
  | _ => false
abbrev Info := List Mark × Nat
def merge (x y : Info) : Info := (x.1 ++ y.1,x.2+y.2)
def cell : Term → Info
  | .app (.app .s a) b => (openPayload b,if isOpen a || isOpen b then 1 else 0)
  | _ => ([],0)
def row : Term → Info
  | .app (.app .s a) b => merge (cell a) (row b)
  | _ => ([],0)
def rail : Term → Info
  | .app (.app (.app (.app .s .s) rowTerm) _) b => merge (row rowTerm) (rail b)
  | _ => ([],0)
def bare : Term → Info
  | .app (.app .s (.app (.app .s .s) w)) t => merge (word w,0) (rail t)
  | _ => ([],0)

def headR (w : Segment) : Region := .join (.raw S) (freshBox w)
def rightR (w : Segment) (g : Term) : Region :=
  .join (.raw S) (.join (.raw (S ⋆ arm S)) (.join (.join (.raw S) (freshBox w)) (.raw g)))
inductive SlotOK : Region → Prop
  | zero (v : Word) : SlotOK (added false v)
  | one (w : Segment) (g : Term) : SlotOK (rightR w g)
def SlotsOK (rs : Sleeve) := ∀ r ∈ rs, SlotOK r

@[simp] theorem added_ok (b v) : SlotOK (added b v) := by
  cases b with
  | false => exact .zero v
  | true => exact .one (.fresh v) (S ⋆ box (emit v))
theorem slot_pop {r r' : Region} {b} (hs : SlotOK r) (h : r.pop = some (b,r')) : SlotOK r' := by
  cases hs with
  | zero v => simp [added,released,Region.pop] at h
  | one w g =>
    rcases w with ⟨hist,(_|⟨x,xs⟩)⟩
    · simp [rightR,freshBox,Region.pop] at h
    · simp [rightR,freshBox,Region.pop] at h
      obtain ⟨rfl,rfl⟩ := h
      exact .one _ _

theorem read_slot {r : Region} (h : SlotOK r) (t : Term) :
    row (r.term ⋆ t) = merge (r.marks,1) (row t) := by
  cases h with
  | zero v => rfl
  | one w g =>
    change merge (word w.term,1) (row t) = _
    rw [word_segment]; simp [rightR,freshBox,Region.marks]

theorem preserveList {Pred : Region → Prop}
    (pres : ∀ {x b y}, Pred x → Region.pop x = some (b,y) → Pred y)
    {s s' : Sleeve} {b} (ok : ∀ x ∈ s, Pred x) (h : popSleeve s = some (b,s')) :
    ∀ x ∈ s', Pred x := by
  induction s generalizing b s' with
  | nil => simp [popSleeve] at h
  | cons x xs ih =>
    have hx := ok x (by simp)
    have hr : ∀ u ∈ xs, Pred u := fun u hu => ok u (by simp [hu])
    cases e : x.pop with
    | some y =>
      obtain ⟨c,z⟩ := y
      simp [popSleeve,e] at h
      obtain ⟨rfl,rfl⟩ := h
      simpa using And.intro (pres hx e) hr
    | none =>
      cases es : popSleeve xs with
      | none => simp [popSleeve,e,es] at h
      | some y =>
        obtain ⟨c,z⟩ := y
        simp [popSleeve,e,es] at h
        obtain ⟨rfl,rfl⟩ := h
        simpa using And.intro hx (ih hr es)

theorem pack_pop {a : Sleeve} {b} {v : Region} (h : (pack a (.raw S)).pop = some (b,v)) :
    ∃ az, popSleeve a = some (b,az) ∧ v = pack az (.raw S) := by
  induction a generalizing b v with
  | nil => simp [pack,Region.pop] at h
  | cons r rs ih =>
    cases e : r.pop with
    | some x =>
      obtain ⟨c,z⟩ := x
      simp [pack,Region.pop,e] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨z::rs,by simp [popSleeve,e],rfl⟩
    | none =>
      cases y : (pack rs (.raw S)).pop with
      | none => simp [pack,Region.pop,e,y] at h
      | some x =>
        obtain ⟨c,z⟩ := x
        simp [pack,Region.pop,e,y] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨zs,ha,rfl⟩ := ih y
        exact ⟨r::zs,by simp [popSleeve,e,ha],rfl⟩

inductive FrameOK (p : Program) : Region → Prop
  | made (a : Sleeve) (h : SlotsOK a) (j : Nat) : FrameOK p (finished p a j)
theorem frame_pop (p) {r r' : Region} {b} (ok : FrameOK p r) (h : r.pop = some (b,r')) : FrameOK p r' := by
  cases ok with
  | made a hk j =>
    cases e : (pack a (.raw S)).pop with
    | none => simp [finished,Region.pop,e] at h
    | some v =>
      obtain ⟨c,z⟩ := v
      simp [finished,Region.pop,e] at h
      obtain ⟨rfl,rfl⟩ := h
      obtain ⟨a',ha,rfl⟩ := pack_pop e
      exact .made a' (preserveList (fun hs hx => slot_pop hs hx) hk ha) j

def OuterOK (p : Program) (s : Sleeve) : Prop :=
  ∃ w rest, s = headR w :: rest ∧ ∀ r ∈ rest, FrameOK p r

theorem outer_append (p) {u} (ok : OuterOK p u) {a} (ha : SlotsOK a) (f) :
    OuterOK p (u ++ [finished p a f]) := by
  obtain ⟨w,rest,rfl,h⟩ := ok
  refine ⟨w,rest ++ [finished p a f],rfl,?_⟩
  intro r hr
  simp at hr
  rcases hr with h1 | rfl
  · exact h r h1
  · exact .made a ha f
theorem outer_pop (p) {s s'} {b} (ok : OuterOK p s) (h : popSleeve s = some (b,s')) :
    OuterOK p s' := by
  obtain ⟨w,rest,rfl,hr⟩ := ok
  rcases w with ⟨hist,(_|⟨c,cs⟩)⟩
  · cases e : popSleeve rest with
    | none => simp [popSleeve,headR,freshBox,Region.pop,e] at h
    | some v =>
      obtain ⟨x,k⟩ := v
      simp [popSleeve,headR,freshBox,Region.pop,e] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨_,k,rfl,preserveList (frame_pop p) hr e⟩
  · simp [popSleeve,headR,freshBox,Region.pop] at h
    obtain ⟨rfl,rfl⟩ := h
    exact ⟨_,rest,rfl,hr⟩

def Valid (p : Program) : Board → Prop
  | .frontier u .. => OuterOK p u
  | .period u a .. => OuterOK p u ∧ SlotsOK a
theorem valid_seed (p w) : Valid p (seed w) := ⟨.fresh w,[],rfl,by simp⟩
theorem valid_pop (p) {s t : Board} {b} (hs : Valid p s) (h : s.pop = some (b,t)) : Valid p t := by
  cases s with
  | frontier u r j =>
    cases e : popSleeve u with
    | none => simp [Board.pop,e] at h
    | some v =>
      obtain ⟨c,m⟩ := v
      simp [Board.pop,e] at h; obtain ⟨rfl,rfl⟩ := h
      exact outer_pop p hs e
  | period u a v vs f r j =>
    obtain ⟨hu,ha⟩ := hs
    cases e : popSleeve u with
    | some x =>
      obtain ⟨c,m⟩ := x; simp [Board.pop,e] at h; obtain ⟨rfl,rfl⟩ := h
      exact ⟨outer_pop p hu e,ha⟩
    | none =>
      cases ea : popSleeve a with
      | none => simp [Board.pop,e,ea] at h
      | some x =>
        obtain ⟨c,m⟩ := x; simp [Board.pop,e,ea] at h; obtain ⟨rfl,rfl⟩ := h
        exact ⟨hu,preserveList (fun hs hx => slot_pop hs hx) ha ea⟩
theorem valid_prepare (p) {s} (h : Valid p s) : Valid p (prepare p s).2.board := by
  cases s with
  | period => exact h
  | frontier u r j => cases r <;> exact ⟨h,by simp [SlotsOK,prepare]⟩
theorem valid_fire (p) (s : Port) (b) (h : Valid p s.board) : Valid p (s.fire p b) := by
  obtain ⟨hu,ha⟩ := h
  have hz : SlotsOK (s.inner ++ [added b s.current]) := by
    intro r hr
    simp at hr
    rcases hr with h1 | rfl
    · exact ha r h1
    · exact added_ok b s.current
  rcases s with ⟨u,a,v,vs,f,r,j⟩
  cases vs with
  | nil => exact outer_append p hu hz f
  | cons => exact ⟨hu,hz⟩
theorem valid_advance (p) {s t : Board} {n} (hs : Valid p s) (h : advance p s = some (n,t)) : Valid p t := by
  unfold advance at h
  cases e : s.pop with
  | none => simp [e] at h
  | some x =>
    obtain ⟨b,s'⟩ := x
    cases hq : prepare p s' with
    | mk k a =>
      simp [e,hq] at h
      obtain ⟨rfl,rfl⟩ := h
      have good := valid_prepare p (valid_pop p hs e)
      rw [hq] at good
      exact valid_fire p a b good

theorem read_fresh (vs : List Word) : row (slots vs) = ([],0) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change merge ([],0) (row (slots vs)) = _
    rw [ih]; rfl

theorem read_row (a : Sleeve) (ha : SlotsOK a) (t : Term) :
    row (plug a t) = merge (sleeveMarks a,a.length) (row t) := by
  induction a with
  | nil => simp [plug,merge,sleeveMarks]
  | cons r rs ih =>
    have hz := read_slot (ha r (by simp)) (plug rs t)
    have hr : SlotsOK rs := fun z h => ha z (by simp [h])
    change row (r.term ⋆ plug rs t) = _
    rw [hz,ih hr]
    simp [sleeveMarks,merge,List.append_assoc]; omega

theorem read_rail0 (p) (r j) : rail (X (template p) r ⋆ X (template p) j) = ([],0) := by
  cases r <;> rfl
theorem read_frames (p) (rs : Sleeve) (h : ∀ r ∈ rs, FrameOK p r) (t : Term) :
    (rail (plug rs t)).1 = sleeveMarks rs ++ (rail t).1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := h r (by simp)
    have hh : ∀ u ∈ rs, FrameOK p u := fun u hu => h u (by simp [hu])
    cases hr with
    | made a ha j =>
      change (merge (row (pack a (.raw S)).term) (rail (plug rs t))).1 = _
      rw [pack_term,read_row a ha]
      simp [merge,finished,Region.marks,Region.term,pack_marks,row,sleeveMarks,List.append_assoc] at ih ⊢
      exact ih hh

theorem read_outer (p) {u : Sleeve} (ok : OuterOK p u) (t : Term) :
    (bare (plug u t)).1 = sleeveMarks u ++ (rail t).1 := by
  obtain ⟨w,rs,rfl,hr⟩ := ok
  change word w.term ++ (rail (plug rs t)).1 = _
  rw [word_segment,read_frames p rs hr]
  simp [sleeveMarks,headR,freshBox,Region.marks,List.append_assoc]

theorem bare_marks (p) (s) (hs : Valid p s) : (bare (s.tree p)).1 = s.marks := by
  cases s with
  | frontier u r j =>
    rw [Board.tree,read_outer p hs,read_rail0]; simp [Board.marks]
  | period u a v vs f r j =>
    obtain ⟨hu,ha⟩ := hs
    rw [Board.tree,read_outer p hu]
    change sleeveMarks u ++ (merge (row (plug a (slots (v::vs)))) (rail (X (template p) r ⋆ X (template p) j))).1 = _
    rw [read_row a ha,read_fresh,read_rail0]
    simp [merge,Board.marks]

theorem valid_sample (p) (w : Word) (n) : Valid p (Bridge.sample p n (seed w)) := by
  induction n with
  | zero => exact valid_seed p w
  | succ n ih =>
    cases h : advance p (Bridge.sample p n (seed w)) with
    | none => simpa [Bridge.sample,Bridge.tick,h] using ih
    | some x =>
      obtain ⟨k,s⟩ := x
      simpa [Bridge.sample,Bridge.tick,h] using (valid_advance p ih h)

def live (t : Term) := remainingMarks (bare t).1

theorem complete_readback (p) (w : Word) (n) : live ((Bridge.sample p n (seed w)).tree p) =
    (Bridge.sample p n (seed w)).queue := by
  rw [live,bare_marks p _ (valid_sample p w n)]
  cases Bridge.sample p n (seed w) <;> simp [Board.marks,Board.queue,sleeve_remaining]

open PureSFormal.Research.ProtectedTrieDeterministicCompiler in
theorem tape_halts_iff_empty_bare_sample (m : DeterministicTape.Instance) :
    DeterministicTape.Halts m ↔
      ∃ n k, k ≤ 4*n ∧ Steps k ((Bridge.input m).tree Bridge.fixed)
        ((Bridge.sample Bridge.fixed n (Bridge.input m)).tree Bridge.fixed) ∧
        live ((Bridge.sample Bridge.fixed n (Bridge.input m)).tree Bridge.fixed) = [] := by
  rw [Bridge.tape_halts_iff_native_samples]
  simp only [Bridge.input,complete_readback]
end UniformS.Readback
