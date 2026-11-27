import PureS.Regions

namespace UniformS
abbrev Sleeve := List Region
def plug : Sleeve → Term → Term
  | [], t => t
  | r::rs, t => r.term ⋆ plug rs t
def pack : Sleeve → Region → Region
  | [], t => t
  | r::rs, t => .join r (pack rs t)
def visible (l : Sleeve) : Word := l.flatMap Region.live
@[simp] theorem plug_append (l k : Sleeve) (t) :
    plug (l++k) t = plug l (plug k t) := by induction l <;> simp_all [plug]
@[simp] theorem pack_term (l t) : (pack l t).term = plug l t.term := by
  induction l <;> simp_all [pack,plug,Region.term]
@[simp] theorem pack_live (l t) : (pack l t).live = visible l ++ t.live := by
  induction l <;> simp_all [pack,visible,Region.live,List.append_assoc]
theorem plug_native (l : Sleeve) {a b} (h : Native a b) :
    Native (plug l a) (plug l b) := by
  induction l with | nil => exact h | cons r rs ih => exact .right _ ih
theorem plug_steps (l : Sleeve) {a b n} (h : Steps n a b) :
    Steps n (plug l a) (plug l b) := by
  induction l with | nil => exact h | cons r rs ih => exact ih.right _

def popSleeve : Sleeve → Option (Bool × Sleeve)
  | [] => none
  | r::rs => match r.pop with
    | some (b,r') => some (b,r'::rs)
    | none => (popSleeve rs).map (fun (b,rs') => (b,r::rs'))

theorem popSleeve_none (l) : popSleeve l = none ↔ visible l = [] := by
  induction l with
  | nil => simp [popSleeve,visible]
  | cons r rs ih =>
    cases h : r.pop with
    | none =>
      change _ ↔ r.live ++ visible rs = []
      simpa [popSleeve,h,(Region.pop_none r).mp h] using ih
    | some p =>
      have hn : r.live ≠ [] := fun he => by have := (Region.pop_none r).mpr he; simp [h] at this
      cases p; simp [visible,popSleeve,h,hn]

theorem popSleeve_sound {l : Sleeve} {b l'} (h : popSleeve l = some (b,l')) :
    visible l = b :: visible l' ∧ ∀ t, Native (plug l t) (plug l' t) := by
  induction l generalizing b l' with
  | nil => simp [popSleeve] at h
  | cons r rs ih =>
    cases e : r.pop with
    | some p =>
      obtain ⟨c,r'⟩ := p
      simp only [popSleeve,e,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      obtain ⟨q,n⟩ := Region.pop_sound e
      exact ⟨by simp [visible,q], fun _ => .left _ n⟩
    | none =>
      cases e' : popSleeve rs with
      | none => simp [popSleeve,e,e'] at h
      | some p =>
        obtain ⟨c,rs'⟩ := p
        simp only [popSleeve,e,e',Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨q,n⟩ := ih e'
        exact ⟨by simpa [visible,(Region.pop_none r).mp e] using q, fun _ => .right _ (n _)⟩

structure Program where
  first : Word
  rest : List Word
  deriving Repr, Inhabited
def Program.period (p : Program) := p.first::p.rest
def slot (w : Word) := pair (arm S) (arm (box (emit w)))
def slots : List Word → Term
  | [] => S
  | w::ws => pair (slot w) (slots ws)
def template (p : Program) := box (slots p.period)
def payload (b : Bool) (v : Word) := if b then v else []

def released : Bool → Word → Region
  | false, w => .raw (pair (opened S S) (arm (box (emit w))))
  | true, w =>
    let x := box (emit w)
    .join (.raw (S ⋆ arm S)) (.join (.join (.raw S) (freshBox (Segment.fresh w))) (.raw (S ⋆ x)))

@[simp] theorem released_live (b v) : (released b v).live = payload b v := by
  cases b <;> simp [released,Region.live,payload,freshBox,Segment.fresh]
theorem fire_slot (b w) : Native (slot w) (released b w).term := by
  cases b with
  | false => exact .left _ (.right _ (release S))
  | true => exact .right _ (release (box (emit w)))

/-- On the frontier the entire previous header and periods sit in the outer
    sleeve. In a period the inner sleeve holds precisely its committed slots. -/
inductive Board where
  | frontier (outer : Sleeve) (r j : Nat)
  | period (outer inner : Sleeve) (v : Word) (vs : List Word) (frame r j : Nat)
  deriving Repr, Inhabited

def frame (list stamp rest : Term) := (box list ⋆ stamp) ⋆ rest
def Board.tree (p : Program) : Board → Term
  | .frontier u r j => plug u (X (template p) r ⋆ X (template p) j)
  | .period u a v vs f r j => plug u (frame (plug a (slots (v::vs))) (X (template p) f)
                                          (X (template p) r ⋆ X (template p) j))
def Board.queue : Board → Word
  | .frontier u _ _ => visible u
  | .period u a .. => visible u ++ visible a
def Board.pending : Board → List Word
  | .frontier .. => []
  | .period _ _ v vs .. => v::vs

def seed (w : Word) : Board := .frontier [.join (.raw S) (freshBox (.fresh w))] 0 0
@[simp] theorem seed_queue (w) : (seed w).queue = w := by simp [seed,Board.queue,visible,Region.live,freshBox,Segment.fresh]
theorem seed_tree (p w) : (seed w).tree p =
    pair (box (emit w)) (X (template p) 0 ⋆ X (template p) 0) := rfl

def Board.pop : Board → Option (Bool × Board)
  | .frontier u r j => (popSleeve u).map (fun (b,u') => (b,.frontier u' r j))
  | .period u a v vs f r j =>
    match popSleeve u with
    | some (b,u') => some (b,.period u' a v vs f r j)
    | none => (popSleeve a).map (fun (b,a') => (b,.period u a' v vs f r j))

theorem Board.pop_none (s : Board) : s.pop = none ↔ s.queue = [] := by
  cases s with
  | frontier u r j => simp [pop,queue,popSleeve_none]
  | period u a v vs f r j =>
    cases hu : popSleeve u with
    | none => simp [pop,queue,hu,(popSleeve_none u).mp hu,popSleeve_none]
    | some z =>
      have hn : visible u ≠ [] := fun h => by have := (popSleeve_none u).mpr h; simp [hu] at this
      cases z; simp [pop,queue,hu,hn]

theorem Board.pop_sound (p) {s s' : Board} {b} (h : s.pop = some (b,s')) :
    s.queue = b :: s'.queue ∧ s'.pending = s.pending ∧ Native (s.tree p) (s'.tree p) := by
  cases s with
  | frontier u r j =>
    cases hp : popSleeve u with
    | none => simp [pop,hp] at h
    | some z =>
      obtain ⟨c,u'⟩ := z
      simp only [pop,hp,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      obtain ⟨q,n⟩ := popSleeve_sound hp
      exact ⟨q,rfl,n _⟩
  | period u a v vs f r j =>
    cases hp : popSleeve u with
    | some z =>
      obtain ⟨c,u'⟩ := z
      simp only [pop,hp,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      obtain ⟨q,n⟩ := popSleeve_sound hp
      exact ⟨by simp [queue,q],rfl,n _⟩
    | none =>
      cases ha : popSleeve a with
      | none => simp [pop,hp,ha] at h
      | some z =>
        obtain ⟨c,a'⟩ := z
        simp only [pop,hp,ha,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨q,n⟩ := popSleeve_sound ha
        exact ⟨by simp [queue,(popSleeve_none u).mp hp,q],rfl,
          plug_native u (.left _ (.left _ (.right _ (n _))))⟩

end UniformS
