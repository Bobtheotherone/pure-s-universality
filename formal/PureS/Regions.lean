import PureS.Native

namespace UniformS

inductive Ctx where
  | hole
  | left (c : Ctx) (r : Term)
  | right (l : Term) (c : Ctx)
  deriving Repr, Inhabited

def Ctx.fill : Ctx → Term → Term
  | .hole, t => t
  | .left c r, t => c.fill t ⋆ r
  | .right l c, t => l ⋆ c.fill t

theorem Ctx.native (c : Ctx) {x y} (h : Native x y) : Native (c.fill x) (c.fill y) := by
  induction c with
  | hole => exact h
  | left _ r ih => exact .left r ih
  | right l _ ih => exact .right l ih

theorem Ctx.steps (c : Ctx) {n x y} (h : Steps n x y) : Steps n (c.fill x) (c.fill y) := by
  induction c with
  | hole => exact h
  | left _ r ih => exact ih.left r
  | right l _ ih => exact ih.right l

def Ctx.comp : Ctx → Ctx → Ctx
  | .hole, d => d
  | .left c r, d => .left (c.comp d) r
  | .right l c, d => .right l (c.comp d)
@[simp] theorem Ctx.comp_fill (c d : Ctx) (x) : (c.comp d).fill x = c.fill (d.fill x) := by
  induction c <;> simp_all [Ctx.comp,Ctx.fill]

abbrev Word := List Bool
def emit : Word → Term
  | [] => S
  | b::w => readCell b (emit w)

structure Segment where
  used : List (Bool × Term)
  todo : Word
  deriving Repr, Inhabited

def shell : List (Bool × Term) → Ctx
  | [] => .hole
  | (b,g)::xs => .left (.right S (shell xs)) (tag b ⋆ g)

def Segment.term (w : Segment) : Term := (shell w.used).fill (emit w.todo)
def Segment.history (w : Segment) := w.used.map Prod.fst
def Segment.fresh (w : Word) : Segment := ⟨[],w⟩
@[simp] theorem fresh_term (w) : (Segment.fresh w).term = emit w := rfl

theorem shell_snoc (xs) (b g v) :
    (shell (xs ++ [(b,g)])).fill v = (shell xs).fill (spent b v g) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a; simp [shell,Ctx.fill,ih]

def Segment.read (used : List (Bool × Term)) (b : Bool) (tail : Word) : Segment := ⟨used ++ [(b,emit tail)],tail⟩
theorem segment_read (used b tail) :
    Native (Segment.term ⟨used,b::tail⟩) (Segment.read used b tail).term := by
  simp only [Segment.term,Segment.read,shell_snoc]
  exact (shell used).native (consume b (emit tail))

/-- An ordered collection of editable executable words. Its leaves are actual
    ground words or opaque ground subterms. Application preserves both roles. -/
inductive Region where
  | raw (t : Term)
  | word (w : Segment)
  | join (l r : Region)
  deriving Repr, Inhabited
def Region.term : Region → Term
  | .raw t => t
  | .word w => w.term
  | .join l r => l.term ⋆ r.term

def Region.live : Region → Word
  | .raw _ => []
  | .word w => w.todo
  | .join l r => l.live ++ r.live

abbrev Mark := Bool × Bool
def marked (a : Bool) (w : Word) : List Mark := w.map (fun b => (a,b))
def Region.marks : Region → List Mark
  | .raw _ => []
  | .word w => marked true w.history ++ marked false w.todo
  | .join l r => l.marks ++ r.marks

/-- Precisely the first unspent token changes. This function is proof
    instrumentation and never updates an executable native tree. -/
def markFirst : List Mark → List Mark
  | [] => []
  | (false,b)::rs => (true,b)::rs
  | (true,b)::rs => (true,b)::markFirst rs

theorem markFirst_prefix (w : Word) (t : List Mark) :
    markFirst (marked true w ++ t) = marked true w ++ markFirst t := by
  induction w <;> simp_all [marked,markFirst]

def freshBox (w : Segment) := Region.join (.raw (S ⋆ S)) (.word w)
def untouched (c : Ctx) (t : Region) : Region :=
  match c with
  | .hole => t
  | .left k r => .join (untouched k t) (.raw r)
  | .right l k => .join (.raw l) (untouched k t)
@[simp] theorem untouched_term (c t) : (untouched c t).term = c.fill t.term := by
  induction c <;> simp_all [untouched,Region.term,Ctx.fill]
@[simp] theorem untouched_live (c t) : (untouched c t).live = t.live := by
  induction c <;> simp_all [untouched,Region.live]
@[simp] theorem untouched_marks (c t) : (untouched c t).marks = t.marks := by
  induction c <;> simp_all [untouched,Region.marks]

/-- Positive-sized editable fields form a left-to-right prefix search. -/
def Region.pop : Region → Option (Bool × Region)
  | .raw _ => none
  | .word ⟨_,[]⟩ => none
  | .word ⟨h,b::v⟩ => some (b,.word (Segment.read h b v))
  | .join l r =>
    match l.pop with
    | some (b,l') => some (b,.join l' r)
    | none => r.pop.map (fun (b,r') => (b,.join l r'))

theorem Region.pop_none (a : Region) : a.pop = none ↔ a.live = [] := by
  induction a with
  | raw => simp [pop,live]
  | word w => cases w with | mk h t => cases t <;> simp [pop,live]
  | join l r il ir =>
    cases hp : l.pop with
    | none => simp [pop,live,hp,il.mp hp,ir]
    | some p => cases p; have hl : l.live ≠ [] := fun h => by simp [hp] at * <;> contradiction
                simp [pop,live,hp,hl]

theorem Region.pop_sound {a : Region} {b a'} (h : a.pop = some (b,a')) :
    a.live = b :: a'.live ∧ Native a.term a'.term := by
  induction a generalizing a' b with
  | raw => simp [pop] at h
  | word w =>
    rcases w with ⟨u,(_|⟨c,cs⟩)⟩
    · simp [pop] at h
    · simp only [pop,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨rfl,segment_read ..⟩
  | join l r il ir =>
    cases hp : l.pop with
    | some p =>
      obtain ⟨c,l'⟩ := p
      simp only [pop,hp,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      obtain ⟨he,hn⟩ := il hp
      exact ⟨by simp [live,he], .left _ hn⟩
    | none =>
      cases hq : r.pop with
      | none => simp [pop,hp,hq] at h
      | some p =>
        obtain ⟨c,r'⟩ := p
        simp only [pop,hp,hq,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        obtain ⟨he,hn⟩ := ir hq
        exact ⟨by simp [live,(pop_none l).mp hp,he], .right _ hn⟩

end UniformS
