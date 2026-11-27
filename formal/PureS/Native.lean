import Std

namespace UniformS

inductive Term where
  | s : Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr, Inhabited

infixl:72 " ⋆ " => Term.app
abbrev S := Term.s
abbrev pair (x y : Term) := S ⋆ x ⋆ y
abbrev box (x : Term) := pair S x
abbrev Address := List Bool

def contract : Term → Option Term
  | .app (.app (.app .s x) y) z => some (x ⋆ z ⋆ (y ⋆ z))
  | _ => none

def reduceAt : Address → Term → Option Term
  | [], t => contract t
  | false :: p, .app l r => (reduceAt p l).map (fun x => x ⋆ r)
  | true :: p, .app l r => (reduceAt p r).map (fun x => l ⋆ x)
  | _ :: _, .s => none

inductive Native : Term → Term → Prop
  | root (x y z) : Native (S ⋆ x ⋆ y ⋆ z) (x ⋆ z ⋆ (y ⋆ z))
  | left {l l'} (r) : Native l l' → Native (l ⋆ r) (l' ⋆ r)
  | right (l) {r r'} : Native r r' → Native (l ⋆ r) (l ⋆ r')

theorem native_hasAddress {a b} (h : Native a b) : ∃ p, reduceAt p a = some b := by
  induction h with
  | root => exact ⟨[], rfl⟩
  | left r _ ih =>
    obtain ⟨p,hp⟩ := ih
    exact ⟨false::p, by simp [reduceAt,hp]⟩
  | right l _ ih =>
    obtain ⟨p,hp⟩ := ih
    exact ⟨true::p, by simp [reduceAt,hp]⟩

theorem contract_sound {t u} (h : contract t = some u) : Native t u := by
  unfold contract at h
  split at h <;> simp_all
  subst u
  constructor

theorem address_sound (p) {a b} (h : reduceAt p a = some b) : Native a b := by
  induction p generalizing a b with
  | nil => exact contract_sound h
  | cons d p ih =>
    cases a with
    | s => simp [reduceAt] at h
    | app l r =>
      cases d <;> simp [reduceAt] at h
      · obtain ⟨t,ht,rfl⟩ := h
        exact .left _ (ih ht)
      · obtain ⟨t,ht,rfl⟩ := h
        exact .right _ (ih ht)

inductive Steps : Nat → Term → Term → Prop
  | refl (a) : Steps 0 a a
  | cons {n a b c} : Native a b → Steps n b c → Steps (n+1) a c

theorem Steps.one {a b} (h : Native a b) : Steps 1 a b := .cons h (.refl _)

theorem Steps.trans {k l a b c} (h : Steps k a b) (g : Steps l b c) : Steps (k+l) a c := by
  induction h with
  | refl => simpa using g
  | cons h _ ih => simpa [Nat.succ_add] using Steps.cons h (ih g)

theorem Steps.left {k a b} (h : Steps k a b) (r) : Steps k (a ⋆ r) (b ⋆ r) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.left _ h) ih

theorem Steps.right {k a b} (h : Steps k a b) (l) : Steps k (l ⋆ a) (l ⋆ b) := by
  induction h with
  | refl => exact .refl _
  | cons h _ ih => exact .cons (.right _ h) ih

inductive Inspection (t : Term) where
  | hit (p : Address) (u : Term) (valid : reduceAt p t = some u)
  | normal (complete : ∀ p, reduceAt p t = none)

def inspect : (t : Term) → Inspection t
  | .s => .normal (by intro p; cases p with
                      | nil => rfl
                      | cons d p => cases d <;> rfl)
  | .app l r =>
    match h : contract (l ⋆ r) with
    | some u => .hit [] u h
    | none =>
      match inspect l with
      | .hit p u ok => .hit (false::p) (u ⋆ r) (by simp [reduceAt,ok])
      | .normal nl =>
        match inspect r with
        | .hit p u ok => .hit (true::p) (l ⋆ u) (by simp [reduceAt,ok])
        | .normal nr => .normal (by intro p; cases p with
                                     | nil => exact h
                                     | cons d p => cases d <;> simp [reduceAt,nl,nr])

def preorder (t : Term) : Option Address :=
  match inspect t with | .hit p _ _ => some p | .normal _ => none

theorem preorder_spec (t) :
    (∀ p, preorder t = some p → ∃ u, reduceAt p t = some u) ∧
    (preorder t = none ↔ ∀ p, reduceAt p t = none) := by
  unfold preorder
  cases inspect t with
  | hit p u ok =>
    constructor
    · intro q h; cases h; exact ⟨u,ok⟩
    · constructor
      · intro h; contradiction
      · intro h; have bad := h p; rw [ok] at bad; contradiction
  | normal h => exact ⟨by intro p hp; contradiction, ⟨fun _ => h,fun _ => rfl⟩⟩

def tag : Bool → Term | false => S | true => S ⋆ S
abbrev readCell (b : Bool) (w : Term) := S ⋆ S ⋆ tag b ⋆ w
abbrev spent (b : Bool) (w ghost : Term) := (S ⋆ w) ⋆ (tag b ⋆ ghost)
abbrev arm (t : Term) := S ⋆ S ⋆ S ⋆ t
abbrev opened (v g : Term) := (S ⋆ v) ⋆ (S ⋆ g)
def X (F : Term) : Nat → Term
  | 0 => S ⋆ (S ⋆ F) ⋆ (S ⋆ F)
  | i+1 => (S ⋆ F) ⋆ X F i
theorem consume (b w) : Native (readCell b w) (spent b w w) := .root _ _ _
theorem release (v) : Native (arm v) (opened v v) := .root _ _ _
theorem reset (F j) : Native (X F 0 ⋆ X F j) (X F (j+1) ⋆ X F (j+1)) := .root _ _ _
theorem allocate (F i j) : Native (X F (i+1) ⋆ X F j) ((F ⋆ X F j) ⋆ (X F i ⋆ X F j)) := .root _ _ _

end UniformS
