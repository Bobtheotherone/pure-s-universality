import PureS.Native
namespace UniformS

def leaves : Term → Nat | .s => 1 | .app l r => leaves l + leaves r
def height : Term → Nat | .s => 0 | .app l r => max (height l) (height r) + 1

theorem positive_leaves (t) : 0 < leaves t := by
  induction t <;> simp_all [leaves] <;> omega
theorem root_leaf_count (x y z) :
    leaves (x ⋆ z ⋆ (y ⋆ z)) + 1 = leaves (S ⋆ x ⋆ y ⋆ z) + leaves z := by
  simp [leaves]; omega
theorem step_cost {a b} (h : Native a b) :
    leaves a ≤ leaves b ∧ leaves b ≤ 2 * leaves a ∧ height b ≤ height a + 1 := by
  induction h with
  | root x y z =>
    have hp := positive_leaves z
    simp only [leaves,height]; omega
  | left _ _ ih => simp only [leaves,height]; omega
  | right _ _ ih => simp only [leaves,height]; omega

theorem trajectory_cost {n a b} (h : Steps n a b) :
    leaves b ≤ 2^n * leaves a ∧ height b ≤ height a + n := by
  induction h with
  | refl => simp
  | @cons n a t b hn _ ih =>
    obtain ⟨_,hl,hh⟩ := step_cost hn
    constructor
    · calc leaves b ≤ 2^n * leaves t := ih.1
           _ ≤ 2^n * (2 * leaves a) := Nat.mul_le_mul_left _ hl
           _ = 2^(n+1) * leaves a := by rw [Nat.pow_succ,Nat.mul_assoc]
    · omega

/-- Path-copy rebuilding with immutable references, represented by the siblings
    of a single occurrence. The equality is about the full unfolded tree. -/
inductive Crumb where | left (r : Term) | right (l : Term)
def rebuild : List Crumb → Term → Term
  | [],v => v
  | .left r::xs,v => rebuild xs (v ⋆ r)
  | .right l::xs,v => rebuild xs (l ⋆ v)
def descend : Address → Term → List Crumb → Option (Term × List Crumb)
  | [],t,c => some (t,c)
  | false::p,.app l r,c => descend p l (.left r::c)
  | true::p,.app l r,c => descend p r (.right l::c)
  | _::_,.s,_ => none
def copyStep (p : Address) (t : Term) : Option Term :=
  (descend p t []).bind (fun (v,cs) => (contract v).map (rebuild cs))

theorem spine_agrees (p : Address) (t : Term) (c : List Crumb) :
    ((descend p t c).bind (fun (v,cs) => (contract v).map (rebuild cs))) =
      (reduceAt p t).map (rebuild c) := by
  induction p generalizing t c with
  | nil => rfl
  | cons d p ih =>
    cases t with
    | s => cases d <;> rfl
    | app l r =>
      cases d
      · rw [descend,ih]; simp [reduceAt,Function.comp_def,rebuild]
      · rw [descend,ih]; simp [reduceAt,Function.comp_def,rebuild]
theorem copy_exact (p t) : copyStep p t = reduceAt p t := by
  unfold copyStep
  simpa [rebuild] using spine_agrees p t []
end UniformS
