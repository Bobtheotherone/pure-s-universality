import PureS.Numerical

namespace UniformS.Numerical
open UniformS
open Micro Certified

theorem macro_reachable (n : Nat) (t : Term) :
    ∃ k, Micro.iterate k (.boundary,t) = (.boundary,orbit n t) := by
  induction n generalizing t with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [orbit_start]
    cases ha : action t with
    | none => simpa [nextTerm,ha] using ih t
    | some a =>
      obtain ⟨j,u⟩ := a
      obtain ⟨k,hk⟩ := ih u
      exact ⟨j+k,by rw [iterate_add,micro_realizes _ _ _ ha,hk]; simp [nextTerm,ha]⟩

theorem done_stays (k : Nat) (t : Term) : (Micro.iterate k (.done,t)).1 = .done := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    cases hi : inspect t with
    | normal h => simpa only [Micro.iterate,one,propose,hi,Option.getD] using ih t
    | hit p u h => simpa only [Micro.iterate,one,propose,hi,Option.getD] using ih u

theorem accepting_stays_at_halt (k : Nat) (t : Term) (he : halt t = true)
    (hit : accepting (Micro.iterate k (.boundary,t)) = true) :
    Micro.iterate k (.boundary,t) = (.boundary,t) := by
  have hr : (fold t).root = none := by simpa only [halt,Option.isNone_iff_eq_none] using he
  induction k with
  | zero => rfl
  | succ k ih =>
    cases hi : inspect t with
    | normal h =>
      simpa [Micro.iterate,one,propose,hr,hi] using
        ih (by simpa [Micro.iterate,one,propose,hr,hi] using hit)
    | hit p u h =>
      simp [Micro.iterate,one,propose,hr,hi,accepting,done_stays] at hit

theorem accepted_tree_origin (k : Nat) (t : Term) (hg : Productive t)
    (hit : accepting (Micro.iterate k (.boundary,t)) = true) :
    ∃ n, Micro.iterate k (.boundary,t) = (.boundary,orbit n t) := by
  induction k using Nat.strongRecOn generalizing t with
  | ind k ih =>
    cases he : halt t with
    | true => exact ⟨0,accepting_stays_at_halt k t he hit⟩
    | false =>
      obtain ⟨l,u,hl⟩ := hg 0 he
      change action t = some (l,u) at hl
      have hlo := (all_terms_native _ _ _ hl).1
      have hu : nextTerm t = u := by simp [nextTerm,hl]
      by_cases short : k < l
      · cases k with
        | zero => simp [Micro.iterate,accepting,he] at hit
        | succ j => simp [accepting,(micro_block _ _ _ hl).2 (j+1) (by omega) short] at hit
      · have hk : k = l + (k-l) := by omega
        have eqn : Micro.iterate k (.boundary,t) = Micro.iterate (k-l) (.boundary,u) := by
          calc
            _ = Micro.iterate (l+(k-l)) (.boundary,t) := congrArg (fun j => Micro.iterate j _) hk
            _ = _ := by rw [iterate_add,micro_realizes _ _ _ hl]
        have prod : Productive u := by
          intro n; rw [← hu,← orbit_start]; exact hg (n+1)
        obtain ⟨n,hn⟩ := ih (k-l) (by omega) u prod (by rwa [← eqn])
        exact ⟨n+1,by rw [eqn,hn,orbit_start,hu]⟩

/-- The inert wrapper is preserved at every contraction. The controller reads
    only the right subtree and its eight-valued mode. -/
def primitiveState (e x k : Nat) : Mode × Term :=
  let w := programWord (source e x)
  let m := Micro.iterate k (.boundary,(seed w).tree Bridge.fixed)
  (m.1,pair (emit w) m.2)
def primitiveH (m : Mode × Term) := decide (m.1 = Mode.boundary) && H m.2

theorem universal_single_natural_io (e x y : Nat) :
    U e x y ↔ ∃ k, primitiveH (primitiveState e x k) = true ∧
      D (primitiveState e x k).2 = some y := by
  let w := programWord (source e x)
  let t := (seed w).tree Bridge.fixed
  rw [universal_natural_io]
  constructor
  · rintro ⟨n,hn,hd⟩
    obtain ⟨k,hk⟩ := macro_reachable n t
    refine ⟨k,?_,?_⟩
    · change (decide ((Micro.iterate k (.boundary,t)).1 = Mode.boundary) &&
        H (pair (emit w) (Micro.iterate k (.boundary,t)).2)) = true
      rw [hk]
      simpa only [E,initial,iter_context,Bool.true_and,decide_true] using hn
    · change D (pair (emit w) (Micro.iterate k (.boundary,t)).2) = some y
      rw [hk]; simpa only [E,initial,iter_context] using hd
  · rintro ⟨k,hh,hd⟩
    have hit : accepting (Micro.iterate k (.boundary,t)) = true := hh
    obtain ⟨n,hn⟩ := accepted_tree_origin k t (seed_productive _ _) hit
    refine ⟨n,?_,?_⟩
    · rw [hn] at hit
      simpa only [E,initial,iter_context,H,pair,accepting,Bool.true_and,decide_true] using hit
    · change D (pair (emit w) (Micro.iterate k (.boundary,t)).2) = some y at hd
      rw [hn] at hd; simpa only [E,initial,iter_context] using hd

end UniformS.Numerical
