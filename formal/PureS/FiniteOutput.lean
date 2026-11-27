import PureS.Certified
namespace UniformS.Output
open UniformS Certified
open PureSFormal.Research.ProtectedTrieDeterministicCompiler

-- A finite family of disjoint deterministic recognizers is the usual
-- semidecision presentation of a partial function into a finite alphabet.
def bundle : List Term → Term
  | [] => S
  | x::xs => pair x (bundle xs)
def update : Term → Term
  | .app (.app .s x) xs => pair (nextTerm x) (update xs)
  | t => t
def atPort : Term → Nat → Option Term
  | .app (.app .s x) _,0 => some x
  | .app (.app .s _) xs,i+1 => atPort xs i
  | _,_ => none
def seen (t : Term) (i : Nat) := ((atPort t i).map halt).getD false
def iter : Nat → Term → Term
  | 0,t => t
  | n+1,t => update (iter n t)
def encode (ms : List DeterministicTape.Instance) :=
  bundle (ms.map (fun m => (Bridge.input m).tree Bridge.fixed))

theorem update_bundle (ts : List Term) : update (bundle ts) = bundle (ts.map nextTerm) := by
  induction ts with | nil => rfl | cons x xs ih => simp [bundle,update,pair,ih]
theorem ports (ts : List Term) (i : Nat) : atPort (bundle ts) i = ts[i]? := by
  induction ts generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with | zero => rfl | succ i => exact ih i
theorem orbit_bundle (ts : List Term) (n) :
    iter n (bundle ts) = bundle (ts.map (orbit n)) := by
  induction n with
  | zero => simp [iter,orbit,bundle]
  | succ n ih => rw [iter,ih,update_bundle]; simp [List.map_map,orbit,Function.comp_def]

theorem next_native (t) : ∃ k, k ≤ 4 ∧ Steps k t (nextTerm t) := by
  cases e : action t with
  | none => exact ⟨0,by decide,by simp [nextTerm,e,Steps.refl]⟩
  | some x =>
    obtain ⟨k,u⟩ := x
    obtain ⟨_,hk,hn⟩ := all_terms_native t u k e
    exact ⟨k,hk,by simpa [nextTerm,e] using hn⟩
theorem round_native (ts : List Term) :
    ∃ k, k ≤ 4*ts.length ∧ Steps k (bundle ts) (update (bundle ts)) := by
  induction ts with
  | nil => exact ⟨0,by decide,.refl _⟩
  | cons t ts ih =>
    obtain ⟨a,ha,hp⟩ := next_native t
    obtain ⟨b,hb,hq⟩ := ih
    refine ⟨a+b,by simp; omega,?_⟩
    exact ((hp.right S).left _).trans (hq.right _)

theorem any_bit_channel (ms : List DeterministicTape.Instance) (i : Nat) (m)
    (h : ms[i]? = some m) :
    DeterministicTape.Halts m ↔ ∃ n, seen (iter n (encode ms)) i = true := by
  rw [universal_selected_halting]
  apply exists_congr
  intro n
  simp [seen,encode,orbit_bundle,ports,List.getElem?_map,h]

def detector (t : Term) := seen t 0 || seen t 1
def decoder (t : Term) : Option Bool :=
  if seen t 0 then some false else if seen t 1 then some true else none

theorem binary_io (a b : DeterministicTape.Instance)
    (disjoint : ¬(DeterministicTape.Halts a ∧ DeterministicTape.Halts b)) (y : Bool) :
    DeterministicTape.Halts (if y then b else a) ↔
      ∃ n, detector (iter n (encode [a,b])) = true ∧ decoder (iter n (encode [a,b])) = some y := by
  have h0 := any_bit_channel [a,b] 0 a rfl
  have h1 := any_bit_channel [a,b] 1 b rfl
  cases y with
  | false =>
    constructor
    · intro h
      obtain ⟨k,hk⟩ := h0.mp h
      exact ⟨k,by simp [detector,hk],by simp [decoder,hk]⟩
    · rintro ⟨k,_,hd⟩
      apply h0.mpr
      refine ⟨k,?_⟩
      cases e : seen (iter k (encode [a,b])) 0
      · cases ee : seen (iter k (encode [a,b])) 1 <;> simp [decoder,e,ee] at hd
      · rfl
  | true =>
    constructor
    · intro h
      obtain ⟨k,hk⟩ := h1.mp h
      have hn : seen (iter k (encode [a,b])) 0 = false := by
        cases e : seen (iter k (encode [a,b])) 0
        · rfl
        · exact False.elim (disjoint ⟨h0.mpr ⟨k,e⟩,h⟩)
      exact ⟨k,by simp [detector,hk],by simp [decoder,hk,hn]⟩
    · rintro ⟨k,_,hd⟩
      apply h1.mpr
      refine ⟨k,?_⟩
      cases e : seen (iter k (encode [a,b])) 0 <;>
        cases ee : seen (iter k (encode [a,b])) 1 <;> simp_all [decoder]
end UniformS.Output
