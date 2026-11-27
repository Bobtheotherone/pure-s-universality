import PureS.Certified
namespace UniformS.Micro
open UniformS BareMacro Certified
inductive Mode where | boundary | first (b : Bool) | second (b : Bool) | third (b : Bool) | done
  deriving Repr,DecidableEq
abbrev Machine := Mode × Term

def choose (b : Bool) (after : Mode) (t : Term) : Option Machine :=
  match fire b t with
  | some z => some (.boundary,z)
  | none => (alloc t).map (fun v => (after,v))
def propose : Machine → Option Machine
  | (.boundary,t) => do
    let b ← (fold t).root
    let u ← pop t
    return (.first b,u)
  | (.first b,t) => choose b (.second b) t
  | (.second b,t) => choose b (.third b) t
  | (.third b,t) => (fire b t).map (fun u => (.boundary,u))
  | (.done,_) => none

def one (s : Machine) : Option Machine :=
  match propose s with
  | some v => some v
  | none => match inspect s.2 with
    | .hit _ u _ => some (.done,u)
    | .normal _ => none

theorem choose_native (b after t m u) (h : choose b after t = some (m,u)) : Native t u := by
  cases hf : fire b t with
  | some v => simp [choose,hf] at h; obtain ⟨rfl,rfl⟩ := h; exact fire_legal _ _ _ hf
  | none =>
    cases ha : alloc t with
    | none => simp [choose,hf,ha] at h
    | some v => simp [choose,hf,ha] at h; obtain ⟨rfl,rfl⟩ := h; exact alloc_legal _ _ ha
theorem propose_native (s v : Machine) (h : propose s = some v) : Native s.2 v.2 := by
  obtain ⟨m,t⟩ := s; obtain ⟨mode,u⟩ := v
  cases m with
  | boundary =>
    cases hb : (fold t).root with
    | none => simp [propose,hb] at h
    | some b =>
      cases hp : pop t with
      | none => simp [propose,hb,hp] at h
      | some z => simp [propose,hb,hp] at h; obtain ⟨rfl,rfl⟩ := h; exact pop_legal _ _ hp
  | first b => exact choose_native _ _ _ _ _ h
  | second b => exact choose_native _ _ _ _ _ h
  | third b =>
    cases hf : fire b t with
    | none => simp [propose,hf] at h
    | some z => simp [propose,hf] at h; obtain ⟨rfl,rfl⟩ := h; exact fire_legal _ _ _ hf
  | done => contradiction
theorem step_native (s v) (h : one s = some v) : Native s.2 v.2 := by
  unfold one at h
  cases hp : propose s with
  | some u => simp [hp] at h; subst v; exact propose_native _ _ hp
  | none =>
    simp only [hp] at h
    cases hi : inspect s.2 with
    | normal _ => simp [hi] at h
    | hit p u hr => simp [hi] at h; subst v; exact address_sound _ hr

theorem normal_exact (s) : one s = none ↔ ∀ p, reduceAt p s.2 = none := by
  constructor
  · intro hz
    unfold one at hz
    cases e : propose s with
    | some v => simp [e] at hz
    | none =>
      simp only [e] at hz
      cases hi : inspect s.2 with
      | normal h => exact h
      | hit p v h => simp [hi] at hz
  · intro hn
    cases e : one s with
    | none => rfl
    | some v =>
      obtain ⟨p,hp⟩ := native_hasAddress (step_native _ _ e)
      simp [hn] at hp

def iterate : Nat → Machine → Machine
  | 0,s => s
  | n+1,s => iterate n ((one s).getD s)
theorem micro_block (t u k) (h : action t = some (k,u)) :
    iterate k (.boundary,t) = (.boundary,u) ∧
    ∀ j, 0 < j → j < k → (iterate j (.boundary,t)).1 ≠ .boundary := by
  cases hb : (fold t).root with
  | none => simp [action,hb] at h
  | some b =>
    cases hp : pop t with
    | none => simp [action,hb,hp] at h
    | some r =>
      cases hf : fire b r with
      | some z =>
        simp [action,hb,hp,finish,hf] at h; obtain ⟨rfl,rfl⟩ := h
        constructor
        · simp [iterate,one,propose,choose,hb,hp,hf]
        · intro j hj hk
          have hcases : j = 1 := by omega
          rcases hcases with rfl <;> simp [iterate,one,propose,choose,hb,hp,hf]
      | none =>
        cases ha : alloc r with
        | none => simp [action,hb,hp,finish,hf,ha] at h
        | some a =>
          cases hf' : fire b a with
          | some z =>
            simp [action,hb,hp,finish,hf,ha,hf'] at h; obtain ⟨rfl,rfl⟩ := h
            constructor
            · simp [iterate,one,propose,choose,hb,hp,hf,ha,hf']
            · intro j hj hk
              have hcases : j = 1 ∨ j = 2 := by omega
              rcases hcases with rfl | rfl <;> simp [iterate,one,propose,choose,hb,hp,hf,ha,hf']
          | none =>
            cases ha' : alloc a with
            | none => simp [action,hb,hp,finish,hf,ha,hf',ha'] at h
            | some a' =>
              cases hf'' : fire b a' with
              | none => simp [action,hb,hp,finish,hf,ha,hf',ha',hf''] at h
              | some z =>
                simp [action,hb,hp,finish,hf,ha,hf',ha',hf''] at h; obtain ⟨rfl,rfl⟩ := h
                constructor
                · simp [iterate,one,propose,choose,hb,hp,hf,ha,hf',ha',hf'']
                · intro j hj hk
                  have hcases : j = 1 ∨ j = 2 ∨ j = 3 := by omega
                  rcases hcases with rfl | rfl | rfl <;> simp [iterate,one,propose,choose,hb,hp,hf,ha,hf',ha',hf'']
theorem micro_realizes (t u k) (h : action t = some (k,u)) :
    iterate k (.boundary,t) = (.boundary,u) := (micro_block t u k h).1

def accepting (s : Machine) : Bool := decide (s.1 = Mode.boundary) && halt s.2

theorem iterate_add (a b : Nat) (s : Machine) :
    iterate (a+b) s = iterate b (iterate a s) := by
  induction a generalizing s with
  | zero => simp [iterate]
  | succ a ih => rw [Nat.succ_add]; exact ih _

theorem orbit_start (n : Nat) (t : Term) : orbit (n+1) t = orbit n (nextTerm t) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg nextTerm ih

theorem macro_to_micro (n : Nat) (t : Term) (h : halt (orbit n t) = true) :
    ∃ k, accepting (iterate k (.boundary,t)) = true := by
  induction n generalizing t with
  | zero => exact ⟨0,by simpa [iterate,accepting,orbit] using h⟩
  | succ n ih =>
    rw [orbit_start] at h
    cases ha : action t with
    | none =>
      simp [nextTerm,ha] at h
      exact ih t h
    | some pair =>
      obtain ⟨j,u⟩ := pair
      simp [nextTerm,ha] at h
      obtain ⟨k,hk⟩ := ih u h
      exact ⟨j+k,by rw [iterate_add,micro_realizes _ _ _ ha]; exact hk⟩

def Productive (t : Term) : Prop := ∀ n, halt (orbit n t) = false →
    ∃ j u, action (orbit n t) = some (j,u)

theorem micro_to_macro (k : Nat) (t : Term) (hg : Productive t)
    (h : accepting (iterate k (.boundary,t)) = true) :
    ∃ n, halt (orbit n t) = true := by
  induction k using Nat.strongRecOn generalizing t with
  | ind k ih =>
    cases he : halt t with
    | true => exact ⟨0,he⟩
    | false =>
      obtain ⟨l,u,hl⟩ := hg 0 he
      change action t = some (l,u) at hl
      have hlo := (all_terms_native _ _ _ hl).1
      have hu : nextTerm t = u := by simp [nextTerm,hl]
      by_cases hshort : k < l
      · cases k with
        | zero => simp [iterate,accepting,he] at h
        | succ j =>
          have hn := (micro_block _ _ _ hl).2 (j+1) (by omega) hshort
          simp [accepting,hn] at h
      · have decomp : k = l + (k-l) := by omega
        have h' : accepting (iterate (k-l) (.boundary,u)) = true := by
          calc
            _ = accepting (iterate (l+(k-l)) (.boundary,t)) := by
              rw [iterate_add,micro_realizes _ _ _ hl]
            _ = true := by rwa [← decomp]
        have hg' : Productive u := by
          intro n
          rw [← hu,← orbit_start]
          exact hg (n+1)
        obtain ⟨n,hn⟩ := ih (k-l) (by omega) u hg' h'
        exact ⟨n+1,by rw [orbit_start,hu]; exact hn⟩

theorem seed_productive (p : Program) (w : Word) : Productive ((seed w).tree p) := by
  intro n
  rw [orbit_literal]
  let s := Bridge.sample p n (seed w)
  have hs : Readback.Valid p s := Readback.valid_sample p w n
  change halt (s.tree p) = false → ∃ j u, action (s.tree p) = some (j,u)
  intro h
  rw [action_valid _ _ hs]
  cases ha : advance p s with
  | some pair => obtain ⟨j,v⟩ := pair; exact ⟨j,v.tree p,rfl⟩
  | none =>
    have hq := (macro_none _ _).mp ha
    simp [halt,head_correct _ _ hs,hq] at h

open PureSFormal.Research.ProtectedTrieDeterministicCompiler in
/-- The guard is read after every single native action. There are no false
    successes at an intermediate stage of a simulated source transition. -/
theorem universal_single_contractions (m : DeterministicTape.Instance) :
    DeterministicTape.Halts m ↔ ∃ k, accepting
      (iterate k (.boundary,(Bridge.input m).tree Bridge.fixed)) = true := by
  rw [universal_selected_halting]
  constructor
  · rintro ⟨n,h⟩; exact macro_to_micro _ _ h
  · rintro ⟨k,h⟩; exact micro_to_macro _ _ (seed_productive _ _) h

end UniformS.Micro
