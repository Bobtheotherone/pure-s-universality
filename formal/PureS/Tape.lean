import PureS.Simulation
import PureSFormal.Computation.DeterministicTapeCook

namespace UniformS.Bridge
open PureSFormal
open PureSFormal.Computation
open PureSFormal.Research.ProtectedTrieDeterministicCompiler

def table (p : CTS.Program) := List.ofFn p.appendant
def compile (p : CTS.Program) : Program := ⟨p.appendant (CTS.zeroPhase p), (table p).drop 1⟩
@[simp] theorem table_len (p) : (table p).length = p.period := by simp [table]
theorem table_split (p : CTS.Program) (i : CTS.Phase p) :
    (table p).drop i.val = p.appendant i :: (table p).drop (i.val+1) := by
  have h : i.val < (table p).length := by simpa using i.isLt
  rw [List.drop_eq_getElem_cons h]
  simp [table]
@[simp] theorem compile_period (p) : (compile p).period = table p := by
  simpa [Program.period,compile,CTS.zeroPhase] using (table_split p (CTS.zeroPhase p)).symm

def cursor (p : CTS.Program) (i : CTS.Phase p) := if i.val = 0 then [] else (table p).drop i.val
theorem cursor_active (p : CTS.Program) (i : CTS.Phase p) :
    (if (cursor p i).isEmpty then (compile p).period else cursor p i) = (table p).drop i.val := by
  by_cases h : i.val = 0
  · simp [cursor,h]
  · simp [cursor,h,table_split p i]
theorem cursor_next (p : CTS.Program) (i : CTS.Phase p) :
    cursor p (CTS.nextPhase p i) = (table p).drop (i.val+1) := by
  by_cases h : i.val+1 < p.period
  · simp [cursor,CTS.nextPhase,Nat.mod_eq_of_lt h]
  · have he : i.val+1 = p.period := by have := i.isLt; omega
    have hd : (table p).drop p.period = [] := List.drop_eq_nil_iff.mpr (by simp)
    simp [cursor,CTS.nextPhase,he,hd]

def snapshot (p : CTS.Program) (a : CTS.Config p) : Config := ⟨a.data,cursor p a.phase⟩
theorem source_agrees (p : CTS.Program) (i : CTS.Phase p) (b : Bool) (v : Word) :
    source (compile p) (snapshot p ⟨i,b::v⟩) =
      some (snapshot p (CTS.absorbingStep p ⟨i,b::v⟩)) := by
  have sel : (if cursor p i = [] then table p else cursor p i) = p.appendant i :: (table p).drop (i.val+1) := by
    simpa using (cursor_active p i).trans (table_split p i)
  cases b <;> simp [source,snapshot,CTS.absorbingStep,CTS.ordinaryStep,CTS.advance,cursor_next,payload,sel]

def tick (p : Program) (s : Board) :=
  match advance p s with | some (_,t) => t | none => s
def sample (p : Program) : Nat → Board → Board
  | 0,s => s
  | n+1,s => tick p (sample p n s)

def Matches {p : CTS.Program} (s : Board) (c : CTS.Config p) : Prop :=
  s.queue = c.data ∧ (c.data ≠ [] → s.pending = cursor p c.phase)

theorem tick_agrees (p : CTS.Program) (s : Board) (c : CTS.Config p)
    (h : Matches s c) : Matches (tick (compile p) s) (CTS.absorbingStep p c) := by
  obtain ⟨i,data⟩ := c
  obtain ⟨hq,hp⟩ := h
  cases data with
  | nil =>
    change s.queue = [] at hq
    have hnone := (macro_none (compile p) s).mpr hq
    simp [tick,hnone,Matches,CTS.absorbingStep,CTS.ordinaryStep,CTS.advance,hq]
  | cons b v =>
    have hp' := hp (by simp)
    change s.queue = b::v at hq
    have hs : observe s = snapshot p ⟨i,b::v⟩ := by
      simp [observe,snapshot,hq,hp']
    have eqn := source_agrees p i b v
    rw [← hs] at eqn
    obtain ⟨k,t,ht,he⟩ := lift_step (compile p) s eqn
    simp only [tick,ht]
    exact ⟨congrArg Config.queue he,fun _ => congrArg Config.remaining he⟩

theorem sample_agrees (p : CTS.Program) (w : Word) (n) :
    Matches (sample (compile p) n (seed w)) (CTS.iterate p n (CTS.initial p w)) := by
  induction n with
  | zero => exact ⟨seed_queue _,fun _ => rfl⟩
  | succ n ih => exact tick_agrees _ _ _ ih

theorem sample_native (p : Program) (s : Board) (n) :
    ∃ k, k ≤ 4*n ∧ Steps k (s.tree p) ((sample p n s).tree p) := by
  induction n with
  | zero => exact ⟨0,by omega,.refl _⟩
  | succ n ih =>
    obtain ⟨k,hk,hn⟩ := ih
    cases e : advance p (sample p n s) with
    | none => exact ⟨k,by omega,by simpa [sample,tick,e] using hn⟩
    | some z =>
      obtain ⟨j,t⟩ := z
      have ht := macro_exact p e
      exact ⟨k+j,by have := ht.2.1; omega,by simpa [sample,tick,e] using hn.trans ht.2.2.1⟩

abbrev fixed := compile Cook.rogozhinCookProgram
def input (m : DeterministicTape.Instance) := seed (DeterministicTapeCook.encodeBits m)

/-- End-to-end halting and native reachability on the new annotated sample
    function. Projection to the independently implemented bare walker is a
    distinct proof obligation. Only the source-to-CTS compiler is imported. -/
theorem tape_halts_iff_native_samples (m : DeterministicTape.Instance) :
    DeterministicTape.Halts m ↔
      ∃ n k, k ≤ 4*n ∧ Steps k ((input m).tree fixed) ((sample fixed n (input m)).tree fixed) ∧
          (sample fixed n (input m)).queue = [] := by
  rw [DeterministicTapeCook.halts_iff_exists_fixedCookEmpty]
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨k,hk,hs⟩ := sample_native fixed (input m) n
    exact ⟨n,k,hk,hs,(sample_agrees _ _ n).1.trans hn⟩
  · rintro ⟨n,k,_,_,hn⟩
    exact ⟨n,(sample_agrees _ _ n).1.symm.trans hn⟩
end UniformS.Bridge
