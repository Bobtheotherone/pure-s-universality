import PureS.Certified

namespace UniformS.Archive
open PureSFormal
open UniformS

/-- Exactly the finite physical consumption ending with an empty queue. -/
inductive Complete (p : CTS.Program) : CTS.Config p → Word → Prop
  | empty (q) : Complete p ⟨q,[]⟩ []
  | consume (q b tail rest) :
      Complete p (CTS.absorbingStep p ⟨q,b::tail⟩) rest →
      Complete p ⟨q,b::tail⟩ (b::rest)

theorem complete_prefix {p c hist} (h : Complete p c hist) :
    ∃ extra, hist = c.data ++ extra := by
  induction h with
  | empty q => exact ⟨[],rfl⟩
  | consume q b tail rest _ ih =>
    obtain ⟨extra,hx⟩ := ih
    cases b
    · exact ⟨extra, congrArg (List.cons false) hx⟩
    · exact ⟨p.appendant q ++ extra, by simpa [List.append_assoc] using congrArg (List.cons true) hx⟩

/-- Physical suffixes supply every data bit. The scanner keeps a phase and a
    window length and never constructs or appends a production word. -/
def windows (p : CTS.Program) (n : Nat) (q : CTS.Phase p) (width : Nat) :
    Word → List (Nat × CTS.Config p)
  | [] => [(n,⟨q,[]⟩)]
  | b::rest => (n,⟨q,(b::rest).take width⟩) ::
      windows p (n+1) (CTS.nextPhase p q)
        (width-1 + if b then (p.appendant q).length else 0) rest

/-- Specification used only in the proof of the scanner. -/
def observations (p : CTS.Program) (n : Nat) (c : CTS.Config p) :
    Nat → List (Nat × CTS.Config p)
  | 0 => [(n,c)]
  | k+1 => (n,c)::observations p (n+1) (CTS.absorbingStep p c) k

theorem windows_exact {p c hist} (h : Complete p c hist) (n) :
    windows p n c.phase c.data.length hist = observations p n c hist.length := by
  induction h generalizing n with
  | empty q => rfl
  | consume q b tail rest hc ih =>
    obtain ⟨extra,hx⟩ := complete_prefix (Complete.consume q b tail rest hc)
    have first : (b::rest).take (b::tail).length = b::tail := by
      rw [hx]; simp
    have ft : rest.take tail.length = tail := (List.cons.inj first).2
    cases b <;> simp [windows,observations,ft] <;>
      simpa [CTS.advance,List.length_append] using ih (n+1)

theorem iterate_shift (p : CTS.Program) (i) (c) :
    CTS.iterate p (i+1) c = CTS.iterate p i (CTS.absorbingStep p c) := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (CTS.absorbingStep p) ih

theorem observations_mem (p n c k) (a : Nat × CTS.Config p) :
    a ∈ observations p n c k ↔
      ∃ j, j ≤ k ∧ a = (n+j,CTS.iterate p j c) := by
  induction k generalizing n c with
  | zero => simp [observations]
  | succ k ih =>
    rw [observations,List.mem_cons,ih]
    constructor
    · rintro (rfl|⟨j,hj,rfl⟩)
      · exact ⟨0,by omega,by simp⟩
      · exact ⟨j+1,by omega,by rw [iterate_shift]; congr 1 <;> omega⟩
    · rintro ⟨(_|j),hj,rfl⟩
      · left; simp
      · right; exact ⟨j,by omega,by rw [iterate_shift]; congr 1 <;> omega⟩

theorem empty_at_end {p c hist} (h : Complete p c hist) :
    (CTS.iterate p hist.length c).data = [] := by
  induction h with
  | empty q => rfl
  | consume q b tail rest hc ih =>
    simpa only [List.length_cons,iterate_shift] using ih

theorem empty_after {p c hist} (h : Complete p c hist) (j : Nat) (hj : hist.length ≤ j) :
    (CTS.iterate p j c).data = [] := by
  have hz := empty_at_end h
  have eqn : j = (j-hist.length) + hist.length := by omega
  rw [eqn,CTS.iterate_add]
  cases e : CTS.iterate p hist.length c with
  | mk q data =>
    rw [e] at hz
    change data = [] at hz
    subst data
    exact CTS.iterate_empty_data _ _ _

def fromBoard (p : Program) : Nat → Board → Board
  | 0,s => s
  | n+1,s => fromBoard p n (Bridge.tick p s)

theorem board_shift (p n s) :
    Bridge.sample p (n+1) s = Bridge.sample p n (Bridge.tick p s) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (Bridge.tick p) ih

theorem from_sample (p n s) : fromBoard p n s = Bridge.sample p n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [fromBoard,ih,board_shift]

theorem from_empty (p n s) (h : s.queue = []) : fromBoard p n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [fromBoard,Bridge.tick,(macro_none p s).mpr h] using ih

theorem native_consumption (p : CTS.Program) (n : Nat) (s : Board) (c : CTS.Config p)
    (hs : Bridge.Matches s c) (before : Word)
    (marks : s.marks = marked true before ++ marked false s.queue)
    (he : (fromBoard (Bridge.compile p) n s).queue = []) :
    ∃ hist, Complete p c hist ∧
      (fromBoard (Bridge.compile p) n s).marks = marked true (before ++ hist) := by
  induction n generalizing s c before with
  | zero =>
    change s.queue = [] at he
    obtain ⟨q,d⟩ := c
    have hd : d = [] := hs.1.symm.trans he
    subst d
    exact ⟨[],.empty q,by simpa [fromBoard,he,marked] using marks⟩
  | succ n ih =>
    obtain ⟨q,d⟩ := c
    cases d with
    | nil =>
      have hq : s.queue = [] := hs.1
      exact ⟨[],.empty q,by rw [from_empty _ _ _ hq]; simpa [hq,marked] using marks⟩
    | cons b tail =>
      let prog := Bridge.compile p
      have hq : s.queue = b::tail := hs.1
      cases ha : advance prog s with
      | none => have := (macro_none prog s).mp ha; simp [hq] at this
      | some pair =>
        obtain ⟨k,t⟩ := pair
        have ht : Bridge.tick prog s = t := by simp [Bridge.tick,ha]
        have hs' := Bridge.tick_agrees p s ⟨q,b::tail⟩ hs
        change Bridge.Matches (Bridge.tick prog s) _ at hs'
        rw [ht] at hs'
        obtain ⟨v,hv,hm⟩ := physical_history_step prog ha before tail b (by simpa [hq] using marks)
        have tl : t.queue = tail ++ payload b v := by
          have hd := (macro_exact prog ha).2.2.2
          change source prog (observe s) = some (observe t) at hd
          change (if s.pending.isEmpty then prog.period else s.pending) = v::t.pending at hv
          change (match s.queue with
            | [] => none
            | b::z => match phaseList prog s with
              | [] => none
              | v::vs => some (Config.mk (z++payload b v) vs)) = some (observe t) at hd
          change phaseList prog s = v :: t.pending at hv
          simp [hq,hv,observe] at hd
          exact hd.symm
        rw [← tl] at hm
        change (fromBoard prog n (Bridge.tick prog s)).queue = [] at he
        rw [ht] at he
        obtain ⟨hist,hh,hhm⟩ := ih t _ hs' (before++[b]) hm he
        refine ⟨b::hist,.consume _ _ _ _ hh,?_⟩
        change (fromBoard prog n (Bridge.tick prog s)).marks = _
        rw [ht]
        simpa [List.append_assoc] using hhm

def bits (t : Term) : Word := (Readback.bare t).1.map Prod.snd

theorem completed_ground (p : CTS.Program) (w : Word) (n : Nat) :
    let t := Certified.orbit n ((seed w).tree (Bridge.compile p))
    Certified.halt t = true → Complete p (CTS.initial p w) (bits t) := by
  dsimp only
  rw [Certified.orbit_literal]
  let s := Bridge.sample (Bridge.compile p) n (seed w)
  have valid : Readback.Valid (Bridge.compile p) s := Readback.valid_sample (Bridge.compile p) w n
  change Certified.halt (s.tree _) = true → _
  intro h
  have he : s.queue = [] := by
    simp only [Certified.halt,Certified.head_correct _ _ valid] at h
    cases e : s.queue with
    | nil => rfl
    | cons b z => simp [e] at h
  have hx := native_consumption p n (seed w) (CTS.initial p w)
    (Bridge.sample_agrees p w 0) [] (by simp [seed_marks,marked]) (by simpa [from_sample] using he)
  obtain ⟨hist,histOK,hm⟩ := hx
  rw [from_sample] at hm
  change s.marks = _ at hm
  change Complete p (CTS.initial p w) (bits (s.tree _))
  unfold bits
  rw [Readback.bare_marks _ s valid,hm]
  simpa [marked,List.map_map,Function.comp_def] using histOK

end UniformS.Archive
