import PureS.FifoArchive
import PureS.Micro
import PureS.FiniteOutput
import PureS.Encoding
import PureSFormal.Computation.CookSeedPassSourceReflection
import PureSFormal.Computation.DeterministicTapeCode

set_option maxHeartbeats 3000000

namespace UniformS.Numerical
open UniformS PureSFormal PureSFormal.Computation
open PureSFormal.Research.ProtectedTrieDeterministicCompiler

abbrev P := Cook.rogozhinCookProgram
abbrev Source := DeterministicTape.Instance
abbrev Row := DeterministicTape.Row

/-- Natural output is the length of the unary block at the terminal tape head. -/
def numeral (r : Row) := ((r.tape.drop r.head).takeWhile id).length
def source (e x : Nat) : Source :=
  ⟨DeterministicTapeCode.machineDecode e,0,List.replicate x true⟩
def Terminal (s : Source) (r : Row) : Prop :=
  (∃ j, DeterministicTape.runFor? s.machine (DeterministicTape.initialRow s) j = some r) ∧
  DeterministicTape.step? s.machine r = none
def Returns (s : Source) (y : Nat) : Prop := ∃ r, Terminal s r ∧ numeral r = y
def U (e x y : Nat) : Prop := Returns (source e x) y

theorem run_unique (m : DeterministicTape.Machine) (j k : Nat) (r u v : Row)
    (a : DeterministicTape.runFor? m r j = some u) (b : DeterministicTape.runFor? m r k = some v)
    (hu : DeterministicTape.step? m u = none) (hv : DeterministicTape.step? m v = none) : u = v := by
  induction j generalizing k r with
  | zero =>
    change some r = some u at a
    obtain rfl := Option.some.inj a
    cases k with
    | zero => exact Option.some.inj b
    | succ k => simp [DeterministicTape.runFor?,hu] at b
  | succ j ih =>
    cases k with
    | zero =>
      change some r = some v at b
      obtain rfl := Option.some.inj b
      simp [DeterministicTape.runFor?,hv] at a
    | succ k =>
      cases hn : DeterministicTape.step? m r with
      | none => simp [DeterministicTape.runFor?,hn] at a
      | some t =>
        simp [DeterministicTape.runFor?,hn] at a b
        exact ih k t a b

theorem result_unique (s : Source) (a b) (ha : Returns s a) (hb : Returns s b) : a = b := by
  obtain ⟨r,⟨⟨i,hi⟩,hr⟩,rfl⟩ := ha
  obtain ⟨v,⟨⟨j,hj⟩,hv⟩,rfl⟩ := hb
  exact congrArg numeral (run_unique _ _ _ _ _ _ hi hj hr hv)

def programWord (s : Source) : Word := DeterministicTapeCook.encodeBits (DeterministicTapeStatePadding.pad s)
def key (t : Term) : Word := (Readback.word t).map Prod.snd
theorem key_emit (w : Word) : key (emit w) = w := by
  simp [key,Readback.word_emit,marked,List.map_map,Function.comp_def]

def initial (s : Source) : Term :=
  pair (emit (programWord s)) ((seed (programWord s)).tree Bridge.fixed)
def E (e x : Nat) := initial (source e x)
def sigma : Term → Term
  | .app (.app .s w) t => pair w (Certified.nextTerm t)
  | t => t
def iter : Nat → Term → Term
  | 0,t => t
  | n+1,t => sigma (iter n t)
def H : Term → Bool
  | .app (.app .s _) t => Certified.halt t
  | _ => false

/-- The parser uses the supplied physical slice, the fixed static key and the
    distinction between the initial and a later arrival. It executes no tape step. -/
def readWindow (w : Word) (a : Nat × CTS.Config P) : Option Nat :=
  (CookSeedPassReadback.decodeTerminalTape? w a.1 a.2).map numeral
def outputs (w physical : Word) : List Nat :=
  (Archive.windows P 0 (CTS.zeroPhase P) w.length physical).filterMap (readWindow w)
def D : Term → Option Nat
  | .app (.app .s w) t =>
    if Certified.halt t then (outputs (key w) (Archive.bits t)).head? else none
  | _ => none

theorem iter_context (w t n) : iter n (pair w t) = pair w (Certified.orbit n t) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter,ih]; rfl

theorem sigma_native (t : Term) : ∃ k, k ≤ 4 ∧ Steps k t (sigma t) := by
  cases t with
  | s => exact ⟨0,by decide,.refl _⟩
  | app l r =>
    cases l with
    | s => exact ⟨0,by decide,.refl _⟩
    | app h w =>
      cases h with
      | app => exact ⟨0,by decide,.refl _⟩
      | s =>
        obtain ⟨k,hk,hn⟩ := Output.next_native r
        exact ⟨k,hk,hn.right _⟩

theorem empty_reader (w : Word) (j : Nat) (q : CTS.Phase P) :
    CookSeedPassReadback.decodeTerminalTape? w j ⟨q,[]⟩ = none := by
  have hp : Cook.passDecode? j ⟨q,[]⟩ = none := by
    unfold Cook.passDecode?
    split
    · have hd : Cook.decodeWord? [] = some [] := by
        simpa using Cook.decodeWord?_encodeWord ([] : List Cook.TagSymbol)
      change (do
        let xs ← Cook.decodeWord? []
        if j = 0 then Cook.decodeCanonical? xs else
          match Cook.decodeArrival? xs with
          | none => none
          | some a => some a.config) = none
      rw [hd]
      cases j with
      | zero => exact (by decide : Cook.decodeCanonical? [] = none)
      | succ k =>
        have hn : Cook.decodeArrival? [] = none := by decide
        change (match Cook.decodeArrival? [] with
          | none => none | some a => some a.config) = none
        rw [hn]
    · rfl
  unfold CookSeedPassReadback.decodeTerminalTape? CookSeedPassReadback.decodeTape?
    CookSeedPassReadback.decodePassCounter? CookSeedPassReadback.decodePassTag?
  cases h : CookSeedReadbackContext.decodeContext? w <;> simp [hp]

theorem physical_outputs (s : Source) (hist : Word)
    (hc : Archive.Complete P (CTS.initial P (programWord s)) hist) (y : Nat) :
    y ∈ outputs (programWord s) hist ↔ Returns s y := by
  let w := programWord s
  let c := CTS.initial P w
  have hw := Archive.windows_exact hc 0
  change Archive.windows P 0 (CTS.zeroPhase P) w.length hist = _ at hw
  change y ∈ (Archive.windows P 0 (CTS.zeroPhase P) w.length hist).filterMap (readWindow w) ↔ _
  rw [hw,List.mem_filterMap]
  constructor
  · rintro ⟨a,ha,found⟩
    obtain ⟨j,_,rfl⟩ := (Archive.observations_mem P 0 c hist.length a).mp ha
    rw [Nat.zero_add] at found
    change (CookSeedPassReadback.decodeTerminalTape? w j (CTS.iterate P j c)).map numeral = some y at found
    cases hd : CookSeedPassReadback.decodeTerminalTape? w j (CTS.iterate P j c) with
    | none => simp [hd] at found
    | some row =>
      simp [hd] at found
      exact ⟨row,CookSeedPassSourceReflection.decodeTerminalTape?_actual_reflects s j row hd,found⟩
  · rintro ⟨row,hr,rfl⟩
    obtain ⟨j,hj⟩ := (CookSeedPassSourceReflection.exists_terminalRow_iff s row).mpr hr
    change CookSeedPassReadback.decodeTerminalTape? w j (CTS.iterate P j c) = some row at hj
    have hjle : j ≤ hist.length := by
      apply Nat.le_of_not_gt
      intro h
      have emp := Archive.empty_after hc j (by omega)
      change (CTS.iterate P j c).data = [] at emp
      cases ec : CTS.iterate P j c with
      | mk q data =>
        rw [ec] at emp hj
        change data = [] at emp
        subst data
        cases (empty_reader w j q).symm.trans hj
    refine ⟨(j,CTS.iterate P j c),(Archive.observations_mem P 0 c hist.length _).mpr
      ⟨j,hjle,by simp⟩,?_⟩
    exact congrArg (Option.map numeral) hj

theorem decode_completed (s : Source) (n : Nat)
    (hit : H (iter n (initial s)) = true) (y : Nat) :
    D (iter n (initial s)) = some y ↔ Returns s y := by
  let w := programWord s
  let t := Certified.orbit n ((seed w).tree Bridge.fixed)
  have he : Certified.halt t = true := by simpa only [initial,iter_context,H,pair] using hit
  have complete : Archive.Complete P (CTS.initial P w) (Archive.bits t) := Archive.completed_ground P w n he
  have spec := physical_outputs s (Archive.bits t) complete
  change D (iter n (pair (emit w) ((seed w).tree Bridge.fixed))) = some y ↔ _
  rw [iter_context]
  change (if Certified.halt t then (outputs (key (emit w)) (Archive.bits t)).head? else none) = some y ↔ _
  rw [he,key_emit]; simp only [if_true]
  cases eqn : outputs w (Archive.bits t) with
  | nil =>
    constructor
    · simp
    · intro ret
      have bad := (spec y).mpr ret
      change y ∈ outputs w _ at bad
      simp [eqn] at bad
  | cons z zs =>
    have hz : Returns s z := (spec z).mp (by change z ∈ outputs w _; simp [eqn])
    constructor
    · intro hy
      exact (Option.some.inj hy) ▸ hz
    · intro hy
      exact congrArg some (result_unique s z y hz hy)

theorem regular_domain (s : Source) :
    DeterministicTape.Halts s ↔ ∃ n, H (iter n (initial s)) = true := by
  rw [← DeterministicTapeStatePadding.halts_pad_iff s,Certified.universal_selected_halting]
  simp only [initial,iter_context,H,pair]
  rfl

theorem tape_natural_io (s : Source) (y : Nat) :
    Returns s y ↔ ∃ n, H (iter n (initial s)) = true ∧ D (iter n (initial s)) = some y := by
  constructor
  · intro hy
    have hreturn := hy
    obtain ⟨row,⟨⟨j,hj⟩,hr⟩,_⟩ := hreturn
    obtain ⟨n,hn⟩ := (regular_domain s).mp ⟨j,row,hj,hr⟩
    exact ⟨n,hn,(decode_completed _ _ hn _).mpr hy⟩
  · rintro ⟨n,hn,hd⟩
    exact (decode_completed _ _ hn _).mp hd

/-- Numerical universality for an independent effective numbering of ordinary
    binary Turing machines with unary numeral input and output. -/
theorem universal_natural_io (e x y : Nat) :
    U e x y ↔ ∃ k : Nat, H (iter k (E e x)) = true ∧ D (iter k (E e x)) = some y :=
  tape_natural_io (source e x) y

theorem all_machine_tables (m : DeterministicTape.Machine) :
    ∃ e : Nat, ∀ x y : Nat, Returns ⟨m,0,List.replicate x true⟩ y ↔
      ∃ k : Nat, H (iter k (E e x)) = true ∧ D (iter k (E e x)) = some y := by
  refine ⟨DeterministicTapeCode.machineCode m,fun x y => ?_⟩
  rw [← universal_natural_io]
  simp [U,source]

theorem unique_output (e x k l a b : Nat)
    (hk : H (iter k (E e x)) = true) (ha : D (iter k (E e x)) = some a)
    (hl : H (iter l (E e x)) = true) (hb : D (iter l (E e x)) = some b) : a = b :=
  result_unique _ _ _ ((universal_natural_io ..).mpr ⟨k,hk,ha⟩)
    ((universal_natural_io ..).mpr ⟨l,hl,hb⟩)

theorem size_exact (s : Source) :
    leaves (initial s) = 24 + 48*Bridge.fixed.period.length +
      4*periodWeight Bridge.fixed.period + 2*wordWeight (programWord s) := by
  change (1 + leaves (emit (programWord s))) + leaves ((seed (programWord s)).tree Bridge.fixed) = _
  rw [word_size,exact_encoder_leaves]
  omega

theorem active_block (w t u : Term) (k : Nat) (h : Certified.action t = some (k,u)) :
    2 ≤ k ∧ k ≤ 4 ∧ Steps k (pair w t) (pair w u) ∧
      Micro.iterate k (.boundary,t) = (.boundary,u) := by
  obtain ⟨lo,hi,steps⟩ := Certified.all_terms_native _ _ _ h
  exact ⟨lo,hi,steps.right _,Micro.micro_realizes _ _ _ h⟩

theorem halt_stable (w t : Term) (h : Certified.halt t = true) :
    sigma (pair w t) = pair w t := by
  cases he : (Certified.fold t).root with
  | none => simp [sigma,pair,Certified.nextTerm,Certified.action,he]
  | some b => simp [Certified.halt,he] at h

end UniformS.Numerical
