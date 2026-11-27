import PureS.Native

namespace UniformS.Automaton

/-- All registers of this summary range over booleans or a three-element tag.
    The marked flags identify the first eligible token, not an address. -/
structure Report where
  pops : Bool := false
  commits : Bool := false
  last : Option Bool := none
  live : Bool := false
  used : Bool := false
  free : Bool := false
  markedLive : Bool := false
  markedZero : Bool := false
  markedOne : Bool := false
  markedEnd : Bool := false
  deriving DecidableEq,Repr,Inhabited

def combine (a b : Report) : Option Report :=
  if (a.live && b.last.isSome) || (a.free && b.used) then none else
  some { pops := a.pops != b.pops, commits := a.commits != b.commits,
         last := b.last.orElse (fun _ => a.last), live := a.live || b.live,
         used := a.used || b.used, free := a.free || b.free,
         markedLive := if a.live then a.markedLive else b.markedLive,
         markedZero := if a.free then a.markedZero else b.markedZero,
         markedOne := if a.free then a.markedOne else b.markedOne,
         markedEnd := a.markedEnd || b.markedEnd }

def joinR (a b : Option Report) := do combine (← a) (← b)
def liveToken (m : Bool) : Report := {live := true, markedLive := m}
def spentToken (b : Bool) : Report := {pops := true,last := some b}
def firedToken : Report := {commits := true,used := true}

inductive Arm where
  | fresh (marked : Bool)
  | fired (word : Option Report)
  deriving Inhabited,DecidableEq,Repr
def slotView : Option Arm → Option Arm → Option Report
  | some (.fresh z), some (.fresh o) => some {free := true,markedZero := z,markedOne := o}
  | some (.fired _), some (.fresh _) => some firedToken
  | some (.fresh _), some (.fired w) => joinR (some firedToken) w
  | _,_ => none

inductive Degree where | z | one | two | three | four | many
  deriving DecidableEq,Repr,Inhabited
def Degree.succ : Degree → Degree
  | .z => .one | .one => .two | .two => .three | .three => .four | _ => .many

structure State where
  degree : Degree := .z
  tag : Option Bool := none
  triple : Bool := false
  reader : Option Bool := none
  rightTag : Option Bool := none
  word : Option Report := none
  unaryWord : Option Report := none
  boxWord : Option Report := none
  unaryBoxWord : Option Report := none
  arm : Option Arm := none
  unaryArm : Option Arm := none
  slot : Option Report := none
  unarySlot : Option Report := none
  list : Option Report := none
  block : Option Report := none
  frameHead : Option Report := none
  rail : Option Report := none
  root : Option Report := none
  deriving DecidableEq,Repr,Inhabited

def leaf : State := {tag := some false, word := some {}, list := some {}}
def node (m : Bool) (l r : State) : State :=
  let sl := l.degree == .z
  let ss := l.tag == some true
  let d := l.degree.succ
  let word := if l.reader.isSome then joinR (some (liveToken m)) r.word else
    r.rightTag.bind (fun b => joinR (some (spentToken b)) l.unaryWord)
  let a := if l.triple then some (Arm.fresh m) else if l.degree == .one then
    some (Arm.fired l.unaryBoxWord) else none
  { degree := d, tag := if sl && r.degree == .z then some true else none,
    triple := ss && r.degree == .z, reader := if ss then r.tag else none, rightTag := l.tag,
    word := word, unaryWord := if sl then r.word else none,
    boxWord := if ss then r.word else none, unaryBoxWord := if sl then r.boxWord else none,
    arm := a, unaryArm := if sl then r.arm else none, slot := slotView l.unaryArm r.arm,
    unarySlot := if sl then r.slot else none, list := joinR l.unarySlot r.list,
    block := if ss && r.degree != .z then r.list else none, frameHead := l.block,
    rail := if d == .three then some {markedEnd := m} else if d == .four then
      joinR l.frameHead r.rail else none, root := joinR l.unaryBoxWord r.rail }

def run : Term → State
  | .s => leaf
  | .app a b => node false (run a) (run b)
def atMark : Address → Term → State
  | [],.app a b => node true (run a) (run b)
  | false::p,.app a b => node false (atMark p a) (run b)
  | true::p,.app a b => node false (run a) (atMark p b)
  | _,.s => leaf

def halt (t : Term) : Bool := match (run t).root with
  | some v => v.pops == v.commits && !v.live
  | none => false
def markedAccept (t : Term) (p : Address) : Bool :=
  match (atMark p t).root with
  | none => false
  | some v =>
    if v.pops == v.commits then (if v.live then v.markedLive else v.markedEnd)
    else if v.free then (match v.last with | none => false | some false => v.markedZero | some true => v.markedOne)
    else v.markedEnd

/-- The finite list is an executable way to evaluate the marked regular
    relation. The separate root walker avoids building this list. -/
def positions : Term → List Address
  | .s => [[]]
  | .app l r => [] :: ((positions l).map (false :: ·) ++ (positions r).map (true :: ·))

def nomination (t : Term) : Option Address := (positions t).find? (markedAccept t)

def certified (t : Term) : Inspection t :=
  match nomination t with
  | none => inspect t
  | some p => match h : reduceAt p t with
    | some u => .hit p u h
    | none => inspect t

def oneStep (t : Term) : Option Term :=
  match certified t with | .hit _ u _ => some u | .normal _ => none

theorem oneStep_native {t u} (h : oneStep t = some u) : Native t u := by
  unfold oneStep at h
  cases e : certified t with
  | hit p a ok => simp only [e,Option.some.injEq] at h; subst u; exact address_sound p ok
  | normal _ => simp [e] at h
theorem reports_normal (t) : oneStep t = none ↔ ∀ p, reduceAt p t = none := by
  unfold oneStep
  cases certified t with
  | hit p u ok =>
    constructor
    · intro h; contradiction
    · intro h; have hv := h p; rw [ok] at hv; contradiction
  | normal h => exact ⟨fun _ => h,fun _ => rfl⟩

end UniformS.Automaton
