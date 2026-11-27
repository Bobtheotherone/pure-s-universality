import PureS.Readback
namespace UniformS.BareMacro
open UniformS Readback

-- Each success reconstructs only the ancestors of the contracted occurrence.
def popW : Term → Option Term
  | t@(.app (.app (.app .s .s) _) _) => contract t
  | .app (.app .s w) g => (popW w).map (fun v => (S ⋆ v) ⋆ g)
  | _ => none
def popY : Term → Option Term
  | .app (.app .s a) (.app (.app .s (.app (.app .s .s) w)) g) =>
     (popW w).map (fun v => pair a ((S ⋆ box v) ⋆ g))
  | _ => none
def fireY (b : Bool) : Term → Option Term
  | .app (.app .s a) r =>
    if isOpen a || isOpen r then none
    else if b then (contract r).map (pair a) else (contract a).map (fun x => pair x r)
  | _ => none

def listAction (f : Term → Option Term) : Term → Option Term
  | .app (.app .s a) t =>
    match f a with
    | some v => some (pair v t)
    | none => (listAction f t).map (pair a)
  | _ => none

def railAction (f fin : Term → Option Term) : Term → Option Term
  | .app (.app (.app (.app .s .s) l) stamp) rest =>
    match listAction f l with
    | some v => some (frame v stamp rest)
    | none => (railAction f fin rest).map (frame l stamp)
  | t => fin t

def boardAction (hdr f fin : Term → Option Term) : Term → Option Term
  | .app (.app .s (.app (.app .s .s) w)) t =>
    match hdr w with
    | some v => some (pair (box v) t)
    | none => (railAction f fin t).map (pair (box w))
  | _ => none
def skip (_ : Term) : Option Term := none
def pop := boardAction popW popY skip
def fire (b : Bool) := boardAction skip (fireY b) skip
def alloc := boardAction skip skip contract

def liftPop {α} (m : Option (Bool × α)) (f : α → Term) (z : Option Term) : Option Term :=
  match m with | none => z | some (_,v) => some (f v)

theorem pop_segment (w : Segment) : popW w.term =
    match w.todo with
    | [] => none
    | b::v => some (Segment.read w.used b v).term := by
  rcases w with ⟨h,w⟩
  induction h with
  | nil => cases w with
    | nil => rfl
    | cons b v => cases b <;> rfl
  | cons x h ih =>
    obtain ⟨c,g⟩ := x
    change (popW (Segment.term ⟨h,w⟩)).map _ = _
    rw [ih]
    cases w <;> rfl

theorem row_single (r : Region) (ok : SlotOK r) (t : Term) :
    listAction popY (r.term ⋆ t) =
      liftPop r.pop (fun v => v.term ⋆ t) ((listAction popY t).map (fun v => r.term ⋆ v)) := by
  cases ok with
  | zero v => rfl
  | one w g =>
    rcases w with ⟨h,(_|⟨b,v⟩)⟩ <;>
      simp [rightR,Region.term,Region.pop,Region.live,freshBox,listAction,popY,pop_segment,liftPop,pair,box]

theorem closed_single (f : Term → Option Term) (r : Region) (ok : SlotOK r) (t : Term)
    (hf : (∃ b, f = fireY b) ∨ f = skip) :
    listAction f (r.term ⋆ t) = (listAction f t).map (fun v => r.term ⋆ v) := by
  rcases hf with ⟨b,rfl⟩ | rfl <;> cases ok <;> rfl

theorem row_pop (rs : Sleeve) (hs : SlotsOK rs) (t : Term) :
    listAction popY (plug rs t) = liftPop (popSleeve rs) (fun v => plug v t)
      ((listAction popY t).map (plug rs)) := by
  induction rs with
  | nil => simp [plug,popSleeve,liftPop]
  | cons r rs ih =>
    have hr := hs r (by simp)
    have hh : SlotsOK rs := fun u hu => hs u (by simp [hu])
    rw [plug,row_single r hr,ih hh]
    cases e : r.pop with
    | some x => cases x; simp [popSleeve,e,liftPop,plug]
    | none =>
      cases es : popSleeve rs with
      | some x => cases x; simp [popSleeve,e,es,liftPop,plug]
      | none => cases listAction popY t <;> simp [popSleeve,e,es,liftPop,plug]

theorem row_closed (f) (rs : Sleeve) (hs : SlotsOK rs) (t : Term)
    (hf : (∃ b, f = fireY b) ∨ f = skip) :
    listAction f (plug rs t) = (listAction f t).map (plug rs) := by
  induction rs with
  | nil => simp [plug]
  | cons r rs ih =>
    have hr := hs r (by simp)
    have hh : SlotsOK rs := fun u hu => hs u (by simp [hu])
    rw [plug,closed_single f r hr _ hf,ih hh]
    cases listAction f t <;> rfl

theorem fresh_pop (vs : List Word) : listAction popY (slots vs) = none := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [slots,slot,listAction,popY,pair,arm,ih]
theorem fresh_fire (b : Bool) (v : Word) (vs : List Word) :
    listAction (fireY b) (slots (v::vs)) = some (pair (released b v).term (slots vs)) := by
  cases b <;> rfl
theorem skip_list : (t : Term) → listAction skip t = none
  | .s => rfl
  | .app .s _ => rfl
  | .app (.app .s a) r => by
    change (listAction skip r).map (pair a) = none
    rw [skip_list r]; rfl
  | .app (.app (.app _ _) _) _ => rfl

theorem pack_moves (a : Sleeve) :
    (pack a (.raw S)).pop = (popSleeve a).map (fun (b,zs) => (b,pack zs (.raw S))) := by
  induction a with
  | nil => rfl
  | cons r rs ih =>
    simp only [pack,Region.pop,popSleeve]
    cases e : r.pop with
    | some x => cases x; rfl
    | none => rw [ih]; cases popSleeve rs with
      | none => rfl
      | some x => cases x; rfl

theorem done_pop (p) (r) (ok : FrameOK p r) (t : Term) :
    railAction popY skip (r.term ⋆ t) = liftPop r.pop (fun v => v.term ⋆ t)
      ((railAction popY skip t).map (fun v => r.term ⋆ v)) := by
  cases ok with
  | made a ha j =>
    simp only [finished,Region.term,pack_term,railAction,row_pop a ha,pack_moves,Region.pop]
    cases e : popSleeve a with
    | some x => cases x; simp [e,liftPop,frame,box,pair,Region.term,pack_term]
    | none => cases railAction popY skip t <;> simp [e,liftPop,listAction,frame,box,pair]

theorem done_closed (p) (r) (ok : FrameOK p r) (t : Term) (f fin)
    (hf : (∃ b, f = fireY b) ∨ f = skip) :
    railAction f fin (r.term ⋆ t) = (railAction f fin t).map (fun v => r.term ⋆ v) := by
  cases ok with
  | made a ha j =>
    simp only [finished,Region.term,pack_term,railAction,row_closed f a ha _ hf]
    cases railAction f fin t <;> rfl

theorem outer_rail_pop (p) (s : Sleeve) (ok : ∀ r ∈ s, FrameOK p r) (t : Term) :
    railAction popY skip (plug s t) = liftPop (popSleeve s) (fun ss => plug ss t)
      ((railAction popY skip t).map (plug s)) := by
  induction s with
  | nil => simp [plug,popSleeve,liftPop]
  | cons r s ih =>
    have hr := ok r (by simp)
    have hh : ∀ v ∈ s, FrameOK p v := fun u hu => ok u (by simp [hu])
    rw [plug,done_pop p r hr,ih hh]
    cases e : r.pop with
    | some x => cases x; simp [popSleeve,e,liftPop,plug]
    | none =>
      cases es : popSleeve s with
      | some x => cases x; simp [popSleeve,e,es,liftPop,plug]
      | none => cases railAction popY skip t <;> simp [popSleeve,e,es,liftPop,plug]

theorem outer_rail_closed (p) (s : Sleeve) (ok : ∀ r ∈ s, FrameOK p r) (t : Term)
    (f fin) (hf : (∃ b, f = fireY b) ∨ f = skip) :
    railAction f fin (plug s t) = (railAction f fin t).map (plug s) := by
  induction s with
  | nil => simp [plug]
  | cons r s ih =>
    have hh : ∀ v ∈ s, FrameOK p v := fun u hu => ok u (by simp [hu])
    rw [plug,done_closed p r (ok r (by simp)) _ _ _ hf,ih hh]
    cases railAction f fin t <;> rfl

theorem outer_pop_spec (p) (s : Sleeve) (ok : OuterOK p s) (t : Term) :
    pop (plug s t) = liftPop (popSleeve s) (fun ss => plug ss t)
      ((railAction popY skip t).map (plug s)) := by
  obtain ⟨w,rs,rfl,hr⟩ := ok
  change (match popW w.term with
    | some v => some (pair (box v) (plug rs t))
    | none => (railAction popY skip (plug rs t)).map (pair (box w.term))) = _
  rw [pop_segment,outer_rail_pop p rs hr]
  rcases w with ⟨h,(_|⟨b,xs⟩)⟩
  · cases es : popSleeve rs with
    | some x => cases x; simp [headR,freshBox,Region.pop,popSleeve,es,liftPop,plug,Region.term,box,pair]
    | none => cases railAction popY skip t <;> simp [headR,freshBox,Region.pop,popSleeve,es,liftPop,plug,Region.term,box,pair]
  · rfl

theorem outer_closed_spec (p) (s : Sleeve) (ok : OuterOK p s) (t : Term)
    (f fin) (hf : (∃ b, f = fireY b) ∨ f = skip) :
    boardAction skip f fin (plug s t) = (railAction f fin t).map (plug s) := by
  obtain ⟨w,rs,rfl,hr⟩ := ok
  change (railAction f fin (plug rs t)).map (pair (box w.term)) = _
  rw [outer_rail_closed p rs hr t f fin hf]
  cases railAction f fin t <;> rfl

theorem front_skip p r j f : railAction f skip (X (template p) r ⋆ X (template p) j) = none := by
  cases r <;> rfl
theorem front_red p r j f : railAction f contract (X (template p) r ⋆ X (template p) j) =
    contract (X (template p) r ⋆ X (template p) j) := by cases r <;> rfl

theorem pop_spec (p) (s : Board) (ok : Valid p s) : pop (s.tree p) = (s.pop.map (fun x => x.2.tree p)) := by
  cases s with
  | frontier u r j =>
    rw [Board.tree,outer_pop_spec p u ok,front_skip]
    cases e : popSleeve u with
    | none => simp [e,liftPop,Board.pop]
    | some x => cases x; simp [e,liftPop,Board.pop,Board.tree]
  | period u a v vs f r j =>
    obtain ⟨hu,ha⟩ := ok
    rw [Board.tree,outer_pop_spec p u hu]
    simp only [frame,box,pair,railAction,row_pop a ha,fresh_pop,front_skip]
    cases eu : popSleeve u with
    | some x => cases x; simp [eu,liftPop,Board.pop,Board.tree,frame,box,pair]
    | none =>
      cases ea : popSleeve a with
      | some x => cases x; simp [eu,ea,liftPop,Board.pop,Board.tree,frame,box,pair]
      | none => simp [eu,ea,liftPop,Board.pop]

end UniformS.BareMacro
