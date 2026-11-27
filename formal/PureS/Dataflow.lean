import PureS.Simulation
namespace UniformS

def remainingMarks (m : List Mark) : Word := m.filterMap (fun (u,b) => if u then none else some b)
def sleeveMarks (s : Sleeve) := s.flatMap Region.marks
def Board.marks : Board → List Mark
  | .frontier s .. => sleeveMarks s
  | .period s a .. => sleeveMarks s ++ sleeveMarks a

@[simp] theorem remaining_join (a b) :
    remainingMarks (a ++ b) = remainingMarks a ++ remainingMarks b := by
  simp [remainingMarks]
@[simp] theorem marked_remaining (u) (w : Word) :
    remainingMarks (marked u w) = if u then [] else w := by
  cases u <;> induction w <;> simp_all [marked,remainingMarks]

theorem region_remaining (r : Region) : remainingMarks r.marks = r.live := by
  induction r with
  | raw t => rfl
  | word w => simp [Region.marks,Region.live]
  | join l r il ir => simp [Region.marks,Region.live,il,ir]

theorem sleeve_remaining (s : Sleeve) : remainingMarks (sleeveMarks s) = visible s := by
  induction s with
  | nil => rfl
  | cons r s ih => simp [sleeveMarks,visible,region_remaining] at ih ⊢; exact ih

theorem mark_append (a b : List Mark) :
    markFirst (a ++ b) =
      if (remainingMarks a).isEmpty then a ++ markFirst b else markFirst a ++ b := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨u,bit⟩ := x
    cases u
    · rfl
    · simp only [List.cons_append,markFirst,remainingMarks,List.filterMap_cons,ite_true] at *
      cases e : (List.filterMap (fun (u,b) => if u then none else some b) xs).isEmpty <;>
        simp_all

theorem region_transfer {r r' : Region} {b} (h : r.pop = some (b,r')) :
    r'.marks = markFirst r.marks := by
  induction r generalizing b r' with
  | raw _ => simp [Region.pop] at h
  | word w =>
    rcases w with ⟨xs,(_|⟨a,t⟩)⟩
    · simp [Region.pop] at h
    · simp only [Region.pop,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      change marked true ((xs ++ [(a,emit t)]).map Prod.fst) ++ marked false t =
        markFirst (marked true (xs.map Prod.fst) ++ marked false (a::t))
      rw [markFirst_prefix]
      simp [marked,markFirst,List.append_assoc]
  | join l r il ir =>
    cases hl : l.pop with
    | some x =>
      obtain ⟨a,m⟩ := x
      simp only [Region.pop,hl,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      have hn : l.live ≠ [] := fun he => by have := (Region.pop_none l).mpr he; simp [hl] at this
      simp [Region.marks,mark_append,region_remaining,hn,il hl]
    | none =>
      cases hr : r.pop with
      | none => simp [Region.pop,hl,hr] at h
      | some x =>
        obtain ⟨a,m⟩ := x
        simp only [Region.pop,hl,hr,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simp [Region.marks,mark_append,region_remaining,(Region.pop_none l).mp hl,ir hr]

theorem sleeve_transfer {s s' : Sleeve} {b} (h : popSleeve s = some (b,s')) :
    sleeveMarks s' = markFirst (sleeveMarks s) := by
  induction s generalizing b s' with
  | nil => simp [popSleeve] at h
  | cons r s ih =>
    cases e : r.pop with
    | some x =>
      obtain ⟨a,m⟩ := x
      simp only [popSleeve,e,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      have hn : r.live ≠ [] := fun he => by have := (Region.pop_none r).mpr he; simp [e] at this
      change m.marks ++ sleeveMarks s = markFirst (r.marks ++ sleeveMarks s)
      simp [mark_append,region_remaining,hn,region_transfer e]
    | none =>
      cases es : popSleeve s with
      | none => simp [popSleeve,e,es] at h
      | some x =>
        obtain ⟨a,m⟩ := x
        simp only [popSleeve,e,es,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        change r.marks ++ sleeveMarks m = markFirst (r.marks ++ sleeveMarks s)
        simp [mark_append,region_remaining,(Region.pop_none r).mp e,ih es]

theorem board_transfer {s s' : Board} {b} (h : s.pop = some (b,s')) :
    s'.marks = markFirst s.marks := by
  cases s with
  | frontier u r j =>
    cases e : popSleeve u with
    | none => simp [Board.pop,e] at h
    | some x =>
      obtain ⟨a,m⟩ := x
      simp only [Board.pop,e,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      exact sleeve_transfer e
  | period u a v vs f r j =>
    cases e : popSleeve u with
    | some x =>
      obtain ⟨d,m⟩ := x
      simp only [Board.pop,e,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      have hn : visible u ≠ [] := fun he => by have := (popSleeve_none u).mpr he; simp [e] at this
      simp [Board.marks,mark_append,sleeve_remaining,hn,sleeve_transfer e]
    | none =>
      cases ea : popSleeve a with
      | none => simp [Board.pop,e,ea] at h
      | some x =>
        obtain ⟨d,m⟩ := x
        simp only [Board.pop,e,ea,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simp [Board.marks,mark_append,sleeve_remaining,(popSleeve_none u).mp e,sleeve_transfer ea]

theorem prepare_marks (p s) : (prepare p s).2.board.marks = s.marks := by
  cases s with
  | period u a v vs st r j => rfl
  | frontier u r j => cases r <;> simp [prepare,Port.board,Board.marks,sleeveMarks]

theorem pack_marks (a : Sleeve) (r : Region) : (pack a r).marks = sleeveMarks a ++ r.marks := by
  induction a <;> simp_all [pack,sleeveMarks,Region.marks,List.append_assoc]

theorem added_marks (b v) : (added b v).marks = marked false (payload b v) := by
  cases b <;> simp [added,released,Region.marks,payload,freshBox,Segment.history,Segment.fresh,marked]

theorem fire_marks (p : Program) (a : Port) (b : Bool) :
    (a.fire p b).marks = a.board.marks ++ marked false (payload b a.current) := by
  rcases a with ⟨u,i,v,vs,f,r,j⟩
  cases vs <;> simp [Port.fire,Board.marks,Port.board,finished,Region.marks,
    pack_marks,sleeveMarks,added_marks,List.append_assoc]

/-- The chronological history moves exactly one original live bit into its spent
    prefix. The sole change to the remainder is the actual activated payload. -/
theorem physical_history_step (p : Program) {s t : Board} {n}
    (h : advance p s = some (n,t)) (hist tail : Word) (b : Bool)
    (hm : s.marks = marked true hist ++ marked false (b::tail)) :
    ∃ v, phaseList p s = v :: t.pending ∧
      t.marks = marked true (hist ++ [b]) ++ marked false (tail ++ payload b v) := by
  unfold advance at h
  cases e : s.pop with
  | none => simp [e] at h
  | some x =>
    obtain ⟨c,s'⟩ := x
    have hq : remainingMarks s.marks = s.queue := by
      cases s <;> simp [Board.marks,Board.queue,sleeve_remaining]
    have hv := (Board.pop_sound p e).1
    rw [hm,remaining_join,marked_remaining,marked_remaining] at hq
    have he : c = b := by simp [hv] at hq; exact hq.1.symm
    subst c
    cases hh : prepare p s' with
    | mk k a =>
      simp [e,hh] at h
      obtain ⟨rfl,rfl⟩ := h
      have pp := prepare_spec p s'
      rw [hh] at pp
      have mp := prepare_marks p s'
      rw [hh] at mp
      have pe : phaseList p s' = phaseList p s := by
        simp [phaseList,(Board.pop_sound p e).2.1]
      refine ⟨a.current,?_,?_⟩
      · rw [←pe,←pp.2.2.2,(fire_spec p a b).2.1]
      · rw [fire_marks,mp,board_transfer e,hm,markFirst_prefix]
        simp [markFirst,marked,List.append_assoc]
@[simp] theorem seed_marks (w : Word) : (seed w).marks = marked false w := by
  simp [seed,Board.marks,sleeveMarks,Region.marks,freshBox,Segment.fresh,Segment.history,marked]

theorem full_history (p : Program) {n a c} (hr : Run p n a c)
    (s : Board) (hist : Word) (ha : observe s = a)
    (hh : s.marks = marked true hist ++ marked false s.queue) :
    ∃ k t, ∃ h' : Word, 2*n ≤ k ∧ k ≤ 4*n ∧ Steps k (s.tree p) (t.tree p) ∧
       observe t = c ∧ h'.length = n ∧ t.marks = marked true (hist ++ h') ++ marked false t.queue := by
  induction hr generalizing hist s with
  | zero =>
    exact ⟨0,s,[],by omega,by omega,.refl _,ha,rfl,by simpa using hh⟩
  | next first _ ih =>
    obtain ⟨cost,t,hstep,ht⟩ := lift_step p s (ha ▸ first)
    obtain ⟨low,high,native,actual⟩ := macro_exact p hstep
    cases hq : s.queue with
    | nil =>
      have bad := (macro_none p s).mpr hq
      simp [bad] at hstep
    | cons b tail =>
      obtain ⟨v,hv,hm⟩ := physical_history_step p hstep hist tail b (hq ▸ hh)
      have rest : t.queue = tail ++ payload b v := by
        change (match s.queue with
            | [] => none
            | x::z => match phaseList p s with
              | [] => none
              | y::ys => some ⟨z ++ payload x y,ys⟩) = some (observe t) at actual
        simp [hq,hv,observe] at actual
        exact actual.symm
      rw [←rest] at hm
      obtain ⟨j,u,bs,lj,hj,step,hu,hlen,marks⟩ := ih t (hist++[b]) ht hm
      exact ⟨cost+j,u,b::bs,by omega,by omega,native.trans step,hu,by simp [hlen],
        by simpa [List.append_assoc] using marks⟩

theorem ground_history (p : Program) (w : Word) {n c} (hr : Run p n ⟨w,[]⟩ c) :
    ∃ k t, ∃ hist : Word, 2*n ≤ k ∧ k ≤ 4*n ∧ Steps k ((seed w).tree p) (t.tree p) ∧
       observe t = c ∧ hist.length = n ∧ t.marks = marked true hist ++ marked false t.queue := by
  have he : observe (seed w) = ⟨w,[]⟩ := by simp [observe,seed_queue]; rfl
  simpa using full_history p hr (seed w) [] he (by simp [marked])
end UniformS
