import PureS.Selected
namespace UniformS.BareMacro
open UniformS Readback
def Legal (f : Term → Option Term) := ∀ t u, f t = some u → Native t u

theorem skip_legal : Legal skip := by intro t u h; cases h
theorem contract_legal : Legal contract := fun _ _ h => contract_sound h

theorem popW_legal : Legal popW := by
  intro t
  induction t using popW.induct with
  | case1 a b => exact fun u h => contract_sound h
  | case2 w g ih =>
    intro v hv
    change (popW w).map _ = some v at hv
    cases e : popW w with
    | none => simp [e] at hv
    | some x =>
      simp [e] at hv; subst v
      exact .left _ (.right _ (ih _ e))
  | case3 t h1 h2 =>
    intro v hv
    rw [popW] at hv <;> first | assumption | contradiction

theorem popY_legal : Legal popY := by
  intro t u h
  unfold popY at h
  split at h
  · rename_i a w g
    cases e : popW w with
    | none => simp [e] at h
    | some v =>
      simp [e] at h; subst u
      exact .right _ (.left _ (.right _ (.right _ (popW_legal _ _ e))))
  · contradiction
theorem fireY_legal (b) : Legal (fireY b) := by
  intro t u h
  unfold fireY at h
  split at h
  · rename_i a g
    split at h
    · contradiction
    · cases b
      · cases e : contract a with
        | none => simp [e] at h
        | some v => simp [e] at h; subst u; exact .left _ (.right _ (contract_sound e))
      · cases e : contract g with
        | none => simp [e] at h
        | some v => simp [e] at h; subst u; exact .right _ (contract_sound e)
  · contradiction

theorem list_legal {f} (hf : Legal f) : Legal (listAction f) := by
  intro t
  induction t using listAction.induct f with
  | case1 a r v e =>
    intro u h; simp [listAction,e] at h; subst u
    exact .left _ (.right _ (hf _ _ e))
  | case2 a r e ih =>
    intro u h
    simp only [listAction,e] at h
    cases er : listAction f r with
    | none => simp [er] at h
    | some v => simp [er] at h; subst u; exact .right _ (ih _ er)
  | case3 t h =>
    intro u hu
    rw [listAction] at hu <;> first | assumption | contradiction

theorem rail_legal {f fin} (hf : Legal f) (hfin : Legal fin) : Legal (railAction f fin) := by
  intro t
  induction t using railAction.induct f with
  | case1 a st z v e =>
    intro u hu; simp [railAction,e] at hu; subst u
    exact .left _ (.left _ (.right _ (list_legal hf _ _ e)))
  | case2 a st z e ih =>
    intro u h
    simp only [railAction,e] at h
    cases ez : railAction f fin z with
    | none => simp [ez] at h
    | some v => simp [ez] at h; subst u; exact .right _ (ih _ ez)
  | case3 t h =>
    intro u hu
    rw [railAction] at hu <;> first | assumption | exact hfin _ _ hu

theorem board_legal {hdr f fin} (hh : Legal hdr) (hf : Legal f) (hfin : Legal fin) :
    Legal (boardAction hdr f fin) := by
  intro t u h
  unfold boardAction at h
  split at h
  · rename_i w t
    cases e : hdr w with
    | some v => simp [e] at h; subst u; exact .left _ (.right _ (.right _ (hh _ _ e)))
    | none =>
      cases e' : railAction f fin t with
      | none => simp [e,e'] at h
      | some v => simp [e,e'] at h; subst u; exact .right _ (rail_legal hf hfin _ _ e')
  · contradiction

theorem pop_legal : Legal pop := board_legal popW_legal popY_legal skip_legal
theorem fire_legal (b) : Legal (fire b) := board_legal skip_legal (fireY_legal b) skip_legal
theorem alloc_legal : Legal alloc := board_legal skip_legal skip_legal contract_legal

theorem finish_legal (b t u k) (h : finish b t = some (k,u)) :
    1 ≤ k ∧ k ≤ 3 ∧ Steps k t u := by
  cases e : fire b t with
  | some v => simp [finish,e] at h; obtain ⟨rfl,rfl⟩ := h; exact ⟨by decide,by decide,.one (fire_legal b _ _ e)⟩
  | none =>
    cases a : alloc t with
    | none => simp [finish,e,a] at h
    | some v =>
      cases e' : fire b v with
      | some z =>
        simp [finish,e,a,e'] at h; obtain ⟨rfl,rfl⟩ := h
        exact ⟨by decide,by decide,.cons (alloc_legal _ _ a) (.one (fire_legal b _ _ e'))⟩
      | none =>
        cases a' : alloc v with
        | none => simp [finish,e,a,e',a'] at h
        | some z =>
          cases e'' : fire b z with
          | none => simp [finish,e,a,e',a',e''] at h
          | some z' =>
            simp [finish,e,a,e',a',e''] at h; obtain ⟨rfl,rfl⟩ := h
            exact ⟨by decide,by decide,.cons (alloc_legal _ _ a) (.cons (alloc_legal _ _ a') (.one (fire_legal b _ _ e'')))⟩

theorem all_input_native (t u k) (h : selected t = some (k,u)) :
    2 ≤ k ∧ k ≤ 4 ∧ Steps k t u := by
  cases hb : (live t).head? with
  | none => simp [selected,hb] at h
  | some b =>
    cases hp : pop t with
    | none => simp [selected,hb,hp] at h
    | some v =>
      cases hf : finish b v with
      | none => simp [selected,hb,hp,hf] at h
      | some x =>
        obtain ⟨n,z⟩ := x
        simp [selected,hb,hp,hf] at h; obtain ⟨rfl,rfl⟩ := h
        obtain ⟨lo,hi,hn⟩ := finish_legal _ _ _ _ hf
        exact ⟨by omega,by omega,.cons (pop_legal _ _ hp) hn⟩
end UniformS.BareMacro
