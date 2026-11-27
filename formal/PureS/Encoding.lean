import PureS.Cost
import PureS.Board
namespace UniformS

def wordWeight : Word → Nat
  | [] => 0
  | b::bs => (if b then 4 else 3) + wordWeight bs
def periodWeight (words : List Word) := (words.map wordWeight).sum

theorem word_size (w) : leaves (emit w) = 1 + wordWeight w := by
  induction w with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [emit,leaves,readCell,tag,wordWeight,ih] <;> omega

theorem list_size (ws) : leaves (slots ws) = 1 + 12*ws.length + periodWeight ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp [slots,leaves,slot,pair,arm,box,word_size,periodWeight,Nat.mul_succ] at ih ⊢
    omega

theorem exact_encoder_leaves (p : Program) (w : Word) :
    leaves ((seed w).tree p) = 22 + 48*p.period.length + 4*periodWeight p.period + wordWeight w := by
  rw [seed_tree]
  simp [X,leaves,template,pair,box,list_size,word_size]
  omega

theorem word_weight_bounds (w) : 3*w.length ≤ wordWeight w ∧ wordWeight w ≤ 4*w.length := by
  induction w with
  | nil => simp [wordWeight]
  | cons b xs ih => cases b <;> simp [wordWeight,Nat.mul_succ] <;> omega
end UniformS
