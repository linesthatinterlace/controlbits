import Mathlib.Data.Nat.SuccPred
import CBAbstract.Order

namespace Nat

lemma eq_false_true_of_cond_succ_lt_of_cond_succ_lt {m n : ℕ} {bn bm : Bool}
(hmn : (m + bif bm then 1 else 0) < n + bif bn then 1 else 0)
(hnm : (n + bif bn then 0 else 1) < m + bif bm then 0 else 1) :
bm = false ∧ bn = true ∧ (m = n) := by
  refine Order.eq_false_true_of_cond_succ_lt_of_cond_succ_lt ?_ ?_
  · cases bm <;> cases bn <;>
    simp only [succ_eq_succ, cond_true, cond_false, id_eq] at hnm hmn ⊢ <;> exact hmn
  · cases bm <;> cases bn <;>
    simp only [succ_eq_succ, cond_true, cond_false, id_eq] at hnm hmn ⊢ <;> exact hnm

end Nat
