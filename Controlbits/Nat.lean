import Mathlib.Data.Nat.SuccPred
import Controlbits.Order

namespace Nat

theorem lt_sub_one_of_lt_of_lt {a b c : ℕ} (hab : a < b) (hbc : b < c) : a < c - 1 :=
Order.lt_pred_of_lt_of_lt hab hbc

theorem lt_add_one_of_lt_of_lt {a b c : ℕ} (hab : a < b) (hbc : b < c) : a + 1 < c :=
Order.succ_lt_of_lt_of_lt hab hbc

lemma eq_false_true_of_cond_succ_lt_of_cond_succ_lt
(hmn : (m + bif bm then 1 else 0) < n + bif bn then 1 else 0)
(hnm : (n + bif bn then 0 else 1) < m + bif bm then 0 else 1) :
bm = false ∧ bn = true ∧ (m = n) := by
  refine Order.eq_false_true_of_cond_succ_lt_of_cond_succ_lt ?_ ?_
  · cases bm <;> cases bn <;>
    simp only [succ_eq_succ, cond_true, cond_false, id_eq] at hnm hmn ⊢ <;> exact hmn
  · cases bm <;> cases bn <;>
    simp only [succ_eq_succ, cond_true, cond_false, id_eq] at hnm hmn ⊢ <;> exact hnm

end Nat
