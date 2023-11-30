import Mathlib.Order.SuccPred.Basic

namespace Order

theorem lt_pred_of_lt_of_lt {α : Type*} [Preorder α] [PredOrder α]
{a b c : α} (hab : a < b) (hbc : b < c) : a < pred c := lt_of_lt_of_le hab (le_pred_of_lt hbc)

theorem succ_lt_of_lt_of_lt {α : Type*} [Preorder α] [SuccOrder α]
{a b c : α} (hab : a < b) (hbc : b < c) : succ a < c := lt_of_le_of_lt (succ_le_of_lt hab) hbc

lemma eq_false_true_of_cond_succ_lt_of_cond_succ_lt {α : Type*} [PartialOrder α] [SuccOrder α]
  [NoMaxOrder α] {m n : α} {bm bn : Bool}
(hmn : (bif bm then succ else id) m < (bif bn then succ else id) n)
(hnm : (bif bn then id else succ) n < (bif bm then id else succ) m)  :
bm = false ∧ bn = true ∧ (m = n) := by
  cases bm <;> cases bn <;>
  simp only [false_and, and_false, true_and, and_self, cond_true, cond_false, id_eq,
  succ_le_iff, succ_lt_succ_iff, lt_succ_iff] at *
  · exact hmn.not_lt hnm
  · exact le_antisymm hmn hnm
  · exact lt_irrefl _ (((hnm.trans (lt_succ _)).trans hmn).trans (lt_succ _))
  · exact hmn.not_lt hnm

end Order
