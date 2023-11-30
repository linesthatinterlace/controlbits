import Mathlib.Data.Fin.Tuple.Basic
import Controlbits.Nat

namespace Fin

lemma modNat_two_eq_zero_or_one (q : Fin (m*2)): modNat q = 0 ∨ modNat q = 1 :=
(exists_fin_two ).mp ⟨_, rfl⟩

lemma succAbove_succAbove_predAbove {i : Fin (m + 1)} {j : Fin (m + 2)} :
(j.succAbove i).succAbove (i.predAbove j) = j := by
rcases j.succAbove_lt_ge i with (h | h)
· rw [succAbove_below _ _ h, succAbove_predAbove (ne_of_lt h).symm]
· rw [succAbove_above _ _ h, predAbove, dif_neg h.not_lt,
    succAbove_below _ _ (castSucc_castLT _ _ ▸ le_castSucc_iff.mp h), castSucc_castLT]

lemma succAbove_succAbove_predAbove_succAbove_eq_succAbove_succAbove {j : Fin (m + 2)} :
(j.succAbove i).succAbove ((i.predAbove j).succAbove k) = j.succAbove (i.succAbove k) := by
  ext ; simp only [succAbove, predAbove, lt_def, coe_castSucc, ite_val, coe_pred,
    coe_castLT, dite_eq_ite, dite_val, val_succ]
  rcases lt_or_le (i : ℕ) (j : ℕ) with (h | h) <;>
  rcases lt_or_le (k : ℕ) (i : ℕ) with (h₂ | h₂)
  · simp_rw [if_pos h, if_pos (Nat.lt_sub_one_of_lt_of_lt h₂ h), if_pos h₂, if_pos (h₂.trans h)]
  · simp_rw [if_pos h, if_neg h₂.not_lt, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff,
      apply_ite (fun z => if z < (i : ℕ) then z else z + 1), if_neg h₂.not_lt,
      if_neg (Nat.le_succ_of_le h₂).not_lt]
  · simp_rw [if_neg h.not_lt, if_pos h₂, apply_ite (fun z => if z < (i + 1 : ℕ) then z else z + 1),
      if_pos (lt_of_lt_of_le h₂ (Nat.le_succ _)), Nat.succ_lt_succ_iff, if_pos h₂]
  · simp_rw [if_neg h.not_lt, if_neg (h.trans h₂).not_lt, Nat.succ_lt_succ_iff, if_neg h₂.not_lt,
      if_neg ((h.trans h₂).trans (Nat.le_succ _)).not_lt]

lemma insertNth_insertNth_eq_insertNth_succAbove_insertNth_predAbove {p : Fin m → α}
{j : Fin (m + 2)} : j.insertNth x (insertNth i y p) =
  (succAbove j i).insertNth y ((predAbove i j).insertNth  x p) := by
  simp_rw [eq_insertNth_iff, insertNth_eq_iff, succAbove_succAbove_predAbove,
    insertNth_apply_succAbove, insertNth_apply_same, true_and,
    succAbove_succAbove_predAbove_succAbove_eq_succAbove_succAbove, insertNth_apply_succAbove]

lemma rev_last {m : ℕ} : (last m).rev = 0 := by
  rw [ext_iff, val_rev, val_last, val_zero, tsub_self]

lemma rev_zero {m : ℕ} : (0 : Fin (m + 1)).rev = (last m) := rfl

lemma lt_last_iff_ne_last {i : Fin (m + 1)} : i < last m ↔ i ≠ last m := lt_top_iff_ne_top

lemma rev_eq_zero_iff_last {i : Fin (m + 1)} : i.rev = 0 ↔ i = last m := by
  convert rev_inj
  exact rev_last.symm

lemma rev_ne_zero_iff_ne_last {i : Fin (m + 1)} : i.rev ≠ 0 ↔ i ≠ last m := by
  simp_rw [ne_eq, rev_eq_zero_iff_last]

lemma rev_pos_iff_lt_last {i : Fin (m + 1)} : 0 < i.rev ↔ i < last m := by
  simp_rw [lt_last_iff_ne_last, pos_iff_ne_zero]
  exact rev_ne_zero_iff_ne_last

lemma eq_zero_iff_rev_eq_last {i : Fin (m + 1)} : i = 0 ↔ i.rev = last m := by
  convert rev_rev i ▸ rev_eq_zero_iff_last

lemma ne_zero_iff_rev_ne_last {i : Fin (m + 1)} : i ≠ 0 ↔ i.rev ≠ last m := by
  convert rev_rev i ▸ rev_ne_zero_iff_ne_last

lemma pos_iff_rev_lt_last {i : Fin (m + 1)} : 0 < i ↔ i.rev < last m := by
  convert rev_rev i ▸ rev_pos_iff_lt_last

lemma rev_castSucc_eq_succ_rev {i : Fin m} : i.castSucc.rev = i.rev.succ := by
  simp_rw [ext_iff, val_rev, coe_castSucc, val_succ, val_rev,
    tsub_add_eq_add_tsub (Nat.succ_le_of_lt i.isLt)]

lemma rev_succ_eq_csucc_rev {i : Fin m}: i.succ.rev = i.rev.castSucc := by
  simp_rw [ext_iff, val_rev, coe_castSucc, val_succ, val_rev,
    Nat.succ_sub_succ_eq_sub]

lemma last_zero : last 0 = 0 := rfl

lemma last_one : last 1 = 1 := rfl

lemma last_zero_add_one : last (0 + 1) = 1 := rfl

end Fin
