import Mathlib.Data.Fin.Tuple.Basic
import Controlbits.Nat

namespace Fin

lemma modNat_two_eq_zero_or_one (q : Fin (m*2)): modNat q = 0 ∨ modNat q = 1 :=
(exists_fin_two ).mp ⟨_, rfl⟩

lemma succAbove_succAbove_predAbove {i : Fin (m + 1)} {j : Fin (m + 2)} :
(j.succAbove i).succAbove (i.predAbove j) = j := by
rcases j.succAbove_lt_ge i with (h | h)
· rw [succAbove_below _ _ h, succAbove_predAbove (ne_of_lt h).symm]
· have h₂ : j = castSucc (castPred j) :=
    (castSucc_castPred (lt_of_le_of_lt h (castSucc_lt_last _))).symm
  rw [succAbove_above _ _ h, predAbove_below _ _ h]
  rw [h₂, le_castSucc_iff] at h
  rw [succAbove_below _ _ h, ← h₂]

lemma succAbove_succAbove_predAbove_succAbove_eq_succAbove_succAbove {j : Fin (m + 2)} :
(j.succAbove i).succAbove ((i.predAbove j).succAbove k) = j.succAbove (i.succAbove k) := by
  ext
  dsimp [succAbove, predAbove]
  rcases j.succAbove_lt_ge i with (h | h) <;>
  [ simp only [h, dite_true, coe_pred, ge_iff_le, lt_tsub_iff_right, dite_val,
    coe_castSucc, val_succ] ;
    simp only [h.not_lt, dite_false, coe_castLT, dite_val, coe_castSucc, val_succ]] <;>
  rcases i.succAbove_lt_ge k with (h₂ | h₂) <;>
  simp only [lt_def, le_def, coe_castSucc] at h h₂
  · simp only [h, ite_true, h₂]
    by_cases h₃ : (k + 1 : ℕ) < (j : ℕ)
    · simp only [Nat.lt_of_succ_lt, h₃, ite_true, h₂]
    · exfalso
      rw [not_lt] at h₃
      exact (Nat.le_of_lt_succ (lt_of_lt_of_le h h₃)).not_lt h₂
  · simp only [h, ite_true, ite_false, h₂.not_lt]
    by_cases h₃ : (k + 1 : ℕ) < (j : ℕ) <;>
    simp only [h₃, ite_true, ite_false, ite_eq_right_iff, self_eq_add_right]
    · exact h₂.not_lt
    · rw [not_lt] at h₃
      exact (lt_of_lt_of_le h h₃).le.not_lt
  · simp only [h₂, ite_true, ite_false, h.not_lt]
    by_cases h₃ : (k : ℕ) < (j : ℕ) <;>
    simp only [h₃, ite_true, ite_false, ite_eq_left_iff, not_lt, add_right_eq_self]
    · exact h₂.le.not_lt
    · rw [Nat.succ_le_succ_iff]
      exact h₂.not_le
  · simp only [h.not_lt, ite_false]
    by_cases h₃ : (k : ℕ) < (j : ℕ) <;>
    simp only [h₃, Nat.succ_lt_succ_iff, h₂.not_lt, ite_false, ite_true]
    · exfalso
      exact h₃.not_le (h.trans h₂)
    · rw [not_lt] at h₃
      simp only [(h₃.trans (Nat.le_succ _)).not_lt, ite_false]

lemma insertNth_insertNth_eq_insertNth_succAbove_insertNth_predAbove {p : Fin m → α}
{j : Fin (m + 2)} : insertNth j x (insertNth i y p) =
  insertNth (succAbove j i) y (insertNth (predAbove i j) x p) := by
  ext k
  simp_rw [succAbove, predAbove]
  simp_rw [← coe_castSucc i, ← lt_def]
  rcases lt_or_ge (i.castSucc) j with (h | h)
  · simp only [h, ite_true, dite_true]
    rcases lt_trichotomy j k with (h₂ | rfl | h₂)
    · simp_rw [insertNth_apply_above h₂, insertNth_apply_above (h.trans h₂),
        insertNth_apply_above (pred_lt_pred_iff.mpr h₂), eq_rec_constant]
      rw [insertNth_apply_above]
      · simp_rw [eq_rec_constant]
      · exact castSucc_lt_castSucc_iff.mp (lt_of_lt_of_le h (le_def.mpr
          (Nat.le_sub_one_of_lt (lt_def.mpr h₂))))
    · simp_rw [insertNth_apply_above h, insertNth_apply_same, eq_rec_constant]
    · simp_rw [insertNth_apply_below h₂, eq_rec_constant]
      rcases lt_trichotomy (i.castSucc) k with (h₃| rfl | h₃)
      · simp_rw [insertNth_apply_above h₃, insertNth_apply_below (pred_lt_pred_iff.mpr h₂),
          eq_rec_constant]
        rw [insertNth_apply_above]
        · simp_rw [eq_rec_constant]
          congr
        · exact h₃
      · simp_rw [castLT_castSucc, insertNth_apply_same]
      · simp_rw [insertNth_apply_below h₃, eq_rec_constant]
        rw [insertNth_apply_below , insertNth_apply_below (Nat.lt_sub_one_of_lt_of_lt h₃ h)]
        · simp_rw [eq_rec_constant]
        · exact (lt_def.mpr (lt_def.mp h₃))
  · simp only [h.not_lt, ite_false, dite_false]
    rw [ge_iff_le, le_castSucc_iff] at h
    rcases lt_trichotomy j k with (h₂ | rfl | h₂)
    · simp_rw [insertNth_apply_above h₂, eq_rec_constant]
      rcases lt_trichotomy (i.succ) k with (h₃| rfl | h₃)
      · simp_rw [insertNth_apply_above h₃]
        rw [insertNth_apply_above, insertNth_apply_above (Nat.lt_sub_one_of_lt_of_lt h h₃)]
        · simp_rw [eq_rec_constant]
        · simp_rw [lt_def, coe_pred]
          exact Nat.lt_pred_iff.mpr h₃
      · simp_rw [pred_succ, insertNth_apply_same]
      · simp_rw [insertNth_apply_below h₃]
        rw [insertNth_apply_below, insertNth_apply_above]
        · simp_rw [eq_rec_constant]
          congr
        · exact h₂
        · rw [lt_def, coe_pred]
          exact Nat.sub_lt_right_of_lt_add (Nat.one_le_of_lt h₂) h₃
    · simp_rw [insertNth_apply_below h, insertNth_apply_same, eq_rec_constant]
    · simp_rw [insertNth_apply_below h₂, insertNth_apply_below (h₂.trans h), eq_rec_constant]
      rw [insertNth_apply_below, insertNth_apply_below]
      simp_rw [eq_rec_constant]
      · rw [lt_def] at h₂
        exact lt_def.mp h₂
      · rw [← le_castSucc_iff, le_def, coe_castSucc] at h
        rw [lt_def] at h₂
        exact lt_def.mpr (lt_of_lt_of_le h₂ h)

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

lemma rev_castSucc_eq_succ_rev {i : Fin m}: rev (castSucc i) = succ (rev i) := by
  rcases m with (_ | m)
  · exact i.elim0
  · simp only [ext_iff, val_rev, coe_castSucc, val_succ, Nat.succ_sub_succ_eq_sub,
      add_le_add_iff_right, tsub_add_eq_add_tsub (Nat.le_of_lt_succ i.isLt)]

lemma last_zero : last 0 = 0 := rfl

lemma last_one : last 1 = 1 := rfl

lemma last_zero_add_one : last (0 + 1) = 1 := rfl

end Fin
