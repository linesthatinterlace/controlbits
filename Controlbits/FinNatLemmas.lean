import Mathlib.Data.Fin.Tuple.Basic

--Fin lemma
lemma Fin.modNat_two_eq_zero_or_one (q : Fin (m*2)): Fin.modNat q = 0 ∨ Fin.modNat q = 1 :=
(Fin.exists_fin_two ).mp ⟨_, rfl⟩

-- FIN LEMMA
lemma succAbove_succAbove_predAbove {i : Fin (m + 1)} {j : Fin (m + 2)} :
(j.succAbove i).succAbove (i.predAbove j) = j := by
rcases j.succAbove_lt_ge i with (h | h)
· rw [Fin.succAbove_below _ _ h, Fin.succAbove_predAbove (ne_of_lt h).symm]
· have h₂ : j = Fin.castSucc (Fin.castPred j) :=
    (Fin.castSucc_castPred (lt_of_le_of_lt h (Fin.castSucc_lt_last _))).symm
  rw [Fin.succAbove_above _ _ h, Fin.predAbove_below _ _ h]
  rw [h₂, Fin.le_castSucc_iff] at h
  rw [Fin.succAbove_below _ _ h, ← h₂]

  -- FIN LEMMA
lemma succAbove_succAbove_predAbove_succAbove_eq_succAbove_succAbove {j : Fin (m + 2)} :
(j.succAbove i).succAbove ((i.predAbove j).succAbove k) = j.succAbove (i.succAbove k) := by
  ext
  dsimp [Fin.succAbove, Fin.predAbove]
  rcases j.succAbove_lt_ge i with (h | h) <;>
  [ simp only [h, dite_true, Fin.coe_pred, ge_iff_le, lt_tsub_iff_right, Fin.dite_val,
    Fin.coe_castSucc, Fin.val_succ] ;
    simp only [h.not_lt, dite_false, Fin.coe_castLT, Fin.dite_val, Fin.coe_castSucc, Fin.val_succ]] <;>
  rcases i.succAbove_lt_ge k with (h₂ | h₂) <;>
  simp only [Fin.lt_def, Fin.le_def, Fin.coe_castSucc] at h h₂
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

--Nat Lemma
lemma Nat.lt_sub_one_of_lt_of_lt {a b c : ℕ} (hab : a < b) (hbc : b < c) : a < c - 1 :=
lt_of_le_of_lt (Nat.le_sub_one_of_lt hab) (Nat.pred_lt_pred (Nat.not_eq_zero_of_lt hab) hbc)

-- Fin lemma

lemma insertNth_insertNth_eq_insertNth_succAbove_insertNth_predAbove {p : Fin m → α}
{j : Fin (m + 2)} : Fin.insertNth j x (Fin.insertNth i y p) =
  Fin.insertNth (Fin.succAbove j i) y (Fin.insertNth (Fin.predAbove i j) x p) := by
  ext k
  simp_rw [Fin.succAbove, Fin.predAbove]
  simp_rw [← Fin.coe_castSucc i, ← Fin.lt_def]
  rcases lt_or_ge (i.castSucc) j with (h | h)
  · simp only [h, ite_true, dite_true]
    rcases lt_trichotomy j k with (h₂ | rfl | h₂)
    · simp_rw [Fin.insertNth_apply_above h₂, Fin.insertNth_apply_above (h.trans h₂),
        Fin.insertNth_apply_above (Fin.pred_lt_pred_iff.mpr h₂), eq_rec_constant]
      rw [Fin.insertNth_apply_above]
      · simp_rw [eq_rec_constant]
      · exact Fin.castSucc_lt_castSucc_iff.mp (lt_of_lt_of_le h (Fin.le_def.mpr
          (Nat.le_sub_one_of_lt (Fin.lt_def.mpr h₂))))
    · simp_rw [Fin.insertNth_apply_above h, Fin.insertNth_apply_same, eq_rec_constant]
    · simp_rw [Fin.insertNth_apply_below h₂, eq_rec_constant]
      rcases lt_trichotomy (i.castSucc) k with (h₃| rfl | h₃)
      · simp_rw [Fin.insertNth_apply_above h₃, Fin.insertNth_apply_below (Fin.pred_lt_pred_iff.mpr h₂),
          eq_rec_constant]
        rw [Fin.insertNth_apply_above]
        · simp_rw [eq_rec_constant]
          congr
        · exact h₃
      · simp_rw [Fin.castLT_castSucc, Fin.insertNth_apply_same]
      · simp_rw [Fin.insertNth_apply_below h₃, eq_rec_constant]
        rw [Fin.insertNth_apply_below , Fin.insertNth_apply_below (Nat.lt_sub_one_of_lt_of_lt h₃ h)]
        · simp_rw [eq_rec_constant]
        · exact (Fin.lt_def.mpr (Fin.lt_def.mp h₃))
  · simp only [h.not_lt, ite_false, dite_false]
    rw [ge_iff_le, Fin.le_castSucc_iff] at h
    rcases lt_trichotomy j k with (h₂ | rfl | h₂)
    · simp_rw [Fin.insertNth_apply_above h₂, eq_rec_constant]
      rcases lt_trichotomy (i.succ) k with (h₃| rfl | h₃)
      · simp_rw [Fin.insertNth_apply_above h₃]
        rw [Fin.insertNth_apply_above, Fin.insertNth_apply_above (Nat.lt_sub_one_of_lt_of_lt h h₃)]
        · simp_rw [eq_rec_constant]
        · simp_rw [Fin.lt_def, Fin.coe_pred]
          exact Nat.lt_pred_iff.mpr h₃
      · simp_rw [Fin.pred_succ, Fin.insertNth_apply_same]
      · simp_rw [Fin.insertNth_apply_below h₃]
        rw [Fin.insertNth_apply_below, Fin.insertNth_apply_above]
        · simp_rw [eq_rec_constant]
          congr
        · exact h₂
        · rw [Fin.lt_def, Fin.coe_pred]
          exact Nat.sub_lt_right_of_lt_add (Nat.one_le_of_lt h₂) h₃
    · simp_rw [Fin.insertNth_apply_below h, Fin.insertNth_apply_same, eq_rec_constant]
    · simp_rw [Fin.insertNth_apply_below h₂, Fin.insertNth_apply_below (h₂.trans h), eq_rec_constant]
      rw [Fin.insertNth_apply_below, Fin.insertNth_apply_below]
      simp_rw [eq_rec_constant]
      · rw [Fin.lt_def] at h₂
        exact Fin.lt_def.mp h₂
      · rw [← Fin.le_castSucc_iff, Fin.le_def, Fin.coe_castSucc] at h
        rw [Fin.lt_def] at h₂
        exact Fin.lt_def.mpr (lt_of_lt_of_le h₂ h)

-- Nat lemma

lemma eq_false_true_of_cond_succ_lt_of_cond_succ_lt
(hmn : (m + bif bm then 1 else 0) < n + bif bn then 1 else 0)
(hnm : (n + bif bn then 0 else 1) < m + bif bm then 0 else 1) :
bm = false ∧ bn = true ∧ (m = n) := by
cases bm <;> cases bn <;>
simp only [false_and, and_false, true_and, and_self, cond_true, cond_false, add_zero, add_lt_add_iff_right] at *
· exact hmn.not_lt hnm
· rw [Nat.lt_succ_iff] at hnm hmn
  exact le_antisymm hmn hnm
· exact (add_lt_iff_neg_left.mp (add_assoc _ 1 1 ▸
    lt_trans ((add_lt_add_iff_right 1).mpr hnm) hmn)).not_le (Nat.zero_le _)
· exact hmn.not_lt hnm
