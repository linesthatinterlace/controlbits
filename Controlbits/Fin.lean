import Mathlib.Data.Fin.Tuple.Basic
import Controlbits.Nat
namespace Fin

lemma modNat_two_eq_zero_or_one (q : Fin (m*2)): modNat q = 0 ∨ modNat q = 1 :=
(exists_fin_two ).mp ⟨_, rfl⟩


lemma succAbove_succAbove_eq {i : Fin (m)} {j : Fin (m + 1)} :
(j.succAbove i).succAbove i = if castSucc i < j then succ i else castSucc i := by
  simp_rw [ext_iff, succAbove, lt_def, dite_val, coe_castSucc, val_succ,
    apply_ite (fun z => if (i : ℕ) < z then (i : ℕ) else (i + 1 : ℕ)),
    if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]

lemma succAbove_succAbove_ne {i : Fin (m)} {j : Fin (m + 1)} (h : t ≠ i) :
(j.succAbove i).succAbove t = if t < i then t.castSucc else t.succ := by
  simp_rw [ext_iff, succAbove, lt_def, dite_val, coe_castSucc, val_succ,
    apply_ite (fun z => if (t : ℕ) < z then (t : ℕ) else (t + 1 : ℕ)), Nat.lt_succ_iff, val_fin_le,
    h.le_iff_lt, val_fin_lt, ite_self]

lemma succAbove_succAbove {i : Fin m} {j : Fin (m + 1)} : (j.succAbove i).succAbove t =
    if t = i then
    if t.castSucc < j then t.succ else t.castSucc else
    if t < i then t.castSucc else t.succ := by
    rcases eq_or_ne t i with (h | h)
    · simp_rw [if_pos h, h, succAbove_succAbove_eq]
    · simp_rw [if_neg h, succAbove_succAbove_ne h]

lemma pred_lt_iff {i : Fin (m)} {j : Fin (m + 1)} (h : j ≠ 0) : pred j h < i ↔ j ≤ castSucc i := by
  rw [ne_eq, Fin.ext_iff, val_zero] at h
  rw [lt_def, le_def, coe_pred, coe_castSucc, ← Nat.pred_eq_sub_one]
  exact ⟨Nat.le_of_pred_lt, fun H => lt_of_lt_of_le (Nat.pred_lt h) H⟩

lemma le_pred_iff {i : Fin (m)} {j : Fin (m + 1)} (h : j ≠ 0) : i ≤ pred j h ↔ castSucc i < j := by
  rw [lt_iff_not_le, ← pred_lt_iff h, not_lt]

lemma castLT_eq_iff_eq_castSucc {n : ℕ} (i : Fin (n + 1)) (hi : (i : ℕ) < n) (j : Fin n) :
  castLT i hi = j ↔ i = castSucc j :=
  ⟨fun h => by simp_rw [← h, castSucc_castLT], fun h => by simp_rw [h, castLT_castSucc]⟩

lemma coe_succ_predAbove_of_le_castSucc {i : Fin (m + 1)} {j : Fin (m + 2)}
  (h : j ≤ castSucc i) : (succ (predAbove i j) : ℕ) = j + 1 := by
  simp_rw [predAbove, dif_neg h.not_lt, val_succ, coe_castLT]

lemma coe_castSucc_predAbove_of_castSucc_lt {i : Fin (m + 1)} {j : Fin (m + 2)}
  (h : castSucc i < j) : (castSucc (predAbove i j) : ℕ) = j - 1 := by
  simp_rw [predAbove, dif_pos h, coe_castSucc, coe_pred]

lemma castSucc_predAbove_eq_of_le_castSucc (h : j ≤ castSucc i) : castSucc (predAbove i j) = j := by
  simp_rw [predAbove, dif_neg h.not_lt, castSucc_castLT]

lemma succ_predAbove_eq_of_castSucc_lt (h : castSucc i < j) : succ (predAbove i j) = j := by
  simp_rw [predAbove, dif_pos h, succ_pred]

lemma castSucc_predAbove_le (i : Fin m) (j) : castSucc (predAbove i j) ≤ j := by
  rcases j.succAbove_lt_ge i with (h | h)
  · exact (castSucc_lt_succ _).le.trans (succ_predAbove_eq_of_castSucc_lt h).le
  · rw [castSucc_predAbove_eq_of_le_castSucc h]

lemma le_succ_predAbove (i : Fin m) (j) : j ≤ succ (predAbove i j) := by
  rcases j.succAbove_lt_ge i with (h | h)
  · rw [succ_predAbove_eq_of_castSucc_lt h]
  · exact (castSucc_predAbove_eq_of_le_castSucc h).symm.le.trans (castSucc_lt_succ _).le

lemma le_castSucc_predAbove_of_le_castSucc (h : j ≤ castSucc i) : j ≤ castSucc (predAbove i j) :=
  (castSucc_predAbove_eq_of_le_castSucc h).symm.le

lemma succ_predAbove_le_of_castSucc_lt (h : castSucc i < j) : succ (predAbove i j) ≤ j :=
  (succ_predAbove_eq_of_castSucc_lt h).le

lemma castSucc_predAbove_lt_iff_castSucc_lt {i : Fin m} {j : Fin (m + 1)} :
  castSucc (predAbove i j) < j ↔ castSucc i < j := by
  refine ⟨?_, ?_⟩
  · simp_rw [lt_iff_not_le]
    exact (le_castSucc_predAbove_of_le_castSucc).mt
  · rw [castSucc_lt_iff_succ_le (i := i.predAbove j)]
    exact succ_predAbove_le_of_castSucc_lt

lemma castSucc_predAbove_eq_iff_le_castSucc {i : Fin (m + 1)} {j : Fin (m + 2)} :
  castSucc (predAbove i j) = j ↔ j ≤ castSucc i := by
    simp_rw [eq_iff_le_not_lt, castSucc_predAbove_le, true_and,
    castSucc_predAbove_lt_iff_castSucc_lt, not_lt]

lemma lt_succ_predAbove_iff_le_castSucc {i : Fin (m + 1)} {j : Fin (m + 2)} :
  j < succ (predAbove i j) ↔ j ≤ castSucc i := by
  refine' ⟨?_, ?_⟩
  · rw [← not_imp_not, not_le, not_lt]
    exact succ_predAbove_le_of_castSucc_lt
  · simp_rw [← le_castSucc_iff]
    exact le_castSucc_predAbove_of_le_castSucc

lemma succ_predAbove_eq_iff_castSucc_lt {i : Fin (m + 1)} {j : Fin (m + 2)} :
  succ (predAbove i j) = j ↔ castSucc i < j := by
  rw [← castSucc_predAbove_lt_iff_castSucc_lt, castSucc_lt_iff_succ_le,
    le_antisymm_iff, and_iff_left_iff_imp]
  exact fun _ => le_succ_predAbove _ _

lemma predAbove_eq : predAbove i j = i ↔ j = castSucc i ∨ j = succ i := by
  simp_rw [or_comm (a := j = castSucc i), predAbove, dite_eq_iff, pred_eq_iff_eq_succ,
    castLT_eq_iff_eq_castSucc, exists_prop]
  exact ⟨Or.imp (And.right) (And.right),
    Or.imp (fun h => ⟨h ▸ castSucc_lt_succ _, h⟩) (fun h => ⟨h ▸ lt_irrefl _, h⟩)⟩

lemma predAbove_lt {i : Fin (m + 1)} {j : Fin (m + 2)} : predAbove i j < i ↔ j < castSucc i := by
  simp_rw [predAbove, lt_def, ite_val, coe_castSucc, coe_castLT, coe_pred]
  refine' ⟨fun h => lt_of_not_le (fun h2 => h.not_le
    (h2.eq_or_lt.elim (fun h3 => _) (fun h3 => _) )), fun h => _⟩
  · simp_rw [dif_neg h3.symm.le.not_lt]
    exact h2
  · simp_rw [dif_pos h3, ← Nat.pred_eq_sub_one]
    exact Nat.le_pred_of_lt h3
  · simp_rw [dif_neg h.le.not_lt]
    exact h

lemma predAbove_gt {i : Fin (m + 1)} {j : Fin (m + 2)} : i < predAbove i j ↔ succ i < j := by
  simp_rw [predAbove, lt_def, ite_val, coe_castSucc, coe_castLT, coe_pred, val_succ]
  refine' ⟨fun h => lt_of_not_le (fun h2 => h.not_le
    (h2.eq_or_lt.elim (fun h3 => _) (fun h3 => _) )), fun h => _⟩
  · simp_rw [h3, dif_pos (Nat.lt_succ_self _)]
    exact (Nat.pred_succ _).le
  · rw [Nat.lt_succ_iff] at h3
    simp_rw [dif_neg h3.not_lt]
    exact h3
  · simp_rw [dif_pos ((Nat.lt_succ_self _).trans h)]
    exact Nat.lt_sub_of_add_lt h

lemma succAbove_succAbove_predAbove {i : Fin (m + 1)} {j : Fin (m + 2)} :
(j.succAbove i).succAbove (i.predAbove j) = j := by
  simp_rw [succAbove_succAbove, predAbove_eq, predAbove_lt, castSucc_predAbove_lt_iff_castSucc_lt,
    ite_eq_iff', succ_predAbove_eq_iff_castSucc_lt, imp_self, castSucc_predAbove_eq_iff_le_castSucc,
    not_lt, true_and, imp_self, implies_true, true_and, not_or, and_imp]
  exact fun H _ => ⟨le_of_lt, fun H2 => lt_of_le_of_ne H2 (Ne.symm H)⟩

lemma succAbove_succAbove_predAbove_succAbove {j : Fin (m + 2)} :
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





lemma insertNth_succAbove_insertNth_predAbove {p : Fin m → α}
{j : Fin (m + 2)} : (succAbove j i).insertNth y ((predAbove i j).insertNth x p)  =
  j.insertNth x (insertNth i y p) := by
  simp_rw [insertNth_eq_iff, succAbove_succAbove_predAbove,
    insertNth_apply_succAbove, insertNth_apply_same, true_and,
    succAbove_succAbove_predAbove_succAbove, insertNth_apply_succAbove]

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
