import Mathlib.Data.Fin.Tuple.Basic
import Controlbits.Nat
import Mathlib.Data.Fintype.Basic

namespace Fin

lemma modNat_two_eq_zero_or_one (q : Fin (m*2)): modNat q = 0 ∨ modNat q = 1 :=
(exists_fin_two ).mp ⟨_, rfl⟩

lemma lt_last_iff_ne_last {i : Fin (m + 1)} : i < last m ↔ i ≠ last m := lt_top_iff_ne_top

lemma rev_eq_zero_iff_last {i : Fin (m + 1)} : i.rev = 0 ↔ i = last m := by
  convert rev_inj
  exact (rev_last m).symm

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

lemma rev_castSucc_succ {i : Fin m}: i.castSucc.succ.rev = i.rev.castSucc.succ := by
  simp_rw [rev_succ, rev_castSucc, succ_castSucc]

lemma rev_succ_castSucc {i : Fin m}: i.succ.castSucc.rev = i.rev.succ.castSucc := by
  simp_rw [← succ_castSucc, rev_castSucc_succ]

lemma castSucc_rev_castSucc {i : Fin m}: i.castSucc.rev.castSucc = i.succ.rev.succ := by
  simp_rw [rev_succ, rev_castSucc, succ_castSucc]

lemma last_zero : last 0 = 0 := rfl

lemma last_one : last 1 = 1 := rfl

lemma last_zero_add_one : last (0 + 1) = 1 := rfl

@[simp]
theorem castSucc_succAbove_last {n : ℕ} (i : Fin (n + 1)) :
    succAbove i.castSucc (last _) = last _ :=
  Fin.succAbove_castSucc_of_le i (last _) (le_last _)


lemma succAbove_succAbove_predAbove {i : Fin (m + 1)} {j : Fin (m + 2)} :
(j.succAbove i).succAbove (i.predAbove j) = j := by
  rcases lt_or_le (castSucc i) j with (h | h)
  · rw [succAbove_of_castSucc_lt _ _ h, predAbove_of_castSucc_lt _ _ h,
    succAbove_castSucc_of_le, succ_pred]
    rw [le_pred_iff, ← castSucc_lt_iff_succ_le]
    exact h
  · rw [succAbove_of_le_castSucc _ _ h, predAbove_of_le_castSucc _ _ h,
    succAbove_succ_of_le, castSucc_castPred]
    rw [castPred_le_iff]
    exact h

lemma succAbove_succAbove_predAbove_succAbove {j : Fin (m + 2)} :
(j.succAbove i).succAbove ((i.predAbove j).succAbove k) = j.succAbove (i.succAbove k) := sorry

end Fin
