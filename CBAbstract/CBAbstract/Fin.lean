import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.Basic

variable {n m : ℕ}

namespace Fin

lemma modNat_two_eq_zero_or_one (q : Fin (m*2)): modNat q = 0 ∨ modNat q = 1 :=
(exists_fin_two ).mp ⟨_, rfl⟩

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

lemma last_one : last 1 = 1 := rfl

lemma last_zero_add_one : last (0 + 1) = 1 := rfl

@[simp]
theorem castSucc_succAbove_last {n : ℕ} (i : Fin (n + 1)) :
    succAbove i.castSucc (last _) = last _ :=
  Fin.succAbove_castSucc_of_le i (last _) (le_last _)

theorem succAbove_eq_castSucc_or_succ (p : Fin (n + 1)) (i : Fin n) :
    p.succAbove i = i.castSucc ∨ p.succAbove i = i.succ := ite_eq_or_eq _ _ _

theorem castSucc_le_succAbove (p : Fin (n + 1)) (i : Fin n) : castSucc i ≤ p.succAbove i := by
  obtain h | h := succAbove_eq_castSucc_or_succ p i <;> rw [h]
  exact (castSucc_lt_succ _).le

theorem succAbove_le_succ (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≤ succ i := by
  obtain h | h := succAbove_eq_castSucc_or_succ p i <;> rw [h]
  exact (castSucc_lt_succ _).le

lemma succAbove_succAbove_predAbove_succAbove {k : Fin m} {i : Fin (m + 1)} {j : Fin (m + 2)} :
(j.succAbove i).succAbove ((i.predAbove j).succAbove k) = j.succAbove (i.succAbove k) := by
  rcases lt_or_ge (castSucc i) j with (hij | hij)
  · rw [succAbove_of_castSucc_lt _ _ hij, predAbove_of_castSucc_lt _ _ hij]
    rcases lt_or_ge (castSucc k) i with (hik | hik)
    · have H := (castSucc_lt_iff_succ_le.mp
      (castSucc_lt_castSucc_iff.mpr hik)).trans_lt hij
      rw [succAbove_of_castSucc_lt _ _ hik, succAbove_of_succ_le _ _ H.le,
      succAbove_of_castSucc_lt _ k ((lt_pred_iff _).mpr H), succAbove_castSucc_of_lt _ _ hik]
    · rw [succAbove_of_le_castSucc _ _ hik,
      succAbove_castSucc_of_le, ← succ_succAbove_succ, succ_pred]
      exact hik.trans (castSucc_le_succAbove _ _)
  · rw [succAbove_of_le_castSucc _ _ hij, predAbove_of_le_castSucc _ _ hij]
    rcases lt_or_ge i (succ k) with (hik | hik)
    · have H := ((hij.trans_lt (castSucc_lt_castSucc_iff.mpr hik)))
      rw [succAbove_of_lt_succ _ _ hik, succAbove_of_le_castSucc _ _ H.le,
      succAbove_of_lt_succ _ k ((castPred_lt_iff _).mpr H), succAbove_succ_of_lt _ _ hik]
    · rw [succAbove_of_succ_le _ _ hik, succAbove_succ_of_le,
      ← castSucc_succAbove_castSucc, castSucc_castPred]
      exact (succAbove_le_succ _ _).trans hik

end Fin
