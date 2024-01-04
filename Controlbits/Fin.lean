import Mathlib.Data.Fin.Tuple.Basic
import Controlbits.Nat
import Mathlib.Data.Fintype.Basic

namespace Fin

lemma modNat_two_eq_zero_or_one (q : Fin (m*2)): modNat q = 0 ∨ modNat q = 1 :=
(exists_fin_two ).mp ⟨_, rfl⟩

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

@[simp] theorem castSucc_le_castSucc_iff {a b : Fin n} :
    Fin.castSucc a ≤ Fin.castSucc b ↔ a ≤ b := .rfl

@[simp]
theorem castSucc_succAbove_last {n : ℕ} (i : Fin (n + 1)) :
    succAbove i.castSucc (last _) = last _ :=
  succAbove_above i.castSucc (last _)
  (by simp only [le_castSucc_iff, succ_last, castSucc_lt_last _])

@[simp]
theorem castSucc_succAbove_castSucc {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.castSucc.succAbove j.castSucc = (i.succAbove j).castSucc := by
  rcases lt_or_le (castSucc j) i with (h | h)
  · rw [succAbove_below _ _ (castSucc_lt_castSucc_iff.mpr h), succAbove_below _ _ h]
  · rw [succAbove_above _ _ (castSucc_le_castSucc_iff.mpr h), succAbove_above _ _ h, succ_castSucc]

end Fin
