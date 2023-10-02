import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Commutator

lemma Fin.perm_fin_two (π : Equiv.Perm (Fin 2)) :
π = (if (π 0 = 1) then Equiv.swap 0 1 else 1) := by
rw [Equiv.ext_iff, Fin.forall_fin_two]
rcases (Fin.exists_fin_two.mp ⟨π 0, rfl⟩) with (h0 | h0) <;>
rcases (Fin.exists_fin_two.mp ⟨π 1, rfl⟩) with (h1 | h1) <;>
simp only [h0, h1, ite_false, Equiv.refl_apply, true_and,
    ite_true, Equiv.swap_apply_left, Equiv.swap_apply_right]
· rw [← h0, Equiv.apply_eq_iff_eq] at h1
  simp only at h1
· rw [← h1, Equiv.apply_eq_iff_eq] at h0
  simp only at h0

lemma Fin.perm_fin_two_mul_self (π : Equiv.Perm (Fin 2)) : π * π  = 1 := by
  have h := Fin.perm_fin_two π
  split_ifs at h <;> rw [h]
  · rw [Equiv.swap_mul_self]
  · rw [mul_one]

lemma Fin.perm_fin_two_apply_apply (π : Equiv.Perm (Fin 2)) : π (π q) = q := by
  rw [← Equiv.Perm.mul_apply, Fin.perm_fin_two_mul_self, Equiv.Perm.one_apply]

lemma Fin.perm_fin_two_of_fix_zero {π : Equiv.Perm (Fin 2)} (h : π 0 = 0) : π = 1 := by
  have h2 := Fin.perm_fin_two π
  simp_rw [h, ite_false] at h2
  exact h2

lemma Fin.perm_fin_two_of_fix_one {π : Equiv.Perm (Fin 2)} (h : π 1 = 1) : π = 1 := by
  have h2 := Fin.perm_fin_two π
  rw [← h] at h2
  simp_rw [EmbeddingLike.apply_eq_iff_eq, ite_false] at h2
  exact h2

lemma Fin.perm_fin_two_of_unfix_zero {π : Equiv.Perm (Fin 2)} (h : π 0 = 1) : π = Equiv.swap 0 1 := by
  have h2 := Fin.perm_fin_two π
  simp_rw [h, ite_true] at h2
  exact h2

lemma Fin.perm_fin_two_of_unfix_one {π : Equiv.Perm (Fin 2)} (h : π 1 = 0) : π = Equiv.swap 0 1 := by
  have h2 := Fin.perm_fin_two π
  rw [← h, Fin.perm_fin_two_apply_apply, h] at h2
  simp only [ite_true] at h2
  exact h2

lemma Fin.cmtr_fin_two {x y : Equiv.Perm (Fin 2)} : ⁅x, y⁆ = 1 := by
  have h := Fin.perm_fin_two x
  have h₂ := Fin.perm_fin_two y
  split_ifs at h h₂ <;> simp_rw [commutatorElement_def, h, h₂]