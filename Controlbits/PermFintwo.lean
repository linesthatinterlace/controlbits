import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Commutator

namespace Fin

lemma perm_fin_two (π : Equiv.Perm (Fin 2)) :
π = (if (π 0 = 1) then Equiv.swap 0 1 else 1) := by
  rw [Equiv.ext_iff, forall_fin_two]
  rcases (exists_fin_two.mp ⟨π 0, rfl⟩) with (h0 | h0) <;>
  rcases (exists_fin_two.mp ⟨π 1, rfl⟩) with (h1 | h1) <;>
  simp only [h0, ite_true, Equiv.swap_apply_left, h1, Equiv.swap_apply_right, one_eq_zero_iff, id_eq,
    OfNat.ofNat_ne_one, and_false, zero_eq_one_iff, ite_false, Equiv.Perm.coe_one,  and_self] <;>
  exact (zero_ne_one ((EmbeddingLike.apply_eq_iff_eq _).mp (h0.trans (h1.symm)))).elim

lemma perm_fin_two_mul_self (π : Equiv.Perm (Fin 2)) : π * π  = 1 := by
  rw [perm_fin_two π]
  split_ifs
  · rw [Equiv.swap_mul_self]
  · rw [mul_one]

lemma perm_fin_two_apply_apply (π : Equiv.Perm (Fin 2)) : π (π q) = q := by
  rw [← Equiv.Perm.mul_apply, perm_fin_two_mul_self, Equiv.Perm.one_apply]

lemma perm_fin_two_of_fix_zero {π : Equiv.Perm (Fin 2)} (h : π 0 = 0) : π = 1 := by
  rw [perm_fin_two π]
  simp_rw [h, zero_eq_one_iff, OfNat.ofNat_ne_one, ite_false]

lemma perm_fin_two_of_fix_one {π : Equiv.Perm (Fin 2)} (h : π 1 = 1) : π = 1 := by
  rw [perm_fin_two π, ← h]
  simp only [EmbeddingLike.apply_eq_iff_eq, zero_eq_one_iff, OfNat.ofNat_ne_one, ite_false]

lemma perm_fin_two_of_unfix_zero {π : Equiv.Perm (Fin 2)} (h : π 0 = 1) : π = Equiv.swap 0 1 := by
  rw [perm_fin_two π]
  simp_rw [h, ite_true]

lemma perm_fin_two_of_unfix_one {π : Equiv.Perm (Fin 2)} (h : π 1 = 0) : π = Equiv.swap 0 1 := by
  rw [perm_fin_two π, ← perm_fin_two_apply_apply (π := π) (q := 1)]
  simp_rw [h, ite_true]

lemma cmtr_fin_two {x y : Equiv.Perm (Fin 2)} : ⁅x, y⁆ = 1 := by
  rw [perm_fin_two x, perm_fin_two y]
  split_ifs <;> simp only [commutatorElement_def, one_mul, inv_one, mul_one, Equiv.swap_inv,
    Equiv.swap_mul_self]

end Fin
