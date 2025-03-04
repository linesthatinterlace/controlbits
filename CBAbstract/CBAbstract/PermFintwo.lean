import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.CharZero.Defs

namespace Fin

lemma perm_fin_two (π : Equiv.Perm (Fin 2)) :
π = (if (π 0 = 1) then Equiv.swap 0 1 else 1) := by
  rw [Equiv.ext_iff, forall_fin_two]
  rcases (exists_fin_two.mp ⟨π 0, rfl⟩) with (h0 | h0) <;>
  rcases (exists_fin_two.mp ⟨π 1, rfl⟩) with (h1 | h1) <;>
  simp only [h0, h1, zero_eq_one_iff, Nat.succ_ne_self, if_false, Equiv.Perm.one_apply,
    if_true, Equiv.swap_apply_left, Equiv.swap_apply_right, true_and] <;>
  exact (Fin.zero_ne_one <| π.injective (h0.trans h1.symm)).elim

lemma perm_fin_two_mul_self (π : Equiv.Perm (Fin 2)) : π * π = 1 := by
  rw [perm_fin_two π]
  split_ifs
  · rw [Equiv.swap_mul_self]
  · rw [mul_one]

lemma perm_fin_two_apply_apply {q : Fin 2} (π : Equiv.Perm (Fin 2)) : π (π q) = q := by
  rw [← Equiv.Perm.mul_apply, perm_fin_two_mul_self, Equiv.Perm.one_apply]

lemma perm_fin_two_of_fix_zero {π : Equiv.Perm (Fin 2)} (h : π 0 = 0) : π = 1 := by
  rw [perm_fin_two π]
  simp_rw [h, zero_eq_one_iff, Nat.succ_ne_self, ite_false]

lemma perm_fin_two_of_fix_one {π : Equiv.Perm (Fin 2)} (h : π 1 = 1) : π = 1 := by
  rw [perm_fin_two π, ← h]
  simp only [EmbeddingLike.apply_eq_iff_eq, zero_eq_one_iff, Nat.succ_ne_self, ite_false]

lemma perm_fin_two_of_unfix_zero {π : Equiv.Perm (Fin 2)} (h : π 0 = 1) : π = Equiv.swap 0 1 := by
  rw [perm_fin_two π]
  simp_rw [h, ite_true]

lemma perm_fin_two_of_unfix_one {π : Equiv.Perm (Fin 2)} (h : π 1 = 0) : π = Equiv.swap 0 1 := by
  rw [perm_fin_two π, ← perm_fin_two_apply_apply (π := π) (q := 1)]
  simp_rw [h, ite_true]

lemma cmtr_fin_two {x y : Equiv.Perm (Fin 2)} : ⁅x, y⁆ = 1 := by
  rw [perm_fin_two x, perm_fin_two y]
  by_cases h : (x 0 = 1)
  · by_cases h₂ : (y 0 = 1)
    · rw [if_pos h, if_pos h₂, commutatorElement_self]
    · rw [if_neg h₂, commutatorElement_one_right]
  · rw [if_neg h, commutatorElement_one_left]

end Fin
