import Mathlib.Data.Fin.Basic

namespace Fin

def mulNat {n : ℕ} (i : Fin n) (m : ℕ) (h : 0 < m) : Fin (n * m) :=
  ⟨i * m, Nat.mul_lt_mul_of_pos_right i.prop h⟩

lemma coe_mulNat {n : ℕ} (i : Fin n) (m : ℕ) (h : 0 < m) : (i.mulNat m h : ℕ) = i * m := rfl

lemma mulNat_mk {n i m : ℕ} (hi : i < n) (h : 0 < m) : mulNat ⟨i, hi⟩ m h = i * m := rfl

def natMul {m : ℕ} (n : ℕ) (i : Fin m) (h : 0 < n) : Fin (n * m) :=
  ⟨n * i, Nat.mul_lt_mul_of_pos_left i.prop h⟩

lemma natMul_mk {m n i : ℕ} (hi : i < m) (h : 0 < n) : natMul n ⟨i, hi⟩ h = n * i := rfl

lemma coe_natMul {m : ℕ} (n : ℕ) (i : Fin m) (h : 0 < n) : (i.natMul n h : ℕ) = n * i := rfl

lemma divNat_mk {n m i : ℕ} (hi : i < m * n) : divNat ⟨i, hi⟩ = i / n := rfl

lemma modNat_mk {n m i : ℕ} (hi : i < m * n) : modNat ⟨i, hi⟩ = i % n := rfl

end Fin
