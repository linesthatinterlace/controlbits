import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Int.Defs

set_option autoImplicit false

section Group

universe u

variable {G : Type u} [Group G] {x y : G}

lemma cmtr_inv_mul_eq_mul_inv_cmtr : ⁅x, y⁆⁻¹ * y = y * ⁅x, y⁻¹⁆ := by
  simp_rw [commutatorElement_inv, commutatorElement_def, inv_inv, mul_assoc]

lemma cmtr_pow_inv_mul_eq_mul_inv_cmtr_pow {k : ℕ} : ((⁅x, y⁆)^k)⁻¹ * y = y * ((⁅x, y⁻¹⁆)^k) := by
  induction k with | zero | succ n hn
  · simp_rw [pow_zero, inv_one, mul_one, one_mul]
  · simp_rw [pow_succ ⁅x, y⁻¹⁆, pow_succ' ⁅x, y⁆, ← mul_assoc, hn.symm, mul_inv_rev, mul_assoc,
    cmtr_inv_mul_eq_mul_inv_cmtr]

lemma cmtr_zpow_inv_mul_eq_mul_inv_cmtr_zpow {k : ℤ} : ((⁅x, y⁆)^k)⁻¹ * y = y * (⁅x, y⁻¹⁆)^k := by
  cases k
  · simp only [Int.ofNat_eq_coe, zpow_natCast, cmtr_pow_inv_mul_eq_mul_inv_cmtr_pow]
  · simp_rw [zpow_negSucc, inv_inv, eq_mul_inv_iff_mul_eq, mul_assoc, ← eq_inv_mul_iff_mul_eq,
      cmtr_pow_inv_mul_eq_mul_inv_cmtr_pow, inv_mul_cancel_left]

lemma cmtr_zpow_mul_eq_mul_inv_cmtr_zpow_inv {k : ℤ} : (⁅x, y⁆)^k * y = y * ((⁅x, y⁻¹⁆)^k)⁻¹ := by
  rw [← zpow_neg, ← cmtr_zpow_inv_mul_eq_mul_inv_cmtr_zpow, zpow_neg, inv_inv]

lemma cmtr_mul_eq_mul_inv_cmtr_inv : ⁅x, y⁆ * y = y * ⁅x, y⁻¹⁆⁻¹ := by
  have H := cmtr_zpow_mul_eq_mul_inv_cmtr_zpow_inv (x := x) (y := y) (k := 1)
  simp_rw [zpow_one] at H
  exact H

lemma cmtr_inv_eq_cmtr_iff_cmtr_square_id : (⁅x, y⁆ = ⁅x, y⁻¹⁆) ↔ (⁅x, y^2⁆ = 1) := by
  simp_rw [pow_two, commutatorElement_eq_one_iff_mul_comm, eq_comm (a := (x * (y * y))),
  commutatorElement_def, mul_assoc, mul_left_cancel_iff, ← inv_mul_eq_one (a := y * (x⁻¹ * y⁻¹)),
  mul_eq_one_iff_eq_inv, mul_inv_rev, inv_inv, mul_assoc, ← eq_inv_mul_iff_mul_eq (b := y),
  mul_inv_eq_iff_eq_mul, mul_assoc]

end Group

section Perm

open Equiv

universe u

variable {α : Type u} {x y : Perm α} {q : α}

lemma cmtr_apply : ⁅x, y⁆ q = x (y (x⁻¹ (y⁻¹ q))) := rfl

lemma mul_cmtr_unfix_of_unfix (hy : ∀ q : α, y q ≠ q) :
∀ q : α, (y * ⁅x, y⁆) q ≠ q:= by
  simp_rw [Perm.mul_apply, cmtr_apply,
    ← Perm.eq_inv_iff_eq (f := y).not, ← Perm.eq_inv_iff_eq (f := x).not]
  exact fun q => hy (x⁻¹ (y⁻¹ q))

lemma mul_cmtr_pow_unfix {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, y q ≠ q) : ∀ q : α, (y * ⁅x, y⁆^k) q ≠ q := by
  induction k using Nat.twoStepInduction with | zero | one | more k IH
  · rw [pow_zero, mul_one]
    exact hy
  · rw [pow_one]
    exact mul_cmtr_unfix_of_unfix hy
  · intros q h
    simp_rw [pow_succ (n := k.succ), pow_succ' (n := k), ← mul_assoc, ← hxy,
      ← cmtr_inv_mul_eq_mul_inv_cmtr, hxy, mul_assoc,
      Perm.mul_apply, Perm.inv_eq_iff_eq] at h
    exact IH (⁅x, y⁆ q) h

lemma cmtr_pow_apply_ne_apply {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, y q ≠ q) : (⁅x, y⁆^k) q ≠ y q := by
  simp_rw [← Perm.eq_inv_iff_eq.not, ← Perm.mul_apply, cmtr_pow_inv_mul_eq_mul_inv_cmtr_pow, hxy]
  exact Ne.symm (mul_cmtr_pow_unfix hxy hy _)

lemma cmtr_mul_unfix_of_unfix (hy : ∀ q : α, y q ≠ q) :
∀ q : α, (⁅x, y⁆ * y) q ≠ q:= by
  simp_rw [Perm.mul_apply, cmtr_apply, Perm.inv_apply_self, ← Perm.eq_inv_iff_eq (f := x).not]
  exact fun q => hy (x⁻¹ q)

lemma cmtr_pow_mul_unfix {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, y q ≠ q) :
∀ q : α, (⁅x, y⁆^k * y) q ≠ q := by
  induction k using Nat.twoStepInduction with | zero | one | more k IH
  · rw [pow_zero, one_mul]
    exact hy
  · rw [pow_one]
    exact cmtr_mul_unfix_of_unfix hy
  · intros q h
    simp_rw [pow_succ (n := k.succ), pow_succ' (n := k), mul_assoc,
      cmtr_mul_eq_mul_inv_cmtr_inv, hxy, Perm.mul_apply,
      ← Perm.eq_inv_iff_eq (f := ⁅x, y⁆)] at h
    exact IH (⁅x, y⁆⁻¹ q) h

lemma cmtr_pow_inv_apply_ne_apply {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, y q ≠ q) : (⁅x, y⁆^k)⁻¹ q ≠ y q := by
  simp_rw [Perm.inv_eq_iff_eq.not]
  exact Ne.symm (cmtr_pow_mul_unfix hxy hy _)

lemma cmtr_zpow_apply_ne_apply {k : ℤ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
  (hy : ∀ q : α, y q ≠ q) : ((⁅x, y⁆)^k) q ≠ y q := by
  cases k
  · simp only [Int.ofNat_eq_coe, zpow_natCast, ne_eq]
    exact cmtr_pow_apply_ne_apply hxy hy
  · simp only [zpow_negSucc, ne_eq]
    simp only [ne_eq, hxy, hy, not_false_eq_true, implies_true,
      cmtr_pow_inv_apply_ne_apply]

lemma cmtr_zpow_apply_ne_apply_cmtr_pow_apply {j k : ℤ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, y q ≠ q) : ((⁅x, y⁆)^j) q ≠ y (((⁅x, y⁆)^k) q) := by
  rw [← sub_add_cancel j k, zpow_add, Perm.mul_apply]
  exact cmtr_zpow_apply_ne_apply hxy hy

end Perm
