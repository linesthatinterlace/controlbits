import Controlbits.BitResiduum
import Controlbits.Cycles
import Controlbits.PermFintwo
import Mathlib.GroupTheory.Commutator
import Mathlib.GroupTheory.Perm.Basic

--set_option autoImplicit false

section Group

universe u

variable {G : Type u} [Group G] {x y : G}

lemma mul_XBXF_eq_XBXF_inv_mul' : y * ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ * y := by
simp_rw [commutatorElement_inv, commutatorElement_def, inv_inv, mul_assoc]

lemma XBXF_mul_eq_mul_XBXF_inv' : ⁅x, y⁆ * y = y * ⁅x, y⁻¹⁆⁻¹ := by
simp_rw [commutatorElement_inv, commutatorElement_def, inv_mul_cancel_right,
  mul_assoc, mul_inv_cancel_left, inv_inv]

lemma mul_XBXF_pow_eq_xBXF_pow_inv_mul' {k : ℕ} : y * ((⁅x, y⁻¹⁆)^k) = ((⁅x, y⁆)^k)⁻¹ * y := by
induction' k with n hn
· simp_rw [Nat.zero_eq, pow_zero, inv_one, mul_one, one_mul]
· simp_rw [pow_succ', ← mul_assoc, hn, ← pow_succ', pow_succ'', mul_inv_rev, mul_assoc,
    mul_XBXF_eq_XBXF_inv_mul']

@[simp]
lemma XBXF_pow_mul_eq_mul_XBXF_pow_inv' {k : ℕ} :
(⁅x, y⁆)^k * y = y * ((⁅x, y⁻¹⁆)^k)⁻¹ := by
rw [eq_mul_inv_iff_mul_eq, mul_assoc, mul_XBXF_pow_eq_xBXF_pow_inv_mul', mul_inv_cancel_left]

lemma mul_XBXF_zpow_eq_XBXF_zpow_inv_mul' {k : ℤ} :
y * (⁅x, y⁻¹⁆)^k = ((⁅x, y⁆)^k)⁻¹ * y := by
cases k
· simp only [Int.ofNat_eq_coe, zpow_coe_nat, zpow_neg]
  exact mul_XBXF_pow_eq_xBXF_pow_inv_mul'
· simp only [zpow_negSucc, zpow_neg, inv_inv]
  exact XBXF_pow_mul_eq_mul_XBXF_pow_inv'.symm

lemma XBXF_zpow_mul_eq_mul_XBXF_zpow_inv' {k : ℤ} :
(⁅x, y⁆)^k * y = y * ((⁅x, y⁻¹⁆)^k)⁻¹ := by
rw [← zpow_neg, mul_XBXF_zpow_eq_XBXF_zpow_inv_mul', zpow_neg, inv_inv]

lemma mul_XBXF_eq_XBXF_inv_mul (hy : ⁅x, y⁆ = ⁅x, y⁻¹⁆) : y * ⁅x, y⁆ = ⁅x, y⁆⁻¹ * y := by
convert (hy ▸ mul_XBXF_eq_XBXF_inv_mul')

lemma XBXF_mul_eq_mul_XBXF_inv (hy : ⁅x, y⁆ = ⁅x, y⁻¹⁆) : ⁅x, y⁆ * y = y * ⁅x, y⁆⁻¹ := by
convert (hy ▸ XBXF_mul_eq_mul_XBXF_inv')

lemma mul_XBXF_pow_eq_xBXF_pow_inv_mul {k : ℕ} (hy : ⁅x, y⁆ = ⁅x, y⁻¹⁆): y * ((⁅x, y⁆)^k) =
((⁅x, y⁆)^k)⁻¹ * y := by
convert (hy ▸ mul_XBXF_pow_eq_xBXF_pow_inv_mul')

@[simp]
lemma XBXF_pow_mul_eq_mul_XBXF_pow_inv {k : ℕ} (hy : ⁅x, y⁆ = ⁅x, y⁻¹⁆) :
(⁅x, y⁆)^k * y = y * ((⁅x, y⁆)^k)⁻¹ := by
convert (hy ▸ XBXF_pow_mul_eq_mul_XBXF_pow_inv')

lemma mul_XBXF_zpow_eq_XBXF_zpow_inv_mul {k : ℤ} (hy : ⁅x, y⁆ = ⁅x, y⁻¹⁆) :
y * (⁅x, y⁆)^k = ((⁅x, y⁆)^k)⁻¹ * y := by
convert (hy ▸ mul_XBXF_zpow_eq_XBXF_zpow_inv_mul')

lemma XBXF_zpow_mul_eq_mul_XBXF_zpow_inv {k : ℤ} (hy : ⁅x, y⁆ = ⁅x, y⁻¹⁆) :
(⁅x, y⁆)^k * y = y * ((⁅x, y⁆)^k)⁻¹ := by
convert (hy ▸ XBXF_zpow_mul_eq_mul_XBXF_zpow_inv')

end Group

section Perm

open Equiv

variable {α : Type u} {x y : Perm α} {q : α}

lemma symm_unfix_of_unfix {y : Perm α} (hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
∀ q : α, ¬ Function.IsFixedPt y.symm q :=
fun q h => hy q (Perm.inv_eq_iff_eq.mp h).symm

lemma unfix_iff_symm_unfix : (∀ q : α, ¬ Function.IsFixedPt y q) ↔ (∀ q : α, ¬ Function.IsFixedPt y.symm q) :=
⟨symm_unfix_of_unfix, symm_unfix_of_unfix⟩

lemma XBXF_apply : ⁅x, y⁆ q = x (y (x⁻¹ (y⁻¹ (q)))) := rfl

@[simp]
lemma mul_XBXF_unfix_of_unfix (hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
∀ q : α, ¬ Function.IsFixedPt (y * ⁅x, y⁆) q := by
  simp_rw [Function.IsFixedPt, Perm.mul_apply, XBXF_apply,
    ← Perm.eq_inv_iff_eq (f := y), ← Perm.eq_inv_iff_eq (f := x)]
  exact fun q => hy (x⁻¹ (y⁻¹ q))

@[simp]
lemma mul_XBXF_unfix_of_unfix'' (hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
∀ q : α, ¬ Function.IsFixedPt (⁅x, y⁆ * y) q := by
  simp_rw [Function.IsFixedPt, Perm.mul_apply, XBXF_apply,
    ← Perm.eq_inv_iff_eq (f := x), Perm.inv_apply_self]
  exact fun q => hy (x⁻¹ q)

@[simp]
lemma mul_XBXF_unfix_of_unfix' (hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
∀ q : α, ¬ Function.IsFixedPt (y * ⁅x, y⁻¹⁆⁻¹) q := by
  simp_rw [← XBXF_mul_eq_mul_XBXF_inv']
  exact mul_XBXF_unfix_of_unfix'' hy

@[simp]
lemma XBXF_apply_ne_inv_apply (hy : ∀ q : α, ¬ Function.IsFixedPt y q) : ⁅x, y⁆ q ≠ y⁻¹ q := by
  simp_rw [XBXF_apply, ne_eq, Perm.eq_inv_iff_eq]
  exact mul_XBXF_unfix_of_unfix hy _


@[simp]
lemma XBXF_apply_ne_inv_apply'' (hy : ∀ q : α, ¬ Function.IsFixedPt y q) : ⁅x, y⁻¹⁆ q ≠ y q := by
  rw [unfix_iff_symm_unfix] at hy
  exact XBXF_apply_ne_inv_apply hy

@[simp]
lemma XBXF_apply_ne_inv_apply' (hy : ∀ q : α, ¬ Function.IsFixedPt y q) : ⁅x, y⁻¹⁆⁻¹ q ≠ y⁻¹ q := by
  simp_rw [ne_eq, Perm.eq_inv_iff_eq, ← Perm.mul_apply]
  exact mul_XBXF_unfix_of_unfix' hy _

@[simp]
lemma XBXF_apply_ne_inv_apply'''' (hy : ∀ q : α, ¬ Function.IsFixedPt y q) : ⁅x, y⁆⁻¹ q ≠ y q := by
  rw [unfix_iff_symm_unfix] at hy
  convert XBXF_apply_ne_inv_apply' hy

lemma mul_XBXF_unfix_of_unfix_of_commute_square {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
∀ q : α, ¬ Function.IsFixedPt (y * ⁅x, y⁆^k) q := by
  induction' k using Nat.twoStepInduction with k IH
  · rw [pow_zero, mul_one]
    exact hy
  · rw [pow_one]
    exact mul_XBXF_unfix_of_unfix hy
  · intros q h
    have H := (hxy ▸ mul_XBXF_eq_XBXF_inv_mul')
    rw [pow_succ'' (n := k.succ), pow_succ' (n := k), ← mul_assoc, H, Function.IsFixedPt, mul_assoc,
      Perm.mul_apply, ←mul_assoc, Perm.mul_apply, Perm.inv_eq_iff_eq] at h
    exact IH (⁅x, y⁆ q) h

lemma mul_XBXF_unfix_of_unfix_of_commute_square''' {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
∀ q : α, ¬ Function.IsFixedPt ((⁅x, y⁆^k)⁻¹ * y) q := by
  simp_rw [← mul_XBXF_pow_eq_xBXF_pow_inv_mul', hxy]
  exact mul_XBXF_unfix_of_unfix_of_commute_square hxy hy

lemma mul_XBXF_unfix_of_unfix_of_commute_square' {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) : ((⁅x, y⁆)^k) q ≠ y⁻¹ q:= by
  simp_rw [ne_eq, Perm.eq_inv_iff_eq]
  exact mul_XBXF_unfix_of_unfix_of_commute_square hxy hy _

lemma mul_XBXF_unfix_of_unfix_of_commute_square'' {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) : (⁅x, y⁆^k) q ≠ y q := by
  simp_rw [ne_eq, ← Perm.eq_inv_iff_eq, ← Perm.mul_apply, ← mul_XBXF_pow_eq_xBXF_pow_inv_mul', hxy]
  exact Ne.symm (mul_XBXF_unfix_of_unfix_of_commute_square hxy hy _)

lemma mul_XBXF_unfix_of_unfix_of_commute_square_inv {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
∀ q : α, ¬ Function.IsFixedPt (⁅x, y⁆^k * y) q := by
  induction' k using Nat.twoStepInduction with k IH
  · rw [pow_zero, one_mul]
    exact hy
  · rw [pow_one]
    exact mul_XBXF_unfix_of_unfix'' hy
  · intros q h
    rw [pow_succ'' (n := k.succ), pow_succ' (n := k),
      mul_assoc, mul_assoc, XBXF_mul_eq_mul_XBXF_inv', hxy, Function.IsFixedPt, Perm.mul_apply,
      ← Perm.eq_inv_iff_eq, ← mul_assoc, Perm.mul_apply] at h
    exact IH (⁅x, y⁆⁻¹ q) h

lemma mul_XBXF_unfix_of_unfix_of_commute_square_inv''' {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
∀ q : α, ¬ Function.IsFixedPt (y * (⁅x, y⁆^k)⁻¹) q := by
  simp_rw [← hxy, ← XBXF_pow_mul_eq_mul_XBXF_pow_inv']
  exact mul_XBXF_unfix_of_unfix_of_commute_square_inv hxy hy

lemma mul_XBXF_unfix_of_unfix_of_commute_square_inv' {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) : (⁅x, y⁆^k)⁻¹ q ≠ y q := by
  rw [ne_eq, Perm.inv_eq_iff_eq, ← Perm.mul_apply, eq_comm]
  exact mul_XBXF_unfix_of_unfix_of_commute_square_inv hxy hy _

lemma mul_XBXF_unfix_of_unfix_of_commute_square_inv'' {k : ℕ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) : (⁅x, y⁆^k)⁻¹ q ≠ y⁻¹ q := by
  rw [ne_eq, Perm.eq_inv_iff_eq, ← Perm.mul_apply, ← hxy, ← XBXF_pow_mul_eq_mul_XBXF_pow_inv']
  exact mul_XBXF_unfix_of_unfix_of_commute_square_inv hxy hy _

lemma XBXF_zpow_ne_apply {k : ℤ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
((⁅x, y⁆)^k) q ≠ y q := by
cases k <;> simp [hxy, hy, mul_XBXF_unfix_of_unfix_of_commute_square_inv', mul_XBXF_unfix_of_unfix_of_commute_square'']

lemma XBXF_zpow_apply_ne_smul_XBXF_apply {j k : ℤ} (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, ¬ Function.IsFixedPt y q) :
((⁅x, y⁆)^j) q ≠ y (((⁅x, y⁆)^k) q) := by
rw [← sub_add_cancel j k, zpow_add, Perm.mul_apply]
exact XBXF_zpow_ne_apply hxy hy

lemma cycleFull_xBXF_disjoint_image [Fintype α] [DecidableEq α] {q : α}
(hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, ¬ Function.IsFixedPt y q) : Disjoint (CycleFull ⁅x, y⁆ q)
((CycleFull ⁅x, y⁆ q).image y) := by
  simp_rw [Finset.disjoint_iff_ne, Finset.mem_image, mem_cycleFull_iff]
  rintro _ ⟨j, rfl⟩ _ ⟨_, ⟨⟨_, rfl⟩, rfl⟩⟩
  exact XBXF_zpow_apply_ne_smul_XBXF_apply hxy hy

lemma cycleMin_apply_eq_apply_cycleMin [Fintype α] [DecidableEq α] [LinearOrder α] (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆)
(hy : ∀ q : α, ¬ Function.IsFixedPt y q) (hy2 : ∀ r q, r < q → y q < y r → r = y q):
CycleMin ⁅x, y⁆ (y q) = y (CycleMin ⁅x, y⁆ q) := by
rcases cycleMin_exists_pow_apply ⁅x, y⁆ q with ⟨j, hjq₂⟩
refine' eq_of_le_of_not_lt _ (fun h => _)
· refine' cycleMin_le ⁅x, y⁆ (y q)  ⟨-j, _⟩
  simp_rw [zpow_neg, ← Perm.mul_apply, ← mul_XBXF_zpow_eq_XBXF_zpow_inv_mul', hxy, Perm.mul_apply, hjq₂]
· rcases cycleMin_exists_pow_apply ⁅x, y⁆  (y q) with ⟨k, hkq₂⟩
  rw [←hkq₂, ← hjq₂, ← Perm.mul_apply, XBXF_zpow_mul_eq_mul_XBXF_zpow_inv', Perm.mul_apply, hxy, ← zpow_neg] at h
  rcases lt_trichotomy ((⁅x, y⁆ ^ (-k)) q) ((⁅x, y⁆ ^ j) q) with H | H | H
  · exact (cycleMin_le ⁅x, y⁆ q ⟨-k, rfl⟩).not_lt (hjq₂.symm ▸ H)
  · exact False.elim (lt_irrefl _ (H ▸ h))
  · exact XBXF_zpow_apply_ne_smul_XBXF_apply hxy hy (hy2 _ _ H h)

end Perm

section MulAction

open Equiv
universe u v

variable {α : Type u} {G : Type v} [Group G] [MulAction G α] {x y : G} {q : α}

lemma inv_unfix_of_unfix (hy : ∀ q : α, y • q ≠ q) : ∀ q : α, y⁻¹ • q ≠ q :=
fun q h => hy q (inv_smul_eq_iff.mp h).symm

lemma unfix_iff_inv_unfix : (∀ q : α, y • q ≠ q) ↔ (∀ q : α, y⁻¹ • q ≠ q) :=
⟨inv_unfix_of_unfix, fun h => inv_inv y ▸ inv_unfix_of_unfix h⟩

lemma XBXF_apply' : ⁅x, y⁆ • q = x • y • x⁻¹ • y⁻¹ • q := by
simp_rw [commutatorElement_def, mul_smul]

@[simp]
lemma XBXF_smul_ne_inv_smul (hy : ∀ q : α, y • q ≠ q) : ⁅x, y⁆ • q ≠ y⁻¹ • q := by
  simp_rw [XBXF_apply', ne_eq, ← eq_inv_smul_iff (y := y⁻¹ • q)]
  exact hy (x⁻¹ • y⁻¹ • q)


lemma XBXF_pow_smul_ne_inv_smul' {k : ℕ} (hy₁ : ∀ q : α, ⁅x, y⁆ • q = ⁅x, y⁻¹⁆ • q) (hy₂ : ∀ q : α, y • q ≠ q) :
((⁅x, y⁆)^k) • q ≠ y⁻¹ • q := by
  induction' k using Nat.twoStepInduction with k IH generalizing q
  · rw [pow_zero, one_smul]
    exact (hy₂ _).symm
  · rw [pow_one, hy₁]
    rw [unfix_iff_inv_unfix] at hy₂
    convert inv_inv y ▸ XBXF_smul_ne_inv_smul hy₂
  · intros h
    rw [pow_succ'' (n := k.succ), pow_succ' (n := k), mul_smul, mul_smul,
      ← eq_inv_smul_iff  (a := ⁅x, y⁆), ← mul_smul _ y⁻¹,
      ← mul_XBXF_eq_XBXF_inv_mul', mul_smul, hy₁] at h
    exact IH h

lemma XBXF_pow_inv_smul_ne_smul' {k : ℕ} (hy₁ : ∀ q : α, ⁅x, y⁆⁻¹ • q = ⁅x, y⁻¹⁆⁻¹ • q) (hy₂ : ∀ q : α, y • q ≠ q) :
(((⁅x, y⁆)^k)⁻¹) • q ≠ y • q := sorry


lemma XBXF_pow_smul_ne_inv_smul {k : ℕ} (hy₁ : y⁻¹ = y) (hy₂ : ∀ q : α, y • q ≠ q) :
((⁅x, y⁆)^k) • q ≠ y • q := by
  induction' k using Nat.twoStepInduction with k IH generalizing q
  · rw [pow_zero, one_smul]
    exact (hy₂ _).symm
  · rw [pow_one]
    convert XBXF_smul_ne_inv_smul hy₂
    exact hy₁.symm
  · intros h
    rw [pow_succ'' (n := k.succ), pow_succ' (n := k), mul_smul, mul_smul,
      ← eq_inv_smul_iff  (a := ⁅x, y⁆), ← mul_smul _ y,
      ← mul_XBXF_eq_XBXF_inv_mul hy₁, mul_smul] at h
    exact (hy₁ ▸ IH) h

lemma XBXF_pow_inv_smul_ne_smul {k : ℕ} (hy₁ : y⁻¹ = y) (hy₂ : ∀ q : α, y • q ≠ q) :
(((⁅x, y⁆)^k)⁻¹) • q ≠ y • q := by
  simp_rw [ne_eq, inv_smul_eq_iff]
  convert (XBXF_pow_smul_ne_inv_smul (q := y • q) hy₁ hy₂).symm
  rw [← inv_smul_eq_iff, hy₁]

@[simp]
lemma XBXF_zpow_ne_smul {k : ℤ} (hy₁ : y⁻¹ = y) (hy₂ : ∀ q : α, y • q ≠ q) : ((⁅x, y⁆)^k) • q ≠ y • q := by
cases k <;> simp [hy₁, hy₂, XBXF_pow_smul_ne_inv_smul, XBXF_pow_inv_smul_ne_smul]

lemma XBXF_zpow_smul_ne_smul_XBXF_zpow {j k : ℤ} (hy₁ : y⁻¹ = y) (hy₂ : ∀ q : α, y • q ≠ q) :
((⁅x, y⁆)^j) • q ≠ y • ((⁅x, y⁆)^k) • q := by
rw [← sub_add_cancel j k, zpow_add, mul_smul]
exact XBXF_zpow_ne_smul hy₁ hy₂

end MulAction



def XBackXForth (π : Equiv.Perm (Fin (2^(m + 1)))) := π * (flipBit 0) * π⁻¹ * (flipBit 0)

lemma xBXF_def : XBackXForth π = π * (flipBit 0) * π⁻¹ * (flipBit 0) := rfl

lemma xBXF_apply : (XBackXForth π) q = π ((flipBit 0) (π⁻¹ (flipBit 0 q))) := rfl

lemma xBXF_refl : XBackXForth (Equiv.refl (Fin (2^(m + 1)))) = Equiv.refl _ := by
simp_rw [Equiv.ext_iff, xBXF_apply, Equiv.Perm.refl_inv, Equiv.Perm.one_apply,
  flipBit_flipBit, forall_const]

lemma xBXF_one : XBackXForth (1 : Equiv.Perm (Fin (2^(m + 1)))) = 1 := xBXF_refl

lemma xBXF_base : XBackXForth (m := 0) π = 1 := by
  have h := Fin.perm_fintwo π
  split_ifs at h <;> simp_rw [Equiv.ext_iff, xBXF_apply, h]

lemma xBXF_inv : (XBackXForth π)⁻¹ = (flipBit 0) * π * (flipBit 0) * π⁻¹ := by
rw [xBXF_def] ; simp only [mul_assoc, mul_inv_rev, flipBit_inv, inv_inv]

lemma xBXF_inv_apply : (XBackXForth π)⁻¹ q = (flipBit 0) (π ((flipBit 0) (π⁻¹ q))) := by
rw [xBXF_inv] ; rfl

lemma flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit : flipBit 0 * XBackXForth π =
(XBackXForth π)⁻¹ * flipBit 0 := by simp_rw [xBXF_inv, xBXF_def, mul_assoc]

lemma flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit : XBackXForth π * flipBit 0 =
flipBit 0 * (XBackXForth π)⁻¹ := by rw [eq_mul_inv_iff_mul_eq, mul_assoc,
  flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, mul_inv_cancel_left]

@[simp]
lemma xBXF_apply_flipBit_eq_flipBit_xBXF_inv :
XBackXForth π (flipBit 0 q) =
flipBit 0 ((XBackXForth π)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_inv_apply_flipBit_eq_flipBit_xBXF : (XBackXForth π)⁻¹ (flipBit 0 q) =
flipBit 0 (XBackXForth π q)
:= by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, Equiv.Perm.mul_apply]

lemma flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit {k : ℕ} : flipBit 0 * ((XBackXForth π)^k) =
((XBackXForth π)^k)⁻¹ * flipBit 0 := by
induction' k with n hn
· rw [Nat.zero_eq, pow_zero, inv_one, mul_one, one_mul]
· simp_rw [pow_succ', ← mul_assoc, hn, ← pow_succ', pow_succ'', mul_inv_rev, mul_assoc,
    flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit]

lemma xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow {k : ℕ} : ((XBackXForth π)^k) * flipBit 0 =
flipBit 0 * ((XBackXForth π)^k)⁻¹ := by
rw [eq_mul_inv_iff_mul_eq, mul_assoc, flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit,
  mul_inv_cancel_left]

@[simp]
lemma xBXF_pow_apply_flipBit_eq_flipBit_xBXF_pow {k : ℕ} :
((XBackXForth π)^k) (flipBit 0 q) =
flipBit 0 (((XBackXForth π)^k)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_pow_inv_apply_flipBit_eq_flipBit_xBXF {k : ℕ} :
((XBackXForth π)^k)⁻¹ (flipBit 0 q)
= flipBit 0 (((XBackXForth π)^k) q)
:= by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit, Equiv.Perm.mul_apply]

lemma xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv {k : ℤ} :
(XBackXForth π)^k * (flipBit 0) = (flipBit 0) * ((XBackXForth π)^k)⁻¹ := by
cases k
· simp only [Int.ofNat_eq_coe, zpow_coe_nat, zpow_neg]
  exact xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow
· simp only [zpow_negSucc, zpow_neg, inv_inv]
  exact flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit.symm

lemma flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit {k : ℤ} :
(flipBit 0) * (XBackXForth π)^k = ((XBackXForth π)^k)⁻¹ * (flipBit 0) := by
rw [← zpow_neg, xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, zpow_neg, inv_inv]

-- Theorem 4.3 (a) (ish)

@[simp]
lemma xBXF_zpow_apply_flipBit_eq_flipBit_xBXF_zpow_inv {k : ℤ} :
((XBackXForth π)^k) (flipBit 0 q) = (flipBit 0) (((XBackXForth π)^k)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, Equiv.Perm.mul_apply]

@[simp]
lemma xBXR_zpow_inv_apply_flipBit_eq_flipBit_xBXF_zpow {k : ℤ} :
(((XBackXForth π)^k)⁻¹) (flipBit 0 q) = flipBit 0 (((XBackXForth π)^k) q) := by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_apply_ne_flipBit : (XBackXForth π) q ≠ (flipBit 0) q := by
simp_rw [xBXF_apply, ne_eq, ← Equiv.Perm.eq_inv_iff_eq (y := (flipBit 0) q)]
exact flipBit_ne_self

@[simp]
lemma xBXF_pow_apply_ne_flipBit {k : ℕ} : ((XBackXForth π)^k) q ≠ (flipBit 0) q := by
induction' k using Nat.twoStepInduction with k IH generalizing q
· rw [pow_zero]
  exact (flipBit_ne_self).symm
· rw [pow_one]
  exact xBXF_apply_ne_flipBit
· intros h
  rw [pow_succ'' (n := k.succ), pow_succ' (n := k), Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    ← Equiv.eq_symm_apply (x := flipBit 0 q), ← Equiv.Perm.inv_def,
    xBXF_inv_apply_flipBit_eq_flipBit_xBXF] at h
  exact IH h

@[simp]
lemma xBXF_pow_inv_ne_flipBit {k : ℕ} : (((XBackXForth π)^k)⁻¹) q ≠ flipBit 0 q := by
simp_rw [ne_eq, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
convert (xBXF_pow_apply_ne_flipBit (q := flipBit 0 q)).symm
exact flipBit_flipBit.symm

@[simp]
lemma xBXF_zpow_ne_flipBit {k : ℤ} : ((XBackXForth π)^k) q ≠ flipBit 0 q := by
cases k <;> simp

-- Theorem 4.3 (b)
lemma xBXF_zpow_ne_flipBit_mul_xBXF_zpow {j k : ℤ}  :
((XBackXForth π)^j) q ≠ flipBit 0 (((XBackXForth π)^k) q) := by
rw [← sub_add_cancel j k, zpow_add, Equiv.Perm.mul_apply]
exact xBXF_zpow_ne_flipBit

lemma cycleFull_xBXF_disjoint_image_flipBit {q : Fin (2 ^ (m + 1))} : Disjoint (CycleFull (XBackXForth π) q)
((CycleFull (XBackXForth π) q).image (flipBit 0)) := by
simp_rw [Finset.disjoint_iff_ne, Finset.mem_image, mem_cycleFull_iff]
rintro _ ⟨j, rfl⟩ _ ⟨_, ⟨⟨_, rfl⟩, rfl⟩⟩
exact xBXF_zpow_ne_flipBit_mul_xBXF_zpow

-- Theorem 4.4
lemma cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin :
CycleMin (XBackXForth π) (flipBit 0 q) = (flipBit 0) (CycleMin (XBackXForth π) q) := by
rcases cycleMin_exists_pow_apply (XBackXForth π) q with ⟨j, hjq₂⟩
refine' eq_of_le_of_not_lt _ (fun h => _)
· refine' cycleMin_le (XBackXForth π) (flipBit 0 q)  ⟨-j, _⟩
  simp_rw [zpow_neg, xBXR_zpow_inv_apply_flipBit_eq_flipBit_xBXF_zpow, hjq₂]
· rcases cycleMin_exists_pow_apply (XBackXForth π) (flipBit 0 q) with ⟨k, hkq₂⟩
  rw [←hkq₂, ← hjq₂, xBXF_zpow_apply_flipBit_eq_flipBit_xBXF_zpow_inv, ← zpow_neg] at h
  rcases lt_trichotomy ((XBackXForth π ^ (-k)) q) ((XBackXForth π ^ j) q) with H | H | H
  · exact (cycleMin_le (XBackXForth π) q ⟨-k, rfl⟩).not_lt (hjq₂.symm ▸ H)
  · exact False.elim (lt_irrefl _ (H ▸ h))
  · exact xBXF_zpow_ne_flipBit_mul_xBXF_zpow (eq_flipBit_of_lt_of_flipBit_gt H h)

lemma cycleMin_apply_flipBit_zero_eq_cycleMin_flipBit_zero_apply :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = CycleMin (XBackXForth π) (flipBit 0 (π q)):= by
rw [cycleMin_eq_cycleMin_apply (x := flipBit 0 (π q)),
  xBXF_apply_flipBit_eq_flipBit_xBXF_inv,
  xBXF_inv_apply, Equiv.Perm.inv_apply_self, flipBit_flipBit]

lemma flipBit_zero_cycleMin_apply_eq_cycleMin_apply_flipBit_zero :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = (flipBit 0) (CycleMin (XBackXForth π) (π q)) := by
rw [cycleMin_apply_flipBit_zero_eq_cycleMin_flipBit_zero_apply,
  cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin]
