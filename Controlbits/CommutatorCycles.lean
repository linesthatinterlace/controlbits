import Controlbits.Cycles
import Controlbits.Commutator

set_option autoImplicit false

universe u

open Equiv

variable {α : Type u} [Fintype α] [DecidableEq α] {x y : Perm α} {q : α}

lemma cycleMin_cmtr_apply_comm [LinearOrder α] :
CycleMin ⁅x, y⁆ (x (y q)) = CycleMin ⁅x, y⁆ (y (x q)):= by
simp_rw [cycleMin_eq_cycleMin_apply (x := y (x q)), ← Perm.mul_apply, ← mul_assoc,
  cmtr_mul_eq_mul_inv_cmtr_inv, commutatorElement_inv, Perm.mul_apply,
  cmtr_apply, inv_inv, Perm.inv_apply_self, Perm.apply_inv_self]

lemma cycleAt_cmtr_disjoint_image
(hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, y q ≠ q) :
  Disjoint (CycleAt ⁅x, y⁆ q) ((CycleAt ⁅x, y⁆ q).image y) := by
  simp_rw [Finset.disjoint_iff_ne, Finset.mem_image, mem_cycleAt_iff]
  rintro _ ⟨j, rfl⟩ _ ⟨_, ⟨⟨_, rfl⟩, rfl⟩⟩
  exact cmtr_zpow_apply_ne_apply_cmtr_pow_apply hxy hy

lemma cycleAt_cmtr_card_le_card_univ_div_two
  (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, y q ≠ q) :
  orderOf ((⁅x, y⁆).cycleOf q) ≤ (Finset.univ (α := α).card)/2 := by
  rw [cycleAt_card_eq_orderOf_cycleOf, Nat.le_div_iff_mul_le (zero_lt_two), mul_comm, two_mul]
  nth_rewrite 2 [← Finset.card_image_of_injective _ (y.injective)]
  rw [← Finset.card_disjoint_union (cycleAt_cmtr_disjoint_image hxy hy)]
  exact Finset.card_le_of_subset (Finset.subset_univ _)

lemma cycleMin_cmtr_right_apply_eq_apply_cycleMin_cmtr [LinearOrder α]
(hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, y q ≠ q)
(hy₂ : ∀ {r q}, r < q → y q < y r → r = y q) :
CycleMin ⁅x, y⁆ (y q) = y (CycleMin ⁅x, y⁆ q) := by
  rcases cycleMin_exists_pow_apply ⁅x, y⁆ q with ⟨j, hjq₂⟩
  refine' eq_of_le_of_not_lt _ (fun h => _)
  · refine' cycleMin_le ⁅x, y⁆ (y q)  ⟨-j, _⟩
    simp_rw [zpow_neg, ← Perm.mul_apply, cmtr_zpow_inv_mul_eq_mul_inv_cmtr_zpow, hxy,
      Perm.mul_apply, hjq₂]
  · rcases cycleMin_exists_pow_apply ⁅x, y⁆  (y q) with ⟨k, hkq₂⟩
    rw [←hkq₂, ← hjq₂, ← Perm.mul_apply, cmtr_zpow_mul_eq_mul_inv_cmtr_zpow_inv, Perm.mul_apply,
      hxy, ← zpow_neg] at h
    rcases lt_trichotomy ((⁅x, y⁆ ^ (-k)) q) ((⁅x, y⁆ ^ j) q) with H | H | H
    · exact (cycleMin_le ⁅x, y⁆ q ⟨-k, rfl⟩).not_lt (hjq₂.symm ▸ H)
    · exact False.elim (lt_irrefl _ (H ▸ h))
    · exact cmtr_zpow_apply_ne_apply_cmtr_pow_apply hxy hy (hy₂ H h)