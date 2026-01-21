import CBAbstract.Commutator
import CBAbstract.Cycles

set_option autoImplicit false

universe u

open Equiv Equiv.Perm

variable {α : Type u}  {x y : Perm α} {q : α}

lemma cycleMin_cmtr_apply_comm [ConditionallyCompleteLinearOrder α] :
CycleMin ⁅x, y⁆ (x (y q)) = CycleMin ⁅x, y⁆ (y (x q)):= by
simp_rw [cycleMin_eq_cycleMin_apply (x := y (x q)), commutatorElement_def,
  Perm.mul_apply, coe_inv, symm_apply_apply]

lemma cycleAt_cmtr_disjoint_image [DecidableRel (⁅x, y⁆).SameCycle]
  [DecidableEq α] (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, y q ≠ q) (q : α) (s t : Finset α):
  Disjoint (s.filter (fun q' => (⁅x, y⁆).SameCycle q q'))
    ((t.filter (fun q' => (⁅x, y⁆).SameCycle q q')).image y) := by
  simp_rw [Finset.disjoint_iff_ne, Finset.mem_image, Finset.mem_filter]
  intro a ⟨_, ⟨j, hj⟩⟩ b ⟨c, ⟨⟨_, ⟨k, hk⟩⟩, hcb⟩⟩
  rw [← hcb, ← hk, ← hj]
  exact cmtr_zpow_apply_ne_apply_cmtr_pow_apply hxy hy

lemma two_mul_filter_sameCycle_card_le_card [DecidableRel (⁅x, y⁆).SameCycle]
    (hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, y q ≠ q) (s : Finset α)
    (hsy : ∀ q, q ∈ s → y q ∈ s) (q : α) :
  2 * (s.filter (fun q' => (⁅x, y⁆).SameCycle q q')).card ≤ s.card := by
  rw [two_mul]
  classical
    nth_rewrite 2 [← Finset.card_image_of_injective _ (y.injective)]
    rw [← Finset.card_union_of_disjoint (cycleAt_cmtr_disjoint_image hxy hy q s s)]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.image_subset_iff.mpr (fun q' hq' => hsy _ (Finset.mem_of_mem_filter _ hq'))))

lemma cycleMin_cmtr_right_apply_eq_apply_cycleMin_cmtr [ConditionallyCompleteLinearOrderBot α]
    [IsWellOrder α (· < ·)](hxy : ⁅x, y⁻¹⁆ = ⁅x, y⁆) (hy : ∀ q : α, y q ≠ q)
    (hy₂ : ∀ {r q}, r < q → y q < y r → r = y q) :
CycleMin ⁅x, y⁆ (y q) = y (CycleMin ⁅x, y⁆ q) := by
  rcases (⁅x, y⁆).cycleMin_exists_zpow_apply q with ⟨j, hjq₂⟩
  refine eq_of_le_of_not_lt ?_ (fun h => ?_)
  let H : OrderBot α := inferInstance
  · refine (⁅x, y⁆).cycleMin_le  ⟨-j, ?_⟩
    simp_rw [zpow_neg, ← Perm.mul_apply, cmtr_zpow_inv_mul_eq_mul_inv_cmtr_zpow, hxy,
      Perm.mul_apply, hjq₂]
  · rcases (⁅x, y⁆).cycleMin_exists_zpow_apply (y q) with ⟨k, hkq₂⟩
    rw [←hkq₂, ← hjq₂, ← Perm.mul_apply, cmtr_zpow_mul_eq_mul_inv_cmtr_zpow_inv, Perm.mul_apply,
      hxy, ← zpow_neg] at h
    rcases lt_trichotomy ((⁅x, y⁆ ^ (-k)) q) ((⁅x, y⁆ ^ j) q) with H | H | H
    · exact ((⁅x, y⁆).cycleMin_le ⟨-k, rfl⟩).not_gt (hjq₂.symm ▸ H)
    · exact False.elim (lt_irrefl _ (H ▸ h))
    · exact cmtr_zpow_apply_ne_apply_cmtr_pow_apply hxy hy (hy₂ H h)
