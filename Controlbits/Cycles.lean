
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace Equiv.Perm
variable {π : Equiv.Perm α} [DecidableEq α] [Fintype α]

theorem cycleOf_pow_apply {β : Type v} [DecidableEq β] [Fintype β] (f : Equiv.Perm β)
(x : β) (y : β) (a : ℕ) :
((cycleOf f x)^a) y = if SameCycle f x y then (f^a) y else y := by
induction' a with a IH generalizing y
· simp_rw [pow_zero, one_apply, ite_self]
· simp_rw [pow_succ', mul_apply, IH, cycleOf_apply]
  by_cases h : f.SameCycle x y
  · simp only [h, ite_true, sameCycle_apply_right]
  · simp only [h, ite_false]

lemma eq_of_apply_pow_eq_of_lt_lt_orderOf_cycleOf (ha : a < orderOf (π.cycleOf x))
  (hb : b < orderOf (π.cycleOf x)) (hab: (π^a) x = (π^b) x) : a = b := by
  refine' pow_injective_of_lt_orderOf _ ha hb _
  ext y
  simp_rw [Equiv.Perm.cycleOf_pow_apply]
  by_cases h : Equiv.Perm.SameCycle π x y
  · simp_rw [h, ite_true]
    rcases h with ⟨c, rfl⟩
    simp_rw [← Perm.mul_apply, ← zpow_coe_nat, zpow_mul_comm, Perm.mul_apply, zpow_coe_nat, hab]
  · simp_rw [h, ite_false]

lemma zero_of_apply_pow_eq_self_of_lt_orderOf_cycleOf (ha : a < orderOf (π.cycleOf x))
  (hab: (π^a) x = x) : a = 0 :=
eq_of_apply_pow_eq_of_lt_lt_orderOf_cycleOf ha (orderOf_pos _) hab

lemma zero_of_apply_zpow_eq_self_of_lt_orderOf_cycleOf_of_nonneg (a : ℤ)
  (ha : a < orderOf (π.cycleOf x)) (hab: (π^a) x = x) (hn : 0 ≤ a) : a = 0 := by
  rcases Int.eq_ofNat_of_zero_le hn with ⟨a, rfl⟩
  rw [Nat.cast_eq_zero]
  rw [Nat.cast_lt] at ha
  exact zero_of_apply_pow_eq_self_of_lt_orderOf_cycleOf ha hab

end Equiv.Perm

section Perm
open Equiv
variable {α : Type u}  [DecidableEq α]  {π : Equiv.Perm α}

-- Definition 2.1

def CycleAt [DecidableEq α] [Fintype α] (π : Perm α) (x : α) : Finset α :=
  Finset.univ.filter fun y => π.SameCycle x y

variable [Fintype α]

open Finset

@[simp]
lemma mem_cycleAt_iff : y ∈ CycleAt π x ↔ π.SameCycle x y := by
  simp_rw [CycleAt, mem_filter, mem_univ, true_and]

lemma self_mem_cycleAt : x ∈ CycleAt π x :=
mem_cycleAt_iff.mpr ⟨0, rfl⟩

lemma apply_mem_cycleAt : π x ∈ CycleAt π x :=
mem_cycleAt_iff.mpr ⟨1, rfl⟩

lemma pow_apply_mem_cycleAt : (π^(k : ℕ)) x ∈ CycleAt π x :=
mem_cycleAt_iff.mpr ⟨k, rfl⟩

lemma pow_inv_apply_mem_cycleAt : (π^(k : ℕ))⁻¹ x ∈ CycleAt π x :=
mem_cycleAt_iff.mpr ⟨-k, by rw [zpow_neg, zpow_coe_nat]⟩

lemma zpow_apply_mem_cycleAt : (π^(k : ℤ)) x ∈ CycleAt π x :=
mem_cycleAt_iff.mpr ⟨k, rfl⟩

lemma cycleAt_nonempty : Finset.Nonempty (CycleAt π x) := ⟨x, self_mem_cycleAt⟩

lemma singleton_subset_cycleAt : {x} ⊆ CycleAt π x := by
  rintro y hy
  rw [Finset.mem_singleton] at hy
  rw [hy]
  exact self_mem_cycleAt

lemma cycleAt_of_fixed (h : Function.IsFixedPt π x) : CycleAt π x = {x} := by
  rw [← Nonempty.subset_singleton_iff cycleAt_nonempty]
  intros _ hx
  rw [mem_cycleAt_iff] at hx
  exact mem_singleton.mpr ((hx.eq_of_left h).symm)

lemma fixedPt_iff_cycleAt_singleton : Function.IsFixedPt π x ↔ CycleAt π x = {x} := by
refine ⟨?_, ?_⟩
· exact cycleAt_of_fixed
· rintro h
  have hx := apply_mem_cycleAt (π := π) (x := x)
  rw [h, Finset.mem_singleton] at hx
  exact hx

lemma card_cycleAt_ne_zero : (CycleAt π x).card ≠ 0 := Finset.card_ne_zero_of_mem self_mem_cycleAt

lemma card_cycleAt_pos : 0 < (CycleAt π x).card := cycleAt_nonempty.card_pos

lemma one_le_card_cycleAt : 1 ≤ (CycleAt π x).card := cycleAt_nonempty.card_pos

lemma card_cycleAt_eq_one_iff_fixedPt : Function.IsFixedPt π x ↔ (CycleAt π x).card = 1 := by
rw [Finset.card_eq_one, fixedPt_iff_cycleAt_singleton] ; refine ⟨?_, ?_⟩
· intro hx
  exact ⟨_, hx⟩
· have h := self_mem_cycleAt (π := π) (x := x)
  rintro ⟨y, hx⟩
  rw [hx] at h ⊢
  rw [mem_singleton, ← singleton_inj] at h
  exact h.symm

lemma cycleAt_apply_eq_cycleAt : CycleAt π (π x) = CycleAt π x := by
  simp_rw [Finset.ext_iff, mem_cycleAt_iff, Perm.sameCycle_apply_left, implies_true]

lemma mem_cycleAt_iff_lt : y ∈ CycleAt π x ↔ ∃ b, b < orderOf (π.cycleOf x) ∧ (π ^ b) x = y := by
  rw [mem_cycleAt_iff]
  refine ⟨?_, ?_⟩
  · rintro hb
    rcases (hb.exists_pow_eq π) with ⟨b, _, _, rfl⟩
    refine ⟨b % orderOf (π.cycleOf x), Nat.mod_lt _ (orderOf_pos _),
      (π.pow_apply_eq_pow_mod_orderOf_cycleOf_apply _ _).symm⟩
  · rintro ⟨b, _, rfl⟩
    exact ⟨b, rfl⟩

lemma mem_cycleAt_iff_le : y ∈ CycleAt π x ↔ ∃ b, b ≤ orderOf (π.cycleOf x) - 1 ∧ (π ^ b) x = y := by
  simp_rw [mem_cycleAt_iff_lt, Nat.lt_iff_le_pred (orderOf_pos _)]

def CycleAtTo (π : Equiv.Perm α) (x : α) (a : ℕ) : Finset α :=
(Finset.Iio a).image fun k => (π ^ k) x

@[simp]
lemma mem_cycleAtTo_iff : y ∈ CycleAtTo π x a ↔ ∃ b < a, (π ^ b) x = y := by
simp_rw [CycleAtTo, Finset.mem_image, Finset.mem_Iio]

lemma apply_pow_mem_cycleAtTo_of_lt (hba : b < a) : (π^b) x ∈ CycleAtTo π x a :=
mem_cycleAtTo_iff.mpr ⟨b, hba, rfl⟩

lemma apply_pow_mem_cycleAtTo_apply_pow_of_ge_of_lt (hba : b < a + c) (hcb : c ≤ b)  :
  (π^b) x ∈ CycleAtTo π ((π^c) x) a := by
rw [← tsub_add_cancel_of_le hcb, pow_add, Perm.mul_apply]
exact apply_pow_mem_cycleAtTo_of_lt (Nat.sub_lt_right_of_lt_add hcb hba)

lemma self_mem_cycleAtTo_iff (ha : 0 < a) : x ∈ CycleAtTo π x a :=
apply_pow_mem_cycleAtTo_of_lt ha

lemma cycleAtTo_nonempty_of_pos (ha : 0 < a) : Finset.Nonempty (CycleAtTo π x a) :=
⟨x, self_mem_cycleAtTo_iff ha⟩

lemma cycleAtTo_zero : CycleAtTo π x 0 = ∅ := by
  simp_rw [Finset.ext_iff, mem_cycleAtTo_iff, not_lt_zero', false_and, exists_false,
    not_mem_empty, implies_true]

lemma cycleAtTo_one : CycleAtTo π x 1 = {x} := by
  simp_rw [Finset.ext_iff, mem_cycleAtTo_iff, Nat.lt_one_iff, exists_eq_left, pow_zero,
    Perm.one_apply, mem_singleton, eq_comm, implies_true]

lemma cycleAtTo_singleton_of_fixedPt (ha : 0 < a) (h : Function.IsFixedPt π x) :
CycleAtTo π x a = {x} := by
  simp_rw [Finset.ext_iff, mem_singleton, mem_cycleAtTo_iff,
    π.pow_apply_eq_self_of_apply_eq_self h, eq_comm (a := x)]
  exact fun _ => ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨0, ha, h⟩⟩

lemma cycleAtTo_mono : Monotone (CycleAtTo π x) := by
  intros a b hab y h
  rw [mem_cycleAtTo_iff] at h ⊢
  rcases h with ⟨c, hca, hc⟩
  exact ⟨c, lt_of_lt_of_le hca hab, hc⟩

lemma card_cycleAtTo_le : (CycleAtTo π x a).card ≤ a := by
  convert Finset.card_image_le
  exact (Nat.card_Iio _).symm

lemma cycleAtTo_card_eq_of_le_orderOf_cycleOf (h : a ≤ orderOf (π.cycleOf x)) :
  (CycleAtTo π x a).card = a := by
  nth_rewrite 2 [← Nat.card_Iio a]
  apply Finset.card_image_iff.mpr
  intros b hb c hc hbc
  simp_rw [coe_Iio, Set.mem_Iio] at hb hc
  exact π.eq_of_apply_pow_eq_of_lt_lt_orderOf_cycleOf (lt_of_lt_of_le hb h) (lt_of_lt_of_le hc h) hbc

lemma cycleAtTo_subset_cycleAt : CycleAtTo π x a ⊆ CycleAt π x := by
  rintro y hy
  rcases (mem_cycleAtTo_iff.mp hy) with ⟨b, _, hb⟩
  exact mem_cycleAt_iff.mpr ⟨b, hb⟩

lemma cycleAt_eq_cycleAtTo_orderOf_cycleOf :
CycleAt π x = CycleAtTo π x (orderOf (π.cycleOf x)) := by
  simp_rw [Finset.ext_iff, mem_cycleAtTo_iff, mem_cycleAt_iff_lt, implies_true]

lemma cycleAt_card_eq_orderOf_cycleOf :
orderOf (π.cycleOf x) = (CycleAt π x).card := by
  simp_rw [cycleAt_eq_cycleAtTo_orderOf_cycleOf, cycleAtTo_card_eq_of_le_orderOf_cycleOf (le_refl _)]

lemma cycleAt_eq_cycleAtTo_ge_orderOf_cycleOf (ha : orderOf (π.cycleOf x) ≤ a) :
CycleAt π x = CycleAtTo π x a := by
refine le_antisymm ?_ ?_
· rw [cycleAt_eq_cycleAtTo_orderOf_cycleOf]
  exact cycleAtTo_mono ha
· exact cycleAtTo_subset_cycleAt

lemma insert_cycleAtTo_eq_succ (a : ℕ) (x) : insert ((π ^ a) x) (CycleAtTo π x a) =
  (CycleAtTo π x (a + 1)) := by
  ext y
  simp_rw [mem_insert, mem_cycleAtTo_iff, Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or,
    exists_eq_left, or_comm (a := y = (π ^ a) x), eq_comm (b := (π^a) x)]

lemma insert_cycleAtTo {a : ℕ} (hak : a ≤ k) (hkb : k < b) :
  insert ((π ^ k) x) (CycleAtTo π x a) ⊆ (CycleAtTo π x b) := by
  intros y hy
  rw [mem_insert] at hy
  rcases hy with (rfl | hy)
  · rw [mem_cycleAtTo_iff]
    exact ⟨k, hkb, rfl⟩
  · exact cycleAtTo_mono (lt_of_le_of_lt hak hkb).le hy

lemma pow_apply_not_mem_cycleAtTo_of_lt_orderOf_cycleOf (h : a < orderOf (π.cycleOf x)) :
(π^a) x ∉ CycleAtTo π x a := by
  intro h
  rw [mem_cycleAtTo_iff] at h
  rcases h with ⟨b, hb, hbx⟩
  exact hb.ne (π.eq_of_apply_pow_eq_of_lt_lt_orderOf_cycleOf (hb.trans h) h hbx)

lemma cycleAtTo_strict_mono (ha : a < orderOf (π.cycleOf x)) (hab : a < b) :
CycleAtTo π x a ⊂ CycleAtTo π x b := by
rw [Finset.ssubset_iff]
exact ⟨_, pow_apply_not_mem_cycleAtTo_of_lt_orderOf_cycleOf ha, insert_cycleAtTo (le_refl _) hab⟩

lemma cycleAt_gt_cycleAtTo_lt_orderOf_cycleOf (h : a < orderOf (π.cycleOf x)) :
CycleAtTo π x a ⊂ CycleAt π x := by
  rw [cycleAt_eq_cycleAtTo_orderOf_cycleOf]
  exact cycleAtTo_strict_mono h h

-- Definition 2.3

def CycleMin [LinearOrder α] (π : Equiv.Perm α) (x : α) : α := (CycleAt π x).min' (cycleAt_nonempty)

section LinearOrder
variable [LinearOrder α]

lemma cycleMin_def : CycleMin π x = (CycleAt π x).min' cycleAt_nonempty := rfl

lemma cycleMin_eq_min_cycleAtTo :
CycleMin π x = (CycleAtTo π x (orderOf (π.cycleOf x))).min' (cycleAtTo_nonempty_of_pos (orderOf_pos _)) := by
  simp_rw [cycleMin_def, cycleAt_eq_cycleAtTo_orderOf_cycleOf]

@[simp]
lemma cycleMin_of_fixed (h : Function.IsFixedPt π x) : CycleMin π x = x := by
  simp_rw [cycleMin_eq_min_cycleAtTo, π.cycleOf_eq_one_iff.mpr h, orderOf_one,
    cycleAtTo_one, min'_singleton]

lemma cycleMin_mem_cycleAt (π : Equiv.Perm α) (x : α) : CycleMin π x ∈ CycleAt π x := Finset.min'_mem _ _

lemma cycleMin_exists_pow_apply (π : Equiv.Perm α) (x : α):
∃ k : ℤ, (π^k) x = CycleMin π x :=
mem_cycleAt_iff.mp (cycleMin_mem_cycleAt π x)

lemma cycleMin_exists_pow_apply'' (π : Equiv.Perm α) (x : α):
∃ k, k ≤ (orderOf (π.cycleOf x)) - 1 ∧ (π^k) x = CycleMin π x :=
mem_cycleAt_iff_le.mp (cycleMin_mem_cycleAt π x)

lemma cycleMin_exists_pow_apply' (π : Equiv.Perm α) (x : α):
∃ k, k < orderOf (π.cycleOf x) ∧ (π^k) x = CycleMin π x :=
mem_cycleAt_iff_lt.mp (cycleMin_mem_cycleAt π x)

lemma cycleMin_eq_min_cycleAtTo_ge (ha : orderOf (π.cycleOf x) ≤ a) :
CycleMin π x = (CycleAtTo π x a).min' cycleAtTo_nonempty := by
simp_rw [cycleMin_def, cycleAt_eq_cycleAtTo_ge_orderOf_cycleOf ha]

lemma cycleMin_le (π : Equiv.Perm α) (x : α) (h : π.SameCycle x y) : CycleMin π x ≤ y := by
  rw [cycleMin_def]
  exact Finset.min'_le _ y (mem_cycleAt_iff.mpr h)

lemma cycleMin_le_self : CycleMin π x ≤ x := cycleMin_le π x ⟨0, rfl⟩

@[simp]
lemma cycleMin_bot [OrderBot α] : CycleMin π ⊥ = ⊥ := le_antisymm cycleMin_le_self bot_le

lemma cycleMin_refl : CycleMin (Equiv.refl α) x = x := cycleMin_of_fixed rfl

lemma cycleMin_one : CycleMin (1 : Equiv.Perm α) x = x := cycleMin_refl

lemma le_cycleMin (h : ∀ y, π.SameCycle x y → z ≤ y) : z ≤ CycleMin π x  := by
simp_rw [cycleMin_def, Finset.le_min'_iff, mem_cycleAt_iff] ; exact h

lemma le_cycleMin_iff : z ≤ CycleMin π x ↔ ∀ y, π.SameCycle x y → z ≤ y := by
simp_rw [cycleMin_def, Finset.le_min'_iff, mem_cycleAt_iff]

def FastCycleMin (n : ℕ) (π : Equiv.Perm α) (x : α) : α :=
  match n with
  | 0 => x
  | (i+1) => min (FastCycleMin i π x) (FastCycleMin i π ((π ^ (2^i : ℕ)) x))

lemma fastCycleMin_zero_eq : FastCycleMin 0 π x = x := rfl

lemma fastCycleMin_succ_eq :
FastCycleMin (i + 1) π x = min (FastCycleMin i π x) (FastCycleMin i π ((π ^ (2^i : ℕ)) x)) := rfl

-- Theorem 2.4

lemma fastCycleMin_eq_min_cycleAtTo :
FastCycleMin i π x = (CycleAtTo π x (2^i)).min' (cycleAtTo_nonempty_of_pos (pow_pos zero_lt_two _)) := by
  induction' i with i hi generalizing x
  · simp_rw [fastCycleMin_zero_eq, pow_zero, cycleAtTo_one, min'_singleton]
  · simp_rw [fastCycleMin_succ_eq, hi, le_antisymm_iff, le_min_iff, Finset.le_min'_iff, min_le_iff,
      mem_cycleAtTo_iff, Nat.pow_succ', Nat.two_mul, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, ← forall_and, ← Equiv.Perm.mul_apply, ← pow_add, imp_and]
    refine' fun b => And.intro (fun h => (lt_or_le b (2^i)).imp _ _) (And.intro _ _) <;>
    refine' fun hb => min'_le _ _ _
    · exact apply_pow_mem_cycleAtTo_of_lt hb
    · exact apply_pow_mem_cycleAtTo_apply_pow_of_ge_of_lt h hb
    · exact apply_pow_mem_cycleAtTo_of_lt (lt_of_lt_of_le hb le_self_add)
    · exact apply_pow_mem_cycleAtTo_of_lt ((add_lt_add_iff_right _).mpr hb)

-- Theorem 2.5

lemma cycleMin_eq_fastCycleMin (h : orderOf (π.cycleOf x) ≤ 2^i) : FastCycleMin i π x = CycleMin π x := by
  rw [fastCycleMin_eq_min_cycleAtTo, cycleMin_eq_min_cycleAtTo_ge h]

-- Theorem 2.2
lemma cycleMin_eq_cycleMin_apply : CycleMin π x = CycleMin π (π x) := by
  simp_rw [cycleMin_def, cycleAt_apply_eq_cycleAt]

lemma cycleMin_eq_cycleMin_apply_inv : CycleMin π x = CycleMin π (π⁻¹ x) := by
rw [cycleMin_eq_cycleMin_apply (x := (π⁻¹ x)), Equiv.Perm.apply_inv_self]

end LinearOrder

section CanonicallyLinearOrderedMonoid

@[simp]
lemma cycleMin_zero [CanonicallyLinearOrderedAddMonoid α] : CycleMin π 0 = 0 :=
le_antisymm cycleMin_le_self (zero_le _)

end CanonicallyLinearOrderedMonoid

section Fin

@[simp]
lemma Fin.cycleMin_zero {τ : Equiv.Perm (Fin m)} [NeZero m] : CycleMin τ 0 = (0 : Fin m) :=
le_antisymm cycleMin_le_self (Fin.zero_le' _)

end Fin

end Perm