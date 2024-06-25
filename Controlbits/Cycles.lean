
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace Equiv.Perm

def FastCycleMin {α : Type*} [Min α] (n : ℕ) (π : Equiv.Perm α) : α → α :=
  match n with
  | 0 => id
  | (i+1) => fun x => min (FastCycleMin i π x) (FastCycleMin i π ((π ^ (2^i : ℕ)) x))

section FastCycleMin
variable {α : Type*} {x : α} {π : Perm α}

section Min

variable [Min α]

@[simp]
lemma fastCycleMin_zero : FastCycleMin 0 π x = x := rfl

@[simp]
lemma fastCycleMin_succ :
FastCycleMin (i + 1) π x = min (FastCycleMin i π x) (FastCycleMin i π ((π ^ (2^i : ℕ)) x)) := rfl

end Min

section LinearOrder

variable [LinearOrder α]

lemma fastCycleMin_le (h : k < 2^i) : FastCycleMin i π x ≤ (π ^ k) x := by
  induction' i with i IH generalizing x k
  · rw [pow_zero, Nat.lt_one_iff] at h
    simp_rw [fastCycleMin_zero, h, pow_zero, one_apply, le_rfl]
  · rw [pow_succ', two_mul] at h
    simp_rw [fastCycleMin_succ, min_le_iff]
    rcases lt_or_le k (2^i) with hk | hk
    · exact Or.inl (IH hk)
    · rw [← Nat.sub_lt_iff_lt_add hk] at h
      convert Or.inr (IH h) using 2
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hk]

lemma exists_lt_fastCycleMin_eq_pow_apply (x : α) (i : ℕ) :
    ∃ k < 2^i, (π ^ k) x = FastCycleMin i π x := by
  simp_rw [eq_comm]
  induction' i with i IH generalizing x
  · exact ⟨0, Nat.two_pow_pos _, rfl⟩
  · rcases (IH (x := x)) with ⟨k, hk, hπk⟩
    rcases (IH (x := (π ^ (2 ^ i)) x)) with ⟨k', hk', hπk'⟩
    simp_rw [fastCycleMin_succ, min_eq_iff, hπk, hπk', ← Equiv.Perm.mul_apply, ← pow_add,
    pow_succ', two_mul]
    rcases lt_or_le ((π ^ k) x) ((π ^ (k' + 2 ^ i)) x) with hkk' | hkk'
    · exact ⟨k, hk.trans (Nat.lt_add_of_pos_right (Nat.two_pow_pos _)),
        Or.inl ⟨rfl, hkk'.le⟩⟩
    · exact ⟨k' + 2^i, Nat.add_lt_add_right hk' _, Or.inr ⟨rfl, hkk'⟩⟩

lemma sameCycle_fastCycleMin : π.SameCycle x (FastCycleMin i π x) := by
  rcases π.exists_lt_fastCycleMin_eq_pow_apply x i with ⟨k, _, hk⟩
  exact ⟨k, hk⟩

-- Theorem 2.4

lemma fastCycleMin_eq_min'_image_interval [DecidableEq α] : FastCycleMin i π x =
    ((Finset.Iio (2^i)).image fun k => (π ^ k) x).min'
    ((Finset.nonempty_Iio.mpr (not_isMin_of_lt (Nat.two_pow_pos _))).image _) := by
  refine' le_antisymm _ (Finset.min'_le _ _ _)
  · simp_rw [Finset.le_min'_iff, Finset.mem_image, Finset.mem_Iio, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
    exact fun _ => fastCycleMin_le
  · simp_rw [Finset.mem_image, Finset.mem_Iio]
    exact exists_lt_fastCycleMin_eq_pow_apply x i

end LinearOrder

end FastCycleMin

section CycleMin

variable {α : Type*} {π : Equiv.Perm α} {x y : α}

lemma sameCycle_nonempty : Set.Nonempty (π.SameCycle x ·) := ⟨x, ⟨0, rfl⟩⟩

def CycleMin [InfSet α] (π : Equiv.Perm α) (x : α) : α := sInf (π.SameCycle x ·)

section InfSet

variable [InfSet α]

lemma cycleMin_def : CycleMin π x = sInf (π.SameCycle x ·) := rfl

-- Theorem 2.2
lemma cycleMin_eq_cycleMin_apply : CycleMin π x = CycleMin π (π x) := by
  simp_rw [cycleMin_def]
  convert rfl using 3 with y
  rw [sameCycle_apply_left]

lemma cycleMin_eq_cycleMin_apply_inv : CycleMin π x = CycleMin π (π⁻¹ x) := by
rw [cycleMin_eq_cycleMin_apply (x := (π⁻¹ x)), Equiv.Perm.apply_inv_self]

end InfSet

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]

@[simp]
lemma cycleMin_of_fixed (h : Function.IsFixedPt π x) : π.CycleMin x = x := by
  rw [cycleMin_def]
  convert csInf_singleton x using 2
  rw [Set.eq_singleton_iff_unique_mem]
  exact ⟨⟨0, rfl⟩, fun _ hy => (SameCycle.symm hy).eq_of_right h⟩

lemma cycleMin_refl : CycleMin (Equiv.refl α) x = x := cycleMin_of_fixed rfl

lemma cycleMin_one : CycleMin (1 : Equiv.Perm α) x = x := cycleMin_refl

lemma le_cycleMin (h : ∀ y, π.SameCycle x y → z ≤ y) : z ≤ CycleMin π x := le_csInf ⟨x, ⟨0, rfl⟩⟩ h

--simp_rw [cycleMin_def, Finset.le_min'_iff, mem_cycleAt_iff] ; exact h

section BddBelow

variable (hsb : BddBelow (π.SameCycle x ·))

lemma cycleMin_le_of_bddBelow_sameCycle (h : π.SameCycle x y) : CycleMin π x ≤ y := by
  rw [cycleMin_def]
  exact csInf_le hsb h

lemma cycleMin_le_of_le_of_bddBelow_sameCycle (h : π.SameCycle x y) (hy : y ≤ a) :
    CycleMin π x ≤ a := (cycleMin_le_of_bddBelow_sameCycle hsb h).trans hy

lemma cycleMin_le_zpow_apply_of_bddBelow_sameCycle (k : ℤ) : CycleMin π x ≤ (π^k) x :=
  cycleMin_le_of_bddBelow_sameCycle hsb ⟨k, rfl⟩

lemma cycleMin_le_pow_apply_of_bddBelow_sameCycle (n : ℕ) : CycleMin π x ≤ (π^n) x :=
  cycleMin_le_of_bddBelow_sameCycle hsb ⟨n, rfl⟩

lemma cycleMin_le_self_of_bddBelow_sameCycle : CycleMin π x ≤ x :=
  cycleMin_le_zpow_apply_of_bddBelow_sameCycle hsb 0

lemma le_cycleMin_iff_of_bddBelow_sameCycle :
  z ≤ CycleMin π x ↔ ∀ y, π.SameCycle x y → z ≤ y := le_csInf_iff hsb sameCycle_nonempty

end BddBelow

section OrderBot

variable [OrderBot α]

lemma cycleMin_le (h : π.SameCycle x y) : CycleMin π x ≤ y := by
  rw [cycleMin_def]
  exact csInf_le (OrderBot.bddBelow _) h

lemma cycleMin_le_of_le (h : π.SameCycle x y) (hy : y ≤ a) : CycleMin π x ≤ a :=
  (cycleMin_le h).trans hy

lemma cycleMin_le_zpow_apply (k : ℤ) : CycleMin π x ≤ (π^k) x :=
  cycleMin_le ⟨k, rfl⟩

lemma cycleMin_le_pow_apply (n : ℕ) : CycleMin π x ≤ (π^n) x :=
  cycleMin_le ⟨n, rfl⟩

lemma cycleMin_le_self : CycleMin π x ≤ x := cycleMin_le_zpow_apply 0

lemma le_cycleMin_iff : z ≤ CycleMin π x ↔ ∀ y, π.SameCycle x y → z ≤ y :=
  le_cycleMin_iff_of_bddBelow_sameCycle (OrderBot.bddBelow _)

@[simp]
lemma cycleMin_bot : CycleMin π ⊥ = ⊥ :=
  le_antisymm cycleMin_le_self bot_le

end OrderBot

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [IsWellOrder α (· < ·)]

lemma sameCycle_cycleMin (x : α) : π.SameCycle x (CycleMin π x) := csInf_mem sameCycle_nonempty

lemma cycleMin_exists_zpow_apply (x : α) : ∃ k : ℤ, (π^k) x = CycleMin π x :=
  π.sameCycle_cycleMin x

lemma cycleMin_exists_pow_apply_of_finite_order (hn : n > 0) (hnx : (π^n) x = x) :
    ∃ k < n, (π^k) x = CycleMin π x := by
  suffices h : ∃ k, (π ^ k) x = π.CycleMin x by
    rcases h with ⟨k, hk⟩
    refine' ⟨k % n, Nat.mod_lt _ hn, (hk.symm.trans _).symm⟩
    nth_rewrite 1 [← Nat.div_add_mod k n, add_comm, pow_add, mul_apply, pow_mul]
    exact congrArg _ (Function.IsFixedPt.perm_pow hnx _)
  rcases π.cycleMin_exists_zpow_apply x with ⟨k | k, hk⟩
  · exact ⟨k, hk⟩
  · refine' ⟨(n - (k + 1) % n) , _⟩
    rw [zpow_negSucc] at hk
    nth_rewrite 1 [← hk, Equiv.Perm.eq_inv_iff_eq, ← mul_apply, ← pow_add,
      ← Nat.div_add_mod (k + 1) n, add_assoc, Nat.add_sub_cancel' (Nat.mod_lt _ hn).le,
      ← Nat.mul_succ, pow_mul]
    exact Function.IsFixedPt.perm_pow hnx _

section BddBelow

variable (hsb : BddBelow (π.SameCycle x ·))

lemma cycleMin_le_fastCycleMin_of_bddBelow_sameCycle :
    CycleMin π x ≤ FastCycleMin i π x := by
  rcases π.exists_lt_fastCycleMin_eq_pow_apply x i with ⟨k, _, hkx⟩
  rw [← hkx]
  exact cycleMin_le_of_bddBelow_sameCycle hsb ⟨k, rfl⟩

end BddBelow

end ConditionallyCompleteLinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α] [IsWellOrder α (· < ·)]

lemma cycleMin_le_fastCycleMin : CycleMin π x ≤ FastCycleMin i π x := by
  rcases π.exists_lt_fastCycleMin_eq_pow_apply x i with ⟨k, _, hkx⟩
  rw [← hkx]
  exact cycleMin_le ⟨k, rfl⟩

lemma cycleMin_eq_fastCycleMin (hn : n > 0) (hn' : n ≤ 2^i) (hnx : (π^n) x = x) :
    FastCycleMin i π x = CycleMin π x := by
  refine' le_antisymm _ cycleMin_le_fastCycleMin
  rcases π.cycleMin_exists_pow_apply_of_finite_order hn hnx with ⟨k, hk, hkx⟩
  rw [← hkx]
  exact fastCycleMin_le (hk.trans_le hn')

lemma blahj (s : Finset α) (π : Equiv.Perm α) (x : α) (hsx : ∀ x, x ∈ s ↔ π x ∈ s)
  (hx : x ∈ s) :
    ∃ k, (k > 0 ∧ k ≤ s.card ∧ (π^k) x = x) := by
  induction' s using Finset.induction with a s has IH
  · simp only [Finset.not_mem_empty, forall_const] at hsx
  · simp [has] at *
    have H : ∀ x, x ∈ s ↔ π x ∈ s := by
      intro x
      specialize hsx x
    by_cases H : ∀ x, x ∈ s ↔ π x ∈ s
    · rcases IH H with ⟨k, hk₁, hk₂, hk₃⟩
      exact ⟨k, hk₁, (hk₂.trans (Nat.le_succ _)), hk₃⟩
    · simp_rw [not_forall, not_iff] at H
      rcases H with ⟨c, hk⟩
      specialize hsx c
      rw [← not_iff_not, not_or, not_or, hk] at hsx
      simp [hk] at hsx
      simp_rw [hk, or_false] at hsx

lemma cycleMin_eq_fastCycleMin_of_mem_finset (s : Finset α)
  (hsi : s.card ≤ 2^i) (hx : ∀ (k : ℤ), (π^k) x ∈ s) : FastCycleMin i π x = CycleMin π x := by
  have h : ∃ k, (k > 0 ∧ k ≤ s.card ∧ (π^k) x = x) := blahj _
  rcases h with ⟨k, hk, hk', hkx⟩
  refine' cycleMin_eq_fastCycleMin hk (hk'.trans hsi) hkx

end ConditionallyCompleteLinearOrderBot

-- Theorem 2.5







/-
lemma cycleMin_eq_min_cycleAtTo :
CycleMin π x = (CycleAtTo π (orderOf (π.cycleOf x)) x).min' (cycleAtTo_nonempty_of_pos (orderOf_pos _)) := by
  simp_rw [cycleMin_def, cycleAt_eq_cycleAtTo_orderOf_cycleOf]
-/

/-
lemma cycleMin_mem_cycleAt (π : Equiv.Perm α) (x : α) : CycleMin π x ∈ CycleAt π x := Finset.min'_mem _ _
-/



lemma cycleMin_exists_pow_apply'' (π : Equiv.Perm α) (x : α) :
    ∃ k, k ≤ (orderOf (π.cycleOf x)) - 1 ∧ (π^k) x = CycleMin π x :=
mem_cycleAt_iff_le.mp (cycleMin_mem_cycleAt π x)

lemma cycleMin_exists_pow_apply' (π : Equiv.Perm α) (x : α):
∃ k, k < orderOf (π.cycleOf x) ∧ (π^k) x = CycleMin π x :=
mem_cycleAt_iff_lt.mp (cycleMin_mem_cycleAt π x)

lemma cycleMin_eq_min_cycleAtTo_ge (ha : orderOf (π.cycleOf x) ≤ a) :
CycleMin π x = (CycleAtTo π a x).min' cycleAtTo_nonempty := by
simp_rw [cycleMin_def, cycleAt_eq_cycleAtTo_ge_orderOf_cycleOf ha]







end LinearOrder

section CanonicallyLinearOrderedMonoid

@[simp]
lemma cycleMin_zero [CanonicallyLinearOrderedAddCommMonoid α] : CycleMin π 0 = 0 :=
le_antisymm cycleMin_le_self (zero_le _)

end CanonicallyLinearOrderedMonoid

section Fin

@[simp]
lemma Fin.cycleMin_zero {τ : Equiv.Perm (Fin m)} [NeZero m] : CycleMin τ 0 = (0 : Fin m) :=
le_antisymm cycleMin_le_self (Fin.zero_le' _)

end Fin


end CycleMin

variable {π : Equiv.Perm α} [DecidableEq α] [Fintype α]

theorem cycleOf_pow_apply {β : Type v} [DecidableEq β] [Fintype β] (f : Equiv.Perm β)
(x : β) (y : β) (a : ℕ) :
((cycleOf f x)^a) y = if SameCycle f x y then (f^a) y else y := by
induction' a with a IH generalizing y
· simp_rw [pow_zero, one_apply, ite_self]
· simp_rw [pow_succ', mul_apply, IH, cycleOf_apply]
  by_cases h : f.SameCycle x y
  · simp only [h, ↓reduceIte, sameCycle_pow_right]
  · simp only [h, ↓reduceIte]

lemma pow_apply_injOn_Iio_orderOf_cycleOf [DecidableEq α] [Fintype α] {π : Equiv.Perm α}
  {x : α} : (Set.Iio $ orderOf (π.cycleOf x)).InjOn (fun t => (π ^ t) x) := by
  rintro a ha b hb hab
  refine' pow_injOn_Iio_orderOf ha hb (ext (fun y => _))
  simp_rw [cycleOf_pow_apply]
  by_cases h : SameCycle π x y
  · simp_rw [h, ite_true]
    rcases h with ⟨c, rfl⟩
    simp_rw [← zpow_natCast, zpow_apply_comm, zpow_natCast, hab]
  · simp_rw [h, ite_false]

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

lemma mem_cycleAt_iff_zpow : y ∈ CycleAt π x ↔ ∃ k : ℤ, (π^k) x = y := by
  simp_rw [mem_cycleAt_iff]
  rfl

lemma zpow_apply_mem_cycleAt (k : ℤ) : (π^k) x ∈ CycleAt π x :=
mem_cycleAt_iff.mpr ⟨k, rfl⟩

lemma pow_apply_mem_cycleAt (n : ℕ) : (π^n) x ∈ CycleAt π x :=
zpow_apply_mem_cycleAt n

lemma pow_inv_apply_mem_cycleAt (n : ℕ) : (π^n)⁻¹ x ∈ CycleAt π x :=
mem_cycleAt_iff.mpr ⟨-n, zpow_neg π n ▸ rfl⟩

lemma self_mem_cycleAt : x ∈ CycleAt π x := pow_apply_mem_cycleAt 0

lemma apply_mem_cycleAt : π x ∈ CycleAt π x := pow_apply_mem_cycleAt 1

lemma cycleAt_nonempty : Finset.Nonempty (CycleAt π x) := ⟨x, self_mem_cycleAt⟩

lemma singleton_subset_cycleAt : {x} ⊆ CycleAt π x :=
  fun _ hy => (eq_of_mem_singleton hy) ▸ self_mem_cycleAt

lemma cycleAt_of_fixed (h : Function.IsFixedPt π x) : CycleAt π x = {x} := by
  simp_rw [Finset.ext_iff, mem_cycleAt_iff_zpow, mem_singleton, (fun k => (h.perm_zpow k).eq),
  exists_const, eq_comm, implies_true]

lemma fixedPt_iff_cycleAt_singleton : Function.IsFixedPt π x ↔ CycleAt π x = {x} :=
  ⟨cycleAt_of_fixed, fun h => eq_of_mem_singleton (h ▸ apply_mem_cycleAt)⟩

lemma card_cycleAt_ne_zero : (CycleAt π x).card ≠ 0 := Finset.card_ne_zero_of_mem self_mem_cycleAt

lemma card_cycleAt_pos : 0 < (CycleAt π x).card := cycleAt_nonempty.card_pos

lemma one_le_card_cycleAt : 1 ≤ (CycleAt π x).card := cycleAt_nonempty.card_pos

lemma card_cycleAt_eq_one_iff_fixedPt : Function.IsFixedPt π x ↔ (CycleAt π x).card = 1 := by
  rw [Finset.card_eq_one, fixedPt_iff_cycleAt_singleton]
  refine ⟨fun hx => ⟨_, hx⟩, ?_⟩
  rintro ⟨_, hx⟩
  rw [hx, singleton_inj, eq_comm, ← mem_singleton, ← hx]
  exact self_mem_cycleAt

lemma cycleAt_apply_eq_cycleAt : CycleAt π (π x) = CycleAt π x := by
  simp_rw [Finset.ext_iff, mem_cycleAt_iff, Perm.sameCycle_apply_left, implies_true]

lemma mem_cycleAt_iff_lt : y ∈ CycleAt π x ↔ ∃ b, b < orderOf (π.cycleOf x) ∧ (π ^ b) x = y := by
  rw [mem_cycleAt_iff]
  refine ⟨?_, ?_⟩
  · rintro hb
    rcases (hb.exists_pow_eq π) with ⟨b, _, _, rfl⟩
    refine ⟨b % orderOf (π.cycleOf x), Nat.mod_lt _ (orderOf_pos _),
      (π.pow_mod_orderOf_cycleOf_apply _ _)⟩
  · rintro ⟨b, _, rfl⟩
    exact ⟨b, rfl⟩

lemma mem_cycleAt_iff_le : y ∈ CycleAt π x ↔ ∃ b, b ≤ orderOf (π.cycleOf x) - 1 ∧ (π ^ b) x = y := by
  simp_rw [mem_cycleAt_iff_lt, Nat.lt_iff_le_pred (orderOf_pos _)]

def CycleAtTo (π : Equiv.Perm α) (a : ℕ) (x : α) : Finset α :=
(Finset.Iio a).image fun k => (π ^ k) x

@[simp]
lemma mem_cycleAtTo_iff : y ∈ CycleAtTo π a x ↔ ∃ b < a, (π ^ b) x = y := by
simp_rw [CycleAtTo, Finset.mem_image, Finset.mem_Iio]

lemma apply_pow_mem_cycleAtTo_of_lt (hba : b < a) : (π^b) x ∈ CycleAtTo π a x :=
mem_cycleAtTo_iff.mpr ⟨b, hba, rfl⟩

lemma apply_pow_mem_cycleAtTo_apply_pow_of_ge_of_lt (hba : b < a + c) (hcb : c ≤ b)  :
  (π^b) x ∈ CycleAtTo π a ((π^c) x) := by
rw [← tsub_add_cancel_of_le hcb, pow_add, Perm.mul_apply]
exact apply_pow_mem_cycleAtTo_of_lt (Nat.sub_lt_right_of_lt_add hcb hba)

lemma self_mem_cycleAtTo_iff (ha : 0 < a) : x ∈ CycleAtTo π a x :=
apply_pow_mem_cycleAtTo_of_lt ha

lemma cycleAtTo_nonempty_of_pos (ha : 0 < a) : Finset.Nonempty (CycleAtTo π a x) :=
⟨x, self_mem_cycleAtTo_iff ha⟩

lemma cycleAtTo_zero : CycleAtTo π 0 x = ∅ := by
  simp_rw [Finset.ext_iff, mem_cycleAtTo_iff, not_lt_zero', false_and, exists_false,
    not_mem_empty, implies_true]

lemma cycleAtTo_one : CycleAtTo π 1 x = {x} := by
  simp_rw [Finset.ext_iff, mem_cycleAtTo_iff, Nat.lt_one_iff, exists_eq_left, pow_zero,
    Perm.one_apply, mem_singleton, eq_comm, implies_true]

lemma cycleAtTo_singleton_of_fixedPt (ha : 0 < a) (h : Function.IsFixedPt π x) :
CycleAtTo π a x = {x} := by
  simp_rw [Finset.ext_iff, mem_singleton, mem_cycleAtTo_iff,
    π.pow_apply_eq_self_of_apply_eq_self h, eq_comm (a := x)]
  exact fun _ => ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨0, ha, h⟩⟩

lemma cycleAtTo_mono : Monotone (CycleAtTo π ·) := by
  intros a b hab x y h
  rw [mem_cycleAtTo_iff] at h ⊢
  rcases h with ⟨c, hca, hc⟩
  exact ⟨c, lt_of_lt_of_le hca hab, hc⟩

lemma cycleAtTo_of_mono : Monotone (CycleAtTo π · x) :=
  fun _ _ hab _ h => cycleAtTo_mono hab _ h

lemma card_cycleAtTo_le : (CycleAtTo π a x).card ≤ a := by
  convert Finset.card_image_le
  exact (Nat.card_Iio _).symm

lemma cycleAtTo_card_eq_of_le_orderOf_cycleOf (h : a ≤ orderOf (π.cycleOf x)) :
  (CycleAtTo π a x).card = a := by
  nth_rewrite 2 [← Nat.card_Iio a]
  apply Finset.card_image_iff.mpr
  intros b hb c hc hbc
  simp_rw [coe_Iio, Set.mem_Iio] at hb hc
  exact π.pow_apply_injOn_Iio_orderOf_cycleOf (lt_of_lt_of_le hb h) (lt_of_lt_of_le hc h) hbc

lemma cycleAtTo_subset_cycleAt : CycleAtTo π a x ⊆ CycleAt π x := by
  rintro y hy
  rcases (mem_cycleAtTo_iff.mp hy) with ⟨b, _, hb⟩
  exact mem_cycleAt_iff.mpr ⟨b, hb⟩

lemma cycleAt_eq_cycleAtTo_orderOf_cycleOf :
CycleAt π x = CycleAtTo π (orderOf (π.cycleOf x)) x := by
  simp_rw [Finset.ext_iff, mem_cycleAtTo_iff, mem_cycleAt_iff_lt, implies_true]

lemma cycleAt_card_eq_orderOf_cycleOf :
orderOf (π.cycleOf x) = (CycleAt π x).card := by
  simp_rw [cycleAt_eq_cycleAtTo_orderOf_cycleOf, cycleAtTo_card_eq_of_le_orderOf_cycleOf (le_refl _)]

lemma cycleAt_eq_cycleAtTo_ge_orderOf_cycleOf (ha : orderOf (π.cycleOf x) ≤ a) :
CycleAt π x = CycleAtTo π a x := by
refine le_antisymm ?_ ?_
· rw [cycleAt_eq_cycleAtTo_orderOf_cycleOf]
  exact cycleAtTo_of_mono ha
· exact cycleAtTo_subset_cycleAt

lemma insert_cycleAtTo_eq_succ (a : ℕ) (x) : insert ((π ^ a) x) (CycleAtTo π a x) =
  (CycleAtTo π (a + 1) x) := by
  ext y
  simp_rw [mem_insert, mem_cycleAtTo_iff, Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or,
    exists_eq_left, or_comm (a := y = (π ^ a) x), eq_comm (b := (π^a) x)]

lemma insert_cycleAtTo {a : ℕ} (hak : a ≤ k) (hkb : k < b) :
  insert ((π ^ k) x) (CycleAtTo π a x) ⊆ (CycleAtTo π b x) := by
  intros y hy
  rw [mem_insert] at hy
  rcases hy with (rfl | hy)
  · rw [mem_cycleAtTo_iff]
    exact ⟨k, hkb, rfl⟩
  · exact cycleAtTo_of_mono (lt_of_le_of_lt hak hkb).le hy

lemma pow_apply_not_mem_cycleAtTo_of_lt_orderOf_cycleOf (h : a < orderOf (π.cycleOf x)) :
(π^a) x ∉ CycleAtTo π a x := by
  intro h
  rw [mem_cycleAtTo_iff] at h
  rcases h with ⟨b, hb, hbx⟩
  exact hb.ne (π.pow_apply_injOn_Iio_orderOf_cycleOf (hb.trans h) h hbx)

lemma cycleAtTo_strict_mono_lt_of_lt_lt_orderOf (ha : a < orderOf (π.cycleOf x)) (hab : a < b) :
CycleAtTo π a x ⊂ CycleAtTo π b x := by
rw [Finset.ssubset_iff]
exact ⟨_, pow_apply_not_mem_cycleAtTo_of_lt_orderOf_cycleOf ha, insert_cycleAtTo (le_refl _) hab⟩

lemma cycleAt_gt_cycleAtTo_lt_orderOf_cycleOf (h : a < orderOf (π.cycleOf x)) :
CycleAtTo π a x ⊂ CycleAt π x := by
  rw [cycleAt_eq_cycleAtTo_orderOf_cycleOf]
  exact cycleAtTo_strict_mono_lt_of_lt_lt_orderOf h h

-- Definition 2.3

def CycleMin [LinearOrder α] (π : Equiv.Perm α) (x : α) : α := (CycleAt π x).min' cycleAt_nonempty

section LinearOrder
variable [LinearOrder α]

lemma cycleMin_def : CycleMin π x = (CycleAt π x).min' cycleAt_nonempty := rfl

lemma cycleMin_eq_min_cycleAtTo :
CycleMin π x = (CycleAtTo π (orderOf (π.cycleOf x)) x).min' (cycleAtTo_nonempty_of_pos (orderOf_pos _)) := by
  simp_rw [cycleMin_def, cycleAt_eq_cycleAtTo_orderOf_cycleOf]

@[simp]
lemma cycleMin_of_fixed (h : Function.IsFixedPt π x) : CycleMin π x = x := by
  simp_rw [cycleMin_eq_min_cycleAtTo, π.cycleOf_eq_one_iff.mpr h, orderOf_one,
    cycleAtTo_one, min'_singleton]

lemma cycleMin_mem_cycleAt (π : Equiv.Perm α) (x : α) : CycleMin π x ∈ CycleAt π x := Finset.min'_mem _ _

lemma cycleMin_exists_pow_apply (π : Equiv.Perm α) (x : α) : ∃ k : ℤ, (π^k) x = CycleMin π x :=
mem_cycleAt_iff.mp (cycleMin_mem_cycleAt π x)

lemma cycleMin_exists_pow_apply'' (π : Equiv.Perm α) (x : α) :
    ∃ k, k ≤ (orderOf (π.cycleOf x)) - 1 ∧ (π^k) x = CycleMin π x :=
mem_cycleAt_iff_le.mp (cycleMin_mem_cycleAt π x)

lemma cycleMin_exists_pow_apply' (π : Equiv.Perm α) (x : α):
∃ k, k < orderOf (π.cycleOf x) ∧ (π^k) x = CycleMin π x :=
mem_cycleAt_iff_lt.mp (cycleMin_mem_cycleAt π x)

lemma cycleMin_eq_min_cycleAtTo_ge (ha : orderOf (π.cycleOf x) ≤ a) :
CycleMin π x = (CycleAtTo π a x).min' cycleAtTo_nonempty := by
simp_rw [cycleMin_def, cycleAt_eq_cycleAtTo_ge_orderOf_cycleOf ha]

lemma cycleMin_le (π : Equiv.Perm α) (x : α) (h : π.SameCycle x y) : CycleMin π x ≤ y := by
  rw [cycleMin_def]
  exact Finset.min'_le _ y (mem_cycleAt_iff.mpr h)

lemma cycleMin_le_zpow_apply (π : Equiv.Perm α) (x : α) (k : ℤ) : CycleMin π x ≤ (π^k) x :=
cycleMin_le _ _ ⟨k, rfl⟩

lemma cycleMin_le_pow_apply (π : Equiv.Perm α) (x : α) (n : ℕ) : CycleMin π x ≤ (π^n) x :=
cycleMin_le _ _ ⟨n, rfl⟩

lemma cycleMin_le_self : CycleMin π x ≤ x := cycleMin_le_zpow_apply π x 0

@[simp]
lemma cycleMin_bot [OrderBot α] : CycleMin π ⊥ = ⊥ := le_antisymm cycleMin_le_self bot_le

lemma cycleMin_refl : CycleMin (Equiv.refl α) x = x := cycleMin_of_fixed rfl

lemma cycleMin_one : CycleMin (1 : Equiv.Perm α) x = x := cycleMin_refl

lemma le_cycleMin (h : ∀ y, π.SameCycle x y → z ≤ y) : z ≤ CycleMin π x  := by
simp_rw [cycleMin_def, Finset.le_min'_iff, mem_cycleAt_iff] ; exact h

lemma le_cycleMin_iff : z ≤ CycleMin π x ↔ ∀ y, π.SameCycle x y → z ≤ y := by
simp_rw [cycleMin_def, Finset.le_min'_iff, mem_cycleAt_iff]




-- Theorem 2.4

lemma fastCycleMin_eq_min_cycleAtTo : FastCycleMin i π x =
    (CycleAtTo π (2^i) x).min' (cycleAtTo_nonempty_of_pos (pow_pos zero_lt_two _)) := by
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

lemma cycleMin_eq_fastCycleMin (h : orderOf (π.cycleOf x) ≤ 2^i) :
    FastCycleMin i π x = CycleMin π x := by
  rw [fastCycleMin_eq_min_cycleAtTo, cycleMin_eq_min_cycleAtTo_ge h]

-- Theorem 2.2
lemma cycleMin_eq_cycleMin_apply : CycleMin π x = CycleMin π (π x) := by
  simp_rw [cycleMin_def, cycleAt_apply_eq_cycleAt]

lemma cycleMin_eq_cycleMin_apply_inv : CycleMin π x = CycleMin π (π⁻¹ x) := by
rw [cycleMin_eq_cycleMin_apply (x := (π⁻¹ x)), Equiv.Perm.apply_inv_self]

end LinearOrder

section CanonicallyLinearOrderedMonoid

@[simp]
lemma cycleMin_zero [CanonicallyLinearOrderedAddCommMonoid α] : CycleMin π 0 = 0 :=
le_antisymm cycleMin_le_self (zero_le _)

end CanonicallyLinearOrderedMonoid

section Fin

@[simp]
lemma Fin.cycleMin_zero {τ : Equiv.Perm (Fin m)} [NeZero m] : CycleMin τ 0 = (0 : Fin m) :=
le_antisymm cycleMin_le_self (Fin.zero_le' _)

end Fin

end Perm
