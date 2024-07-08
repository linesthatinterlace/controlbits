
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Fintype.Order

namespace Equiv.Perm

theorem SameCycle.exists_pow_eq_of_mem_support' [Fintype α] [DecidableEq α]
    (f : Perm α) (h : SameCycle f x y)
  (hx : x ∈ f.support) : ∃ i : ℕ, 0 < i ∧ i ≤ (f.cycleOf x).support.card ∧ (f ^ i) x = y := by
  obtain ⟨k, hk, hk'⟩ := h.exists_pow_eq_of_mem_support hx
  cases' k with k
  · refine ⟨(f.cycleOf x).support.card, ?_, le_rfl, ?_⟩
    · refine zero_lt_one.trans (one_lt_card_support_of_ne_one ?_)
      simpa using hx
    · simp only [Nat.zero_eq, pow_zero, coe_one, id_eq] at hk'
      subst hk'
      rw [← (isCycle_cycleOf _ <| mem_support.1 hx).orderOf, ← cycleOf_pow_apply_self,
        pow_orderOf_eq_one, one_apply]
  · exact ⟨k + 1, by simp, hk.le, hk'⟩

lemma exists_pow_fixpoint_mem_finite_of_fix [DecidableEq α] (π : Equiv.Perm α) {s : Set α}
  [Fintype s] (hsx : ∀ x, x ∈ s ↔ π x ∈ s) (hx : x ∈ s) :
    ∃ k, (k > 0 ∧ k ≤ Fintype.card s ∧ (π^k) x = x) := by
  rcases eq_or_ne (π x) x with hxπ | hxπ
  · haveI : Nonempty s := ⟨x, hx⟩
    exact ⟨1, zero_lt_one, Nat.succ_le_of_lt (Fintype.card_pos), hxπ⟩
  · have H := (SameCycle.refl (π.subtypePerm hsx) ⟨x, hx⟩).exists_pow_eq_of_mem_support' _
    simp only [mem_support, subtypePerm_apply, ne_eq, Subtype.mk.injEq, subtypePerm_pow] at H
    rcases H hxπ with ⟨k, hk, hkx, hkπ⟩
    exact ⟨k, hk, hkx.trans (Finset.card_le_univ _), hkπ⟩

def FastCycleMin {α : Type*} [Min α] (i : ℕ) (π : Equiv.Perm α) : α → α :=
  match i with
  | 0 => id
  | (i+1) => fun x => min (FastCycleMin i π x) (FastCycleMin i π <| (π ^ 2^i) x)

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

lemma fastCycleMin_le : ∀ k < 2^i, FastCycleMin i π x ≤ (π ^ k) x := by
  induction' i with i IH generalizing x
  · simp_rw [pow_zero, Nat.lt_one_iff, fastCycleMin_zero, forall_eq, pow_zero, one_apply, le_rfl]
  · simp_rw [pow_succ', two_mul, fastCycleMin_succ, min_le_iff]
    intro k hk'
    rcases lt_or_le k (2^i) with hk | hk
    · exact Or.inl (IH _ hk)
    · rw [← Nat.sub_lt_iff_lt_add hk] at hk'
      convert Or.inr (IH _ hk') using 2
      rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hk]

lemma le_fastCycleMin : ∀ z, (∀ k < 2^i, z ≤ (π ^ k) x) → z ≤ FastCycleMin i π x := by
  induction' i with i IH generalizing x
  · simp_rw [pow_zero, Nat.lt_one_iff, forall_eq, pow_zero, one_apply, fastCycleMin_zero, imp_self,
    implies_true]
  · simp_rw [fastCycleMin_succ, le_min_iff]
    intros z hz
    refine' ⟨_, _⟩
    · exact IH _ (fun _ hk => hz _ (hk.trans
        (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _))))
    · rw [pow_succ', two_mul] at hz
      refine' IH _ (fun _ hk => _)
      simp_rw [← Perm.mul_apply, ← pow_add]
      exact hz _ (add_lt_add_right hk _)

lemma fastCycleMin_le_iff :
    ∀ z, FastCycleMin i π x ≤ z ↔ (∀ y, (∀ k < 2^i, y ≤ (π ^ k) x) → y ≤ z) :=
  fun _ => ⟨fun h _ hy => h.trans' (le_fastCycleMin _ hy), fun h => h _ fastCycleMin_le⟩

lemma fastCycleMin_le_self : FastCycleMin i π x ≤ x := fastCycleMin_le _ (Nat.two_pow_pos _)

lemma le_fastcycleMin_iff : ∀ z, z ≤ FastCycleMin i π x ↔ ∀ k < 2^i, z ≤ (π ^ k) x :=
  fun _ => ⟨fun h _ hk => h.trans (fastCycleMin_le _ hk), le_fastCycleMin _⟩

lemma self_eq_fastCycleMin_iff : x = FastCycleMin i π x ↔ x ≤ FastCycleMin i π x:= by
  simp_rw [eq_iff_le_not_lt, not_lt, fastCycleMin_le_self, and_true]

lemma fastCycleMin_eq_self_iff : FastCycleMin i π x = x ↔ x ≤ FastCycleMin i π x:= by
  simp_rw [← self_eq_fastCycleMin_iff, eq_comm]

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
    exact fun _ => fastCycleMin_le _
  · simp_rw [Finset.mem_image, Finset.mem_Iio]
    exact exists_lt_fastCycleMin_eq_pow_apply x i

lemma min_fastCycleMin_apply :
    min (FastCycleMin i π (π x)) x = min (FastCycleMin i π x) ((π ^ 2^i) x) := by
  simp_rw [fastCycleMin_eq_min'_image_interval, ← Finset.min'_insert, ← mul_apply,
  ← pow_succ, ← Finset.image_insert (fun k => (π ^ k) x), Finset.Iio_insert]
  congr 1
  ext y
  simp_rw [Finset.mem_insert, Finset.mem_image, Finset.mem_Iio, Finset.mem_Iic, eq_comm (a := y),
  ← Nat.succ_le_iff, Nat.succ_eq_add_one]
  nth_rewrite 2 [← Nat.or_exists_succ]
  simp_rw [zero_le, pow_zero, one_apply, true_and]

section OrderBot

variable [OrderBot α]

lemma fastCycleMin_apply_bot : FastCycleMin i π ⊥ = ⊥ := by
  rw [eq_bot_iff]
  exact fastCycleMin_le_self

end OrderBot

end LinearOrder

section Nat

lemma fastCycleMin_apply_zero {π : Perm ℕ} : FastCycleMin i π 0 = 0 := by
  rw [fastCycleMin_eq_self_iff]
  exact zero_le _

end Nat

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

lemma fastCycleMin_eq_cycleMin_of_order_le (hn : n > 0) (hn' : n ≤ 2^i) (hnx : (π^n) x = x) :
    FastCycleMin i π x = CycleMin π x := by
  refine' le_antisymm _ cycleMin_le_fastCycleMin
  rcases π.cycleMin_exists_pow_apply_of_finite_order hn hnx with ⟨k, hk, hkx⟩
  rw [← hkx]
  exact fastCycleMin_le _ (hk.trans_le hn')

lemma fastCycleMin_eq_cycleMin_of_mem_finite_fix (s : Set α) [Fintype s]
  (hsi : Fintype.card s ≤ 2^i) (hsx : ∀ x, x ∈ s ↔ π x ∈ s) (hx : x ∈ s) :
    FastCycleMin i π x = CycleMin π x := by
  rcases (exists_pow_fixpoint_mem_finite_of_fix π hsx hx) with ⟨k, hk, hk', hkx⟩
  exact fastCycleMin_eq_cycleMin_of_order_le hk (hk'.trans hsi) hkx

end ConditionallyCompleteLinearOrderBot

namespace Nat

@[simp]
lemma cycleMin_zero {π : Perm ℕ} : CycleMin π (0 : ℕ) = 0 :=
le_antisymm cycleMin_le_self (zero_le _)

end Nat

namespace Fin

@[simp]
lemma cycleMin_zero {τ : Equiv.Perm (Fin (m + 1))} :
  CycleMin τ 0 = (0 : Fin (m + 1)) := le_antisymm cycleMin_le_self (Fin.zero_le' _)

end Fin

end CycleMin

end Equiv.Perm
