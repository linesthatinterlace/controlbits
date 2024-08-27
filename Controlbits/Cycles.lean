
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Fintype.Order

namespace Equiv.Perm

theorem SameCycle.exists_pow_lt_finset_card_of_apply_zpow_mem {f : Perm α} (s : Finset α) {x y : α}
    (hf : ∀ i : ℤ, (f ^ i) x ∈ s) : SameCycle f x y → ∃ i, i < s.card ∧ (f ^ i) x = y := by
  have H : ∃ i ≤ s.card, ∃ j ≤ s.card, i ≠ j ∧ (f ^ i) x = (f ^ j) x := by
    simp_rw [← Nat.lt_succ_iff, ← Finset.mem_range]
    exact Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (Finset.card_range _ ▸ Nat.lt_succ_self _) (fun i _ => hf i)
  obtain ⟨i, hi, j, hj, hij', hijf⟩ := H
  wlog hij : i < j
  · exact this _ hf _ hj _ hi hij'.symm hijf.symm (hij'.symm.lt_of_le (le_of_not_lt hij))
  rw [← inv_eq_iff_eq, ← mul_apply, ← inv_pow_sub _ hij.le,
    inv_pow, inv_eq_iff_eq, eq_comm, ← zpow_natCast, Int.natCast_sub hij.le] at hijf
  have hij : (0 : ℤ) < ↑j - ↑i := by rwa [sub_pos, Nat.cast_lt]
  rintro ⟨k, hkf⟩
  rw [← Int.emod_add_ediv k (j - i), zpow_add, mul_apply, zpow_mul,
    Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hijf,
    ← Int.natAbs_of_nonneg (Int.emod_nonneg _ hij.ne'), zpow_natCast] at hkf
  have hks : (k % (↑j - ↑i)).natAbs < s.card := by
    rw [←Int.ofNat_lt, Int.natCast_natAbs, abs_eq_self.mpr (Int.emod_nonneg _ hij.ne')]
    refine (Int.emod_lt_of_pos _ hij).trans_le ?_
    rw [tsub_le_iff_right]
    exact (Nat.cast_le.mpr hj).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  exact ⟨(k % (↑j - ↑i)).natAbs, hks, hkf⟩

def FastCycleMin {α : Type*} [Min α] (i : ℕ) (π : Equiv.Perm α) (x : α) : α :=
  match i with
  | 0 => x
  | (i+1) => min (FastCycleMin i π x) (FastCycleMin i π <| (π ^ 2^i) x)



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
    refine ⟨?_, ?_⟩
    · exact IH _ (fun _ hk => hz _ (hk.trans
        (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _))))
    · rw [pow_succ', two_mul] at hz
      refine IH _ (fun _ hk => ?_)
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

lemma sameCycle_fastCycleMin (π : Perm α) (x : α) : π.SameCycle x (FastCycleMin i π x) := by
  rcases π.exists_lt_fastCycleMin_eq_pow_apply x i with ⟨k, _, hk⟩
  exact ⟨k, hk⟩

-- Theorem 2.4

lemma fastCycleMin_eq_min'_image_interval [DecidableEq α] : FastCycleMin i π x =
    ((Finset.Iio (2^i)).image fun k => (π ^ k) x).min'
    ((Finset.nonempty_Iio.mpr (not_isMin_of_lt (Nat.two_pow_pos _))).image _) := by
  refine le_antisymm ?_ (Finset.min'_le _ _ ?_)
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
  nth_rewrite 2 [← Nat.or_exists_add_one]
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

variable {α : Type*} {π : Perm α} {x y : α}

lemma sameCycle_nonempty (π : Perm α) : Set.Nonempty (π.SameCycle x ·) := ⟨x, ⟨0, rfl⟩⟩

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

section BddBelow

variable (hsb : BddBelow (π.SameCycle x ·))

include hsb

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
  z ≤ CycleMin π x ↔ ∀ y, π.SameCycle x y → z ≤ y := le_csInf_iff hsb π.sameCycle_nonempty

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

variable [ConditionallyCompleteLinearOrder α]

lemma sameCycle_cycleMin [IsWellOrder α (· < ·)] (π : Perm α) (x : α) :
  π.SameCycle x (CycleMin π x) := csInf_mem π.sameCycle_nonempty

lemma cycleMin_exists_zpow_apply [IsWellOrder α (· < ·)] (x : α) :
    ∃ k : ℤ, (π^k) x = CycleMin π x := π.sameCycle_cycleMin x

lemma cycleMin_exists_pow_apply_of_finite_order [IsWellOrder α (· < ·)] (hn : n > 0)
    (hnx : (π^n) x = x) : ∃ k < n, (π^k) x = CycleMin π x := by
  suffices h : ∃ k, (π ^ k) x = π.CycleMin x by
    rcases h with ⟨k, hk⟩
    refine ⟨k % n, Nat.mod_lt _ hn, (hk.symm.trans ?_).symm⟩
    nth_rewrite 1 [← Nat.div_add_mod k n, add_comm, pow_add, mul_apply, pow_mul]
    exact congrArg _ (Function.IsFixedPt.perm_pow hnx _)
  rcases π.cycleMin_exists_zpow_apply x with ⟨k | k, hk⟩
  · exact ⟨k, hk⟩
  · refine ⟨(n - (k + 1) % n) , ?_⟩
    rw [zpow_negSucc] at hk
    nth_rewrite 1 [← hk, Equiv.Perm.eq_inv_iff_eq, ← mul_apply, ← pow_add,
      ← Nat.div_add_mod (k + 1) n, add_assoc, Nat.add_sub_cancel' (Nat.mod_lt _ hn).le,
      ← Nat.mul_succ, pow_mul]
    exact Function.IsFixedPt.perm_pow hnx _

section BddBelow

lemma cycleMin_le_fastCycleMin_of_bddBelow_sameCycle (hsb : BddBelow (π.SameCycle x ·)) :
    CycleMin π x ≤ FastCycleMin i π x := by
  rcases π.exists_lt_fastCycleMin_eq_pow_apply x i with ⟨k, _, hkx⟩
  rw [← hkx]
  exact cycleMin_le_of_bddBelow_sameCycle hsb ⟨k, rfl⟩

end BddBelow

end ConditionallyCompleteLinearOrder

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α]

lemma cycleMin_le_fastCycleMin : CycleMin π x ≤ FastCycleMin i π x := by
  rcases π.exists_lt_fastCycleMin_eq_pow_apply x i with ⟨k, _, hkx⟩
  rw [← hkx]
  exact cycleMin_le ⟨k, rfl⟩

lemma fastCycleMin_eq_cycleMin_of_zpow_apply_mem_finset [IsWellOrder α (· < ·)]
    {x : α} (s : Finset α) (hs : s.card ≤ 2^i)
    (hxs : ∀ i : ℤ, (π ^ i) x ∈ s) : FastCycleMin i π x = CycleMin π x := by
  refine le_antisymm ?_ cycleMin_le_fastCycleMin
  obtain ⟨k, hk, hkx⟩ := (π.sameCycle_cycleMin x).exists_pow_lt_finset_card_of_apply_zpow_mem s hxs
  exact (fastCycleMin_le _ (hk.trans_le hs)).trans_eq hkx

end ConditionallyCompleteLinearOrderBot

@[simp]
lemma _root_.Nat.cycleMin_zero {π : Perm ℕ} : CycleMin π (0 : ℕ) = 0 :=
le_antisymm cycleMin_le_self (zero_le _)

@[simp]
lemma _root_.Fin.cycleMin_zero [NeZero m] {τ : Equiv.Perm (Fin m)} :
  CycleMin τ 0 = 0 := le_antisymm cycleMin_le_self (Fin.zero_le' _)

end CycleMin

end Equiv.Perm
