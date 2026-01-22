import CBConcrete.PermOf.Basic
import CBConcrete.Lib.MulAction
import CBConcrete.Lib.Vector

namespace PermOf

variable {n : ℕ}

lemma isOfFinOrder (a : PermOf n) : IsOfFinOrder a := isOfFinOrder_of_finite _

lemma orderOf_pos (a : PermOf n) : 0 < orderOf a := by
  rw [orderOf_pos_iff]
  exact a.isOfFinOrder

section MulActionNat

theorem fixedBy_of_ge (a : PermOf n) {i : ℕ} (h : n ≤ i) :
    i ∈ MulAction.fixedBy ℕ a := by
  rw [MulAction.mem_fixedBy]
  exact a.smul_of_ge h

theorem Ici_subset_fixedBy (a : PermOf n) :
    Set.Ici n ⊆ MulAction.fixedBy ℕ a := fun _ => a.fixedBy_of_ge

theorem Ici_subset_fixedPoints :
    Set.Ici n ⊆ MulAction.fixedPoints (PermOf n) ℕ := fun _ hx a => a.smul_of_ge hx

open Pointwise in
theorem Iic_mem_set_fixedBy (a : PermOf n) :
    Set.Iio n ∈ MulAction.fixedBy (Set ℕ) a := Set.ext <| fun _ => by
  rw [← inv_inv a]
  simp_rw [Set.mem_inv_smul_set_iff, Set.mem_Iio, smul_lt_iff_lt]

theorem period_eq_one_of_ge (a : PermOf n) {i : ℕ} (hi : n ≤ i) : MulAction.period a i = 1 := by
  simp_rw [MulAction.period_eq_one_iff, a.smul_of_ge hi]

theorem period_eq_one_iff (a : PermOf n) {i : ℕ} :
    MulAction.period a i = 1 ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [MulAction.period_eq_one_iff]
  rcases lt_or_ge i n with hi | hi
  · simp_rw [hi, forall_true_left, a.smul_of_lt hi]
  · simp_rw [hi.not_gt, forall_false, iff_true, a.smul_of_ge hi]

@[simp]
theorem getElem_pow_period (a : PermOf n) {i : ℕ} (hi : i < n) :
    (a ^ MulAction.period a i)[i] = i := by
  rw [← smul_of_lt hi, MulAction.pow_period_smul]

theorem getElem_pow_mod_period (a : PermOf n) {i : ℕ} (hi : i < n) (k : ℕ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt hi, MulAction.pow_mod_period_smul]

theorem getElem_zpow_mod_period (a : PermOf n) {i : ℕ} (hi : i < n) (k : ℤ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt hi, MulAction.zpow_mod_period_smul]

theorem period_nat_pos (a : PermOf n) {i : ℕ} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_eq_one_of_zero (a : PermOf 0) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_eq_one_of_one (a : PermOf 1) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_le_card_of_getElem_pow_mem (a : PermOf n) {i : ℕ} (hi : i < n)
  (s : Finset ℕ) : (∀ k < s.card + 1, (a ^ k)[i] ∈ s) → MulAction.period a i ≤ s.card := by
  simp_rw [← smul_of_lt hi]
  exact MulAction.period_le_card_of_smul_pow_mem _ _

theorem getElem_injOn_range_period (a : PermOf n) {i : ℕ} (hi : i < n) :
    Set.InjOn (fun k => (a ^ k)[i]) (Finset.range (MulAction.period a i)) := by
  simp_rw [← smul_of_lt hi]
  exact MulAction.smul_injOn_range_period _

theorem period_le_of_lt (a : PermOf n) {i : ℕ} (hi : i < n) : MulAction.period a i ≤ n := by
  refine (period_le_card_of_getElem_pow_mem a hi (Finset.range n) ?_).trans_eq
    (Finset.card_range _)
  simp_rw [Finset.card_range, Finset.mem_range, getElem_lt, implies_true]

theorem period_le_of_neZero [NeZero n] (a : PermOf n) {i : ℕ} : MulAction.period a i ≤ n :=
  (lt_or_ge i n).by_cases
  a.period_le_of_lt <| NeZero.one_le.trans_eq' ∘ Eq.symm ∘ a.period_eq_one_of_ge

theorem exists_pos_le_pow_getElem_eq (a : PermOf n) {i : ℕ} (hi : i < n) :
    ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k)[i] = i :=
  ⟨MulAction.period a i, a.period_nat_pos, a.period_le_of_lt hi, a.getElem_pow_period _⟩

end MulActionNat

def cycleOf (a : PermOf n) (x : ℕ) : Finset ℕ :=
  if h : x < n then (Finset.range n).image (fun k => (a ^ k)[x]) else {x}

theorem cycleOf_lt (a : PermOf n) {x : ℕ} (hx : x < n) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k)[x]) := by
  unfold cycleOf
  simp_rw [dif_pos hx, Finset.ext_iff, Finset.mem_image, Finset.mem_range]
  refine fun _ => ⟨fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos,
    by simp_rw [getElem_pow_mod_period, h]⟩, fun ⟨_, hlt, h⟩ =>
    ⟨_, (hlt.trans_le <| a.period_le_of_lt hx), h⟩⟩

theorem cycleOf_ge (a : PermOf n) {x : ℕ} (hx : n ≤ x) :
    a.cycleOf x = {x} := dif_neg (not_lt_of_ge hx)

theorem card_cycleOf (a : PermOf n) (x : ℕ) : (a.cycleOf x).card = MulAction.period a x := by
  rcases lt_or_ge x n with hx | hx
  · refine Eq.trans ?_ (Finset.card_range (MulAction.period a x))
    rw [a.cycleOf_lt hx, Finset.card_image_iff]
    exact getElem_injOn_range_period _ _
  · rw [a.cycleOf_ge hx, a.period_eq_one_of_ge hx, Finset.card_singleton]

theorem cycleOf_eq_map_smul_range_period (a : PermOf n) (x : ℕ) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k) • x) := by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [a.cycleOf_lt hx, smul_of_lt hx]
  · simp_rw [a.cycleOf_ge hx, smul_of_ge hx, Finset.ext_iff, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range, exists_and_right]
    exact fun _ => ⟨fun h => h ▸ ⟨⟨0, a.period_nat_pos⟩, rfl⟩, fun h => h.2.symm⟩

theorem mem_cycleOf_iff_exists_pow_lt_period_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i) • x = y := by
  rw [cycleOf_eq_map_smul_range_period]
  simp_rw [Finset.mem_image, Finset.mem_range]

theorem mem_cycleOf_iff_exists_pow_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_lt_period_smul]
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩,
    fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos, ?_⟩⟩
  simp_rw [MulAction.pow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_zpow_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_smul]
  refine ⟨fun ⟨_, h⟩ => ⟨_, (zpow_natCast a _).symm ▸ h⟩,
    fun ⟨k, h⟩ => ⟨(k % MulAction.period a x).toNat, ?_⟩⟩
  simp_rw [← zpow_natCast, Int.toNat_of_nonneg
    (Int.emod_nonneg _ ((Nat.cast_ne_zero (R := ℤ)).mpr (a.period_nat_pos (i := x)).ne')),
    MulAction.zpow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_getElem_pow_lt_period (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_lt_period_smul, smul_of_lt hx]

theorem mem_cycleOf_iff_exists_getElem_pow (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul, smul_of_lt hx]

theorem mem_cycleOf_iff_exists_getElem_zpow (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul, smul_of_lt hx]

theorem self_mem_cycleOf (a : PermOf n) (x : ℕ) : x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨0, by simp only [pow_zero, one_smul]⟩

theorem nonempty_cycleOf (a : PermOf n) {x : ℕ} : (a.cycleOf x).Nonempty :=
  ⟨_, a.self_mem_cycleOf x⟩

theorem smul_mem_cycleOf (a : PermOf n) (x : ℕ) : (a • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨1, by simp only [pow_one]⟩

theorem smul_inv_mem_cycleOf (a : PermOf n) (x : ℕ) : (a⁻¹ • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨-1, by simp only [zpow_neg, zpow_one]⟩

theorem smul_pow_mem_cycleOf (a : PermOf n) (x k : ℕ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨k, rfl⟩

theorem smul_zpow_mem_cycleOf (a : PermOf n) (x : ℕ) (k : ℤ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨k, rfl⟩

theorem getElem_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) : a[x] ∈ a.cycleOf x := by
  convert a.smul_mem_cycleOf x
  rw [smul_of_lt hx]

theorem getElem_inv_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) : a⁻¹[x] ∈ a.cycleOf x := by
  convert a.smul_inv_mem_cycleOf x
  rw [smul_of_lt hx]

theorem getElem_pow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℕ) :
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_pow_mem_cycleOf x k
  rw [smul_of_lt hx]

theorem getElem_zpow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℤ) :
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_zpow_mem_cycleOf x k
  rw [smul_of_lt hx]

theorem getElem_inv_pow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℕ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  convert a.getElem_zpow_mem_cycleOf hx (-(k : ℤ))
  simp_rw [inv_pow, zpow_neg, zpow_natCast]

theorem getElem_inv_zpow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℤ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  simp only [inv_zpow']
  exact a.getElem_zpow_mem_cycleOf hx (-k)

def CycleMinVectorAux (a : PermOf n) : ℕ → PermOf n × Vector ℕ n
  | 0 => ⟨1, Vector.range n⟩
  | 1 =>
    ⟨a, (Vector.range n).zipWith min a.toVector⟩
  | (i+2) =>
    let ⟨ρ, b⟩ := a.CycleMinVectorAux (i + 1)
    let ρ' := ρ ^ 2
    ⟨ρ', b.zipWith min (b.shuffle ρ')⟩

@[simp]
theorem cycleMinAux_zero_fst (a : PermOf n) : (a.CycleMinVectorAux 0).1 = 1 := rfl

@[simp]
theorem cycleMinAux_succ_fst (a : PermOf n) (i : ℕ) :
    (a.CycleMinVectorAux (i + 1)).1 = a ^ (2 ^ i) := by
  induction i with | zero | succ i IH
  · rw [pow_zero, pow_one]
    rfl
  · rw [pow_succ, pow_mul]
    exact IH ▸ rfl

def CycleMinVector (a : PermOf n) (i : ℕ) : Vector ℕ n := (a.CycleMinVectorAux i).2

@[simp]
theorem cycleMinAux_snd_val (a : PermOf n) {i : ℕ} :
    (a.CycleMinVectorAux i).2 = CycleMinVector a i := rfl

@[simp] theorem getElem_cycleMinVector_zero (a : PermOf n) {x : ℕ} (hx : x < n) :
  (a.CycleMinVector 0)[x] = x := Vector.getElem_range _

theorem getElem_cycleMinVector_succ (a : PermOf n) {i x : ℕ}
    (hx : x < n) :
    (a.CycleMinVector (i + 1))[x] = min ((a.CycleMinVector i)[x])
    ((a.CycleMinVector i)[(a^2 ^ i)[x]]) := by
  rcases i with (_ | i) <;>
  refine (Vector.getElem_zipWith _).trans ?_
  · simp_rw [Vector.getElem_range, getElem_toVector, pow_zero, pow_one,
      getElem_cycleMinVector_zero]
  · simp_rw [Vector.getElem_shuffle, cycleMinAux_snd_val,
      cycleMinAux_succ_fst, ← pow_mul, ← pow_succ]

@[simp] theorem getElem_cycleMinVector_le_self {a : PermOf n} {k i : ℕ}
    {hx : i < n} : (a.CycleMinVector k)[i] ≤ i := by
  induction k generalizing a i with | zero => _ | succ k IH => _
  · simp_rw [getElem_cycleMinVector_zero, le_rfl]
  · simp_rw [getElem_cycleMinVector_succ, min_le_iff, IH, true_or]

theorem getElem_one_cycleMinVector {k i : ℕ} (hi : i < n) :
    ((1 : PermOf n).CycleMinVector k)[i] = i := by
  induction k generalizing n i with | zero => _ | succ k IH => _
  · simp_rw [getElem_cycleMinVector_zero]
  · simp_rw [getElem_cycleMinVector_succ, one_pow, getElem_one, IH, min_self]

theorem one_cycleMinVector {k : ℕ} : (1 : PermOf n).CycleMinVector k = Vector.range n := by
  ext i hi
  simp_rw [getElem_one_cycleMinVector, Vector.getElem_range]

@[simp]
theorem getElem_cycleMinVector_lt (a : PermOf n) {i : ℕ} {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] < n := by
  induction i generalizing x with | zero | succ i IH
  · simp_rw [getElem_cycleMinVector_zero]
    exact hx
  · simp_rw [getElem_cycleMinVector_succ, min_lt_iff, IH, true_or]

theorem min_getElem_cycleMinVector_getElem_cycleMinVector_getElem (a : PermOf n)
    {i x : ℕ} (hx : x < n) :
    min x ((a.CycleMinVector i)[a[x]]) = min (a.CycleMinVector i)[x] ((a^2 ^ i)[x]) := by
  induction i generalizing a x with | zero => _ | succ i IH => _
  · simp_rw [getElem_cycleMinVector_zero, pow_zero, pow_one]
  · simp_rw [getElem_cycleMinVector_succ, ← min_assoc, IH, min_assoc, ← getElem_mul, pow_mul_comm',
      getElem_mul, IH, ← getElem_mul, ← pow_add, ← two_mul, ← pow_succ']

theorem getElem_cycleMinVector_eq_min'_getElem_pow_image_range (a : PermOf n)
    {i x : ℕ} (hx : x < n) :
    (a.CycleMinVector i)[x] =
    ((Finset.range (2 ^ i)).image (fun k => (a ^ k)[x])).min'
      (Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.two_pow_pos i).ne')) := by
  induction i generalizing a x with | zero => _ | succ i IH => _
  · simp_rw [getElem_cycleMinVector_zero, pow_zero, Finset.range_one, Finset.image_singleton,
      pow_zero, getElem_one, Finset.min'_singleton]
  · simp_rw [getElem_cycleMinVector_succ, IH, le_antisymm_iff, getElem_pow_add,
      le_inf_iff, Finset.le_min'_iff, inf_le_iff, Finset.mem_image, Finset.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine ⟨fun k hk => (lt_or_ge k (2 ^ i)).imp
      (fun hk' => Finset.min'_le _ _ ?_) (fun hk' => Finset.min'_le _ _ ?_),
      fun k hk => Finset.min'_le _ _ ?_, fun k hk => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [Finset.mem_image, Finset.mem_range]
    exacts [⟨k, hk', rfl⟩,
      ⟨k - 2 ^ i, Nat.sub_lt_right_of_lt_add hk' (Nat.two_mul _ ▸ Nat.pow_succ' ▸ hk),
        (Nat.sub_add_cancel hk').symm ▸ rfl⟩,
      ⟨k, hk.trans (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _)), rfl⟩,
      ⟨k + 2 ^ i, (Nat.pow_succ' ▸ Nat.two_mul _ ▸ (Nat.add_lt_add_right hk _)), rfl⟩]

lemma getElem_cycleMinVector_le_getElem_pow_lt (a : PermOf n) {i : ℕ} {x : ℕ}
    {k : ℕ} (hk : k < 2 ^ i) (hx : x < n) :
    (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range]
  refine Finset.min'_le _ _ ?_
  simp_rw [Finset.mem_image, Finset.mem_range]
  exact ⟨k, hk, rfl⟩

lemma getElem_cycleMinVector_le (a : PermOf n) {i : ℕ} {x y : ℕ}
    {hx : x < n} (hk : ∃ k < 2 ^ i, y = (a ^ k)[x]) :
    (a.CycleMinVector i)[x] ≤ y :=
  hk.choose_spec.2 ▸ a.getElem_cycleMinVector_le_getElem_pow_lt hk.choose_spec.1 _

lemma exists_lt_getElem_cycleMin_eq_getElem_pow (a : PermOf n) (i : ℕ) {x : ℕ}
      (hx : x < n) :
    ∃ k < 2 ^ i, (a.CycleMinVector i)[x] = (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range]
  have H := Finset.min'_mem ((Finset.range (2 ^ i)).image (fun k => (a ^ k)[x]))
    (Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.two_pow_pos i).ne'))
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  exact ⟨H.choose, H.choose_spec.1, H.choose_spec.2.symm⟩

lemma le_getElem_cycleMin_iff (a : PermOf n) (i : ℕ) {x y : ℕ}
      (hx : x < n) :
    y ≤ (a.CycleMinVector i)[x] ↔ ∀ k < 2 ^ i, y ≤ (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range, Finset.le_min'_iff,
    Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

@[simp] theorem getElem_cycleMinVector_of_self_le_getElem {a : PermOf n} {k i : ℕ}
    {hx : i < n} (hxa : ∀ k, i ≤ (a ^ k)[i]) : (a.CycleMinVector k)[i] = i := by
  simp_rw [le_antisymm_iff, le_getElem_cycleMin_iff, hxa,
    getElem_cycleMinVector_le_self, implies_true, and_self]

theorem getElem_zero_cycleMinVector [NeZero n]
    {a : PermOf n} {k : ℕ} : (a.CycleMinVector k)[0]'(NeZero.pos _) = 0 :=
  getElem_cycleMinVector_of_self_le_getElem (fun _ => zero_le _)

lemma getElem_cycleMinVector_eq_min'_cycleOf (a : PermOf n) {i : ℕ} {x : ℕ}
      (hai : MulAction.period a x ≤ 2 ^ i) (hx : x < n) :
      (a.CycleMinVector i)[x] = (a.cycleOf x).min' a.nonempty_cycleOf := by
  refine le_antisymm (getElem_cycleMinVector_le _ ?_) (Finset.min'_le _ _ ?_)
  · have H := Finset.min'_mem (a.cycleOf x) a.nonempty_cycleOf
    simp_rw [mem_cycleOf_iff_exists_getElem_pow_lt_period _ hx] at H
    exact ⟨H.choose, H.choose_spec.1.trans_le hai, H.choose_spec.2.symm⟩
  · simp_rw [a.mem_cycleOf_iff_exists_getElem_pow hx]
    exact ⟨(a.exists_lt_getElem_cycleMin_eq_getElem_pow i hx).choose,
    ((a.exists_lt_getElem_cycleMin_eq_getElem_pow i hx).choose_spec).2.symm⟩

lemma getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow (a : PermOf n) {i : ℕ} {x : ℕ}
    (hx : x < n) (hai : MulAction.period a x ≤ 2 ^ i) :
    ∀ k, (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := fun k => by
  simp_rw [a.getElem_cycleMinVector_eq_min'_cycleOf hai,
    Finset.min'_le _ _ (a.getElem_pow_mem_cycleOf hx k)]

lemma getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow (a : PermOf n) {i : ℕ} {x : ℕ}
      (hx : x < n) (hai : MulAction.period a x ≤ 2 ^ i) :
    ∀ k : ℤ, (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := fun k => by
  simp_rw [a.getElem_cycleMinVector_eq_min'_cycleOf hai,
    Finset.min'_le _ _ (a.getElem_zpow_mem_cycleOf hx k)]

lemma cycleMinVector_eq_apply_cycleMinVector (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : ∀ {x : ℕ}, MulAction.period a x ≤ 2 ^ i) (hx : x < n) :
   (a.CycleMinVector i)[x] = (a.CycleMinVector i)[a[x]] := by
  simp_rw [getElem_cycleMinVector_eq_min'_cycleOf _ hai, le_antisymm_iff, Finset.le_min'_iff]
  refine ⟨fun y hy => Finset.min'_le _ _ ?_, fun y hy => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hx,
      mem_cycleOf_iff_exists_getElem_zpow _ (getElem_lt _)] at hy ⊢
  exacts [⟨hy.choose + 1, zpow_add_one a _ ▸ getElem_mul _ ▸ hy.choose_spec⟩,
      ⟨hy.choose - 1, zpow_sub_one a _ ▸ getElem_mul _ ▸
      inv_mul_cancel_right _ a ▸ hy.choose_spec⟩]

def CycleMin (a : PermOf n) (i : ℕ) (x : ℕ) : ℕ := (a.CycleMinVector i)[x]?.getD x

theorem getElem_cycleMinVector (a : PermOf n) (i : ℕ) {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] = a.CycleMin i x :=
  (Vector.getD_of_lt _ _ _ _).symm

theorem cycleMin_of_lt (a : PermOf n) {i x : ℕ} (hx : x < n) :
    a.CycleMin i x = (a.CycleMinVector i)[x] := Vector.getD_of_lt _ _ _ _

theorem cycleMin_of_getElem {a b : PermOf n} {i x : ℕ} (hx : x < n) :
    a.CycleMin i (b[x]) = (a.CycleMinVector i)[b[x]] :=
  Vector.getD_of_lt _ _ _ _

theorem cycleMin_of_ge (a : PermOf n) {i x : ℕ} (hx : n ≤ x) :
    a.CycleMin i x = x := Vector.getD_of_ge _ _ _ hx

@[simp] theorem one_cycleMin {k x : ℕ} : (1 : PermOf n).CycleMin k x = x := by
  rcases lt_or_ge x n with hx | hx
  · rw [cycleMin_of_lt _ hx, one_cycleMinVector, Vector.getElem_range]
  · rwa [cycleMin_of_ge]

@[simp]
theorem cycleMin_zero (a : PermOf n) {x : ℕ} :
  a.CycleMin 0 x = x := if hx : x < n then
    (a.cycleMin_of_lt hx).trans <| Array.getElem_range _ else a.cycleMin_of_ge (le_of_not_gt hx)

@[simp]
theorem cycleMin_succ (a : PermOf n) {i x : ℕ} :
    a.CycleMin (i + 1) x = min (a.CycleMin i x) (a.CycleMin i (a^2 ^ i • x)) := by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [smul_of_lt hx, a.cycleMin_of_lt hx, cycleMin_of_getElem, getElem_cycleMinVector_succ]
  · simp_rw [smul_of_ge hx, a.cycleMin_of_ge hx, min_self]

@[simp]
theorem cycleMin_lt_iff_lt (a : PermOf n) {i : ℕ} {x : ℕ} :
    a.CycleMin i x < n ↔ x < n := by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, hx, getElem_cycleMinVector_lt]
  · simp_rw [a.cycleMin_of_ge hx]

lemma cycleMin_le_smul_pow_lt_two_pow (a : PermOf n) {i : ℕ} (x : ℕ) {k : ℕ} (hk : k < 2 ^ i) :
    a.CycleMin i x ≤ (a ^ k) • x := by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinVector_le_getElem_pow_lt _ hk _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_pow_smul_of_period_le_two_pow (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2 ^ i) : ∀ k, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow _ _ hai _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_zpow_smul_of_period_le_two_pow (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2 ^ i) :
    ∀ k : ℤ, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow _ _ hai _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_self (a : PermOf n) (i : ℕ) {x : ℕ} :
    a.CycleMin i x ≤ x := by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx]
    exact getElem_cycleMinVector_le_self
  · simp_rw [a.cycleMin_of_ge hx, le_rfl]

lemma exists_lt_cycleMin_eq_smul_pow (a : PermOf n) (i : ℕ) {x : ℕ} :
    ∃ k < 2 ^ i, a.CycleMin i x = (a ^ k) • x := by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt hx]
    exact exists_lt_getElem_cycleMin_eq_getElem_pow _ _ _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge hx]
    exact ⟨0, Nat.two_pow_pos _, trivial⟩

lemma cycleMin_eq_min'_cycleOf (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2 ^ i) :
    a.CycleMin i x = (a.cycleOf x).min' a.nonempty_cycleOf := by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx]
    exact getElem_cycleMinVector_eq_min'_cycleOf _  hai _
  · simp_rw [a.cycleMin_of_ge hx, a.cycleOf_ge hx]
    exact rfl

lemma cycleMin_eq_apply_cycleMin (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : ∀ {x : ℕ}, MulAction.period a x ≤ 2 ^ i) :
    a.CycleMin i x = a.CycleMin i (a • x) := by
  rcases lt_or_ge x n with hx | hx
  · simp_rw [cycleMin_eq_min'_cycleOf _ _ hai, le_antisymm_iff, Finset.le_min'_iff]
    refine ⟨fun y hy => Finset.min'_le _ _ ?_, fun y hy => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hx,
      mem_cycleOf_iff_exists_getElem_zpow _ (a.smul_lt_of_lt hx), a.smul_of_lt hx] at hy ⊢
    exacts [⟨hy.choose + 1, zpow_add_one a _ ▸ getElem_mul _ ▸ hy.choose_spec⟩,
      ⟨hy.choose - 1, zpow_sub_one a _ ▸ getElem_mul _ ▸
      inv_mul_cancel_right _ a ▸ hy.choose_spec⟩]
  · simp_rw [a.cycleMin_of_ge hx]
    rw [a.cycleMin_of_ge (le_of_not_gt (a.lt_of_smul_lt.mt hx.not_gt)), a.smul_of_ge hx]

end PermOf
