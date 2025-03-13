import CBConcrete.PermOf
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise

@[simp]
lemma finTwoEquiv_apply : ∀ j, finTwoEquiv j = decide (j = 1) :=
(Fin.forall_fin_two).mpr ⟨rfl, rfl⟩

@[simp]
lemma finTwoEquiv_symm_apply : ∀ j, finTwoEquiv.symm j = bif j then 1 else 0 :=
  (Bool.forall_bool).mpr ⟨rfl, rfl⟩

@[simps!]
def boolInversion : Equiv.Perm Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

namespace Equiv

/-- A subtype of a `Prod` that depends only on the second component is equivalent to the
first type times the corresponding subtype of the second type. -/
@[simps!]
def prodSubtypeSndEquivSubtypeProd {α β : Type*} {p : β → Prop} :
    {s : α × β // p s.2} ≃ α × {b // p b} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Equiv

namespace Bool

variable {a b b' : Bool} {p : ℕ} {α β : Type*}

theorem toNat_decide {P : Prop} [Decidable P] : toNat P = if P then 1 else 0 :=
  cond_decide _ _ _

@[simp]
theorem toNat_pos {P : Prop} [Decidable P] (p : P) : toNat P = 1 := by
  simp_rw [p, decide_true, toNat_true]

@[simp]
theorem toNat_neg {P : Prop} [Decidable P] (p : ¬P) : toNat P = 0 := by
  simp_rw [p, _root_.decide_false, toNat_false]

theorem toNat_not : (!b).toNat = 1 - b.toNat := by cases b <;> rfl

theorem toNat_not_add_toNat : (!b).toNat + b.toNat = 1 := by cases b <;> rfl

theorem toNat_add_toNat_not : b.toNat + (!b).toNat = 1 := by cases b <;> rfl

theorem toNat_True : toNat True = 1 := by simp_rw [decide_true, toNat_true]

theorem toNat_False : toNat False = 0 := by simp_rw [_root_.decide_false, toNat_false]

theorem decide_toNat_eq_one : (b.toNat = 1 : Bool) = b := by simp_rw [toNat_eq_one, decide_eq_true]

theorem toNat_injective : toNat b = toNat b' → b = b' := b'.recOn
  (by simp_rw [toNat_false, toNat_eq_zero, imp_self])
  (by simp_rw [toNat_true, toNat_eq_one, imp_self])

@[simp]
theorem decide_mod_two_eq_one_toNat : (p % 2 = 1 : Bool).toNat = p % 2 := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · rw [h, toNat_neg zero_ne_one]
  · rw [h, toNat_pos rfl]

@[simp]
theorem decide_toNat_mod_two_eq_one : (b.toNat % 2 = 1 : Bool) = b := toNat_injective <| by
  simp_rw [decide_mod_two_eq_one_toNat, Nat.mod_eq_of_lt (Bool.toNat_lt _)]

theorem eq_iff_iff' : a = b ↔ (a = false ↔ b = false) := by
  simp only [coe_false_iff_false, Bool.eq_not_iff, ne_eq, Bool.not_not_eq]

theorem decide_and_eq_decide_and {P : Prop} [Decidable P] :
    (decide P && b) = (decide P && b') ↔ P → b = b' := by
  rcases Classical.em P with p | p
  · simp_rw [p, decide_true, true_and, true_implies]
  · simp only [p, _root_.decide_false, false_and, false_implies]

theorem apply_apply_apply_not_of_comm {f : β → β → α}
    (hf : ∀ x y, f x y = f y x) (b b' : Bool) (g : Bool → β)  :
    f (g b) (g b.not) = f (g b') (g b'.not) := by
  cases b <;> cases b'
  · rfl
  · exact hf _ _
  · exact hf _ _
  · rfl

theorem apply_false_apply_true_of_comm {f : β → β → α}
    (hf : ∀ x y, f x y = f y x) (b : Bool) (g : Bool → β) :
    f (g false) (g true) = f (g b) (g b.not) := by
  cases b
  · rfl
  · exact hf _ _

theorem apply_true_apply_false_of_comm {f : β → β → α}
    (hf : ∀ x y, f x y = f y x) (b : Bool) (g : Bool → β)  :
    f (g true) (g false) = f (g b) (g b.not) := by
  cases b
  · exact hf _ _
  · rfl

end Bool

namespace Fin

variable {m : ℕ}

theorem val_succAbove {i : Fin m} {j : Fin (m + 1)} :
    (j.succAbove i : ℕ) = i.val + (decide (j.val ≤ i.val)).toNat := by
  rcases le_or_lt j (i.castSucc) with h | h
  · rw [succAbove_of_le_castSucc _ _ h]
    rw [Fin.le_iff_val_le_val, coe_castSucc] at h
    simp_rw [val_succ, Bool.toNat_pos h]
  · rw [succAbove_of_castSucc_lt _ _ h]
    rw [Fin.lt_iff_val_lt_val, coe_castSucc] at h
    simp_rw [coe_castSucc, Bool.toNat_neg h.not_le, add_zero]

theorem val_predAbove {i : Fin m} {j : Fin (m + 1)} :
    (i.predAbove j : ℕ) = j.val - (decide (i.val < j.val)).toNat := by
  rcases le_or_lt j (i.castSucc) with h | h
  · rw [predAbove_of_le_castSucc _ _ h]
    rw [Fin.le_iff_val_le_val, coe_castSucc] at h
    simp_rw [coe_castPred, Bool.toNat_neg h.not_lt, Nat.sub_zero]
  · rw [predAbove_of_castSucc_lt _ _ h]
    rw [Fin.lt_iff_val_lt_val, coe_castSucc] at h
    simp_rw [coe_pred, Bool.toNat_pos h]

@[simp]
theorem val_xor {i j : Fin m} : (i ^^^ j).val = (i.val ^^^ j.val) % m := rfl

end Fin

namespace Nat

section Size

@[simp]
theorem size_succ {x : ℕ} : x.succ.size ≠ 0 := by
  simp_rw [ne_eq, Nat.size_eq_zero, Nat.succ_ne_zero, not_false_eq_true]

theorem size_le_self {n : ℕ} (hn : n ≠ 0) : 2^(n.size - 1) ≤ n := by
  rw [← Nat.lt_size]
  exact Nat.sub_one_lt (by simp_rw [Nat.size_eq_zero.not, hn, not_false_eq_true])

end Size

section DivMod

theorem divMod_ext_iff {x y : ℕ} (d : ℕ) : x = y ↔ x / d = y / d ∧ x % d = y % d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp_rw [Nat.div_zero, mod_zero, true_and]
  · haveI : NeZero d := ⟨hd⟩
    rw [← (Nat.divModEquiv d).apply_eq_iff_eq]
    simp_rw [divModEquiv_apply, Prod.mk.injEq, Fin.ext_iff, Fin.val_natCast]

end DivMod

section Bit

lemma bit_true_zero : bit true 0 = 1 := rfl

end Bit

section BOdd

@[simp]
theorem bodd_toNat {m : ℕ} : m.bodd.toNat = m % 2 := (mod_two_of_bodd _).symm

end BOdd

section TestBit

theorem testBit_zero_eq_bodd (m : ℕ) : m.testBit 0 = m.bodd := by
  simp_rw [Nat.bodd_eq_one_and_ne_zero, testBit.eq_def, shiftRight_zero]

theorem testBit_succ_eq_testBit_div2 (m i : ℕ) : m.testBit (i + 1) = m.div2.testBit i := by
  simp_rw [testBit_succ, div2_val]

theorem testBit_bit (m : ℕ) (b : Bool) (n : ℕ) :
    (Nat.bit b n).testBit m = if m = 0 then b else n.testBit (m - 1) := by
  cases' m
  · simp_rw [Nat.testBit_bit_zero, if_true]
  · simp_rw [Nat.testBit_bit_succ, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]

@[simp]
theorem testBit_size_self {x : ℕ} : x.testBit x.size = false :=
  Nat.testBit_eq_false_of_lt x.lt_size_self

theorem testBit_pred_size_self {x : ℕ} : x ≠ 0 → x.testBit (x.size - 1) = true := by
  induction' x using Nat.binaryRec with b n IH
  · simp_rw [ne_eq, not_true_eq_false, false_implies]
  · intros H
    rw [Nat.size_bit H, succ_eq_add_one, Nat.add_sub_cancel, testBit_bit]
    rw [Nat.bit_ne_zero_iff] at H
    cases' n with n
    · simp_rw [size_zero, if_true]
      exact H rfl
    · simp_rw [size_succ, if_false]
      exact IH (succ_ne_zero _)

theorem lt_pow_two_iff_ge_imp_testBit_eq_false {n : Nat} {x : Nat} :
    x < 2 ^ n ↔ ∀ (i : Nat), i ≥ n → x.testBit i = false :=
  ⟨fun h _ hin => testBit_eq_false_of_lt (h.trans_le (Nat.pow_le_pow_of_le one_lt_two hin)),
  lt_pow_two_of_testBit _⟩

theorem exists_eq_add_iff_le {m n : ℕ} : m ≤ n ↔ ∃ k, n = m + k := by exact
  le_iff_exists_add

theorem testBit_ext_iff {q q' : ℕ} : q = q' ↔ (∀ i : ℕ, q.testBit i = q'.testBit i) :=
  ⟨fun h _ => h ▸ rfl, Nat.eq_of_testBit_eq⟩

theorem testBit_ne_iff {q q' : ℕ} : q ≠ q' ↔ (∃ i : ℕ, q.testBit i ≠ q'.testBit i) := by
  simp_rw [ne_eq, testBit_ext_iff, not_forall]

theorem testBit_ext_div_two_pow_iff {q q' m : ℕ} : q / 2^m = q' / 2^m ↔
  (∀ i ≥ m, q.testBit i = q'.testBit i) := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow, le_iff_exists_add',
  forall_exists_index, forall_eq_apply_imp_iff]

theorem testBit_ext_mod_two_pow_iff {q q' m : ℕ} : q % 2^m = q' % 2^m ↔
  (∀ i < m, q.testBit i = q'.testBit i) := by
  simp_rw [testBit_ext_iff, testBit_mod_two_pow, Bool.decide_and_eq_decide_and]

theorem testBit_one_succ {k : ℕ} : testBit 1 (k + 1) = false := by
  rw [testBit_succ, div_eq_of_lt one_lt_two, zero_testBit]

theorem testBit_one {k : ℕ} : testBit 1 k = decide (k = 0) := by
  cases k
  · exact testBit_one_zero
  · simp_rw [testBit_one_succ, Nat.succ_ne_zero, _root_.decide_false]

theorem testBit_toNat_zero {b : Bool} : b.toNat.testBit 0 = b :=
  b.recOn (zero_testBit _) testBit_one_zero

theorem testBit_toNat_succ {b : Bool} {k : ℕ} : b.toNat.testBit (k + 1) = false :=
  b.recOn (zero_testBit _) testBit_one_succ

theorem testBit_toNat {b : Bool} {k : ℕ} : b.toNat.testBit k = (decide (k = 0) && b) := b.recOn
((zero_testBit _).trans (Bool.and_false _).symm) (testBit_one.trans (Bool.and_true _).symm)

theorem testBit_true_iff_two_pow_le_mod_two_pow_succ {i k : ℕ} :
    testBit k i = true ↔ 2^i ≤ k % 2^(i + 1) := by
  rw [Nat.mod_pow_succ, ← Nat.one_le_div_iff (Nat.two_pow_pos i),
  Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), mod_div_self, zero_add,
  testBit_to_div_mod, decide_eq_true_eq]
  rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ i) with h | h
  · simp_rw [h, zero_lt_one.not_le, Nat.zero_ne_one]
  · simp_rw [h, le_rfl]

theorem testBit_false_iff_mod_two_pow_succ_lt_two_pow {i k : ℕ} :
    testBit k i = false ↔ k % 2^(i + 1) < 2^i := by
  rw [lt_iff_not_le, ← testBit_true_iff_two_pow_le_mod_two_pow_succ, Bool.not_eq_true]

theorem testBit_two_pow' (n : ℕ) (m : ℕ) : (2 ^ n).testBit m = decide (n = m) := by
  rcases eq_or_ne n m with rfl | h
  · simp_rw [testBit_two_pow_self, decide_true]
  · simp_rw [testBit_two_pow_of_ne h, h, decide_false]

theorem testBit_add_two_pow_eq (x : Nat) (i : Nat) :
    (x + 2^i).testBit i = !x.testBit i := by rw [add_comm, testBit_two_pow_add_eq]

theorem testBit_add_mul_two_pow (a : Nat) {b : Nat} {i : Nat} (b_lt : b < 2 ^ i) (j : Nat) :
    (b + 2 ^ i * a).testBit j = if j < i then b.testBit j else a.testBit (j - i) := by
  rw [add_comm]
  exact testBit_mul_pow_two_add a b_lt j

theorem testBit_add_mul_two_pow_eq (a : Nat) (b : Nat) (i : Nat) :
    (b + 2 ^ i * a).testBit i = (decide (a % 2 = 1)).xor (b.testBit i) := by
  rw [add_comm]
  exact testBit_mul_two_pow_add_eq a b i

theorem testBit_two_pow_add_ne_of_testBit_false {i : Nat} {j : Nat} (hij : i ≠ j) {x : Nat}
    (hx : x.testBit i = false) : (2 ^ i + x).testBit j = x.testBit j := by
  rcases hij.lt_or_lt with hij | hij
  · rw [testBit_to_div_mod, decide_eq_false_iff_not, ← ne_eq, mod_two_ne_one] at hx
    rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
    simp_rw [testBit_to_div_mod, decide_eq_decide,
    add_assoc, pow_add _ i,  pow_succ', ← Nat.div_div_eq_div_mul,
    Nat.add_div_left _ (Nat.two_pow_pos _)]
    rw [← div_add_mod (x / 2^i) 2]
    simp_rw [hx, add_assoc, Nat.mul_add_div (zero_lt_two), Nat.zero_div, zero_add,
    div_eq_of_lt (one_lt_two)]
  · rw [testBit_two_pow_add_gt hij]

theorem testBit_add_two_pow_ne_of_testBit_false {i : Nat} {j : Nat} (hij : i ≠ j) {x : Nat}
    (hx : x.testBit i = false)  : (x + 2^i).testBit j = x.testBit j := by
  rw [add_comm, testBit_two_pow_add_ne_of_testBit_false hij hx]

theorem testBit_sub_two_pow_ne_of_testBit_true {i : Nat} {j : Nat} (hij : i ≠ j) {x : Nat}
    (hx : x.testBit i = true) : (x - 2^i).testBit j = x.testBit j := by
  rcases Nat.exists_eq_add_of_le' (Nat.testBit_implies_ge hx) with ⟨x, rfl⟩
  rw [testBit_add_two_pow_eq, Bool.not_eq_true'] at hx
  exact Nat.add_sub_cancel _ _ ▸ (testBit_add_two_pow_ne_of_testBit_false hij hx).symm

theorem testBit_sub_two_pow_eq_of_testBit_true {i : Nat} {x : Nat}
    (hx : x.testBit i = true) : (x - 2^i).testBit i = !x.testBit i := by
  rcases Nat.exists_eq_add_of_le' (Nat.testBit_implies_ge hx) with ⟨x, rfl⟩
  rw [testBit_add_two_pow_eq, Bool.not_eq_true'] at hx
  rw [Nat.add_sub_cancel, testBit_add_two_pow_eq, Bool.not_not]

theorem exists_pow_two_mul_of_testBit {k : ℕ} (b : ℕ) (hb : ∀ i < k, b.testBit i = false) :
    ∃ n, b = 2^k * n := by
  induction' k with k IH generalizing b
  · exact ⟨b, by rw [pow_zero, one_mul]⟩
  · rcases IH _ (fun i hi => hb i  (hi.trans (Nat.lt_succ_self _))) with ⟨b, rfl⟩
    have h := hb k (Nat.lt_succ_self _)
    simp_rw [testBit_mul_pow_two, le_refl, decide_true, Bool.true_and, Nat.sub_self,
      testBit_zero, decide_eq_false_iff_not, mod_two_ne_one, ← Nat.dvd_iff_mod_eq_zero] at h
    rcases h with ⟨b, rfl⟩
    exact ⟨b, by rw [← mul_assoc, pow_succ]⟩

theorem nat_eq_testBit_sum_range {a m : ℕ} (ha : a < 2^m) :
    a = ∑ i ∈ Finset.range m, (a.testBit i).toNat * 2^i := by
  induction' m with m IH generalizing a
  · simp_rw [pow_zero, lt_one_iff] at ha
    simp_rw [ha, Finset.range_zero, zero_testBit, Bool.toNat_false, zero_mul,
      Finset.sum_const_zero]
  · rw [Finset.sum_range_succ]
    rcases lt_or_le a (2^m) with h | h
    · rw [testBit_lt_two_pow h, Bool.toNat_false, zero_mul, add_zero]
      exact IH h
    · rcases (Nat.exists_eq_add_of_le h) with ⟨a, rfl⟩
      rw [pow_succ', two_mul, add_lt_add_iff_left] at ha
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha,
      Bool.not_false, Bool.toNat_true, one_mul]
      nth_rewrite 1 [add_comm, add_left_inj, IH ha]
      apply Finset.sum_equiv (Equiv.refl _) (by simp_rw [Equiv.refl_apply, implies_true])
      simp_rw [Finset.mem_range, Equiv.refl_apply, mul_eq_mul_right_iff, pow_eq_zero_iff',
        two_ne_zero, false_and, or_false]
      exact fun _ hi => (Nat.testBit_two_pow_add_gt hi _) ▸ rfl

theorem nat_eq_testBit_tsum {a : ℕ} :
    a = ∑' i, (a.testBit i).toNat * 2^i := by
  rcases pow_unbounded_of_one_lt a one_lt_two with ⟨k, ha⟩
  refine (nat_eq_testBit_sum_range ha).trans (tsum_eq_sum ?_).symm
  simp_rw [Finset.mem_range, not_lt, _root_.mul_eq_zero, Bool.toNat_eq_zero, pow_eq_zero_iff',
    two_ne_zero, false_and, or_false]
  exact fun _ hj => testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_of_le one_lt_two hj))

end TestBit


def bitMatchUnder {n : ℕ} (i : ℕ) (x : Fin (2^n)) :=
  (Finset.range (2 ^ n)).filter (fun y => ∀ k < i, y.testBit k = (x : ℕ).testBit k)

section BitMatchUnder

variable {n : ℕ} {x : Fin (2^n)} {i : ℕ}

@[simp]
theorem mem_bitMatchUnder_iff {q : ℕ} :
    q ∈ bitMatchUnder i x ↔ q < 2 ^ n ∧ ∀ k < i, q.testBit k = (x : ℕ).testBit k := by
  unfold bitMatchUnder
  simp_rw [Finset.mem_filter, Finset.mem_range]

theorem card_bitMatchUnder (i : ℕ) (x : Fin (2^n)) :
    (bitMatchUnder i x).card = 2^(n - i) := by
  rw [← Fintype.card_fin (2^(n - i)),
    Fintype.card_congr finFunctionFinEquiv.symm]
  refine Finset.card_eq_of_equiv_fintype
    (Equiv.ofBijective (fun a t => finTwoEquiv.symm (a.1.testBit ((t : ℕ) + i)))
    ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_, ?_⟩)
  · simp_rw [Subtype.mk.injEq, funext_iff, Equiv.apply_eq_iff_eq, Fin.forall_iff,
      Nat.lt_sub_iff_add_lt, testBit_ext_iff]
    simp_rw [mem_bitMatchUnder_iff] at ha hb
    intro hab t
    rcases lt_or_le t n with htn | htn
    · rcases lt_or_le t i with hti | hti
      · rw [ha.2 _ hti, hb.2 _ hti]
      · rcases Nat.exists_eq_add_of_le' hti with ⟨_, rfl⟩
        exact hab _ htn
    · rw [Nat.testBit_eq_false_of_lt (ha.1.trans_le
        (Nat.pow_le_pow_right zero_lt_two htn)),
        Nat.testBit_eq_false_of_lt (hb.1.trans_le
        (Nat.pow_le_pow_right zero_lt_two htn))]
  · unfold Function.Surjective
    simp_rw [Equiv.forall_congr_left finFunctionFinEquiv, Subtype.exists, exists_prop,
       mem_bitMatchUnder_iff, funext_iff, Equiv.symm_apply_eq, finTwoEquiv_apply,
       Fin.forall_iff, Nat.lt_sub_iff_add_lt,
       Fin.ext_iff, Fin.val_one, finFunctionFinEquiv_symm_apply_val, ← Nat.testBit_zero,
       Nat.testBit_div_two_pow, Nat.zero_add]
    refine fun b hb => ⟨x % 2^(i : ℕ) + 2^(i : ℕ)*b, ?_⟩
    simp_rw [testBit_add_mul_two_pow b (Nat.mod_lt _ (Nat.two_pow_pos _)), testBit_mod_two_pow,
      add_lt_iff_neg_right, Nat.not_lt_zero, if_false, Nat.add_sub_cancel, implies_true,
      and_true]
    refine ⟨?_, fun _ h => (if_pos h).trans
        (Bool.and_iff_right_iff_imp.mpr (fun _ => decide_eq_true h))⟩
    rcases le_or_lt i n with hi | hi
    · refine Nat.lt_of_div_lt_div (c := 2^(i : ℕ)) ?_
      rwa [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), zero_add,
        Nat.pow_div hi zero_lt_two]
    · rw [Nat.sub_eq_zero_of_le hi.le, pow_zero, Nat.lt_one_iff] at hb
      rw [hb, mul_zero, add_zero]
      exact (Nat.mod_le _ _).trans_lt x.isLt

end BitMatchUnder

section Lor

theorem or_one {a : ℕ} : a ||| 1 = bit true a.div2 := by
  simp_rw [testBit_ext_iff, testBit_or, testBit_one,
    testBit_bit, div2_val, testBit_div_two]
  rintro (_ | i)
  · simp_rw [testBit_zero, decide_true, Bool.or_true, if_true]
  · simp_rw [add_eq_zero, one_ne_zero, and_false, decide_false,
    Bool.or_false, add_tsub_cancel_right, if_false]

theorem or_eq_add_two_pow_mul_of_lt_right {a b i : ℕ} (ha : a < 2^i) :
    2^i * b ||| a = 2^i * b + a := (mul_add_lt_is_or ha _).symm

theorem or_eq_add_two_pow_mul_of_lt_left {a b i : ℕ} (ha : a < 2^i) :
    a ||| 2^i * b = a + 2^i * b := by rw [lor_comm, add_comm, or_eq_add_two_pow_mul_of_lt_right ha]

theorem or_eq_add_two_pow_of_lt_left {a i: ℕ} (ha : a < 2^i) :
    a ||| 2^i = a + 2^i := by
  rw [← (Nat.mul_one (2^i)), or_eq_add_two_pow_mul_of_lt_left ha]

theorem or_eq_add_two_pow_of_lt_right {a i: ℕ} (ha : a < 2^i) :
    2^i ||| a = 2^i + a := by
  rw [lor_comm, add_comm]
  exact or_eq_add_two_pow_of_lt_left ha

theorem or_shiftLeft {a b i : ℕ} : (a ||| b) <<< i = (a <<< i) ||| (b <<< i) := by
  rw [testBit_ext_iff]
  simp only [testBit_or, testBit_shiftLeft]
  intros j
  rcases lt_or_le j i with hji | hji
  · simp_rw [hji.not_le, decide_false, Bool.false_and, Bool.false_or]
  · simp_rw [hji, decide_true, Bool.true_and]

theorem or_shiftRight {a b i : ℕ} : (a ||| b) >>> i = (a >>> i) ||| (b >>> i) := by
  simp only [testBit_ext_iff, testBit_or, testBit_shiftRight, implies_true]

end Lor

section Land

theorem and_shiftLeft {a b i : ℕ} : (a &&& b) <<< i = (a <<< i) &&& (b <<< i) := by
  rw [testBit_ext_iff]
  simp only [testBit_and, testBit_shiftLeft]
  intros j
  rcases lt_or_le j i with hji | hji
  · simp_rw [hji.not_le, decide_false, Bool.false_and]
  · simp_rw [hji, decide_true, Bool.true_and]

theorem and_shiftRight {a b i : ℕ} : (a &&& b) >>> i = (a >>> i) &&& (b >>> i) := by
  simp only [testBit_ext_iff, testBit_and, testBit_shiftRight, implies_true]

end Land

section Lxor

theorem xor_shiftLeft {a b i : ℕ} : (a ^^^ b) <<< i = (a <<< i) ^^^ (b <<< i) := by
  rw [testBit_ext_iff]
  simp only [testBit_xor, testBit_shiftLeft]
  intros j
  rcases lt_or_le j i with hji | hji
  · simp_rw [hji.not_le, decide_false, Bool.false_and, Bool.false_xor]
  · simp_rw [hji, decide_true, Bool.true_and]

theorem xor_shiftRight {a b i : ℕ} : (a ^^^ b) >>> i = (a >>> i) ^^^ (b >>> i) := by
  simp only [testBit_ext_iff, testBit_xor, testBit_shiftRight, implies_true]

end Lxor

section ShiftLeft

@[simp]
theorem shiftLeft_one {m : ℕ} : m <<< 1 = 2 * m := rfl

end ShiftLeft

section ShiftLeft'

theorem shiftLeft'_zero {b : Bool} {m : ℕ}  : shiftLeft' b m 0 = m := rfl
theorem shiftLeft'_succ {b : Bool} {m i: ℕ} :
    (shiftLeft' b m i.succ) = bit b (shiftLeft' b m i) := rfl

theorem testBit_shiftLeft' {b : Bool} {m i j : ℕ}  :
    (shiftLeft' b m i).testBit j = bif j < i then b else m.testBit (j - i) := by
  induction' i with i IH generalizing j
  · simp_rw [shiftLeft'_zero, Nat.not_lt_zero, decide_false, cond_false, Nat.sub_zero]
  · simp_rw [shiftLeft'_succ, Nat.lt_succ_iff]
    cases b
    · simp_rw [bit_false]
      rw [← pow_one 2, testBit_mul_pow_two, IH]
      cases' j
      · simp_rw [zero_lt_one.not_le, decide_false, Bool.false_and, zero_le, decide_true, cond_true]
      · simp_rw [Nat.add_sub_cancel, Nat.add_sub_add_right, Nat.succ_le_iff, zero_lt_succ,
          decide_true, Bool.true_and]
    · simp_rw [bit_true, Bool.cond_true_left]
      rw [← pow_one 2, testBit_mul_pow_two_add _ (one_lt_two), IH]
      simp only [pow_one, Bool.cond_true_left]
      cases' j
      · simp_rw [zero_lt_one, if_true, zero_le, decide_true, Bool.true_or,
          testBit_zero, decide_true]
      · simp_rw [Nat.add_sub_cancel, Nat.add_sub_add_right, Nat.succ_le_iff, Nat.succ_lt_succ_iff,
        Nat.not_lt_zero, if_false]

theorem testBit_shiftLeft'_true {m i j : ℕ}  :
    (shiftLeft' true m i).testBit j = ((j < i) || m.testBit (j - i)) := by
  rw [testBit_shiftLeft']
  rcases lt_or_le j i with hji | hji
  · simp_rw [hji, decide_true, cond_true, Bool.true_or]
  · simp_rw [hji.not_lt, decide_false, cond_false, Bool.false_or]

theorem testBit_shiftLeft'_false {m i j : ℕ}  :
    (shiftLeft' false m i).testBit j = (!(j < i) && m.testBit (j - i)) := by
  rw [testBit_shiftLeft']
  rcases lt_or_le j i with hji | hji
  · simp_rw [hji, decide_true, cond_true, Bool.not_true, Bool.false_and]
  · simp_rw [hji.not_lt, decide_false, cond_false, Bool.not_false, Bool.true_and]

theorem shiftLeft'_true {m : ℕ} (n : ℕ) :
    shiftLeft' true m n = (m <<< n) ^^^ (1 <<< n - 1) := by
  simp_rw [testBit_ext_iff, testBit_shiftLeft'_true, testBit_xor, testBit_shiftLeft,
  shiftLeft_eq_mul_pow, one_mul, testBit_two_pow_sub_one]
  intro i
  rcases lt_or_le i n with hin | hin
  · simp_rw [hin, hin.not_le, decide_true, decide_false, Bool.false_and,
    Bool.false_xor, Bool.true_or]
  · simp_rw [hin.not_lt, hin, decide_true, decide_false, Bool.true_and,
    Bool.xor_false, Bool.false_or]

theorem shiftLeft'_eq_shiftLeft_xor_shiftLeft_sub_one {m : ℕ} {b : Bool} (n : ℕ) :
    shiftLeft' b m n = (m <<< n) ^^^ (b.toNat <<< n - 1) := by
  cases b
  · rw [shiftLeft'_false, Bool.toNat_false, zero_shiftLeft, Nat.zero_sub, xor_zero]
  · rw [shiftLeft'_true, Bool.toNat_true]

end ShiftLeft'

section BitResiduum

variable {p q i j k m n : ℕ} {b b' : Bool}

def testRes (q i : ℕ) := ((q >>> (i + 1)) <<< i) ||| (q &&& (2^i - 1))

def mergeBitRes (b : Bool) (p : ℕ) (i : ℕ) :=
  ((p >>> i) <<< (i + 1)) ||| (p &&& (2^i - 1)) ||| (b.toNat <<< i)

theorem testRes_def : q.testRes i = (q >>> (i + 1)) <<< i ||| q &&& (2^i - 1) := rfl

theorem mergeBitRes_def : p.mergeBitRes b i =
    ((p >>> i) <<< (i + 1)) ||| (p &&& (2^i - 1)) ||| (b.toNat <<< i) := rfl

-- inductive definition
theorem testRes_zero : q.testRes 0 = q.div2 := by
  simp_rw [testRes_def, zero_add, shiftLeft_zero, pow_zero, tsub_self, and_zero,
    or_zero, shiftRight_one, div2_val]

theorem mergeBitRes_zero : q.mergeBitRes b 0 = q.bit b := by
  simp_rw [mergeBitRes_def, shiftRight_zero, zero_add, pow_zero, tsub_self,
    and_zero, or_zero, shiftLeft_zero, shiftLeft_one]
  cases b
  · simp_rw [Bool.toNat_false, or_zero, bit_false]
  · simp_rw [Bool.toNat_true, or_one, div2_bit0]

theorem testRes_succ {q : ℕ} : q.testRes (i + 1) = (q.div2.testRes i).bit q.bodd := by
  simp_rw [testRes_def, and_pow_two_sub_one_eq_mod, testBit_ext_iff, testBit_bit, testBit_or,
    testBit_shiftLeft, testBit_shiftRight, testBit_mod_two_pow]
  rintro (_ | _)
  · simp_rw [le_zero_iff, succ_ne_zero, if_true, zero_lt_succ, decide_true, decide_false,
      Bool.false_and, Bool.false_or, Bool.true_and, testBit_zero_eq_bodd]
  · simp_rw [succ_ne_zero, if_false, add_le_add_iff_right, add_lt_add_iff_right,
      add_tsub_cancel_right, add_tsub_add_eq_tsub_right,
      Nat.add_right_comm _ 1, testBit_succ_eq_testBit_div2]

theorem mergeBitRes_succ {q : ℕ} :
    q.mergeBitRes b (i + 1) = (q.div2.mergeBitRes b i).bit q.bodd := by
  simp_rw [mergeBitRes_def, and_pow_two_sub_one_eq_mod, testBit_ext_iff, testBit_bit, testBit_or,
    testBit_shiftLeft, testBit_shiftRight, testBit_mod_two_pow]
  rintro (_ | _)
  · simp_rw [le_zero_iff, succ_ne_zero, if_true, zero_lt_succ, decide_true, decide_false,
      Bool.false_and, Bool.false_or, Bool.or_false, Bool.true_and, testBit_zero_eq_bodd]
  · simp_rw [succ_ne_zero, if_false, add_le_add_iff_right, add_lt_add_iff_right,
      add_tsub_cancel_right, add_tsub_add_eq_tsub_right,
      Nat.add_right_comm _ 1, testBit_succ_eq_testBit_div2]

-- basic combination eq theorems

@[simp]
theorem testBit_mergeBitRes_of_eq {p : ℕ} : (p.mergeBitRes b i).testBit i = b := by
  induction i generalizing p b with | zero => _ | succ _ IH => _
  · simp_rw [mergeBitRes_zero, testBit_bit_zero]
  · simp_rw [mergeBitRes_succ, testBit_succ_eq_testBit_div2, div2_bit, IH]

@[simp]
theorem testRes_mergeBitRes_of_eq {p : ℕ} : (p.mergeBitRes b i).testRes i = p := by
  induction i generalizing p b with | zero => _ | succ _ IH => _
  · simp_rw [mergeBitRes_zero, testRes_zero, div2_bit]
  · simp_rw [mergeBitRes_succ, testRes_succ, div2_bit, bodd_bit, IH, bit_decomp]

@[simp]
theorem mergeBitRes_testBit_testRes_of_eq {q : ℕ} :
    (q.testRes i).mergeBitRes (q.testBit i) i = q := by
  induction i generalizing q with | zero => _ | succ _ IH => _
  · simp_rw [mergeBitRes_zero, testRes_zero, testBit_zero_eq_bodd, bit_decomp]
  · simp_rw [mergeBitRes_succ, testRes_succ, testBit_succ_eq_testBit_div2,
      div2_bit, bodd_bit, IH, bit_decomp]

-- Equivalence family

section MergeBitEquiv

open Equiv

@[pp_nodot, simps! symm_apply_fst symm_apply_snd apply]
def mergeBitResEquiv (i : ℕ) : Bool × ℕ ≃ ℕ where
  toFun bp := bp.2.mergeBitRes bp.1 i
  invFun n := (n.testBit i, n.testRes i)
  left_inv _ := Prod.ext testBit_mergeBitRes_of_eq testRes_mergeBitRes_of_eq
  right_inv _ := mergeBitRes_testBit_testRes_of_eq

theorem mergeBitResEquiv_zero : mergeBitResEquiv 0 = boolProdNatEquivNat := by
  simp_rw [Equiv.ext_iff, Equiv.boolProdNatEquivNat_apply, Function.uncurry_def,
    mergeBitResEquiv_apply, mergeBitRes_zero, implies_true]

theorem mergeBitResEquiv_succ : mergeBitResEquiv (i + 1) =
  (prodCongrRight (fun _ => (mergeBitResEquiv 0).symm)).trans (
    (Equiv.prodAssoc _ _ _).symm.trans (
      (prodCongrLeft (fun _ => Equiv.prodComm _ _)).trans (
        (Equiv.prodAssoc _ _ _).trans ((prodCongrRight (fun _ => mergeBitResEquiv i)).trans
        (mergeBitResEquiv 0))))) := by
  simp_rw [Equiv.ext_iff, trans_apply, prodAssoc_symm_apply, prodCongrLeft_apply, prodComm_apply,
    Prod.swap_prod_mk, prodAssoc_apply, mergeBitResEquiv_apply, Prod.forall,
    prodCongrRight_apply, mergeBitResEquiv_symm_apply_fst, mergeBitResEquiv_symm_apply_snd,
    mergeBitResEquiv_apply, mergeBitRes_succ, mergeBitRes_zero, testBit_zero_eq_bodd,
    testRes_zero, implies_true]

end MergeBitEquiv

-- basic application theorems

theorem testRes_apply : q.testRes i = 2^i * (q / 2^(i + 1)) + q % 2^i := by
  induction i generalizing q with | zero => _ | succ _ IH => _
  · simp_rw [testRes_zero, div2_val, pow_zero, zero_add, pow_one, one_mul, mod_one, add_zero]
  · simp_rw [testRes_succ, IH, bit_val, div2_val, bodd_toNat, pow_succ', mod_mul, mul_add,
    mul_assoc, Nat.div_div_eq_div_mul, add_assoc, add_comm]

theorem mergeBitRes_apply : p.mergeBitRes b i = p + 2^i * ((p / 2^i) + b.toNat) := by
  induction i generalizing p b with | zero => _ | succ _ IH => _
  · simp_rw [mergeBitRes_zero, bit_val, pow_zero, Nat.div_one, one_mul, two_mul, add_assoc]
  · simp_rw [mergeBitRes_succ, IH, bit_val, div2_val, bodd_toNat, pow_succ', mul_add, mul_assoc,
      Nat.div_div_eq_div_mul, add_right_comm, Nat.div_add_mod]

-- apply lemmas

theorem mergeBitRes_apply_false {p : ℕ} : p.mergeBitRes false i = p + (2^i) * (p / 2^i) := by
  simp_rw [mergeBitRes_apply, Bool.toNat_false, add_zero]

theorem mergeBitRes_apply_false_of_lt_two_pow {p : ℕ} (hp : p < 2^i) :
    p.mergeBitRes false i = p := by
  simp_rw [mergeBitRes_apply_false, Nat.div_eq_of_lt hp, mul_zero, add_zero]

theorem mergeBitRes_apply_true {p : ℕ} : p.mergeBitRes true i = p + (2^i) * (p / 2^i) + (2^i) := by
  simp_rw [mergeBitRes_apply, Bool.toNat_true, mul_add, mul_one, add_assoc]

theorem mergeBitRes_apply_false_add_pow_two {p : ℕ} :
    p.mergeBitRes false i + 2^i = p.mergeBitRes true i := by
  simp_rw [mergeBitRes_apply_false, mergeBitRes_apply_true]

theorem mergeBitRes_apply_true_sub_pow_two {p : ℕ} :
    p.mergeBitRes true i - 2^i = p.mergeBitRes false i := by
  simp_rw [mergeBitRes_apply_false, mergeBitRes_apply_true, Nat.add_sub_cancel]

theorem mergeBitRes_apply_not {p : ℕ} : p.mergeBitRes (!b) i =
    (bif b then p.mergeBitRes b i - 2^i else p.mergeBitRes b i + 2^i) := by
  cases b
  · rw [Bool.not_false, cond_false, mergeBitRes_apply_false_add_pow_two]
  · rw [Bool.not_true, cond_true, mergeBitRes_apply_true_sub_pow_two]

-- testBit_testRes

theorem testBit_testRes_of_lt {i j q : ℕ} (hij : i < j) :
    (q.testRes j).testBit i = q.testBit i := by
  simp_rw [testRes_def, testBit_or, testBit_and, testBit_shiftLeft, testBit_two_pow_sub_one,
  hij.not_le, hij, decide_false, Bool.false_and, Bool.false_or,
  decide_true, Bool.and_true]

theorem testBit_testRes_of_ge {i j q : ℕ} (hij : j ≤ i) :
    (q.testRes j).testBit i = q.testBit (i + 1) := by
  simp_rw [testRes_def, testBit_or, testBit_shiftLeft, testBit_shiftRight, add_right_comm,
  add_tsub_cancel_of_le hij, testBit_and, testBit_two_pow_sub_one, hij.not_lt, hij,
  decide_true, Bool.true_and, decide_false, Bool.and_false, Bool.or_false]

theorem testBit_testRes {i j q : ℕ} :
    (q.testRes j).testBit i = q.testBit (i + (decide (j ≤ i)).toNat) := by
  rcases le_or_lt j i with hij | hij
  · rw [testBit_testRes_of_ge hij, Bool.toNat_pos hij]
  · rw [testBit_testRes_of_lt hij, Bool.toNat_neg hij.not_le, add_zero]

theorem testBit_pred_testRes_of_gt {i j q : ℕ} (hij : j < i) :
    (q.testRes j).testBit (i - 1) = q.testBit i := by
  rw [testBit_testRes_of_ge (Nat.le_sub_one_of_lt hij), Nat.sub_add_cancel (one_le_of_lt hij)]

theorem testBit_testRes_succ_of_le {i j q : ℕ} (hij : i ≤ j) :
    (q.testRes (j + 1)).testBit i = q.testBit i := by
  rw [testBit_testRes_of_lt (Nat.lt_succ_of_le hij)]

-- testRes equalities and inequalities

theorem testRes_div_two_pow_eq (h : i ≤ k) : q.testRes i / 2^k = q / 2^(k + 1) := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow,
  testBit_testRes_of_ge (h.trans (Nat.le_add_left _ _)), Nat.add_assoc, implies_true]

theorem testRes_mod_two_pow_eq (h : k ≤ i) : q.testRes i % 2^k = q % 2^k := by
  simp_rw [testBit_ext_iff, testBit_mod_two_pow]
  intro j
  rcases lt_or_le j k with hjk | hjk
  · simp_rw [hjk, testBit_testRes_of_lt (hjk.trans_le h)]
  · simp_rw [hjk.not_lt, decide_false, Bool.false_and]

theorem testRes_modEq_two_pow (h : k ≤ i) : q.testRes i ≡ q [MOD 2^k] := testRes_mod_two_pow_eq h

theorem testRes_lt_iff_lt_two_mul (hin : 2^i ∣ n) : q.testRes i < n ↔ q < 2 * n := by
  rcases hin with ⟨k, rfl⟩
  simp_rw [← mul_assoc, ← pow_succ', mul_comm _ k,
  ← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), testRes_div_two_pow_eq le_rfl]

theorem testRes_lt_div_two_iff_lt (hin : 2^(i + 1) ∣ n) : q.testRes i < n / 2 ↔ q < n := by
  rcases hin with ⟨k, rfl⟩
  rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ (zero_lt_two),
    ← testRes_lt_iff_lt_two_mul (dvd_mul_right _ _)]

theorem testRes_lt_two_pow_mul_iff_lt_two_pow_mul (h : i ≤ k) (n : ℕ) :
    q.testRes i < 2^k * n ↔ q < 2^(k + 1) * n := by
  rw [testRes_lt_iff_lt_two_mul (dvd_mul_of_dvd_left (pow_dvd_pow _ h) _), pow_succ', mul_assoc]

theorem testRes_lt_two_pow_iff_lt_two_pow (h : i ≤ m) : q.testRes i < 2^m ↔ q < 2^(m + 1) := by
  have H := testRes_lt_two_pow_mul_iff_lt_two_pow_mul h 1 (q := q)
  simp_rw [mul_one] at H
  exact H

-- testBit_mergeBitRes

theorem testBit_mergeBitRes_of_lt {i j p : ℕ} (hij : i < j) :
    (p.mergeBitRes b j).testBit i = p.testBit i := by
  simp only [mergeBitRes_def, and_pow_two_sub_one_eq_mod, testBit_or, testBit_shiftLeft, ge_iff_le,
    (lt_succ_of_lt hij).not_le, decide_false, testBit_shiftRight, Bool.false_and,
    testBit_mod_two_pow, hij, decide_true, Bool.true_and, Bool.false_or, hij.not_le, Bool.or_false]

theorem testBit_mergeBitRes_of_gt {i j p : ℕ} (hij : j < i) :
    (p.mergeBitRes b j).testBit i = p.testBit (i - 1) := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
  simp_rw [mergeBitRes_def, and_pow_two_sub_one_eq_mod, testBit_or, testBit_shiftLeft,
    testBit_shiftRight,
    testBit_mod_two_pow, ← Nat.add_sub_assoc (succ_le_of_lt hij), succ_eq_add_one,
    Nat.add_sub_add_left, succ_le_of_lt hij, add_comm j, Nat.add_right_comm _ j,
    Nat.add_sub_cancel, testBit_toNat_succ, (Nat.le_add_left j _).not_lt, decide_true,
    Bool.true_and, decide_false, Bool.false_and, Bool.and_false, Bool.or_false]

theorem testBit_mergeBitRes_of_ne {i j p : ℕ} (hij : i ≠ j) : (p.mergeBitRes b j).testBit i =
    p.testBit (i - (decide (j < i)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [testBit_mergeBitRes_of_lt hij, Bool.toNat_neg (hij.not_lt), tsub_zero] ;
  · simp only [testBit_mergeBitRes_of_gt hij, Bool.toNat_pos hij]

theorem testBit_mergeBitRes {i j p : ℕ} : (p.mergeBitRes b j).testBit i =
    bif (i = j) then b else p.testBit (i - (decide (j < i)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testBit_mergeBitRes_of_eq, decide_true, cond_true]
  · simp_rw [hij, testBit_mergeBitRes_of_ne hij, decide_false, cond_false]

theorem testBit_mergeBitRes_succ_of_le {i j p : ℕ} (hij : i ≤ j) :
    (p.mergeBitRes b (j + 1)).testBit i = p.testBit i := by
  rw [testBit_mergeBitRes_of_lt (Nat.lt_succ_of_le hij)]

theorem testBit_succ_mergeBitRes_of_ge {i j p : ℕ} (hij : j ≤ i) :
    (p.mergeBitRes b j).testBit (i + 1) = p.testBit i := by
  rw [testBit_mergeBitRes_of_gt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

-- Remaining of_eq theorems

theorem mergeBitRes_eq_iff : p.mergeBitRes b i = q ↔ (b = testBit q i) ∧ (p = q.testRes i) :=
  ⟨fun H => H ▸ ⟨testBit_mergeBitRes_of_eq.symm, testRes_mergeBitRes_of_eq.symm⟩,
    fun h => by simp_rw [h, mergeBitRes_testBit_testRes_of_eq]⟩

theorem mergeBitRes_eq_mergeBitRes_iff {r : ℕ} :
    q.mergeBitRes b i = r.mergeBitRes b' i ↔ b = b' ∧ q = r := by
  rw [mergeBitRes_eq_iff, testBit_mergeBitRes_of_eq, testRes_mergeBitRes_of_eq]

theorem mergeBitRes_inj {p q : ℕ} : p.mergeBitRes b i = q.mergeBitRes b i ↔ p = q := by
  simp_rw [mergeBitRes_eq_mergeBitRes_iff, true_and]

theorem mergeBitRes_inj_right {p : ℕ} : p.mergeBitRes b i = p.mergeBitRes b' i ↔ b = b' := by
  simp_rw [mergeBitRes_eq_mergeBitRes_iff, and_true]

theorem eq_mergeBitRes_iff : p = q.mergeBitRes b i ↔ (testBit p i = b) ∧ (p.testRes i = q) := by
  simp_rw [eq_comm (a := p), mergeBitRes_eq_iff, eq_comm]

theorem testRes_eq_iff : p.testRes i = q ↔ p = q.mergeBitRes (p.testBit i) i := by
  simp_rw [eq_mergeBitRes_iff, true_and]

theorem eq_testRes_iff : p = q.testRes i ↔ p.mergeBitRes (q.testBit i) i = q := by
  simp_rw [mergeBitRes_eq_iff, true_and]

theorem mergeBitRes_injective : (mergeBitRes b · i).Injective := fun _ _ => by
  simp_rw [mergeBitRes_inj, imp_self]

theorem mergeBitRes_right_injective : (mergeBitRes · p i).Injective := fun _ _ => by
  simp_rw [mergeBitRes_inj_right, imp_self]

-- inequalities

theorem mergeBitRes_strictMono : StrictMono (mergeBitRes b · i) := by
  refine Monotone.strictMono_of_injective
    (fun p q hpq => ?_) mergeBitRes_injective
  simp_rw [mergeBitRes_apply, mul_add, ← add_assoc]
  exact Nat.add_le_add_right (Nat.add_le_add hpq (Nat.mul_le_mul_left _
    (Nat.div_le_div_right hpq))) _

theorem mergeBitRes_false_lt_mergeBitRes_true {q : ℕ} :
    q.mergeBitRes false i < q.mergeBitRes true i :=
  mergeBitRes_apply_false_add_pow_two ▸ Nat.lt_add_of_pos_right (Nat.two_pow_pos _)

theorem mergeBitRes_strictMono_right : StrictMono (mergeBitRes · p i) := by
  refine Monotone.strictMono_of_injective
    (fun b b' => b.rec (fun _ => b'.rec le_rfl mergeBitRes_false_lt_mergeBitRes_true.le)
    (fun hbb' => hbb' rfl ▸ le_rfl)) mergeBitRes_right_injective

theorem mergeBitRes_lt_mergeBitRes_iff_lt {r : ℕ} :
    q.mergeBitRes b i < r.mergeBitRes b i ↔ q < r :=
  mergeBitRes_strictMono.lt_iff_lt

theorem mergeBitRes_le_mergeBitRes_iff_le {r : ℕ} :
    q.mergeBitRes b i ≤ r.mergeBitRes b i ↔ q ≤ r :=
  mergeBitRes_strictMono.le_iff_le

theorem lt_testRes_iff {p : ℕ} : q < p.testRes i ↔ q.mergeBitRes (p.testBit i) i < p := by
  nth_rewrite 3 [← mergeBitRes_testBit_testRes_of_eq (q := p) (i := i)]
  rw [mergeBitRes_lt_mergeBitRes_iff_lt]

theorem testRes_lt_iff {p : ℕ} : p.testRes i < q ↔ p < q.mergeBitRes (p.testBit i) i := by
  nth_rewrite 2 [← mergeBitRes_testBit_testRes_of_eq (q := p) (i := i)]
  rw [mergeBitRes_lt_mergeBitRes_iff_lt]

theorem testRes_lt_testRes_iff_lt_of_testBit_eq_testBit {p q : ℕ} (h : p.testBit i = q.testBit i) :
    p.testRes i < q.testRes i ↔ p < q := by
  rw [lt_testRes_iff, ← h, mergeBitRes_testBit_testRes_of_eq]

theorem le_testRes_iff {p : ℕ} : q ≤ p.testRes i ↔ q.mergeBitRes (p.testBit i) i ≤ p := by
  nth_rewrite 3 [← mergeBitRes_testBit_testRes_of_eq (q := p) (i := i)]
  rw [mergeBitRes_le_mergeBitRes_iff_le]

theorem testRes_le_iff {p : ℕ} : p.testRes i ≤ q ↔ p ≤ q.mergeBitRes (p.testBit i) i := by
  nth_rewrite 2 [← mergeBitRes_testBit_testRes_of_eq (q := p) (i := i)]
  rw [mergeBitRes_le_mergeBitRes_iff_le]

theorem testRes_le_testRes_iff_lt_of_testBit_eq {p q : ℕ} (h : p.testBit i = q.testBit i) :
    q.testRes i ≤ p.testRes i ↔ q ≤ p := by
  rw [le_testRes_iff, h, mergeBitRes_testBit_testRes_of_eq]

-- testRes_mergeBitRes

theorem testRes_mergeBitRes_of_gt {p : ℕ} (hij : j < i) :
    (p.mergeBitRes b j).testRes i = (p.testRes (i - 1)).mergeBitRes b j := by
  simp only [hij, decide_true, Bool.toNat_true, testBit_ext_iff,
    testBit_testRes, testBit_mergeBitRes, tsub_le_iff_right]
  intro k
  rcases lt_trichotomy j (k + (decide (i ≤ k)).toNat) with hjk | rfl | hjk
  · have H : j < k := (le_or_lt i k).by_cases (lt_of_le_of_lt' · hij)
      (fun h => hjk.trans_eq (by simp_rw [h.not_le, decide_false, Bool.toNat_false, add_zero]))
    simp only [hjk.ne', decide_false, hjk, decide_true, Bool.toNat_true,
      Nat.sub_add_comm (one_le_of_lt H), cond_false, H.ne', H,
      Nat.sub_one_add_one_eq_of_pos (zero_lt_of_lt H)]
  · simp only [decide_true, lt_self_iff_false, decide_false, Bool.toNat_false,
      tsub_zero, cond_true, self_eq_add_right, Bool.toNat_eq_zero, decide_eq_false_iff_not,
      not_le, (le_self_add).trans_lt hij, add_lt_iff_neg_left, not_lt_zero']
  · have hkj : k < j := le_self_add.trans_lt hjk
    have hik : ¬ i ≤ k + 1 := ((succ_le_of_lt hkj).trans_lt hij).not_le
    have hik' : ¬ i ≤ k := lt_asymm hkj ∘ hij.trans_le
    simp only [hik, hkj.not_lt, hkj.ne, hik', Bool.toNat_neg, add_zero,
      decide_false, Bool.toNat_false, tsub_zero, cond_false]

theorem testRes_mergeBitRes_of_lt {p : ℕ} (hij : i < j) :
    (p.mergeBitRes b j).testRes i = (p.testRes i).mergeBitRes b (j - 1) := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨j, rfl⟩
  simp only [testBit_ext_iff, testBit_testRes, testBit_mergeBitRes, add_tsub_cancel_right]
  intro k
  rcases le_or_lt i k with hik | hik
  · simp only [hik, decide_true, Bool.toNat_true, add_left_inj, add_lt_add_iff_right]
    rcases lt_trichotomy (i + j) k with hjk | rfl | hjk
    · simp only [hjk.ne', decide_false, hjk, decide_true, Bool.toNat_true, add_tsub_cancel_right,
      cond_false, (le_add_right _ _).trans (Nat.le_sub_one_of_lt hjk), decide_true,
      Bool.toNat_true, Nat.sub_add_cancel (one_le_of_lt hjk)]
    · simp only [decide_true, lt_self_iff_false, decide_false, Bool.toNat_false, tsub_zero,
      testBit_succ, cond_true, le_add_iff_nonneg_right, _root_.zero_le, Bool.toNat_true]
    · simp only [hjk.ne, decide_false, hjk.not_lt, Bool.toNat_false, tsub_zero, testBit_succ,
      cond_false, hik, decide_true, Bool.toNat_true]
  · simp only [hik.not_le, decide_false, Bool.toNat_false, add_zero, (hik.trans hij).ne,
      (hik.trans hij).not_lt, tsub_zero, cond_false, hik.trans_le (Nat.le_add_right _ _), ne_of_lt,
      not_lt_of_lt]

theorem testRes_mergeBitRes_of_ne {p : ℕ} (hij : i ≠ j) : (p.mergeBitRes b j).testRes i =
    (p.testRes (i - (decide (j < i)).toNat)).mergeBitRes b (j - (decide (i < j)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [testRes_mergeBitRes_of_lt hij, hij.not_lt, decide_false, Bool.toNat_false, tsub_zero,
    hij, decide_true, Bool.toNat_true]
  · simp only [testRes_mergeBitRes_of_gt hij, hij, decide_true, Bool.toNat_true, hij.not_lt,
    decide_false, Bool.toNat_false, tsub_zero]

theorem testRes_mergeBitRes {i j p : ℕ} : (p.mergeBitRes b j).testRes i = bif i = j then p else
    (p.testRes (i - (decide (j < i)).toNat)).mergeBitRes b  (j - (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testRes_mergeBitRes_of_eq, decide_true, cond_true]
  · simp_rw [hij, testRes_mergeBitRes_of_ne hij, decide_false, cond_false]

theorem testRes_succ_mergeBitRes_of_ge {p : ℕ} (hij : j ≤ i) :
    (p.mergeBitRes b j).testRes (i + 1) = (p.testRes i).mergeBitRes b j := by
  rw [testRes_mergeBitRes_of_gt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

theorem testRes_mergeBitRes_succ_of_le {p : ℕ} (hij : i ≤ j) :
    (p.mergeBitRes b (j + 1)).testRes i = (p.testRes i).mergeBitRes b j := by
  rw [testRes_mergeBitRes_of_lt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

-- mergeBitRes_testRes

theorem mergeBitRes_testRes_of_le {q : ℕ} (hij : i ≤ j) : (q.testRes j).mergeBitRes b i =
    (q.mergeBitRes b i).testRes (j + 1) := (testRes_succ_mergeBitRes_of_ge hij).symm

theorem mergeBitRes_testRes_of_ge {q : ℕ} (hij : j ≤ i) :
    (q.testRes j).mergeBitRes b i = (q.mergeBitRes b (i + 1)).testRes j :=
  (testRes_mergeBitRes_succ_of_le hij).symm

theorem mergeBitRes_testRes_of_ne {q : ℕ} (hij : i ≠ j) :
    (q.testRes j).mergeBitRes b i =
    (q.mergeBitRes b (i + (decide (j < i)).toNat)).testRes (j + (decide (i < j)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [mergeBitRes_testRes_of_le hij.le, hij, not_lt_of_lt, decide_false, Bool.toNat_false,
    add_zero, decide_true, Bool.toNat_true]
  · simp only [mergeBitRes_testRes_of_ge hij.le, hij, decide_true, Bool.toNat_true, not_lt_of_lt,
    decide_false, Bool.toNat_false, add_zero]

theorem mergeBitRes_not_testBit_testRes_of_eq {q : ℕ} :
    (q.testRes i).mergeBitRes (!q.testBit i) i =
  (bif q.testBit i then q - 2^i else q + 2^i) := by
  rw [mergeBitRes_apply_not, mergeBitRes_testBit_testRes_of_eq]

theorem mergeBitRes_testRes_of_eq {i q : ℕ} : (q.testRes i).mergeBitRes b i =
    bif (q.testBit i).xor !b then q else bif q.testBit i then q - 2^i else q + 2^i := by
  rcases Bool.eq_or_eq_not b (q.testBit i) with rfl | rfl
  · simp_rw [mergeBitRes_testBit_testRes_of_eq, Bool.bne_not_self, cond_true]
  · simp_rw [Bool.not_not, bne_self_eq_false, mergeBitRes_not_testBit_testRes_of_eq, cond_false]

theorem mergeBitRes_testRes {i j : ℕ} : (q.testRes j).mergeBitRes b i =
    bif i = j then bif (q.testBit i).xor !b then q else (bif q.testBit i then q - 2^i else q + 2^i)
    else (q.mergeBitRes b (i + (decide (j < i)).toNat)).testRes (j + (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp only [decide_true, lt_self_iff_false, decide_false, Bool.toNat_false, add_zero,
    testRes_mergeBitRes_of_eq, cond_true, mergeBitRes_testRes_of_eq]
  · simp_rw [hij, mergeBitRes_testRes_of_ne hij, decide_false, cond_false]

theorem mergeBitRes_testRes_pred_of_lt {q : ℕ} (hij : i < j) :
    (q.testRes (j - 1)).mergeBitRes b i =
    (q.mergeBitRes b i).testRes j := (testRes_mergeBitRes_of_gt hij).symm

theorem mergeBitRes_pred_testRes_of_gt {q : ℕ} (hij : j < i) :
    (q.testRes j).mergeBitRes b (i - 1) =
    (q.mergeBitRes b i).testRes j := (testRes_mergeBitRes_of_lt hij).symm

-- testRes_testRes

theorem testRes_testRes_of_lt {i j q : ℕ} (hij : i < j) : (q.testRes j).testRes i =
  (q.testRes i).testRes (j - 1) := by
  simp_rw [testBit_ext_iff, testBit_testRes, tsub_le_iff_right]
  intro k
  rcases lt_or_le k i with (hik | hik)
  · have hkj : k + 1 < j := (Nat.succ_le_of_lt hik).trans_lt hij
    have hkj' : k < j := lt_of_succ_lt hkj
    simp only [hik.not_le, hkj'.not_le, hkj.not_le, decide_false, Bool.toNat_false, add_zero]
  · have h : i ≤ k + (decide (j ≤ k + 1)).toNat := le_add_of_le_left hik
    simp_rw [hik, h, decide_true, Bool.toNat_true, add_assoc, add_comm]

theorem testRes_testRes_of_ge {i j q : ℕ} (hij : j ≤ i) :
    (q.testRes j).testRes i = (q.testRes (i + 1)).testRes j := by
  simp_rw [testBit_ext_iff, testBit_testRes]
  intro k
  rcases le_or_lt i k with (hik | hik)
  · have hjk : j ≤ k := hij.trans hik
    have hjk' : j ≤ k + 1 := hjk.trans (le_succ _)
    simp only [hik,  hjk', hjk, decide_true, Bool.toNat_true, add_le_add_iff_right]
  · have h : k + (decide (j ≤ k)).toNat < i + 1 := add_lt_add_of_lt_of_le hik (Bool.toNat_le _)
    simp only [hik.not_le, h.not_le, decide_false, Bool.toNat_false, add_zero]

theorem testRes_testRes {i j q : ℕ} : (q.testRes j).testRes i =
    (q.testRes (i + (decide (j ≤ i)).toNat)).testRes (j - (!decide (j ≤ i)).toNat) := by
  rcases lt_or_le i j with hij | hij
  · simp_rw [testRes_testRes_of_lt hij, hij.not_le, decide_false, Bool.toNat_false,
    add_zero, Bool.not_false, Bool.toNat_true]
  · simp_rw [testRes_testRes_of_ge hij, hij, decide_true, Bool.toNat_true,
    Bool.not_true, Bool.toNat_false, tsub_zero]

theorem testRes_testRes_succ_of_le {i j q : ℕ} (hij : i ≤ j) : (q.testRes (j + 1)).testRes i =
    (q.testRes i).testRes j := by
  rw [testRes_testRes_of_lt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

theorem testRes_pred_testRes_of_gt {i j q : ℕ} (hij : j < i) : (q.testRes j).testRes (i - 1) =
    (q.testRes i).testRes j := by
  rw [testRes_testRes_of_ge (Nat.le_sub_one_of_lt hij), Nat.sub_add_cancel (one_le_of_lt hij)]


-- mergeBitRes_mergeBitRes

theorem mergeBitRes_mergeBitRes_of_le {i j p : ℕ} {b b' : Bool} (hij : i ≤ j) :
    (p.mergeBitRes b' j).mergeBitRes b i = (p.mergeBitRes b i).mergeBitRes b' (j + 1) := by
  simp_rw [mergeBitRes_eq_iff (i := i), testRes_mergeBitRes_succ_of_le hij,
  testBit_mergeBitRes_succ_of_le hij, testBit_mergeBitRes_of_eq, testRes_mergeBitRes_of_eq, true_and]

theorem mergeBitRes_mergeBitRes_of_gt {i j p : ℕ} {b b' : Bool} (hij : j < i) :
    (p.mergeBitRes b' j).mergeBitRes b i = (p.mergeBitRes b (i - 1)).mergeBitRes b' j := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
  rw [Nat.add_sub_cancel, ← mergeBitRes_mergeBitRes_of_le (Nat.le_of_lt_succ hij)]

theorem mergeBitRes_mergeBitRes_of_eq {i p : ℕ} {b b' : Bool} :
    (p.mergeBitRes b' i).mergeBitRes b i = (p.mergeBitRes b i).mergeBitRes b' (i + 1) :=
  mergeBitRes_mergeBitRes_of_le le_rfl

theorem mergeBitRes_mergeBitRes_of_ne {i j p : ℕ} {b b' : Bool} (hij : i ≠ j) :
    (p.mergeBitRes b' j).mergeBitRes b i =
    (p.mergeBitRes b (i - (decide (j < i)).toNat)).mergeBitRes b' (j + (decide (i < j)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [mergeBitRes_mergeBitRes_of_le hij.le, hij, hij.not_lt, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero]
  · simp_rw [mergeBitRes_mergeBitRes_of_gt hij, hij, hij.not_lt, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, add_zero]

theorem mergeBitRes_mergeBitRes {i j p : ℕ} {b b' : Bool} : (p.mergeBitRes b' j).mergeBitRes b i  =
    (p.mergeBitRes b (i - (decide (j < i)).toNat)).mergeBitRes b' (j + (decide (i ≤ j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [mergeBitRes_mergeBitRes_of_eq, lt_irrefl, le_rfl, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero]
  · simp_rw [mergeBitRes_mergeBitRes_of_ne hij, hij.le_iff_lt]

theorem mergeBitRes_succ_mergeBitRes_of_ge {i j p : ℕ} {b b' : Bool} (h : j ≤ i) :
    (p.mergeBitRes b j).mergeBitRes b' (i + 1) = (p.mergeBitRes b' i).mergeBitRes b j :=
  (mergeBitRes_mergeBitRes_of_le h).symm

theorem mergeBitRes_mergeBitRes_pred_of_lt {i j p : ℕ} {b b' : Bool} (h : i < j) :
    (p.mergeBitRes b (j - 1) ).mergeBitRes b' i = (p.mergeBitRes b' i).mergeBitRes b j :=
  (mergeBitRes_mergeBitRes_of_gt h).symm

-- mergeBitRes equalities and inequalities

theorem mergeBitRes_div_two_pow_eq (h : i ≤ k) : q.mergeBitRes b i / 2^(k + 1) = q / 2^k := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow, ← Nat.add_assoc,
  testBit_succ_mergeBitRes_of_ge ((h.trans (Nat.le_add_left _ _))), implies_true]

theorem mergeBitRes_mod_two_pow_eq (h : k ≤ i) : q.mergeBitRes b i % 2^k = q % 2^k := by
  simp_rw [testBit_ext_iff, testBit_mod_two_pow]
  intro j
  rcases lt_or_le j k with hjk | hjk
  · simp_rw [hjk, testBit_mergeBitRes_of_lt (hjk.trans_le h)]
  · simp_rw [hjk.not_lt, decide_false, Bool.false_and]

theorem mergeBitRes_modEq_two_pow (h : k ≤ i) : q.mergeBitRes b i ≡ q [MOD 2^k] :=
  mergeBitRes_mod_two_pow_eq h

theorem mergeBitRes_lt_iff_lt_div_two (hin : 2^(i + 1) ∣ n) :
    q.mergeBitRes b i < n ↔ q < n / 2 := by
  rw [← testRes_lt_div_two_iff_lt hin, testRes_mergeBitRes_of_eq]

theorem mergeBitRes_lt_two_mul_iff_lt (hin : 2^i ∣ n) :
    q.mergeBitRes b i < 2 * n ↔ q < n := by
  rw [← testRes_lt_iff_lt_two_mul hin, testRes_mergeBitRes_of_eq]

theorem mergeBitRes_lt_two_pow_mul_iff_lt_two_pow_mul (h : i ≤ k) (n : ℕ) :
    q.mergeBitRes b i < 2^(k + 1) * n ↔ q < 2^k * n := by
  simp_rw [← testRes_lt_two_pow_mul_iff_lt_two_pow_mul h, testRes_mergeBitRes_of_eq]

theorem mergeBitRes_lt_two_pow_iff_lt_two_pow (h : i ≤ k) :
    q.mergeBitRes b i < 2^(k + 1) ↔ q < 2^k := by
  simp_rw [← testRes_lt_two_pow_iff_lt_two_pow h, testRes_mergeBitRes_of_eq]

theorem mergeBitRes_testRes_lt_iff_lt (hin : 2^(i + 1) ∣ n) :
    (q.testRes i).mergeBitRes b i < n ↔ q < n := by
  rw [mergeBitRes_lt_iff_lt_div_two hin, testRes_lt_div_two_iff_lt hin]

theorem zero_testRes : (0 : ℕ).testRes i = 0 := by
  rw [testRes_def, zero_shiftRight, zero_shiftLeft, zero_and, or_zero]

theorem zero_mergeBitRes : (0 : ℕ).mergeBitRes b i = b.toNat * 2^i := by
  simp_rw [mergeBitRes_def, zero_shiftRight, zero_shiftLeft, zero_and, or_zero, zero_or, shiftLeft_eq]

theorem zero_mergeBitRes_true : (0 : ℕ).mergeBitRes true i = 2^i := by
  simp_rw [zero_mergeBitRes, Bool.toNat_true, one_mul]

theorem zero_mergeBitRes_false : (0 : ℕ).mergeBitRes false i = 0 := by
  simp_rw [zero_mergeBitRes, Bool.toNat_false, zero_mul]

theorem two_pow_testRes_of_eq : (2 ^ i).testRes i = 0 :=
  zero_mergeBitRes_true ▸ testRes_mergeBitRes_of_eq

theorem two_pow_testRes_of_lt (hij : i < j) : (2 ^ i).testRes j = 2 ^ i := by
  rw [← zero_mergeBitRes_true, testRes_mergeBitRes_of_gt hij, zero_testRes]

theorem two_pow_testRes_of_gt (hij : j < i) : (2 ^ i).testRes j = 2 ^ (i - 1) := by
  simp_rw [← zero_mergeBitRes_true, testRes_mergeBitRes_of_lt hij, zero_testRes]

theorem testRes_eq_mod_of_lt (hq : q < 2^(i + 1)) : q.testRes i = q % 2^i := by
  rw [testRes_apply, Nat.div_eq_of_lt hq, mul_zero, zero_add]

theorem testRes_eq_of_lt (hq : q < 2^i) : q.testRes i = q := by
  rw [testRes_eq_mod_of_lt (hq.trans (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _))),
    mod_eq_of_lt hq]

theorem two_pow_mergeBitRes_false (hq : q < 2^j) : q.mergeBitRes false j = q := by
  simp_rw [mergeBitRes_eq_iff, testRes_eq_of_lt hq, Nat.testBit_eq_false_of_lt hq, true_and]

end BitResiduum

section FlipBit

variable {p q b i j k n m : ℕ} {b : Bool}

def flipBit (q i : ℕ) := q ^^^ 1 <<< i

theorem flipBit_def : ∀ (i q : ℕ), q.flipBit i = q ^^^ 1 <<< i := fun _ _ => rfl

-- inductive theorems

theorem flipBit_zero : q.flipBit 0 = bit (!q.bodd) q.div2 := by
  cases q using bitCasesOn with | h b q => _
  simp_rw [flipBit_def, shiftLeft_zero, div2_bit, bodd_bit]
  refine (xor_bit b q true 0).trans ?_
  simp_rw [Bool.bne_true, xor_zero]

theorem flipBit_succ : q.flipBit i.succ = bit q.bodd (q.div2.flipBit i) := by
  cases q using bitCasesOn with | h b q => _
  simp_rw [flipBit_def, shiftLeft_succ, div2_bit, bodd_bit]
  refine (xor_bit b q false (1 <<< i)).trans ?_
  simp_rw [Bool.bne_false]

-- testBit_flipBit

theorem testBit_flipBit : (q.flipBit j).testBit i = (q.testBit i).xor (i = j) := by
  simp_rw [flipBit_def, testBit_xor, testBit_shiftLeft, testBit_one, Nat.sub_eq_zero_iff_le,
    le_antisymm_iff (a := i), Bool.decide_and, Bool.and_comm]

@[simp]
theorem testBit_flipBit_of_eq : (q.flipBit i).testBit i = !(q.testBit i) := by
  simp_rw [testBit_flipBit, decide_true, Bool.xor_true]

theorem testBit_flipBit_of_ne {i j : ℕ} (hij : i ≠ j) :
    (q.flipBit j).testBit i = q.testBit i := by
  simp_rw [testBit_flipBit, hij, decide_false, Bool.xor_false]

-- representations of flipBit

theorem flipBit_apply {i : ℕ} :
    q.flipBit i = (q.testRes i).mergeBitRes (!(testBit q i)) i := by
  simp_rw [testBit_ext_iff]
  intro j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [testBit_flipBit_of_ne hij.ne', testBit_mergeBitRes_of_gt hij, testBit_pred_testRes_of_gt hij]
  · rw [testBit_flipBit_of_eq, testBit_mergeBitRes_of_eq]
  · rw [testBit_flipBit_of_ne hij.ne, testBit_mergeBitRes_of_lt hij, testBit_testRes_of_lt hij]

theorem flipBit_eq_of_testBit_false {i : ℕ} (hqi : q.testBit i = false) :
    q.flipBit i = (q.testRes i).mergeBitRes true i := by
  rw [flipBit_apply, hqi, Bool.not_false]

theorem flipBit_eq_of_testBit_true {i : ℕ} (hqi : q.testBit i = true) :
    q.flipBit i = (q.testRes i).mergeBitRes false i := by
  rw [flipBit_apply, hqi, Bool.not_true]

theorem flipBit_eq_cond {i : ℕ} : q.flipBit i = bif testBit q i then q - 2^i else q + 2^i := by
  rw [flipBit_apply, mergeBitRes_not_testBit_testRes_of_eq]

-- flipBit equalities and inequalities

theorem flipBit_div_two_pow_eq {i : ℕ} (h : i < k) : q.flipBit i / 2^k = q / 2^k := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow,
  testBit_flipBit_of_ne (h.trans_le (Nat.le_add_left _ _)).ne', implies_true]

theorem flipBit_mod_two_pow_eq {i : ℕ} (h : k ≤ i) : q.flipBit i % 2^k = q % 2^k := by
  simp_rw [testBit_ext_iff, testBit_mod_two_pow]
  intro j
  rcases eq_or_ne j i with rfl | hji
  · simp_rw [h.not_lt, decide_false, Bool.false_and]
  · simp_rw [testBit_flipBit_of_ne hji]

theorem flipBit_modEq_two_pow (h : k ≤ i) : q.flipBit i ≡ q [MOD 2^k] := flipBit_mod_two_pow_eq h

@[simp]
theorem flipBit_lt_iff_lt (hin : 2^(i + 1) ∣ n) : q.flipBit i < n ↔ q < n := by
  rcases hin with ⟨k, rfl⟩
  simp_rw [mul_comm _ k, ← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
     flipBit_div_two_pow_eq i.lt_succ_self]

theorem lt_of_flipBit_le (hq : q.flipBit i ≤ n) : q < n + 2 ^ (i + 1) := by
  have H := hq.trans_lt <| Nat.lt_mul_div_succ n (Nat.two_pow_pos (i + 1))
  rw [flipBit_lt_iff_lt (dvd_mul_right _ _), mul_succ] at H
  exact H.trans_le (Nat.add_le_add_right (Nat.mul_div_le _ _) _)

theorem flipBit_lt_of_le (hq : q ≤ n) : q.flipBit i < n + 2 ^ (i + 1) := by
  have H := hq.trans_lt <| Nat.lt_mul_div_succ n (Nat.two_pow_pos (i + 1))
  rw [← flipBit_lt_iff_lt (dvd_mul_right _ _), mul_succ] at H
  exact H.trans_le (Nat.add_le_add_right (Nat.mul_div_le _ _) _)

theorem flipBit_lt_two_pow_mul_iff_lt_two_pow_mul (h : i < k) (n : ℕ) :
    q.flipBit i < 2^k * n ↔ q < 2^k * n :=
  flipBit_lt_iff_lt (dvd_mul_of_dvd_left (pow_dvd_pow _ h) _)

theorem flipBit_lt_two_pow_iff_lt_two_pow {m : ℕ} (h : i < m) :
    q.flipBit i < 2^m ↔ q < 2^m := by
  have H := flipBit_lt_two_pow_mul_iff_lt_two_pow_mul h 1 (q := q)
  simp_rw [mul_one] at H
  exact H

theorem flipBit_mem_bitMatchUnder {k : ℕ} {i : ℕ} {x : Fin (2^n)}
    (hk : k ∈ Set.Ico i n) (q : ℕ) :
    q ∈ bitMatchUnder i x → q.flipBit k ∈ bitMatchUnder i x := by
  simp_rw [mem_bitMatchUnder_iff,
    Nat.flipBit_lt_iff_lt (Nat.pow_dvd_pow _ ( Nat.succ_le_of_lt hk.2)),
    testBit_flipBit]
  exact And.imp_right (fun hq _ hjk => by
    simp_rw [hq _ hjk, (hjk.trans_le hk.1).ne, decide_false, Bool.xor_false])

theorem flipBit_testRes_of_lt (hij : i < j):
    (q.testRes j).flipBit i = (q.flipBit i).testRes j := by
  simp_rw [flipBit_apply, testRes_testRes_of_lt hij, testBit_testRes_of_lt hij,
  testRes_mergeBitRes_of_gt hij]

theorem flipBit_testRes_of_ge (hij : j ≤ i):
    (q.testRes j).flipBit i = (q.flipBit (i + 1)).testRes j := by
  simp_rw [flipBit_apply, testRes_testRes_of_ge hij, testBit_testRes_of_ge hij,
  mergeBitRes_testRes_of_ge hij]

theorem flipBit_testRes :
    (q.testRes j).flipBit i = (q.flipBit (i + (decide (j ≤ i)).toNat)).testRes j := by
  rcases lt_or_le i j with hij | hij
  · simp_rw [flipBit_testRes_of_lt hij, hij.not_le, decide_false, Bool.toNat_false, add_zero]
  · simp_rw [flipBit_testRes_of_ge hij, hij, decide_true, Bool.toNat_true]

-- testRes_flipBit

theorem testRes_flipBit_of_gt (hij : j < i):
    (q.flipBit j).testRes i = (q.testRes i).flipBit j := (flipBit_testRes_of_lt hij).symm

theorem testRes_flipBit_of_lt (hij : i < j):
    (q.flipBit j).testRes i = (q.testRes i).flipBit (j - 1) := by
  rw [flipBit_testRes_of_ge (Nat.le_sub_one_of_lt hij), Nat.sub_add_cancel (one_le_of_lt hij)]

theorem testRes_flipBit_of_ne (hij : i ≠ j) :
    (q.flipBit j).testRes i = (q.testRes i).flipBit (j - (decide (i < j)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [testRes_flipBit_of_lt hij, hij, not_lt_of_lt, decide_false, Bool.toNat_false,
    add_zero, decide_true, Bool.toNat_true]
  · simp only [testRes_flipBit_of_gt hij, hij, decide_true, Bool.toNat_true, not_lt_of_lt,
    decide_false, Bool.toNat_false, Nat.sub_zero]

@[simp]
theorem testRes_flipBit_of_eq : (q.flipBit i).testRes i = q.testRes i := by
  rw [flipBit_apply, testRes_mergeBitRes_of_eq]

theorem testRes_flipBit : (q.flipBit j).testRes i = bif i = j then q.testRes i else
    (q.testRes i).flipBit (j - (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testRes_flipBit_of_eq, decide_true, cond_true]
  · simp_rw [testRes_flipBit_of_ne hij, hij, decide_false, cond_false]

-- flipBit_mergeBitRes

theorem flipBit_mergeBitRes_of_eq : (p.mergeBitRes b i).flipBit i = p.mergeBitRes (!b) i := by
  rw [flipBit_apply, testBit_mergeBitRes_of_eq, testRes_mergeBitRes_of_eq]

theorem flipBit_mergeBitRes_of_lt (hij : i < j) :
    (p.mergeBitRes b j).flipBit i = (p.flipBit i).mergeBitRes b j := by
  rw [flipBit_apply, flipBit_apply, testBit_mergeBitRes_of_lt hij,
  testRes_mergeBitRes_of_lt hij, mergeBitRes_mergeBitRes_pred_of_lt hij]

theorem flipBit_mergeBitRes_of_gt (hij : j < i) :
    (p.mergeBitRes b j).flipBit i = (p.flipBit (i - 1)).mergeBitRes b j := by
  rw [flipBit_apply, flipBit_apply, testBit_mergeBitRes_of_gt hij,
  testRes_mergeBitRes_of_gt hij, mergeBitRes_mergeBitRes_pred_of_lt hij]

theorem flipBit_mergeBitRes_of_ne (hij : i ≠ j) :
    (p.mergeBitRes b j).flipBit i = (p.flipBit (i - (decide (j < i)).toNat)).mergeBitRes b j := by
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [flipBit_mergeBitRes_of_lt hij, hij.not_lt, decide_false, Bool.toNat_false,
    Nat.sub_zero]
  · simp_rw [flipBit_mergeBitRes_of_gt hij, hij, decide_true, Bool.toNat_true]

theorem flipBit_mergeBitRes :
    (p.mergeBitRes b j).flipBit i = if i = j then p.mergeBitRes (!b) i else
    (p.flipBit (i - (decide (j < i)).toNat)).mergeBitRes b j := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [flipBit_mergeBitRes_of_eq, if_true]
  · simp_rw [flipBit_mergeBitRes_of_ne hij, hij, if_false]

-- properties of flipBit

theorem ne_of_testBit_eq_not_testBit {r : ℕ} (i : ℕ)(h : q.testBit i = !r.testBit i) :
    q ≠ r := by
  rw [testBit_ne_iff]
  exact ⟨i, h ▸ Bool.not_ne_self _⟩

theorem ne_of_not_testBit_eq_testBit {r : ℕ} (i : ℕ) (h : (!q.testBit i) = r.testBit i) :
    q ≠ r := by
  rw [testBit_ne_iff]
  exact ⟨i, h ▸ Bool.self_ne_not _⟩

theorem ne_flipBit_of_testBit_eq {r : ℕ} (h : q.testBit i = r.testBit i) : q ≠ r.flipBit i :=
  ne_of_not_testBit_eq_testBit i (h ▸ testBit_flipBit_of_eq.symm)

theorem flipBit_ne_of_testBit_eq {r : ℕ} (h : q.testBit i = r.testBit i) : q.flipBit i ≠ r :=
  ne_of_testBit_eq_not_testBit i (h ▸ testBit_flipBit_of_eq)

theorem testRes_lt_testRes_iff {r : ℕ} :
    q.testRes i < r.testRes i ↔
    (q < r ∧ q.testBit i = r.testBit i) ∨ (q < r.flipBit i ∧ q.testBit i = !r.testBit i) := by
  rw [testRes_lt_iff]
  rcases Bool.eq_or_eq_not (q.testBit i) (r.testBit i) with hqr | hqr
  · simp_rw [hqr, mergeBitRes_testBit_testRes_of_eq,
      Bool.eq_not_self, and_true, and_false, or_false]
  · simp_rw [hqr, ← flipBit_apply, Bool.not_eq_self, and_true, and_false, false_or]

theorem testRes_eq_testRes_iff {r : ℕ} :
    q.testRes i = r.testRes i ↔ q = r ∨ q = r.flipBit i := by
  rw [testRes_eq_iff]
  rcases Bool.eq_or_eq_not (q.testBit i) (r.testBit i) with hqr | hqr
  · simp_rw [hqr, mergeBitRes_testBit_testRes_of_eq, ne_flipBit_of_testBit_eq hqr, or_false]
  · simp_rw [hqr, flipBit_apply, ne_of_testBit_eq_not_testBit i hqr, false_or]

theorem testRes_le_testRes_iff {r : ℕ} :
    q.testRes i ≤ r.testRes i ↔
    (q ≤ r ∧ q.testBit i = r.testBit i) ∨ (q ≤ r.flipBit i ∧ q.testBit i = !r.testBit i) := by
  simp_rw [le_iff_lt_or_eq, or_and_right, testRes_eq_testRes_iff, testRes_lt_testRes_iff]
  rw [or_or_or_comm]
  exact or_congr
    (or_congr Iff.rfl (iff_self_and.mpr (fun h => h ▸ rfl)))
    (or_congr Iff.rfl (iff_self_and.mpr (fun h => h ▸ testBit_flipBit_of_eq)))

theorem flipBit_lt_iff_lt_flipBit_of_testBit_eq_not_testBit {r : ℕ}
    (h : q.testBit i ≠ r.testBit i) : q.flipBit i < r ↔ q < r.flipBit i := by
  simp_rw [flipBit_apply, Bool.not_eq.mpr h, ← Bool.eq_not.mpr h,
    ← testRes_lt_iff, ← lt_testRes_iff]

@[simp]
theorem flipBit_flipBit_of_eq : (q.flipBit i).flipBit i = q := by
  simp_rw [flipBit_def, Nat.xor_cancel_right]

theorem flipBit_lt_flipBit_iff_lt_of_testBit_eq_testBit {q r : ℕ}
    (h : q.testBit i = r.testBit i) : q.flipBit i < r.flipBit i ↔ q < r := by
  rw [flipBit_lt_iff_lt_flipBit_of_testBit_eq_not_testBit
    (testBit_flipBit_of_eq ▸ (Bool.not_eq_not.mpr h)), flipBit_flipBit_of_eq]

theorem flipBit_flipBit (i j) : (q.flipBit i).flipBit j = (q.flipBit j).flipBit i := by
  simp_rw [testBit_ext_iff, testBit_flipBit, Bool.xor_assoc, Bool.xor_comm, implies_true]

@[simp]
theorem flipBit_ne_self : q.flipBit i ≠ q := by
  simp_rw [ne_eq, testBit_ext_iff, not_forall]
  exact ⟨i, by simp_rw [testBit_flipBit_of_eq, Bool.not_eq_self, not_false_eq_true]⟩

@[simp]
theorem self_ne_flipBit : q ≠ q.flipBit i := flipBit_ne_self.symm

theorem testBit_eq_false_true_of_lt_of_flipBit_ge {r : ℕ} (hrq : r < q)
    (hf : q.flipBit i ≤ r.flipBit i) : r.testBit i = false ∧ q.testBit i = true := by
  simp_rw [flipBit_eq_cond] at hf
  rcases hr : r.testBit i <;> rcases hq : q.testBit i <;> simp_rw [hr, hq] at hf
  · simp_rw [Bool.cond_false, add_le_add_iff_right] at hf
    exact (hf.not_lt hrq).elim
  · simp_rw [and_self]
  · simp_rw [Bool.cond_true, Bool.cond_false] at hf
    exact ((Nat.sub_le _ _).not_lt ((hrq.trans_le (Nat.le_add_right _ _)).trans_le hf)).elim
  · simp_rw [Bool.cond_true, tsub_le_iff_right, Nat.sub_add_cancel (testBit_implies_ge hr)] at hf
    exact (hf.not_lt hrq).elim

theorem testBit_eq_of_le_of_flipBit_lt_ge {r : ℕ} (hrq : r ≤ q)
    (hf : q.flipBit i ≤ r.flipBit i) (hik : i < k) : r.testBit k = q.testBit k := by
  simp_rw [testBit_to_div_mod, decide_eq_decide]
  suffices hs : r / 2^k = q / 2 ^ k by rw [hs]
  refine le_antisymm (Nat.div_le_div_right hrq) ?_
  rw [← flipBit_div_two_pow_eq hik, ← flipBit_div_two_pow_eq (q := r) hik]
  exact Nat.div_le_div_right hf

theorem testBit_eq_flipBit_testBit_of_le_of_flipBit_le_ge {r : ℕ} (hrq : r < q)
    (hf : q.flipBit i ≤ r.flipBit i) (hik : i ≤ k) : r.testBit k = (q.flipBit i).testBit k := by
  rcases hik.lt_or_eq with hik | rfl
  · rw [testBit_flipBit_of_ne hik.ne']
    exact testBit_eq_of_le_of_flipBit_lt_ge hrq.le hf hik
  · simp_rw [testBit_flipBit_of_eq, Bool.eq_not_iff,
    testBit_eq_false_true_of_lt_of_flipBit_ge hrq hf]
    exact Bool.false_ne_true

theorem eq_flipBit_of_lt_of_flipBit_ge_of_lt_testBit_eq {r : ℕ} (hrq : r < q)
    (hf : q.flipBit i ≤ r.flipBit i) (h : ∀ {k}, k < i → r.testBit k = q.testBit k) :
    r = q.flipBit i := by
  rw [testBit_ext_iff]
  intros k
  rcases lt_or_le k i with hik | hik
  · rw [testBit_flipBit_of_ne hik.ne, h hik]
  · exact testBit_eq_flipBit_testBit_of_le_of_flipBit_le_ge hrq hf hik

theorem flipBit_lt_flipBit_of_lt_of_ne_flipBit_of_lt_testBit_eq {r : ℕ} (hrq : r < q)
    (hrq' : r ≠ q.flipBit i) (h : ∀ {k}, k < i → r.testBit k = q.testBit k) :
    r.flipBit i < q.flipBit i := by
  rw [← not_le]
  exact fun H => hrq' (eq_flipBit_of_lt_of_flipBit_ge_of_lt_testBit_eq hrq H h)

@[pp_nodot, simps!]
def flipBitPerm (i : ℕ) : Equiv.Perm ℕ :=
  ⟨(flipBit · i), (flipBit · i), xor_cancel_right _, xor_cancel_right _⟩

@[simp]
theorem flipBitPerm_inv_apply : ∀ (x i : ℕ), (flipBitPerm i)⁻¹ x = x.flipBit i := fun _ _ => rfl

theorem flipBitPerm_eq_permCongr (i : ℕ) :
    flipBitPerm i = (mergeBitResEquiv i).permCongr (boolInversion.prodCongr (Equiv.refl _)) := by
  simp_rw [Equiv.ext_iff, flipBitPerm_apply,
    flipBit_apply, Equiv.permCongr_apply, mergeBitResEquiv_apply,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, boolInversion_apply,
    mergeBitResEquiv_symm_apply_fst, mergeBitResEquiv_symm_apply_snd, implies_true]

end FlipBit

section CondFlipBit


def condFlipBit (q : ℕ) (i : ℕ) {l : ℕ} (c : Vector Bool l) : ℕ :=
  q ^^^ ((c[q.testRes i]?.getD false).toNat <<< i)

variable {p q l k i j n m : ℕ} {c d :  Vector Bool l} {b : Bool}

theorem condFlipBit_apply_of_testRes_lt (h : q.testRes i < l) :
    q.condFlipBit i c = bif c[q.testRes i] then q.flipBit i else q := by
  unfold condFlipBit
  rw [getElem?_pos c _ h, Option.getD_some]
  rcases c[q.testRes i]
  · rw [cond_false, Bool.toNat_false, zero_shiftLeft, xor_zero]
  · rw [cond_true, Bool.toNat_true, flipBit_def]

theorem condFlipBit_apply_of_le_testRes {c : Vector Bool l} (h : l ≤ q.testRes i) :
    q.condFlipBit i c = q := by
  unfold condFlipBit
  rw [getElem?_neg c _ h.not_lt, Option.getD_none, Bool.toNat_false, zero_shiftLeft, xor_zero]

theorem condFlipBit_apply :
    q.condFlipBit i c = bif c[q.testRes i]?.getD false then q.flipBit i else q := by
  rcases lt_or_le (q.testRes i) l with h | h
  · rw [condFlipBit_apply_of_testRes_lt h, getElem?_pos c _ h, Option.getD_some]
  · rw [condFlipBit_apply_of_le_testRes h, getElem?_neg c _ h.not_lt,
      Option.getD_none, Bool.cond_false]

theorem testRes_condFlipBit_of_eq : (q.condFlipBit i c).testRes i = q.testRes i := by
  rw [condFlipBit_apply, Bool.apply_cond (testRes · i), testRes_flipBit_of_eq, Bool.cond_self]

theorem testBit_condFlipBit_of_ne (hij : i ≠ j) :
    (q.condFlipBit j c).testBit i = q.testBit i := by
  rw [condFlipBit_apply, Bool.apply_cond (testBit · i), testBit_flipBit_of_ne hij, Bool.cond_self]

theorem testBit_condFlipBit_of_eq :
    (q.condFlipBit i c).testBit i = (c[q.testRes i]?.getD false).xor (q.testBit i) := by
  rw [condFlipBit_apply, Bool.apply_cond (testBit · i), testBit_flipBit_of_eq]
  rcases (c[q.testRes i]?.getD false)
  · rw [cond_false, Bool.xor, Bool.false_bne]
  · rw [cond_true, Bool.xor, Bool.true_bne]

theorem testBit_condFlipBit_of_le_testRes (h : l ≤ q.testRes i) :
    (q.condFlipBit i c).testBit j = q.testBit j := by
  rw [condFlipBit_apply_of_le_testRes h]

theorem testBit_condFlipBit_of_testRes_lt_of_eq (h : q.testRes i < l) :
  (q.condFlipBit i c).testBit i = (c[q.testRes i]).xor (q.testBit i) := by
  rw [testBit_condFlipBit_of_eq, getElem?_pos c _ h, Option.getD_some]

theorem testBit_condFlipBit : (q.condFlipBit j c).testBit i =
    (decide (i = j) && (c[q.testRes i]?.getD false)).xor (q.testBit i) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [decide_true, Bool.true_and, testBit_condFlipBit_of_eq]
  · simp_rw [hij, decide_false, Bool.false_and, Bool.false_xor, testBit_condFlipBit_of_ne hij]

theorem condflipBit_apply : q.condFlipBit i c =
    (q.testRes i).mergeBitRes ((c[q.testRes i]?.getD false).xor (q.testBit i)) i  := by
  simp_rw [eq_mergeBitRes_iff, testRes_condFlipBit_of_eq, testBit_condFlipBit_of_eq, true_and]

theorem condflipBit_apply_of_testRes_lt (h : q.testRes i < l) :
    q.condFlipBit i c = (q.testRes i).mergeBitRes (c[q.testRes i].xor (q.testBit i)) i := by
  simp_rw [eq_mergeBitRes_iff, testRes_condFlipBit_of_eq, testBit_condFlipBit_of_testRes_lt_of_eq h,
    true_and]

theorem condFlipBit_apply_comm :
(q.condFlipBit i d).condFlipBit i c = (q.condFlipBit i c).condFlipBit i d := by
simp_rw [condflipBit_apply, testRes_mergeBitRes_of_eq,
  testBit_mergeBitRes_of_eq, Bool.xor_left_comm]

theorem condFlipBit_mergeBitRes :
    (p.mergeBitRes b i).condFlipBit i c = p.mergeBitRes ((c[p]?.getD false).xor b) i := by
  rw [condflipBit_apply, testRes_mergeBitRes_of_eq, testBit_mergeBitRes_of_eq]

theorem condFlipBit_eq_dite : q.condFlipBit i c = if h : q.testRes i < l then
    bif c[q.testRes i] then q.flipBit i else q else q := by
  symm
  rw [dite_eq_iff']
  exact ⟨fun h => (condFlipBit_apply_of_testRes_lt h).symm,
  fun h => (condFlipBit_apply_of_le_testRes (le_of_not_lt h)).symm⟩

@[simp]
theorem condFlipBit_condFlipBit_of_eq : (q.condFlipBit i c).condFlipBit i c = q := by
  simp_rw [condflipBit_apply, testRes_mergeBitRes_of_eq, testBit_mergeBitRes_of_eq,
    Bool.xor, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor, mergeBitRes_testBit_testRes_of_eq]

theorem condFlipBit_condFlipBit {d : Vector Bool l} :
    (q.condFlipBit i c).condFlipBit i d = (q.condFlipBit i d).condFlipBit i c := by
  simp_rw [testBit_ext_iff, testBit_condFlipBit]
  intro k
  rcases eq_or_ne k i with rfl | hki
  · simp_rw [decide_true, Bool.true_and, testRes_condFlipBit_of_eq,
    ← Bool.xor_assoc, Bool.xor_comm]
  · simp_rw [hki, decide_false, Bool.false_and]

theorem condFlipBit_of_all_of_lt_l (hq : q.testRes i < l)
    (hc : ∀ (i : ℕ) (h : i < l), c[i] = true) :
    q.condFlipBit i c = q.flipBit i := by
  simp_rw [condFlipBit_eq_dite, hq, dite_true, hc _ hq, cond_true]

theorem condFlipBit_of_mkVector_true :
    q.condFlipBit i (Vector.mkVector n true) = if q.testRes i < n then q.flipBit i else q := by
  simp_rw [condFlipBit_eq_dite, Vector.getElem_mkVector, cond_true, dite_eq_ite]

theorem condFlipBit_of_all_not (hc : c.all (fun x => !x)) :
    q.condFlipBit i c = q := by
  unfold Vector.all at hc
  simp_rw [Array.all_eq_true, Bool.not_eq_true',
    Vector.size_toArray, Vector.getElem_toArray] at hc
  simp_rw [condFlipBit_eq_dite]
  split_ifs with hq
  · simp_rw [hc _ hq, cond_false]
  · rfl

theorem condFlipBit_of_mkVector_false :
    q.condFlipBit i (Vector.mkVector n false) = q := by
  simp_rw [condFlipBit_eq_dite, Vector.getElem_mkVector, cond_false, dite_eq_ite, ite_self]

@[simp]
theorem condFlipBit_lt_iff_lt (hin : 2^(i + 1) ∣ n) :
    q.condFlipBit i c < n ↔ q < n := by
  rw [condFlipBit_apply]
  cases' c[q.testRes i]?.getD false
  · rw [cond_false]
  · rw [cond_true, flipBit_lt_iff_lt hin]

theorem condFlipBit_lt_two_pow_mul_iff_lt_two_pow_mul (h : i < m) (n : ℕ):
    q.condFlipBit i c < 2^m * n ↔ q < 2^m * n := by
  rw [condFlipBit_lt_iff_lt (dvd_mul_of_dvd_left (pow_dvd_pow _ h) _)]

theorem condFlipBit_lt_two_pow_iff_lt_two_pow (h : i < m) :
    q.condFlipBit i c < 2^m ↔ q < 2^m := by
  rw [condFlipBit_lt_iff_lt (pow_dvd_pow _ h)]

@[pp_nodot, simps!]
def condFlipBitPerm (i : ℕ) (c : Vector Bool l) : Equiv.Perm ℕ where
  toFun := (condFlipBit · i c)
  invFun := (condFlipBit · i c)
  left_inv _ := condFlipBit_condFlipBit_of_eq
  right_inv _ := condFlipBit_condFlipBit_of_eq

end CondFlipBit

end Nat

namespace Vector

section FlipBit

variable {α : Type*} {n i : ℕ}

def flipBitIndicesAux (v : Vector α n) (i t : ℕ) : Vector α n :=
  t.fold (fun k _ v => v.swapIfInBounds (k.mergeBitRes false i) (k.mergeBitRes true i)) v

@[simp]
theorem flipBitIndicesAux_zero {v : Vector α n} {i : ℕ} : flipBitIndicesAux v i 0 = v := rfl
@[simp]
theorem flipBitIndicesAux_succ {v : Vector α n} {i t : ℕ} :
    flipBitIndicesAux v i (t.succ) =
    (flipBitIndicesAux v i t).swapIfInBounds (t.mergeBitRes false i) (t.mergeBitRes true i) := rfl

theorem getElem_flipBitIndicesAux {v : Vector α n} {i t k : ℕ}
    (hk : k < n) : (flipBitIndicesAux v i t)[k] =
    if hk' : k.testRes i < t ∧ k.flipBit i < n then v[k.flipBit i] else v[k] := by
  induction' t with t IH generalizing k
  · rfl
  · simp_rw [Nat.lt_succ_iff, flipBitIndicesAux_succ, getElem_swapIfInBounds,
      getElem_swap_eq_getElem_swap_apply, IH]
    rcases eq_or_ne (k.testRes i) t with rfl | hkt
    · simp_rw [le_rfl, true_and, lt_irrefl, false_and, dite_false]
      have H1 := (k.testBit i).apply_false_apply_true_of_comm
        Equiv.swap_comm ((k.testRes i).mergeBitRes · i)
      have H2 := (k.testBit i).apply_false_apply_true_of_comm
        (fun x _ => propext (and_comm (a := x < n))) ((k.testRes i).mergeBitRes · i)
      simp_rw [H1, H2, Nat.mergeBitRes_testBit_testRes_of_eq,
        Equiv.swap_apply_left, Nat.testRes_mergeBitRes_of_eq, Nat.flipBit_mergeBitRes_of_eq,
        Bool.not_not, Nat.mergeBitRes_testBit_testRes_of_eq, Nat.flipBit_apply,
        lt_irrefl, hk, true_and, false_and, dite_false]
    · have H : ∀ {b}, k ≠ t.mergeBitRes b i := fun h => hkt (h ▸ Nat.testRes_mergeBitRes_of_eq)
      simp_rw [Equiv.swap_apply_of_ne_of_ne H H, hkt.le_iff_lt]
      split_ifs <;> rfl

def flipBitIndices (v : Vector α n) (i : ℕ) : Vector α n := v.flipBitIndicesAux i (n.testRes i)

theorem getElem_flipBitIndices {v : Vector α n} {i k : ℕ} (hk : k < n) :
    (v.flipBitIndices i)[k] = if hk : k.flipBit i < n then v[k.flipBit i] else v[k] := by
  refine (getElem_flipBitIndicesAux hk).trans ?_
  simp_rw [Nat.testRes_lt_testRes_iff, hk, true_and, Bool.eq_not]
  rcases eq_or_ne (k.testBit i) (n.testBit i) with hkn | hkn
  · simp_rw [hkn, true_or, true_and]
  · simp_rw [ne_eq, hkn, not_false_eq_true, false_or, and_true,
      Nat.flipBit_lt_iff_lt_flipBit_of_testBit_eq_not_testBit hkn, and_self]

@[simp] theorem flipBitIndices_flipBitIndices {v : Vector α n} :
    (v.flipBitIndices i).flipBitIndices i = v := by
  ext i hi
  simp_rw [getElem_flipBitIndices, Nat.flipBit_flipBit_of_eq, hi, dite_true, dite_eq_ite,
    ite_eq_left_iff, dite_eq_right_iff]
  exact fun C h => (C h).elim

def flipBitVals (v : Vector ℕ n) (i : ℕ) : Vector ℕ n := v.map
  (fun k => if k.flipBit i < n then k.flipBit i else k)

theorem getElem_flipBitVals {v : Vector ℕ n} {i k : ℕ} (hk : k < n) :
    (flipBitVals v i)[k] = if v[k].flipBit i < n then v[k].flipBit i else v[k] :=
  getElem_map _ _ _ _

@[simp] theorem flipBitVals_flipBitVals_of_lt {v : Vector ℕ n} (hv : ∀ i (hi : i < n), v[i] < n) :
    (v.flipBitVals i).flipBitVals i = v := by
  ext i hi
  simp_rw [getElem_flipBitVals]
  split_ifs with _ C
  · simp_rw [Nat.flipBit_flipBit_of_eq]
  · simp_rw [Nat.flipBit_flipBit_of_eq] at C
    exact (C (hv _ _)).elim
  · rfl

end FlipBit

section CondFlipBit

variable {α : Type*} {n i l : ℕ} {c : Vector Bool l}

def condFlipBitIndicesAux (v : Vector α n) (i : ℕ) (c : Vector Bool l) (t : ℕ) : Vector α n :=
    t.fold (fun k _ v => v.swapIfInBounds (k.mergeBitRes false i)
    (k.mergeBitRes (c[k]?.getD false) i)) v

@[simp]
theorem condFlipBitIndicesAux_zero {v : Vector α n} {i : ℕ} {c : Vector Bool l} :
    condFlipBitIndicesAux v i c 0 = v := rfl

@[simp]
theorem condFlipBitIndicesAux_succ {v : Vector α n} {i t : ℕ} {c : Vector Bool l} :
    condFlipBitIndicesAux v i c t.succ = (condFlipBitIndicesAux v i c t).swapIfInBounds
    (t.mergeBitRes false i) (t.mergeBitRes (c[t]?.getD false) i) := rfl

theorem getElem_condFlipBitIndicesAux {v : Vector α n} {i t k : ℕ} {c : Vector Bool l}
    (hk : k < n) :
    (condFlipBitIndicesAux v i c t)[k] =
    if hk' : k.testRes i < t ∧ k.condFlipBit i c < n then
      v[k.condFlipBit i c] else v[k] := by
  induction' t with t IH generalizing k
  · rfl
  · simp_rw [condFlipBitIndicesAux_succ, getElem_swapIfInBounds, getElem_swap, IH,
      Nat.testRes_mergeBitRes_of_eq, lt_self_iff_false, false_and, dite_false,
      Nat.eq_mergeBitRes_iff, Nat.lt_succ_iff]
    rcases lt_trichotomy (k.testRes i) t with hkt | rfl | hkt
    · simp_rw [hkt, hkt.ne, hkt.le, and_false, ite_false, true_and]
      split_ifs <;> rfl
    · simp_rw [and_true, lt_self_iff_false, false_and, dite_false, le_refl, true_and]
      rcases lt_or_le (k.testRes i) l with hkc | hkc
      · simp_rw [getElem?_pos c (k.testRes i) hkc, Option.getD_some,
        Nat.condFlipBit_apply_of_testRes_lt hkc]
        rcases Bool.eq_false_or_eq_true (c[k.testRes i]) with hc | hc <;> simp_rw [hc]
        · simp_rw [cond_true]
          rcases Bool.eq_false_or_eq_true (k.testBit i) with hki | hki <;> simp_rw [hki]
          · simp_rw [Bool.true_eq_false, ite_false, ite_true, ← Bool.not_true, ← hki,
              ← Nat.flipBit_apply, Nat.mergeBitRes_testBit_testRes_of_eq, hk, and_true]
          · simp_rw [if_true, ← Bool.not_false, ← hki, ← Nat.flipBit_apply,
              Nat.mergeBitRes_testBit_testRes_of_eq, hk, true_and]
        · simp_rw [cond_false, hk, dite_true]
          split_ifs with _ h
          · simp_rw [← h, Nat.mergeBitRes_testBit_testRes_of_eq]
          · rfl
          · rfl
      · simp_rw [getElem?_neg c (k.testRes i) hkc.not_lt,
          Option.getD_none, Nat.condFlipBit_apply_of_le_testRes hkc, hk, dite_true]
        split_ifs with _ h
        · simp_rw [← h, Nat.mergeBitRes_testBit_testRes_of_eq]
        · rfl
        · rfl
    · simp_rw [hkt.ne', hkt.not_lt, hkt.not_le,  and_false, false_and, dite_false, ite_false]
      split_ifs <;> rfl

def condFlipBitIndices (v : Vector α n) (i : ℕ) (c : Vector Bool l) :
    Vector α n := v.condFlipBitIndicesAux i c (min l (n.testRes i))

@[simp] theorem getElem_condFlipBitIndices {v : Vector α n} {c : Vector Bool l} {i k : ℕ}
    (hk : k < n) :
  (v.condFlipBitIndices i c)[k] = if hk : k.condFlipBit i c < n then
    v[k.condFlipBit i c] else v[k] := by
  refine (getElem_condFlipBitIndicesAux hk).trans ?_
  simp_rw [lt_min_iff]
  rcases lt_or_le (k.testRes i) l with hkl | hkl
  · simp_rw [hkl, true_and, Nat.condFlipBit_apply_of_testRes_lt hkl]
    rcases (c[k.testRes i]).eq_false_or_eq_true with hkc | hkc
    · simp_rw [hkc, cond_true]
      simp_rw [Nat.testRes_lt_testRes_iff, hk, true_and, Bool.eq_not]
      rcases eq_or_ne (k.testBit i) (n.testBit i) with hkn | hkn
      · simp_rw [hkn, true_or, true_and]
      · simp_rw [ne_eq, hkn, not_false_eq_true, false_or, and_true,
          Nat.flipBit_lt_iff_lt_flipBit_of_testBit_eq_not_testBit hkn, and_self]
    · simp_rw [hkc, cond_false]
      split_ifs <;> rfl
  · simp_rw [Nat.condFlipBit_apply_of_le_testRes hkl]
    split_ifs <;> rfl

@[simp] theorem condFlipBitIndices_condFlipBitIndices {v : Vector α n} :
    (v.condFlipBitIndices i c).condFlipBitIndices i c = v := by
  ext i hi
  simp_rw [getElem_condFlipBitIndices, Nat.condFlipBit_condFlipBit_of_eq, hi, dite_true]
  split_ifs <;> rfl

def condFlipBitVals (v : Vector ℕ n) (i : ℕ) (c : Vector Bool l) : Vector ℕ n :=
  v.map (fun k => if k.condFlipBit i c < n then k.condFlipBit i c else k)

theorem getElem_condFlipBitVals {v : Vector ℕ n} {i : ℕ} {c : Vector Bool l} {k : ℕ}
    (hk : k < n) : (condFlipBitVals v i c)[k] =
    if v[k].condFlipBit i c < n then v[k].condFlipBit i c else v[k] := getElem_map _ _ _ _

@[simp] theorem condFlipBitVals_condFlipBitVals_of_lt {v : Vector ℕ n}
    (hv : ∀ i (hi : i < n), v[i] < n) :
    (v.condFlipBitVals i c).condFlipBitVals i c = v := by
  ext i hi
  simp_rw [getElem_condFlipBitVals]
  split_ifs with _ C
  · simp_rw [Nat.condFlipBit_condFlipBit_of_eq]
  · simp_rw [Nat.condFlipBit_condFlipBit_of_eq] at C
    exact (C (hv _ _)).elim
  · rfl

end CondFlipBit

end Vector

namespace PermOf

section FlipBit

variable {n : ℕ}

def flipBitIndices (a : PermOf n) (i : ℕ) : PermOf n where
  fwdVector := a.fwdVector.flipBitIndices i
  bwdVector := a.bwdVector.flipBitVals i
  getElem_fwdVector_lt := fun hi => by
    simp_rw [Vector.getElem_flipBitIndices, getElem_fwdVector]
    split_ifs <;> exact getElem_lt _ _
  getElem_bwdVector_getElem_fwdVector := fun {j} hk => by
    simp_rw [Vector.getElem_flipBitIndices, Vector.getElem_flipBitVals,
      getElem_fwdVector, getElem_bwdVector]
    by_cases hj : j.flipBit i < n
    · simp_rw [hj, dite_true, getElem_inv_getElem, Nat.flipBit_flipBit_of_eq, hk, ite_true]
    · simp_rw [hj, dite_false, getElem_inv_getElem, hj, if_false]

def flipBitVals (a : PermOf n) (i : ℕ) : PermOf n := (a⁻¹.flipBitIndices i)⁻¹

variable {a b : PermOf n} {i k : ℕ}

theorem getElem_flipBitIndices {hk : k < n} :
    (a.flipBitIndices i)[k] =
    if hk : k.flipBit i < n then a[k.flipBit i] else a[k] := Vector.getElem_flipBitIndices _

theorem getElem_flipBitVals {hk : k < n} :
    (a.flipBitVals i)[k] =
    if a[k].flipBit i < n then a[k].flipBit i else a[k] := Vector.getElem_flipBitVals _

theorem getElem_inv_flipBitIndices {hk : k < n} :
    (a.flipBitIndices i)⁻¹[k] = if a⁻¹[k].flipBit i < n then a⁻¹[k].flipBit i else a⁻¹[k] :=
  Vector.getElem_flipBitVals _

theorem getElem_inv_flipBitVals {hk : k < n} :
    (a.flipBitVals i)⁻¹[k] =
    if hk : k.flipBit i < n then a⁻¹[k.flipBit i] else a⁻¹[k] :=
  Vector.getElem_flipBitIndices _

def flipBit (i : ℕ) : PermOf n := (1 : PermOf n).flipBitIndices i

theorem getElem_flipBit {hk : k < n} :
    (flipBit i)[k] = if k.flipBit i < n then k.flipBit i else k := by
  unfold flipBit
  simp_rw [getElem_flipBitIndices, getElem_one, dite_eq_ite]

theorem getElem_inv_flipBit {hk : k < n} :
    (flipBit i)⁻¹[k] = if k.flipBit i < n then k.flipBit i else k := by
  unfold flipBit
  simp_rw [getElem_inv_flipBitIndices, inv_one, getElem_one]

@[simp] theorem actOnIndices_flipBit {α : Type*} (v : Vector α n) :
    ((flipBit i).actOnIndices v) = v.flipBitIndices i := by
  ext j hj
  simp_rw [Vector.getElem_flipBitIndices, getElem_actOnIndices, getElem_flipBit]
  split_ifs <;> rfl

@[simp]
theorem flipBit_inv : (flipBit i : PermOf n)⁻¹ = flipBit i := by
  ext : 1
  simp_rw [getElem_flipBit, getElem_inv_flipBit]

@[simp]
theorem flipBit_mul_self : (flipBit i : PermOf n) * flipBit i = 1 := by
  rw [← eq_inv_iff_mul_eq_one, flipBit_inv]

@[simp] theorem getElem_flipBit_flipBit {hk : k < n} :
    (flipBit i : PermOf n)[(flipBit i : PermOf n)[k]] = k:= by
  simp_rw [← getElem_mul, flipBit_mul_self, getElem_one]

@[simp]
theorem flipBit_mul_self_mul : flipBit i * (flipBit i * a) = a := by
  rw [← mul_assoc, flipBit_mul_self, one_mul]

@[simp]
theorem mul_flipBit_mul_self : a * flipBit i * flipBit i = a := by
  rw [mul_assoc, flipBit_mul_self, mul_one]

theorem flipBitIndices_eq_mul_flipBit (a : PermOf n) :
    a.flipBitIndices i = a * flipBit i := by
  ext k hk : 1
  simp only [getElem_flipBitIndices, getElem_flipBit, getElem_mul, getElem_one]
  split_ifs <;> rfl

theorem flipBitVals_eq_flipBit_mul (a : PermOf n) :
    a.flipBitVals i = flipBit i * a := by
  ext k hk : 1
  simp only [getElem_flipBitVals, getElem_flipBit, getElem_mul, getElem_one]

@[simp]
theorem inv_flipBitVals {a : PermOf n} {i : ℕ} :
    a⁻¹.flipBitVals i = (a.flipBitIndices i)⁻¹ := by
  simp_rw [flipBitIndices_eq_mul_flipBit, flipBitVals_eq_flipBit_mul, mul_inv_rev, flipBit_inv]

@[simp]
theorem inv_flipBitIndices  {a : PermOf n} {i : ℕ} :
    a⁻¹.flipBitIndices i = (a.flipBitVals i)⁻¹ := by
  simp_rw [flipBitIndices_eq_mul_flipBit, flipBitVals_eq_flipBit_mul, mul_inv_rev, flipBit_inv]

theorem flipBitIndices_inv_eq_flipBit_mul (a : PermOf n) :
    (a.flipBitIndices i)⁻¹ = flipBit i * a⁻¹ := by
  rw [← inv_flipBitVals, flipBitVals_eq_flipBit_mul]

theorem flipBitVals_inv_eq_mul_flipBit (a : PermOf n) :
    (a.flipBitVals i)⁻¹ = a⁻¹ * flipBit i := by
  rw [← inv_flipBitIndices, flipBitIndices_eq_mul_flipBit]

@[simp]
theorem one_flipBitIndices : (1 : PermOf n).flipBitIndices i = flipBit i := by
  rw [flipBitIndices_eq_mul_flipBit, one_mul]
@[simp]
theorem one_flipBitVals : (1 : PermOf n).flipBitVals i = flipBit i := by
  rw [flipBitVals_eq_flipBit_mul, mul_one]

@[simp]
theorem mul_flipBitIndices : (a * b).flipBitIndices i = a * b.flipBitIndices i := by
  simp_rw [flipBitIndices_eq_mul_flipBit, mul_assoc]

@[simp]
theorem mul_flipBitVals : (a * b).flipBitVals i = a.flipBitVals i * b := by
  simp_rw [flipBitVals_eq_flipBit_mul, mul_assoc]

theorem flipBitIndices_mul : a.flipBitIndices i * b = a * b.flipBitVals i := by
  simp_rw [flipBitIndices_eq_mul_flipBit, flipBitVals_eq_flipBit_mul, mul_assoc]

@[simp]
theorem flipBit_flipBitIndices : (flipBit i : PermOf n).flipBitIndices i = 1 := by
  rw [flipBitIndices_eq_mul_flipBit, flipBit_mul_self]
@[simp]
theorem flipBit_flipBitVals : (flipBit i : PermOf n).flipBitVals i = 1 := by
  rw [flipBitVals_eq_flipBit_mul, flipBit_mul_self]

theorem flipBitVals_comm_flipBitIndices {j : ℕ}:
    (a.flipBitVals i).flipBitIndices j = (a.flipBitIndices j).flipBitVals i := by
  simp_rw [flipBitVals_eq_flipBit_mul, flipBitIndices_eq_mul_flipBit, mul_assoc]

theorem flipBitIndices_flipBitIndices_of_eq :
    (a.flipBitIndices i).flipBitIndices i = a := by
  simp_rw [flipBitIndices_eq_mul_flipBit, mul_flipBit_mul_self]

theorem flipBitVals_flipBitVals_of_eq :
    (a.flipBitVals i).flipBitVals i = a := by
  simp_rw [flipBitVals_eq_flipBit_mul, flipBit_mul_self_mul]

theorem getElem_flipBit_of_flipBit_lt {hk : k < n} (hk' : k.flipBit i < n) :
    (flipBit i)[k] = k.flipBit i := by
  simp_rw [getElem_flipBit, hk', ite_true]

theorem getElem_flipBit_of_le_flipBit {hk : k < n} (hk' : n ≤ k.flipBit i) :
    (flipBit i)[k] = k := by
  simp_rw [getElem_flipBit, hk'.not_lt, ite_false]

theorem flipBit_smul_eq_self {x : ℕ} :
    (flipBit i : PermOf n) • x = x ↔ n ≤ x ∨ n ≤ x.flipBit i := by
  simp_rw [smul_eq_dite, getElem_flipBit,
    dite_eq_ite, ite_eq_right_iff, Nat.flipBit_ne_self, imp_false,
    imp_iff_or_not, not_lt, or_comm]

theorem flipBit_smul_ne_self {x : ℕ} :
    (flipBit i : PermOf n) • x ≠ x ↔ x < n ∧ x.flipBit i < n := by
  simp_rw [ne_eq, flipBit_smul_eq_self, not_or, not_le]

theorem mem_fixedBy_flipBit {x : ℕ} :
    x ∈ MulAction.fixedBy ℕ (flipBit i : PermOf n) ↔ n ≤ x ∨ n ≤ x.flipBit i := by
  simp_rw [MulAction.mem_fixedBy, flipBit_smul_eq_self]

theorem movedBy_flipBit {x : ℕ} :
    x ∈ (MulAction.fixedBy ℕ (flipBit i : PermOf n))ᶜ ↔ x < n ∧ x.flipBit i < n := by
  simp only [Set.mem_compl_iff, MulAction.mem_fixedBy, flipBit_smul_ne_self]

theorem getElem_flipBit_ne_self_of_flipBit_lt {hk : k < n} (hk' : k.flipBit i < n) :
    (flipBit i)[k] ≠ k := by
  simp_rw [← smul_of_lt _ hk, flipBit_smul_ne_self]
  exact ⟨hk, hk'⟩

theorem getElem_flipBitIndices_of_flipBit_lt {hk : k < n} (hk' : k.flipBit i < n) :
    (a.flipBitIndices i)[k] = a[k.flipBit i] := by
  simp_rw [flipBitIndices_eq_mul_flipBit, getElem_mul, getElem_flipBit_of_flipBit_lt hk']

theorem getElem_flipBitIndices_of_le_flipBit {hk : k < n} (hk' : n ≤ k.flipBit i) :
    (a.flipBitIndices i)[k] = a[k] := by
  simp_rw [flipBitIndices_eq_mul_flipBit, getElem_mul, getElem_flipBit_of_le_flipBit hk']

theorem flipBitIndices_smul_eq_smul {x : ℕ} :
    (a.flipBitIndices i) • x = a • x ↔ n ≤ x ∨ n ≤ x.flipBit i := by
  simp_rw [flipBitIndices_eq_mul_flipBit, mul_smul, smul_left_cancel_iff, flipBit_smul_eq_self]

theorem flipBitIndices_smul_ne_smul {x : ℕ} :
     (a.flipBitIndices i) • x ≠ a • x ↔ x < n ∧ x.flipBit i < n := by
  simp_rw [ne_eq, flipBitIndices_smul_eq_smul, not_or, not_le]

theorem getElem_flipBitIndices_ne_self_of_flipBit_lt {hk : k < n} (hk' : k.flipBit i < n) :
    (a.flipBitIndices i)[k] ≠ a[k] := by
  simp_rw [← smul_of_lt _ hk, flipBitIndices_smul_ne_smul]
  exact ⟨hk, hk'⟩

theorem getElem_flipBitVals_of_flipBit_lt {hk : k < n} (hk' : a[k].flipBit i < n) :
    (a.flipBitVals i)[k] = a[k].flipBit i := by
  simp_rw [flipBitVals_eq_flipBit_mul, getElem_mul, getElem_flipBit_of_flipBit_lt hk']

theorem getElem_flipBitVals_of_le_flipBit {hk : k < n} (hk' : n ≤ a[k].flipBit i) :
    (a.flipBitVals i)[k] = a[k] := by
  simp_rw [flipBitVals_eq_flipBit_mul, getElem_mul, getElem_flipBit_of_le_flipBit hk']

theorem flipBitVals_smul_eq_smul {x : ℕ} :
    (a.flipBitVals i) • x = a • x ↔ n ≤ x ∨ n ≤ (a • x).flipBit i := by
  simp_rw [flipBitVals_eq_flipBit_mul, mul_smul, flipBit_smul_eq_self, ← not_lt, smul_lt_iff_lt]

theorem flipBitVals_smul_ne_smul {x : ℕ} :
     (a.flipBitVals i) • x ≠ a • x ↔ x < n ∧ (a • x).flipBit i < n := by
  simp_rw [ne_eq, flipBitVals_smul_eq_smul, not_or, not_le]

theorem getElem_flipBitVals_ne_self_of_flipBit_lt {hk : k < n} (hk' : a[k].flipBit i < n) :
    (a.flipBitVals i)[k] ≠ a[k] := by
  simp_rw [← smul_of_lt _ hk, flipBitVals_smul_ne_smul, smul_of_lt _ hk]
  exact ⟨hk, hk'⟩


variable (hin : 2 ^ (i + 1) ∣ n)

include hin

theorem getElem_flipBit_of_div {k : ℕ} {hk : k < n} : (flipBit i)[k] = k.flipBit i := by
  simp_rw [getElem_flipBit, k.flipBit_lt_iff_lt hin, hk, ite_true]

theorem getElem_flipBit_ne_self_of_div {hk : k < n} :
    (flipBit i)[k] ≠ k := by
  simp_rw [getElem_flipBit_of_div hin]
  exact Nat.flipBit_ne_self

@[simp]
theorem flipBit_mul_flipBit_of_le {j : ℕ} (hij : j ≤ i) :
    (flipBit i : PermOf n) * flipBit j = flipBit j * flipBit i := by
  ext : 1
  simp_rw [getElem_mul, getElem_flipBit_of_div hin,
    getElem_flipBit_of_div ((Nat.pow_dvd_pow _ (Nat.succ_le_succ hij)).trans hin),
    Nat.flipBit_flipBit]

theorem getElem_flipBitIndices_of_div {hk : k < n} :
    (a.flipBitIndices i)[k] = a[k.flipBit i]'((k.flipBit_lt_iff_lt hin).mpr hk) := by
  simp_rw [getElem_flipBitIndices, (k.flipBit_lt_iff_lt hin), hk, dite_true]

theorem getElem_inv_flipBitIndices_of_div {hk : k < n} :
    (a.flipBitIndices i)⁻¹[k] = a⁻¹[k].flipBit i := by
  simp_rw [getElem_inv_flipBitIndices, Nat.flipBit_lt_iff_lt hin, getElem_lt, ite_true]

theorem getElem_flipBitIndices_ne_self_of_div {hk : k < n} :
    (a.flipBitIndices i)[k] ≠ a[k] := by
  simp_rw [getElem_flipBitIndices_of_div hin, getElem_ne_iff]
  exact Nat.flipBit_ne_self

theorem getElem_flipBitVals_of_div {hk : k < n} :
    (a.flipBitVals i)[k] = a[k].flipBit i := by
  simp_rw [getElem_flipBitVals, Nat.flipBit_lt_iff_lt hin, getElem_lt, ite_true]

theorem getElem_inv_flipBitVals_of_div {hk : k < n} :
    (a.flipBitVals i)⁻¹[k] = a⁻¹[k.flipBit i]'((k.flipBit_lt_iff_lt hin).mpr hk) := by
  simp_rw [getElem_inv_flipBitVals, (k.flipBit_lt_iff_lt hin), hk, dite_true]

theorem getElem_flipBitVals_ne_self_of_div {hk : k < n} :
    (a.flipBitVals i)[k] ≠ a[k] := by
  simp_rw [getElem_flipBitVals_of_div hin]
  exact Nat.flipBit_ne_self

open Equiv.Perm in
theorem natPerm_flipBit : natPerm (n := n) (flipBit i) =
    ofSubtype ((Nat.flipBitPerm i).subtypePerm (fun k => (k.flipBit_lt_iff_lt hin).symm)) := by
  ext k : 1
  simp_rw [natPerm_apply_apply]
  rcases lt_or_le k n with hk | hk
  · rw [Equiv.Perm.ofSubtype_subtypePerm_of_mem (p := fun i => i < n) _ hk]
    simp_rw [Nat.flipBitPerm_apply, smul_of_lt _ hk, getElem_flipBit, Nat.flipBit_lt_iff_lt hin,
      if_pos hk]
  · rw [Equiv.Perm.ofSubtype_subtypePerm_of_not_mem (p := fun i => i < n) _ hk.not_lt,
      smul_of_ge _ hk]

end FlipBit

section CondFlipBit

variable {n l i j : ℕ}

def condFlipBitIndices (a : PermOf n) (i : ℕ) (c : Vector Bool l) : PermOf n where
  fwdVector := a.fwdVector.condFlipBitIndices i c
  bwdVector := a.bwdVector.condFlipBitVals i c
  getElem_fwdVector_lt := fun hi => by
    simp_rw [Vector.getElem_condFlipBitIndices, getElem_fwdVector]
    split_ifs <;> exact getElem_lt _ _
  getElem_bwdVector_getElem_fwdVector := fun {j} hk => by
    simp_rw [Vector.getElem_condFlipBitIndices, Vector.getElem_condFlipBitVals,
      getElem_fwdVector, getElem_bwdVector]
    by_cases hj : j.condFlipBit i c < n
    · simp_rw [hj, dite_true, getElem_inv_getElem, Nat.condFlipBit_condFlipBit_of_eq, hk, ite_true]
    · simp_rw [hj, dite_false, getElem_inv_getElem, hj, if_false]

def condFlipBitVals (a : PermOf n) (i : ℕ) (c : Vector Bool l) : PermOf n :=
  (a⁻¹.condFlipBitIndices i c)⁻¹

variable {a b : PermOf n} {i k : ℕ} {c : Vector Bool l}

theorem getElem_condFlipBitIndices {hk : k < n} :
    (a.condFlipBitIndices i c)[k] =
    if hk : k.condFlipBit i c < n then a[k.condFlipBit i c] else a[k] :=
  Vector.getElem_condFlipBitIndices _

theorem getElem_condFlipBitVals {hk : k < n} :
    (a.condFlipBitVals i c)[k] =
    if a[k].condFlipBit i c < n then a[k].condFlipBit i c else a[k] :=
  Vector.getElem_condFlipBitVals _

theorem getElem_inv_condFlipBitIndices {hk : k < n} :
    (a.condFlipBitIndices i c)⁻¹[k] =
    if a⁻¹[k].condFlipBit i c < n then a⁻¹[k].condFlipBit i c else a⁻¹[k] :=
  Vector.getElem_condFlipBitVals _

theorem getElem_inv_condFlipBitVals {hk : k < n} :
    (a.condFlipBitVals i c)⁻¹[k] =
    if hk : k.condFlipBit i c < n then a⁻¹[k.condFlipBit i c] else a⁻¹[k] :=
Vector.getElem_condFlipBitIndices _

@[simp] theorem condFlipBitIndices_of_mkVector_false :
    (a.condFlipBitIndices i (Vector.mkVector l false)) = a := by
  ext
  simp_rw [getElem_condFlipBitIndices, Nat.condFlipBit_of_mkVector_false,
    dite_eq_right_iff, implies_true]

@[simp] theorem condFlipBitVals_of_mkVector_false :
    (a.condFlipBitVals i (Vector.mkVector l false)) = a := by
  ext
  simp_rw [getElem_condFlipBitVals, Nat.condFlipBit_of_mkVector_false, ite_self]


def condFlipBit (i : ℕ) (c : Vector Bool l) : PermOf n :=
  (1 : PermOf n).condFlipBitIndices i c

theorem getElem_condFlipBit {hk : k < n} :
    (condFlipBit i c)[k] = if k.condFlipBit i c < n then k.condFlipBit i c else k := by
  unfold condFlipBit
  simp_rw [getElem_condFlipBitIndices, getElem_one, dite_eq_ite]

@[simp] theorem condFlipBit_of_mkVector_false :
    (condFlipBit i (Vector.mkVector l false)) = (1 : PermOf n) := by
  ext
  simp_rw [getElem_condFlipBit, Nat.condFlipBit_of_mkVector_false, ite_self, getElem_one]

theorem getElem_inv_condFlipBit {hk : k < n} :
    (condFlipBit i c)⁻¹[k] = if k.condFlipBit i c < n then k.condFlipBit i c else k := by
  unfold condFlipBit
  simp_rw [getElem_inv_condFlipBitIndices, inv_one, getElem_one]

@[simp]
theorem condFlipBit_inv : (condFlipBit i c : PermOf n)⁻¹ = condFlipBit i c := by
  ext : 1
  simp_rw [getElem_condFlipBit, getElem_inv_condFlipBit]

@[simp]
theorem condFlipBit_mul_self : (condFlipBit i c : PermOf n) * condFlipBit i c = 1 := by
  rw [← eq_inv_iff_mul_eq_one, condFlipBit_inv]

@[simp] theorem getElem_condFlipBit_condFlipBit {hk : k < n} :
    (condFlipBit i c : PermOf n)[(condFlipBit i c : PermOf n)[k]] = k:= by
  simp_rw [← getElem_mul, condFlipBit_mul_self, getElem_one]

@[simp]
theorem condFlipBit_mul_self_mul : condFlipBit i c * (condFlipBit i c * a) = a := by
  rw [← mul_assoc, condFlipBit_mul_self, one_mul]

@[simp]
theorem mul_condFlipBit_mul_self : a * condFlipBit i c * condFlipBit i c = a := by
  rw [mul_assoc, condFlipBit_mul_self, mul_one]

theorem condFlipBitIndices_eq_mul_condFlipBit (a : PermOf n) :
    a.condFlipBitIndices i c = a * condFlipBit i c := by
  ext k hk : 1
  simp only [getElem_condFlipBitIndices, getElem_condFlipBit, getElem_mul, getElem_one]
  split_ifs <;> try {rfl}

theorem condFlipBitVals_eq_condFlipBit_mul (a : PermOf n) :
    a.condFlipBitVals i c = condFlipBit i c * a := by
  ext k hk : 1
  simp only [getElem_condFlipBitVals, getElem_condFlipBit, getElem_mul, getElem_one]

@[simp]
theorem inv_condFlipBitVals {a : PermOf n} {i : ℕ} :
    a⁻¹.condFlipBitVals i c = (a.condFlipBitIndices i c)⁻¹ := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, condFlipBitVals_eq_condFlipBit_mul,
    mul_inv_rev, condFlipBit_inv]

@[simp]
theorem inv_condFlipBitIndices  {a : PermOf n} {i : ℕ} :
    a⁻¹.condFlipBitIndices i c = (a.condFlipBitVals i c)⁻¹ := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, condFlipBitVals_eq_condFlipBit_mul,
    mul_inv_rev, condFlipBit_inv]

theorem condFlipBitIndices_inv_eq_condFlipBit_mul (a : PermOf n) :
    (a.condFlipBitIndices i c)⁻¹ = condFlipBit i c * a⁻¹ := by
  rw [← inv_condFlipBitVals, condFlipBitVals_eq_condFlipBit_mul]

theorem condFlipBitVals_inv_eq_mul_condFlipBit (a : PermOf n) :
    (a.condFlipBitVals i c)⁻¹ = a⁻¹ * condFlipBit i c := by
  rw [← inv_condFlipBitIndices, condFlipBitIndices_eq_mul_condFlipBit]

@[simp]
theorem one_condFlipBitIndices : (1 : PermOf n).condFlipBitIndices i c = condFlipBit i c := by
  rw [condFlipBitIndices_eq_mul_condFlipBit, one_mul]

@[simp]
theorem one_condFlipBitVals : (1 : PermOf n).condFlipBitVals i c = condFlipBit i c := by
  rw [condFlipBitVals_eq_condFlipBit_mul, mul_one]

@[simp]
theorem mul_condFlipBitIndices : a * b.condFlipBitIndices i c = (a * b).condFlipBitIndices i c := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, mul_assoc]

@[simp]
theorem condFlipBitVals_mul : a.condFlipBitVals i c * b = (a * b).condFlipBitVals i c := by
  simp_rw [condFlipBitVals_eq_condFlipBit_mul, mul_assoc]

theorem condFlipBitVals_comm_condFlipBitIndices {d : Vector Bool l} :
    (a.condFlipBitVals i c).condFlipBitIndices j d =
    (a.condFlipBitIndices j d).condFlipBitVals i c := by
  simp_rw [condFlipBitVals_eq_condFlipBit_mul, condFlipBitIndices_eq_mul_condFlipBit, mul_assoc]

theorem condFlipBitIndices_condFlipBitIndices_of_eq :
    (a.condFlipBitIndices i c).condFlipBitIndices i c = a := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, mul_condFlipBit_mul_self]

theorem condFlipBitVals_condFlipBitVals_of_eq :
    (a.condFlipBitVals i c).condFlipBitVals i c = a := by
  simp_rw [condFlipBitVals_eq_condFlipBit_mul, condFlipBit_mul_self_mul]

theorem getElem_condFlipBit_of_condFlipBit_lt {hk : k < n} (hk' : k.condFlipBit i c < n) :
    (condFlipBit i c)[k] = k.condFlipBit i c := by
  simp_rw [getElem_condFlipBit, hk', ite_true]

theorem getElem_condFlipBit_of_le_condFlipBit {hk : k < n} (hk' : n ≤ k.condFlipBit i c) :
    (condFlipBit i c)[k] = k := by
  simp_rw [getElem_condFlipBit, hk'.not_lt, ite_false]

theorem getElem_condFlipBitIndices_of_condFlipBit_lt {hk : k < n} (hk' : k.condFlipBit i c < n) :
    (a.condFlipBitIndices i c)[k] = a[k.condFlipBit i c] := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, getElem_mul,
  getElem_condFlipBit_of_condFlipBit_lt hk']

theorem getElem_condFlipBitIndices_of_le_condFlipBit {hk : k < n} (hk' : n ≤ k.condFlipBit i c) :
    (a.condFlipBitIndices i c)[k] = a[k] := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, getElem_mul,
  getElem_condFlipBit_of_le_condFlipBit hk']

theorem getElem_condFlipBitVals_of_condFlipBit_lt {hk : k < n} (hk' : a[k].condFlipBit i c < n) :
    (a.condFlipBitVals i c)[k] = a[k].condFlipBit i c := by
  simp_rw [condFlipBitVals_eq_condFlipBit_mul, getElem_mul,
  getElem_condFlipBit_of_condFlipBit_lt hk']

theorem getElem_condFlipBitVals_of_le_condFlipBit {hk : k < n} (hk' : n ≤ a[k].condFlipBit i c) :
    (a.condFlipBitVals i c)[k] = a[k] := by
  simp_rw [condFlipBitVals_eq_condFlipBit_mul, getElem_mul,
  getElem_condFlipBit_of_le_condFlipBit hk']

variable (hin : 2 ^ (i + 1) ∣ n)

include hin

theorem getElem_condFlipBit_of_div {k : ℕ} {hk : k < n} :
    (condFlipBit i c)[k] = k.condFlipBit i c := by
  simp_rw [getElem_condFlipBit, k.condFlipBit_lt_iff_lt hin, hk, ite_true]

@[simp]
theorem condFlipBit_mul_condFlipBit_of_lt {d : Vector Bool l}  :
    (condFlipBit i c : PermOf n) * condFlipBit i d = condFlipBit i d * condFlipBit i c := by
  ext : 1
  simp_rw [getElem_mul, getElem_condFlipBit_of_div hin, Nat.condFlipBit_condFlipBit]

theorem getElem_condFlipBitIndices_of_div {hk : k < n} :
    (a.condFlipBitIndices i c)[k] = a[k.condFlipBit i c]'
    ((k.condFlipBit_lt_iff_lt hin).mpr hk) := by
  simp_rw [getElem_condFlipBitIndices, (k.condFlipBit_lt_iff_lt hin), hk, dite_true]

theorem getElem_inv_condFlipBitIndices_of_div {hk : k < n} :
    (a.condFlipBitIndices i c)⁻¹[k] = a⁻¹[k].condFlipBit i c := by
  simp_rw [getElem_inv_condFlipBitIndices, Nat.condFlipBit_lt_iff_lt hin, getElem_lt, ite_true]

theorem getElem_condFlipBitVals_of_div {hk : k < n} :
    (a.condFlipBitVals i c)[k] = a[k].condFlipBit i c := by
  simp_rw [getElem_condFlipBitVals, Nat.condFlipBit_lt_iff_lt hin, getElem_lt, ite_true]

theorem getElem_inv_condFlipBitVals_of_div {hk : k < n} :
    (a.condFlipBitVals i c)⁻¹[k] = a⁻¹[k.condFlipBit i c]'
    ((k.condFlipBit_lt_iff_lt hin).mpr hk) := by
  simp_rw [getElem_inv_condFlipBitVals, (k.condFlipBit_lt_iff_lt hin), hk, dite_true]

open Equiv.Perm in
theorem natPerm_condFlipBit : natPerm (n := n) (condFlipBit i c) =
    ofSubtype ((Nat.condFlipBitPerm i c).subtypePerm
    (fun k => (k.condFlipBit_lt_iff_lt hin).symm)) := by
  ext k : 1
  simp_rw [natPerm_apply_apply]
  rcases lt_or_le k n with hk | hk
  · rw [Equiv.Perm.ofSubtype_subtypePerm_of_mem (p := fun i => i < n) _ hk]
    simp_rw [Nat.condFlipBitPerm_apply, smul_of_lt _ hk, getElem_condFlipBit,
      Nat.condFlipBit_lt_iff_lt hin, if_pos hk]
  · rw [Equiv.Perm.ofSubtype_subtypePerm_of_not_mem (p := fun i => i < n) _ hk.not_lt,
      smul_of_ge _ hk]

end CondFlipBit

section FlipBitCommutator

variable {n p : ℕ}

def flipBitCommutator (a : PermOf n) (i : ℕ) : PermOf n :=
  (a.flipBitIndices i) * (a⁻¹.flipBitIndices i)

variable {a : PermOf n} {i k : ℕ}

theorem flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv :
    (a.flipBitCommutator i) = (a.flipBitIndices i) * (a.flipBitVals i)⁻¹ := rfl

theorem flipBitCommutator_eq_flipBitIndices_mul_flipBitIndices :
    (a.flipBitCommutator i) = (a.flipBitIndices i) * (a⁻¹.flipBitIndices i) := rfl

theorem flipBitCommutator_inv_eq_flipBitVals_mul_flipBitVals :
    (a.flipBitCommutator i)⁻¹ = (a.flipBitVals i) * (a⁻¹.flipBitVals i) := rfl

@[simp] theorem one_flipBitCommutator :
    ((1 : PermOf n).flipBitCommutator i) = 1 := by
  rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv,
    one_flipBitIndices, one_flipBitVals, flipBit_inv, flipBit_mul_self]

theorem flipBitCommutator_eq_commutatorElement :
    (a.flipBitCommutator i) = ⁅a, flipBit i⁆ := by
  simp_rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv,
  commutatorElement_def, flipBitIndices_eq_mul_flipBit, flipBitVals_eq_flipBit_mul,
  mul_inv_rev, mul_assoc]

theorem flipBitCommutator_inv_eq_commutatorElement :
    (a.flipBitCommutator i)⁻¹ = ⁅(flipBit i : PermOf n), a⁆ := by
  rw [flipBitCommutator_eq_commutatorElement, commutatorElement_inv]

theorem getElem_flipBitCommutator {hk : k < n} :
    (a.flipBitCommutator i)[k] =
    if hk : k.flipBit i < n then
    if hk' : a⁻¹[k.flipBit i].flipBit i < n then a[a⁻¹[k.flipBit i].flipBit i] else k.flipBit i
    else if hk' : a⁻¹[k].flipBit i < n then a[a⁻¹[k].flipBit i] else k := by
  simp_rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitIndices,
    getElem_mul, getElem_flipBitIndices]
  split_ifs
  · rfl
  · simp_rw [getElem_getElem_inv]
  · rfl
  · simp_rw [getElem_getElem_inv]

theorem getElem_inv_flipBitCommutator {hk : k < n} :
    (a.flipBitCommutator i)⁻¹[k] =
    if hk : a⁻¹[k].flipBit i < n then
    if a[a⁻¹[k].flipBit i].flipBit i < n then a[a⁻¹[k].flipBit i].flipBit i else a[a⁻¹[k].flipBit i]
    else if k.flipBit i < n then k.flipBit i else k := by
  simp_rw [flipBitCommutator_inv_eq_flipBitVals_mul_flipBitVals, getElem_mul, getElem_flipBitVals]
  split_ifs
  · rfl
  · simp_rw [getElem_getElem_inv]

theorem flipBitCommutator_flipBitCommutator :
    (a.flipBitCommutator i).flipBitCommutator i =
    a.flipBitCommutator i * a.flipBitCommutator i := by
  simp_rw [flipBitCommutator_eq_commutatorElement, commutatorElement_def, mul_inv_rev, inv_inv,
    mul_assoc, flipBit_inv, flipBit_mul_self_mul]

theorem flipBitCommutator_two_pow_flipBitCommutator :
    ((a.flipBitCommutator i)^(2^p)).flipBitCommutator i =
    (a.flipBitCommutator i ^ (2^(p + 1))) := by
  induction' p with p IH
  · simp_rw [zero_add, pow_zero, pow_one, pow_two]
    exact flipBitCommutator_flipBitCommutator
  · nth_rewrite 2 [pow_succ]
    rw [pow_mul]
    simp_rw [← IH, pow_two]
    exact flipBitCommutator_flipBitCommutator

@[simp]
theorem inv_flipBitCommutator_flipBitIndices_inv :
    ((a.flipBitCommutator i).flipBitIndices i)⁻¹ = (a.flipBitCommutator i).flipBitIndices i := by
  simp_rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitIndices, mul_flipBitIndices,
  flipBitIndices_flipBitIndices_of_eq, mul_inv_rev, flipBitIndices_mul, inv_flipBitVals, inv_inv]

@[simp]
theorem inv_flipBitCommutator_flipBitVals_inv :
    ((a.flipBitCommutator i).flipBitVals i)⁻¹ = (a.flipBitCommutator i).flipBitVals i := by
  simp_rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv, mul_flipBitVals,
    mul_inv_rev, inv_inv, ← flipBitVals_comm_flipBitIndices, flipBitIndices_mul,
    inv_flipBitVals]

theorem flipBitCommutator_inv_eq_flipBitIndices_flipBitVals_flipBitCommutator :
    (a.flipBitCommutator i)⁻¹ = ((a.flipBitCommutator i).flipBitVals i).flipBitIndices i := by
  rw [← inv_flipBitCommutator_flipBitVals_inv, inv_flipBitIndices, flipBitVals_flipBitVals_of_eq]

theorem flipBitCommutator_inv_eq_flipBitVals_flipBitIndices_flipBitCommutator :
    (a.flipBitCommutator i)⁻¹ = ((a.flipBitCommutator i).flipBitIndices i).flipBitVals i := by
  rw [← inv_flipBitCommutator_flipBitIndices_inv, inv_flipBitVals,
  flipBitIndices_flipBitIndices_of_eq]

theorem inv_flipBitCommutator_flipBitIndices :
    (a.flipBitCommutator i)⁻¹.flipBitIndices i = (a.flipBitCommutator i).flipBitVals i := by
  simp only [inv_flipBitIndices, inv_flipBitCommutator_flipBitVals_inv]

theorem inv_flipBitCommutator_flipBitVals :
    (a.flipBitCommutator i)⁻¹.flipBitVals i = (a.flipBitCommutator i).flipBitIndices i := by
  simp only [inv_flipBitVals, inv_flipBitCommutator_flipBitIndices_inv]

@[simp]
theorem flipBitCommutator_pow_flipBitIndices_inv :
    (((a.flipBitCommutator i)^p).flipBitIndices i)⁻¹ =
    ((a.flipBitCommutator i)^p).flipBitIndices i := by
  induction' p with p IH
  · simp_rw [pow_zero, one_flipBitIndices, flipBit_inv]
  · nth_rewrite 1 [pow_succ']
    simp_rw [pow_succ, mul_flipBitIndices, mul_inv_rev, IH, flipBitIndices_mul,
      inv_flipBitCommutator_flipBitVals]

@[simp]
theorem flipBitCommutator_pow_flipBitVals_inv :
    (((a.flipBitCommutator i)^p).flipBitVals i)⁻¹ =
    ((a.flipBitCommutator i)^p).flipBitVals i := by
  induction' p with p IH
  · simp_rw [pow_zero, one_flipBitVals, flipBit_inv]
  · nth_rewrite 1 [pow_succ']
    simp_rw [pow_succ, mul_flipBitVals, mul_inv_rev, inv_flipBitCommutator_flipBitVals_inv,
      ← flipBitIndices_mul, inv_flipBitIndices, IH]

theorem inv_flipBitCommutator_pow_flipBitIndices :
    ((a.flipBitCommutator i)^p)⁻¹.flipBitIndices i = ((a.flipBitCommutator i)^p).flipBitVals i := by
  simp only [inv_flipBitIndices, flipBitCommutator_pow_flipBitVals_inv]

theorem inv_flipBitCommutator_pow_flipBitVals :
    ((a.flipBitCommutator i)^p)⁻¹.flipBitVals i = ((a.flipBitCommutator i)^p).flipBitIndices i := by
  simp only [inv_flipBitVals, flipBitCommutator_pow_flipBitIndices_inv]

@[simp]
theorem flipBitCommutator_zpow_flipBitIndices_inv {p : ℤ} :
    (((a.flipBitCommutator i)^p).flipBitIndices i)⁻¹ =
    ((a.flipBitCommutator i)^p).flipBitIndices i := by
  cases p
  · simp_rw [Int.ofNat_eq_coe, zpow_natCast, flipBitCommutator_pow_flipBitIndices_inv]
  · simp_rw [zpow_negSucc, inv_flipBitCommutator_pow_flipBitIndices,
      flipBitCommutator_pow_flipBitVals_inv]

@[simp]
theorem flipBitCommutator_zpow_flipBitVals_inv {p : ℤ} :
    (((a.flipBitCommutator i)^p).flipBitVals i)⁻¹ =
    ((a.flipBitCommutator i)^p).flipBitVals i := by
  cases p
  · simp_rw [Int.ofNat_eq_coe, zpow_natCast, flipBitCommutator_pow_flipBitVals_inv]
  · simp_rw [zpow_negSucc, inv_flipBitCommutator_pow_flipBitVals,
      flipBitCommutator_pow_flipBitIndices_inv]

theorem inv_flipBitCommutator_zpow_flipBitIndices {p : ℤ} :
    ((a.flipBitCommutator i)^p)⁻¹.flipBitIndices i = ((a.flipBitCommutator i)^p).flipBitVals i := by
  simp only [inv_flipBitIndices, flipBitCommutator_zpow_flipBitVals_inv]

theorem inv_flipBitCommutator_zpow_flipBitVals {p : ℤ} :
    ((a.flipBitCommutator i)^p)⁻¹.flipBitVals i = ((a.flipBitCommutator i)^p).flipBitIndices i := by
  simp only [inv_flipBitVals, flipBitCommutator_zpow_flipBitIndices_inv]

theorem flipBitCommutator_smul_eq_flipBit :
    (a.flipBitCommutator i) • k = (flipBit i : PermOf n) • k ↔
    n ≤ k ∨ n ≤ (a⁻¹ • (flipBit i : PermOf n) • k).flipBit i := by
  simp_rw [flipBitCommutator_eq_commutatorElement, commutatorElement_def, mul_smul,
    ← eq_inv_smul_iff (g := a), flipBit_inv, flipBit_smul_eq_self, ← not_lt, smul_lt_iff_lt]

theorem flipBitCommutator_smul_ne_flipBit :
    (a.flipBitCommutator i) • k ≠ (flipBit i : PermOf n) • k ↔
    k < n ∧ (a⁻¹ • (flipBit i : PermOf n) • k).flipBit i < n := by
  simp_rw [ne_eq, flipBitCommutator_smul_eq_flipBit, not_or, not_le]

theorem getElem_flipBitCommutator_ne_flipBit {hk : k < n}
    (hk' : (a⁻¹ • (flipBit i : PermOf n) • k).flipBit i < n) :
    (a.flipBitCommutator i)[k] ≠ (flipBit i : PermOf n)[k] := by
  simp_rw [← smul_of_lt _ hk, flipBitCommutator_smul_ne_flipBit]
  exact ⟨hk, hk'⟩

theorem flipBitCommutator_flipBitIndices_smul_eq_self :
    (a.flipBitCommutator i).flipBitIndices i • k = k ↔ n ≤ k ∨ n ≤ (a⁻¹ • k).flipBit i := by
  simp_rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitIndices, mul_flipBitIndices,
    flipBitIndices_flipBitIndices_of_eq, flipBitIndices_eq_mul_flipBit, mul_smul,
    ← eq_inv_smul_iff (g := a), flipBit_smul_eq_self, ← not_lt, smul_lt_iff_lt]

theorem flipBitCommutator_flipBitIndices_smul_ne_self :
    (a.flipBitCommutator i).flipBitIndices i • k ≠ k ↔ k < n ∧ (a⁻¹ • k).flipBit i < n := by
  simp_rw [ne_eq, flipBitCommutator_flipBitIndices_smul_eq_self, not_or, not_le]

theorem getElem_flipBitCommutator_flipBitIndices_ne_self {hk : k < n}
    (hk' : (a⁻¹ • k).flipBit i < n) : ((a.flipBitCommutator i).flipBitIndices i)[k] ≠ k := by
  simp_rw [← smul_of_lt _ hk, flipBitCommutator_flipBitIndices_smul_ne_self]
  exact ⟨hk, hk'⟩

theorem flipBitCommutator_flipBitVals_smul_eq_self :
    (a.flipBitCommutator i).flipBitVals i • k = k ↔
    n ≤ k ∨ n ≤ (a⁻¹ • (flipBit i : PermOf n) • k).flipBit i := by
  simp_rw [flipBitCommutator_eq_commutatorElement, commutatorElement_def, mul_flipBitVals,
    flipBitVals_eq_flipBit_mul, mul_smul, ← eq_inv_smul_iff (g := (flipBit i)),
    ← eq_inv_smul_iff (g := a), flipBit_smul_eq_self, ← not_lt, smul_lt_iff_lt, flipBit_inv]

theorem flipBitCommutator_flipBitVals_smul_ne_self :
    (a.flipBitCommutator i).flipBitVals i • k ≠ k ↔ k < n ∧
      (a⁻¹ • (flipBit i : PermOf n) • k).flipBit i < n := by
  simp_rw [ne_eq, flipBitCommutator_flipBitVals_smul_eq_self, not_or, not_le]

theorem getElem_flipBitCommutator_flipBitVals_ne_self {hk : k < n}
    (hk' : (a⁻¹ • (flipBit i : PermOf n) • k).flipBit i < n) :
    ((a.flipBitCommutator i).flipBitVals i)[k] ≠ k := by
  simp_rw [← smul_of_lt _ hk, flipBitCommutator_flipBitVals_smul_ne_self]
  exact ⟨hk, hk'⟩

variable (hin : 2^(i + 1) ∣ n)

include hin

@[simp]
theorem getElem_flipBitCommutator_of_div {hk : k < n} :
    (a.flipBitCommutator i)[k] =
      a[(a⁻¹[k.flipBit i]'((k.flipBit_lt_iff_lt hin).mpr hk)).flipBit i]'
      ((Nat.flipBit_lt_iff_lt hin).mpr (getElem_lt _ _)) := by
  simp_rw [getElem_flipBitCommutator, Nat.flipBit_lt_iff_lt hin, getElem_lt, hk, dite_true]

@[simp]
theorem getElem_inv_flipBitCommutator_of_div {hk : k < n} :
    (a.flipBitCommutator i)⁻¹[k] = (a[a⁻¹[k].flipBit i]'
    ((Nat.flipBit_lt_iff_lt hin).mpr (getElem_lt _)) ).flipBit i := by
  simp_rw [getElem_inv_flipBitCommutator, Nat.flipBit_lt_iff_lt hin, hk,
  getElem_lt, dite_true, if_true]

theorem getElem_flipBitIndices_flipBitCommutator {hk : k < n} :
    ((a.flipBitCommutator i).flipBitIndices i)[k] =
    (a.flipBitCommutator i)⁻¹[k].flipBit i := by
  simp_rw [← inv_flipBitCommutator_flipBitVals, getElem_flipBitVals_of_div hin]

theorem getElem_flipBitIndices_flipBitCommutator_inv {hk : k < n} :
    ((a.flipBitCommutator i)⁻¹.flipBitIndices i)[k] =
    (a.flipBitCommutator i)[k].flipBit i := by
  rw [inv_flipBitCommutator_flipBitIndices, getElem_flipBitVals_of_div hin]

theorem getElem_flipBitIndices_flipBitCommutator_pow_inv {hk : k < n} :
    (((a.flipBitCommutator i)^p)⁻¹.flipBitIndices i)[k] =
    ((a.flipBitCommutator i)^p)[k].flipBit i := by
  rw [inv_flipBitCommutator_pow_flipBitIndices, getElem_flipBitVals_of_div hin]

theorem getElem_flipBit_flipBitCommutator_pow {hk : k < n} :
    (((a.flipBitCommutator i)^p).flipBitIndices i)[k] =
    ((a.flipBitCommutator i)^p)⁻¹[k].flipBit i := by
  rw [← inv_flipBitCommutator_pow_flipBitVals, getElem_flipBitVals_of_div hin]

theorem getElem_flipBit_flipBitCommutator_zpow_inv {p : ℤ} {hk : k < n} :
    (((a.flipBitCommutator i)^p)⁻¹.flipBitIndices i)[k] =
    ((a.flipBitCommutator i)^p)[k].flipBit i := by
  rw [inv_flipBitCommutator_zpow_flipBitIndices, getElem_flipBitVals_of_div hin]

theorem getElem_flipBit_flipBitCommutator_zpow {p : ℤ} {hk : k < n} :
    (((a.flipBitCommutator i)^p).flipBitIndices i)[k] =
    ((a.flipBitCommutator i)^p)⁻¹[k].flipBit i := by
  rw [← inv_flipBitCommutator_zpow_flipBitVals, getElem_flipBitVals_of_div hin]

theorem getElem_flipBitCommutator_ne_flipBit_of_div {hk : k < n} :
    (a.flipBitCommutator i)[k] ≠ k.flipBit i := by
  simp_rw [← getElem_flipBit_of_div hin (hk := hk), ← smul_of_lt _ hk,
  flipBitCommutator_smul_ne_flipBit, Nat.flipBit_lt_iff_lt hin, smul_lt_iff_lt, and_self, hk]

theorem getElem_flipBitCommutator_flipBit_ne {hk : k < n} :
    (a.flipBitCommutator i)[k].flipBit i ≠ k := by
  simp_rw [← getElem_flipBitVals_of_div hin, ← smul_of_lt _ hk,
    flipBitCommutator_flipBitVals_smul_ne_self, Nat.flipBit_lt_iff_lt hin, smul_lt_iff_lt,
    and_self, hk]

theorem getElem_pow_flipBitCommutator_ne_flipBit {hk : k < n} {p : ℕ} :
    ((a.flipBitCommutator i) ^ p)[k] ≠ k.flipBit i := by
  induction' p using Nat.twoStepInduction with p IH generalizing k
  · rw [pow_zero, getElem_one]
    exact Nat.flipBit_ne_self.symm
  · rw [pow_one]
    exact a.getElem_flipBitCommutator_ne_flipBit_of_div hin
  · have hk' : k.flipBit i < n := by rwa [Nat.flipBit_lt_iff_lt hin]
    simp_rw [pow_succ (n := p.succ), pow_succ' (n := p), getElem_mul,
    ← (ne_getElem_inv_iff _ _ hk'),
    getElem_inv_flipBitCommutator_of_div hin, getElem_flipBitCommutator_of_div hin]
    exact IH

theorem getElem_flipBitCommutator_pow_flipBit_ne {hk : k < n} {p : ℕ} :
    ((a.flipBitCommutator i) ^ p)[k].flipBit i ≠ k := by
  intros H
  apply (a.getElem_pow_flipBitCommutator_ne_flipBit hin (hk := hk) (p := p))
  nth_rewrite 2 [← H]
  simp_rw [Nat.flipBit_flipBit_of_eq]

theorem getElem_zpow_flipBitCommutator_ne_flipBit {hk : k < n} {p : ℤ} :
    ((a.flipBitCommutator i) ^ p)[k] ≠ k.flipBit i := by
  cases p
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact getElem_pow_flipBitCommutator_ne_flipBit hin
  · have hk' : k.flipBit i < n := by rwa [Nat.flipBit_lt_iff_lt hin]
    simp_rw [zpow_negSucc, getElem_inv_ne_iff _ _ hk']
    exact (Nat.flipBit_flipBit_of_eq (i := i)).symm.trans_ne
      (getElem_pow_flipBitCommutator_ne_flipBit hin).symm

theorem getElem_flipBitCommutator_zpow_flipBit_ne {hk : k < n} {p : ℤ} :
    ((a.flipBitCommutator i) ^ p)[k].flipBit i ≠ k := by
  intros H
  apply (a.getElem_zpow_flipBitCommutator_ne_flipBit hin (hk := hk) (p := p))
  nth_rewrite 2 [← H]
  simp_rw [Nat.flipBit_flipBit_of_eq]

theorem getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow {hk : k < n}
    {p q : ℤ} : ((a.flipBitCommutator i) ^ p)[k] ≠
    ((a.flipBitCommutator i) ^ q)[k].flipBit i := by
  rw [← sub_add_cancel p q, zpow_add, getElem_mul]
  exact getElem_zpow_flipBitCommutator_ne_flipBit hin

theorem disjoint_flipBitCommutator_cycleOf_map_self_flipBitPerm (k : ℕ) :
    Disjoint ((a.flipBitCommutator i).cycleOf k)
  (((a.flipBitCommutator i).cycleOf k).map <| Nat.flipBitPerm i) := by
  simp_rw [Finset.disjoint_iff_ne, Finset.mem_map, Equiv.coe_toEmbedding, Nat.flipBitPerm_apply,
    mem_cycleOf_iff_exists_zpow_smul, forall_exists_index, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff]
  rcases lt_or_le k n with hk | hk
  · simp_rw [smul_of_lt _ hk]
    exact fun _ _ => getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow hin
  · simp_rw [smul_of_ge _ hk]
    exact fun _ _ => Nat.flipBit_ne_self.symm

theorem two_mul_filter_sameCycle_card_le_card (s : Finset ℕ)
    (hsy : ∀ q, q ∈ s → q.flipBit i ∈ s) (k : ℕ) (hsc : (a.flipBitCommutator i).cycleOf k ⊆ s) :
  MulAction.period (a.flipBitCommutator i) k ≤ s.card / 2 := by
  rw [← card_cycleOf, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  nth_rewrite 2 [← Finset.card_map (Nat.flipBitPerm i).toEmbedding]
  rw [← Finset.card_union_of_disjoint
    (a.disjoint_flipBitCommutator_cycleOf_map_self_flipBitPerm hin k)]
  refine Finset.card_le_card (Finset.union_subset hsc ?_)
  simp_rw [Finset.map_subset_iff_subset_preimage, Finset.subset_iff, Finset.mem_preimage,
  Equiv.coe_toEmbedding, Nat.flipBitPerm_apply]
  exact fun _ h => (hsy _ (hsc h))

end FlipBitCommutator

end PermOf

section BitInvariant

variable {n i k x l : ℕ}

namespace PermOf

theorem getElem_testBit_of_ge (a : PermOf n) {k : ℕ} (h : n ≤ 2^k) {i : ℕ} (hi : i < n) :
    a[i].testBit k = false :=
  Nat.testBit_eq_false_of_lt <| (a.getElem_lt).trans_le h

open Nat

def BitInvariant (i : ℕ) (a : PermOf n) : Prop :=
  a.fwdVector.map (testBit · i) = (Vector.range n).map (testBit · i)

variable {a b : PermOf n}

theorem one_bitInvariant : BitInvariant i (1 : PermOf n) := rfl

theorem bitInvariant_iff_testBit_getElem_eq_testBit : a.BitInvariant i ↔
    ∀ {x} (h : x < n), a[x].testBit i = x.testBit i := by
  unfold BitInvariant
  simp_rw [Vector.ext_iff]
  simp_rw [Vector.getElem_map, getElem_fwdVector, Vector.getElem_range]

theorem bitInvariant_of_ge (h : n ≤ 2^i) : a.BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, a.getElem_testBit_of_ge h]
  exact fun (hx : _ < n) => (Nat.testBit_eq_false_of_lt (hx.trans_le h)).symm

theorem bitInvariant_of_ge_of_ge (h : n ≤ 2^i) (hk : i ≤ k) : a.BitInvariant k :=
  bitInvariant_of_ge (h.trans (Nat.pow_le_pow_right zero_lt_two hk))

theorem forall_lt_bitInvariant_iff_eq_one_of_ge (hin : n ≤ 2^i) :
    (∀ k < i, a.BitInvariant k) ↔ a = 1 := by
  refine ⟨fun h => PermOf.ext ?_, fun h _ _ => h ▸ one_bitInvariant⟩
  simp only [getElem_one, testBit_ext_iff]
  intro j hj k
  rcases lt_or_le k i with hk | hk
  · simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit] at h
    apply h _ hk
  · have H := a.bitInvariant_of_ge_of_ge hin hk
    simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit] at H
    apply H

@[simp]
theorem BitInvariant.testBit_getElem_eq_testBit (ha : a.BitInvariant i) {x : ℕ}
    (h : x < n) : a[x].testBit i = x.testBit i :=
  bitInvariant_iff_testBit_getElem_eq_testBit.mp ha h

theorem bitInvariant_of_testBit_getElem_eq_testBit (h : ∀ {x} (h : x < n),
    a[x].testBit i = x.testBit i) : a.BitInvariant i :=
  bitInvariant_iff_testBit_getElem_eq_testBit.mpr h

@[simp]
theorem BitInvariant.inv (ha : a.BitInvariant i) :
    BitInvariant i a⁻¹ := bitInvariant_of_testBit_getElem_eq_testBit <| fun hi => by
  rw [← ha.testBit_getElem_eq_testBit (getElem_lt _), getElem_getElem_inv]

theorem BitInvariant.of_inv (ha : a⁻¹.BitInvariant i) : BitInvariant i a := ha.inv

theorem bitInvariant_iff_bitInvariant_inv : a⁻¹.BitInvariant i ↔ a.BitInvariant i :=
  ⟨fun h => h.inv, fun h => h.inv⟩

theorem BitInvariant.mul (ha : a.BitInvariant i) (hb : b.BitInvariant i) :
    BitInvariant i (a * b) := bitInvariant_of_testBit_getElem_eq_testBit <| by
  simp_rw [getElem_mul, ha.testBit_getElem_eq_testBit,
  hb.testBit_getElem_eq_testBit, implies_true]

theorem BitInvariant.pow (ha : a.BitInvariant i) (p : ℕ) : (a ^ p).BitInvariant i := by
  induction' p with p IH
  · exact one_bitInvariant
  · rw [pow_succ]
    exact BitInvariant.mul IH ha

theorem BitInvariant.zpow (ha : a.BitInvariant i) (p : ℤ) : (a ^ p).BitInvariant i := by
  cases' p
  · simp_rw [Int.ofNat_eq_coe, zpow_natCast]
    exact ha.pow _
  · simp only [zpow_negSucc]
    exact (ha.pow _).inv

theorem getElem_eq_self_of_forall_bitInvariant_lt_of_lt (ha : ∀ k < i, a.BitInvariant k)
    (hx : x < 2^i) (hin : 2^i ≤ n) : ∀ k, x ≤ (a^k)[x] := fun k => by
  refine Nat.le_of_testBit ?_
  intro j
  rcases lt_or_le j i with hj | hj
  · simp_rw [((ha _ hj).pow _).testBit_getElem_eq_testBit, imp_self]
  · simp_rw [testBit_lt_two_pow (hx.trans_le (Nat.pow_le_pow_of_le one_lt_two hj)),
      Bool.false_eq_true, false_implies]

theorem flipBit_of_ne {j : ℕ} (hij : i ≠ j) :
    (flipBit j : PermOf n).BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, getElem_flipBit,
    apply_ite (fun (k : ℕ) => k.testBit i), testBit_flipBit_of_ne hij, ite_self, implies_true]

theorem condFlipBit_of_ne {j : ℕ} {c : Vector Bool l} (hij : i ≠ j) :
    (condFlipBit j c : PermOf n).BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, getElem_condFlipBit,
    apply_ite (fun (k : ℕ) => k.testBit i), testBit_condFlipBit_of_ne hij, ite_self, implies_true]

theorem BitInvariant.flipBitIndices_of_ne (ha : a.BitInvariant i) {j : ℕ} (hij : i ≠ j) :
    (a.flipBitIndices j).BitInvariant i := by
  simp_rw [flipBitIndices_eq_mul_flipBit]
  exact ha.mul (flipBit_of_ne hij)

theorem BitInvariant.flipBitVals_of_ne (ha : a.BitInvariant i) {j : ℕ} (hij : i ≠ j) :
    (a.flipBitVals j).BitInvariant i := by
  simp_rw [flipBitVals_eq_flipBit_mul]
  exact (flipBit_of_ne hij).mul ha

theorem BitInvariant.flipBitCommutator_of_ne (ha : a.BitInvariant i) {j : ℕ} (hij : i ≠ j) :
    (a.flipBitCommutator j).BitInvariant i := by
  simp_rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv]
  exact (ha.flipBitIndices_of_ne hij).mul (ha.flipBitVals_of_ne hij).inv

theorem cycleOf_subset_bitMatchUnder {x : ℕ} (a : PermOf (2^(n + 1))) (i : ℕ)
  (ha : ∀ k < (i : ℕ), a.BitInvariant k) (hk : x < 2^(n + 1)) :
  a.cycleOf x ⊆ bitMatchUnder i ⟨x, hk⟩ := by
  simp_rw [Finset.subset_iff, mem_cycleOf_iff_exists_getElem_zpow _ hk, mem_bitMatchUnder_iff,
      forall_exists_index, forall_apply_eq_imp_iff, getElem_lt _,
      true_and]
  intros _ _ hk
  exact ((ha _ hk).zpow _).testBit_getElem_eq_testBit _

theorem flipBitCommutator_cycleMinVector_of_period_bounded (a : PermOf (2^(n + 1)))
    {hk : k < 2^(n + 1)}
    (ha : ∀ {x : ℕ}, MulAction.period (a.flipBitCommutator i) x ≤ 2 ^ (n - i)):
    ((a.flipBitCommutator i).CycleMinVector (n - i))[a[(flipBit i)[k]]] =
    ((a.flipBitCommutator i).CycleMinVector (n - i))[(flipBit i)[a[k]]]'(getElem_lt _) := by conv =>
  rhs
  rw [cycleMinVector_eq_apply_cycleMinVector _ _ ha]
  congr
  · rfl
  · rw [flipBitCommutator_eq_commutatorElement, commutatorElement_def]
    simp only [getElem_mul, getElem_inv_getElem]

theorem period_le_two_pow_sub_of_bitInvariant_lt {a : PermOf (2^(n + 1))} {i : ℕ}
    (ha : ∀ k < i, a.BitInvariant k) :
    ∀ {k : ℕ}, MulAction.period (a.flipBitCommutator i) k ≤ 2 ^ (n - i) := fun {k} => by
  rcases le_or_lt i n with hi | hi
  · have hin := (Nat.pow_dvd_pow 2 (Nat.succ_le_succ hi))
    rcases lt_or_le k (2^(n + 1)) with hk | hk
    · rw [← Nat.mul_div_cancel (2^(n - i)) (zero_lt_two), ← pow_succ,
        ← Nat.sub_add_comm hi, ← card_bitMatchUnder i ⟨k, hk⟩]
      refine two_mul_filter_sameCycle_card_le_card
        (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi)) _ ?_ _ ?_
      · exact flipBit_mem_bitMatchUnder ⟨le_rfl, Nat.lt_succ_of_le hi⟩
      · exact (a.flipBitCommutator i).cycleOf_subset_bitMatchUnder _
          (fun _ hl => (ha _ hl).flipBitCommutator_of_ne hl.ne) _
    · rw [period_eq_one_of_ge _ hk]
      exact Nat.one_le_pow _ _ zero_lt_two
  · rw [forall_lt_bitInvariant_iff_eq_one_of_ge (Nat.pow_le_pow_of_le one_lt_two hi)] at ha
    simp_rw [ha, one_flipBitCommutator, MulAction.period_one, Nat.one_le_iff_ne_zero]
    exact (Nat.two_pow_pos (n - i)).ne'

theorem flipBit_getElem_cycleMinVector_flipBitCommutator_comm (a : PermOf (2^(n + 1)))
    (ha : ∀ k < i, a.BitInvariant k) {k : ℕ}
    (hk : k < 2^(n + 1)) (hi : i < n + 1):
    ((a.flipBitCommutator i).CycleMinVector (n - i))[(k.flipBit i)]'
    (by rwa [flipBit_lt_iff_lt <| (Nat.pow_dvd_pow _ hi).trans (dvd_of_eq rfl)]) =
    (((a.flipBitCommutator i).CycleMinVector (n - i))[k]).flipBit i
     := by
  have hin : 2 ^ ((i : ℕ) + 1) ∣ 2^(n + 1) := Nat.pow_dvd_pow _ hi
  have hk' := (flipBit_lt_two_pow_iff_lt_two_pow hi).mpr hk
  simp_rw [getElem_cycleMinVector_eq_min'_cycleOf _
    (period_le_two_pow_sub_of_bitInvariant_lt ha)]
  have HP := Finset.min'_mem ((a.flipBitCommutator i).cycleOf k) (nonempty_cycleOf _)
  simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hk] at HP
  rcases HP with ⟨p, hp⟩
  have HQ := Finset.min'_mem ((a.flipBitCommutator i).cycleOf (k.flipBit i))
    (nonempty_cycleOf _)
  simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hk'] at HQ
  rcases HQ with ⟨q, hq⟩
  simp_rw [← getElem_flipBit_of_div hin (hk := hk), ← getElem_mul,
    ← flipBitIndices_eq_mul_flipBit, getElem_flipBit_of_div hin (hk := hk),
    a.getElem_flipBit_flipBitCommutator_zpow hin, ← zpow_neg] at hq
  simp_rw [le_antisymm_iff]
  refine ⟨Finset.min'_le _ _ ?_, ?_⟩
  · simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hk']
    refine ⟨-p, ?_⟩
    simp_rw [zpow_neg, ← hp, ← a.getElem_flipBit_flipBitCommutator_zpow_inv hin (hk := hk),
      getElem_flipBitIndices_of_div hin]
  · have H := Finset.min'_le _ _ ((a.flipBitCommutator i).getElem_zpow_mem_cycleOf
      hk (-q))
    rcases H.eq_or_lt with H | H
    · rw [H, hq]
    · rw [←hq, ← hp]
      rw [← hp] at H
      have HHH := Nat.flipBit_lt_flipBit_of_lt_of_ne_flipBit_of_lt_testBit_eq H
        (getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow hin)
      refine (HHH fun hi => ?_).le
      simp_rw [(((ha _ hi).flipBitCommutator_of_ne hi.ne).zpow  _).testBit_getElem_eq_testBit]

theorem flipBitCommutator_cycleMin_flipBit_comm (a : PermOf (2^(n + 1))) {i : ℕ}
    (ha : ∀ k < (i : ℕ), BitInvariant k a) (k : ℕ) :
    ((a.flipBitCommutator i).CycleMin (n - i)) (k.flipBit i) =
    (((a.flipBitCommutator i).CycleMin (n - i)) k).flipBit i := by
  rcases lt_or_le i (n + 1) with hi | hi
  · have hin :  2 ^ ((i : ℕ) + 1) ∣ 2^(n + 1) := Nat.pow_dvd_pow _ hi
    rcases lt_or_le k (2^(n + 1)) with hk | hk
    · have H := flipBit_getElem_cycleMinVector_flipBitCommutator_comm a ha hk hi
      simp_rw [getElem_cycleMinVector] at H
      exact H
    · simp_rw [cycleMin_of_ge _ hk, cycleMin_of_ge _ <| le_of_not_lt <|
      (Nat.flipBit_lt_iff_lt hin).not.mpr hk.not_lt]
  · rw [forall_lt_bitInvariant_iff_eq_one_of_ge (Nat.pow_le_pow_of_le one_lt_two hi)] at ha
    simp_rw [ha, one_flipBitCommutator, one_cycleMin]

end PermOf

end BitInvariant
