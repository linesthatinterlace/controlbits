import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Ring.Defs
import Controlbits.Fin
import Controlbits.Equivs
import Controlbits.Submonoid
import Controlbits.FunctionEnd
import Controlbits.ArrayPerm

namespace Equiv

/-- A subtype of a `Prod` that depends only on the second component is equivalent to the
first type times the corresponding subtype of the second type. -/
@[simps!]
def prodSubtypeSndEquivSubtypeProd {p : β → Prop} : {s : α × β // p s.2} ≃ α × {b // p b} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Equiv

namespace Bool

theorem toNat_decide {P : Prop} [Decidable P] : toNat P = if P then 1 else 0 :=
  cond_decide _ _ _

@[simp]
theorem toNat_pos {P : Prop} [Decidable P] (p : P) : toNat P = 1 := by
  simp_rw [p, decide_true_eq_true, toNat_true]

@[simp]
theorem toNat_neg {P : Prop} [Decidable P] (p : ¬P) : toNat P = 0 := by
  simp_rw [p, decide_false_eq_false, toNat_false]

theorem toNat_True : toNat True = 1 := by rw [decide_true_eq_true, toNat_true]

theorem toNat_False : toNat False = 0 := by rw [decide_false_eq_false, toNat_false]

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
  · simp_rw [p, decide_true_eq_true, true_and, true_implies]
  · simp only [p, decide_false_eq_false, false_and, false_implies]

end Bool

namespace Fin

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
theorem val_xor {i j : Fin n} : (i ^^^ j).val = (i.val ^^^ j.val) % n := rfl

end Fin

namespace Nat

section Size

@[simp]
theorem size_succ {x : ℕ} : x.succ.size ≠ 0 := by
  simp_rw [ne_eq, Nat.size_eq_zero, not_false_eq_true]

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

section TestBit

theorem testBit_bit (m : ℕ) (b : Bool) (n : ℕ) :
    (Nat.bit b n).testBit m = if m = 0 then b else n.testBit (m - 1) := by
  cases' m
  · simp_rw [Nat.testBit_bit_zero, if_true]
  · simp_rw [Nat.testBit_bit_succ, if_false, Nat.add_sub_cancel]

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

theorem testBit_div_two (x : Nat) (i : Nat) : (x / 2).testBit i = x.testBit i.succ :=
  (testBit_succ x i).symm

theorem testBit_div_two_pow (x i j : ℕ) : testBit (x/2^i) j = testBit x (i + j) := by
  induction' i with i IH generalizing x j
  · rw [pow_zero, Nat.div_one, zero_add]
  · rw [pow_succ, ← Nat.div_div_eq_div_mul, testBit_div_two, IH,
      succ_eq_add_one, add_comm j, add_assoc]

theorem testBit_ext_iff {q q' : ℕ} : q = q' ↔ (∀ i : ℕ, q.testBit i = q'.testBit i) :=
  ⟨fun h _ => h ▸ rfl, Nat.eq_of_testBit_eq⟩

theorem testBit_ext_div_two_pow_iff {q q' m : ℕ} : q / 2^m = q' / 2^m ↔
  (∀ i ≥ m, q.testBit i = q'.testBit i) := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow, le_iff_exists_add,
  forall_exists_index, forall_eq_apply_imp_iff]

theorem testBit_ext_mod_two_pow_iff {q q' m : ℕ} : q % 2^m = q' % 2^m ↔
  (∀ i < m, q.testBit i = q'.testBit i) := by
  simp_rw [testBit_ext_iff, testBit_mod_two_pow, Bool.decide_and_eq_decide_and]

theorem testBit_one_succ {k : ℕ} : testBit 1 (k + 1) = false := by
  rw [testBit_succ, div_eq_of_lt one_lt_two, zero_testBit]

theorem testBit_one {k : ℕ} : testBit 1 k = decide (k = 0) := by
  cases k
  · exact testBit_one_zero
  · simp_rw [testBit_one_succ, decide_false_eq_false]

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
  · simp_rw [h, zero_lt_one.not_le]
  · simp_rw [h, le_rfl]

theorem testBit_false_iff_mod_two_pow_succ_lt_two_pow {i k : ℕ} :
    testBit k i = false ↔ k % 2^(i + 1) < 2^i := by
  rw [lt_iff_not_le, ← testBit_true_iff_two_pow_le_mod_two_pow_succ, Bool.not_eq_true]

theorem testBit_two_pow' (n : ℕ) (m : ℕ) : (2 ^ n).testBit m = decide (n = m) := by
  rcases eq_or_ne n m with rfl | h
  · simp_rw [testBit_two_pow_self, decide_true_eq_true]
  · simp_rw [testBit_two_pow_of_ne h, h, decide_false_eq_false]

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
  · rw [testBit_to_div_mod, decide_eq_false_iff_not, mod_two_ne_one] at hx
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


theorem exists_pow_two_mul_of_testBit (b : ℕ) (hb : ∀ i < k, b.testBit i = false) :
    ∃ n, b = 2^k * n := by
  induction' k with k IH generalizing b
  · exact ⟨b, by rw [pow_zero, one_mul]⟩
  · rcases IH _ (fun i hi => hb i  (hi.trans (Nat.lt_succ_self _))) with ⟨b, rfl⟩
    have h := hb k (Nat.lt_succ_self _)
    simp_rw [testBit_mul_pow_two, le_refl, decide_true_eq_true, Bool.true_and, Nat.sub_self,
      testBit_zero, decide_eq_false_iff_not, mod_two_ne_one, ← Nat.dvd_iff_mod_eq_zero] at h
    rcases h with ⟨b, rfl⟩
    exact ⟨b, by rw [← mul_assoc, pow_succ]⟩

theorem nat_eq_testBit_sum_range {a : ℕ} (ha : a < 2^m) :
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
        false_and, or_false]
      exact fun _ hi => (Nat.testBit_two_pow_add_gt hi _) ▸ rfl

theorem nat_eq_testBit_tsum {a : ℕ} :
    a = ∑' i, (a.testBit i).toNat * 2^i := by
  rcases pow_unbounded_of_one_lt a one_lt_two with ⟨k, ha⟩
  refine (nat_eq_testBit_sum_range ha).trans (tsum_eq_sum ?_).symm
  simp_rw [Finset.mem_range, not_lt, _root_.mul_eq_zero, Bool.toNat_eq_zero, pow_eq_zero_iff',
    false_and, or_false]
  exact fun _ hj => testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_of_le one_lt_two hj))

end TestBit

section Lor

theorem or_eq_add_two_pow_mul_of_lt_right {a b i: ℕ} (ha : a < 2^i) :
    2^i * b ||| a = 2^i * b + a:= (mul_add_lt_is_or ha _).symm

theorem or_eq_add_two_pow_mul_of_lt_left {a b i: ℕ} (ha : a < 2^i) :
    a ||| 2^i * b = a + 2^i * b := by rw [lor_comm, add_comm, or_eq_add_two_pow_mul_of_lt_right ha]

theorem or_eq_add_two_pow_of_lt_left {a i: ℕ} (ha : a < 2^i) :
    a ||| 2^i = a + 2^i := by
  rw [← (Nat.mul_one (2^i)), or_eq_add_two_pow_mul_of_lt_left ha]

theorem or_eq_add_two_pow_of_lt_right {a i: ℕ} (ha : a < 2^i) :
    2^i ||| a = 2^i + a:= by
  rw [lor_comm, add_comm]
  exact or_eq_add_two_pow_of_lt_left ha

end Lor

section BitResiduum

def testRes (q i : ℕ) := ((q >>> (i + 1)) <<< i) ||| (q &&& (2^ i - 1))

def mergeBit (p : ℕ) (i : ℕ) (b : Bool)  :=
  ((p >>> i) <<< (i + 1)) ||| (p &&& (2^ i - 1)) ||| (b.toNat <<< i)

theorem testRes_def : q.testRes i = (q >>> (i + 1)) <<< i ||| q &&& (2^ i - 1) := rfl

theorem mergeBit_def : p.mergeBit i b =
    ((p >>> i) <<< (i + 1)) ||| (p &&& (2^ i - 1)) ||| (b.toNat <<< i) := rfl

-- application theorems

theorem testRes_apply : q.testRes i = 2^i * (q / 2^(i + 1)) + q % 2^i := by
  rw [testRes_def, and_pow_two_is_mod, shiftLeft_eq_mul_pow, shiftRight_eq_div_pow,
    mul_comm, or_eq_add_two_pow_mul_of_lt_right (mod_lt _ (Nat.two_pow_pos _))]

theorem mergeBit_apply : p.mergeBit i b =
    2^(i + 1) * (p / 2^i) + p % 2^i + 2^i * b.toNat := by
  rw [mergeBit_def, and_pow_two_is_mod]
  cases b
  · simp_rw [Bool.toNat_false, Nat.zero_shiftLeft, mul_zero, add_zero,
    Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow, or_zero, mul_comm (p / 2 ^ i),
    pow_succ, mul_assoc]
    rw [or_eq_add_two_pow_mul_of_lt_right (mod_lt _ (Nat.two_pow_pos _))]
  · have h : 2^i < 2^(i + 1) := Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _)
    simp_rw [Bool.toNat_true, mul_one, Nat.shiftLeft_eq_mul_pow, one_mul,
    Nat.shiftRight_eq_div_pow, mul_comm (p / 2 ^ i), lor_assoc, add_assoc,
    or_eq_add_two_pow_mul_of_lt_right
      (Nat.or_lt_two_pow ((mod_lt _ (Nat.two_pow_pos _)).trans h) h),
    or_eq_add_two_pow_of_lt_left (mod_lt _ (Nat.two_pow_pos _))]

theorem mergeBit_apply_true {p : ℕ} : p.mergeBit i true = p.mergeBit i false + 2^i := by
  simp_rw [mergeBit_apply, Bool.toNat_false, Bool.toNat_true, mul_zero, add_zero, mul_one]

theorem mergeBit_apply_false {p : ℕ} : p.mergeBit i false = p.mergeBit i true - 2^i := by
  simp_rw [mergeBit_apply_true, add_tsub_cancel_right]

theorem mergeBit_apply_not {p : ℕ} : p.mergeBit i (!b) =
    (bif b then p.mergeBit i b - 2^i else p.mergeBit i b + 2^i) := by
  cases b
  · rw [Bool.not_false, cond_false, mergeBit_apply_true]
  · rw [Bool.not_true, cond_true, mergeBit_apply_false]

-- testBit_testRes

theorem testBit_testRes_of_lt {i j q : ℕ} (hij : i < j) :
    (q.testRes j).testBit i = q.testBit i := by
  simp_rw [testRes_def, testBit_or, testBit_and, testBit_shiftLeft, testBit_two_pow_sub_one,
  hij.not_le, hij, decide_false_eq_false, Bool.false_and, Bool.false_or,
  decide_true_eq_true, Bool.and_true]

theorem testBit_testRes_of_ge {i j q : ℕ} (hij : j ≤ i) :
    (q.testRes j).testBit i = q.testBit (i + 1) := by
  simp_rw [testRes_def, testBit_or, testBit_shiftLeft, testBit_shiftRight, add_right_comm,
  add_tsub_cancel_of_le hij, testBit_and, testBit_two_pow_sub_one, hij.not_lt, hij,
  decide_true_eq_true, Bool.true_and, decide_false_eq_false, Bool.and_false, Bool.or_false]

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
  testBit_testRes_of_ge (h.trans (Nat.le_add_right _ _)), Nat.add_right_comm, implies_true]

theorem testRes_mod_two_pow_eq (h : k ≤ i) : q.testRes i % 2^k = q % 2^k := by
  simp_rw [testBit_ext_iff, testBit_mod_two_pow]
  intro j
  rcases lt_or_le j k with hjk | hjk
  · simp_rw [hjk, testBit_testRes_of_lt (hjk.trans_le h)]
  · simp_rw [hjk.not_lt, decide_False, Bool.false_and]

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

-- testBit_mergeBit

@[simp]
theorem testBit_mergeBit_of_eq {p : ℕ} : (p.mergeBit i b).testBit i = b := by
  simp only [mergeBit_def, and_pow_two_is_mod, testBit_or, testBit_shiftLeft, ge_iff_le,
    add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, decide_false_eq_false,
    le_add_iff_nonneg_right, _root_.zero_le, tsub_eq_zero_of_le, testBit_zero, Bool.false_and,
    testBit_mod_two_pow, lt_self_iff_false, Bool.or_self, le_refl, decide_true_eq_true,
    Bool.decide_toNat_mod_two_eq_one, Bool.true_and, Bool.false_or]

theorem testBit_mergeBit_of_lt {i j p : ℕ} (hij : i < j) :
    (p.mergeBit j b).testBit i = p.testBit i := by
  simp only [mergeBit_def, and_pow_two_is_mod, testBit_or, testBit_shiftLeft, ge_iff_le,
    (lt_succ_of_lt hij).not_le, decide_false_eq_false, testBit_shiftRight, Bool.false_and,
    testBit_mod_two_pow, hij, decide_true_eq_true, Bool.true_and, Bool.false_or, hij.not_le, Bool.or_false]

theorem testBit_mergeBit_of_gt {i j p : ℕ} (hij : j < i) :
    (p.mergeBit j b).testBit i = p.testBit (i - 1) := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
  simp_rw [mergeBit_def, and_pow_two_is_mod, testBit_or, testBit_shiftLeft, testBit_shiftRight,
    testBit_mod_two_pow, ← Nat.add_sub_assoc (succ_le_of_lt hij), succ_eq_add_one,
    Nat.add_sub_add_left, succ_le_of_lt hij, add_comm j, Nat.add_right_comm _ j,
    Nat.add_sub_cancel, testBit_toNat_succ, (Nat.le_add_left j _).not_lt, decide_true_eq_true,
    Bool.true_and, decide_false_eq_false, Bool.false_and, Bool.and_false, Bool.or_false]

theorem testBit_mergeBit_of_ne {i j p : ℕ} (hij : i ≠ j) : (p.mergeBit j b).testBit i =
    p.testBit (i - (decide (j < i)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [testBit_mergeBit_of_lt hij, Bool.toNat_neg (hij.not_lt), tsub_zero] ;
  · simp only [testBit_mergeBit_of_gt hij, Bool.toNat_pos hij]

theorem testBit_mergeBit {i j p : ℕ} : (p.mergeBit j b).testBit i =
    bif (i = j) then b else p.testBit (i - (decide (j < i)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testBit_mergeBit_of_eq, decide_true_eq_true, cond_true]
  · simp_rw [hij, testBit_mergeBit_of_ne hij, decide_false_eq_false, cond_false]

theorem testBit_mergeBit_succ_of_le {i j p : ℕ} (hij : i ≤ j) :
    (p.mergeBit (j + 1) b).testBit i = p.testBit i := by
  rw [testBit_mergeBit_of_lt (Nat.lt_succ_of_le hij)]

theorem testBit_succ_mergeBit_of_ge {i j p : ℕ} (hij : j ≤ i) :
    (p.mergeBit j b).testBit (i + 1) = p.testBit i := by
  rw [testBit_mergeBit_of_gt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

-- Remaining of_eq theorems

@[simp]
theorem mergeBit_testBit_testRes_of_eq {q : ℕ} : (q.testRes i).mergeBit i (q.testBit i) = q := by
  simp only [testBit_ext_iff]
  intro k
  rcases lt_trichotomy i k with hik | rfl | hik
  · rw [testBit_mergeBit_of_gt hik, testBit_testRes_of_ge (Nat.le_sub_one_of_lt hik),
    Nat.sub_add_cancel (one_le_of_lt hik)]
  · rw [testBit_mergeBit_of_eq]
  · rw [testBit_mergeBit_of_lt hik, testBit_testRes_of_lt hik]

@[simp]
theorem testRes_mergeBit_of_eq {p : ℕ} : (p.mergeBit i b).testRes i = p := by
  simp only [testBit_ext_iff, testBit_testRes, testBit_mergeBit]
  intro k
  rcases le_or_lt i k with hik | hik
  · simp only [hik, decide_true_eq_true, Bool.toNat_true, (lt_succ_of_le hik).ne',
    decide_false_eq_false, lt_succ_of_le hik, add_tsub_cancel_right, cond_false]
  · simp only [gt_iff_lt, hik, not_le_of_lt, decide_false_eq_false, Bool.toNat_false,
    add_zero, ne_of_lt, not_lt_of_lt, tsub_zero, cond_false]

theorem mergeBit_eq_iff : p.mergeBit i b = q ↔ (testBit q i = b) ∧ (q.testRes i = p) :=
  ⟨fun H => H ▸ ⟨testBit_mergeBit_of_eq, testRes_mergeBit_of_eq⟩,
    fun ⟨rfl, rfl⟩ => mergeBit_testBit_testRes_of_eq⟩

theorem eq_mergeBit_iff : q = p.mergeBit i b ↔ (testBit q i = b) ∧ (q.testRes i = p) := by
  rw [← mergeBit_eq_iff, eq_comm]

-- testRes_mergeBit

theorem testRes_mergeBit_of_gt {p : ℕ} (hij : j < i) :
    (p.mergeBit j b).testRes i = (p.testRes (i - 1)).mergeBit j b := by
  simp only [hij, decide_true_eq_true, Bool.toNat_true, testBit_ext_iff, testBit_testRes, testBit_mergeBit,
    tsub_le_iff_right]
  intro k
  rcases lt_trichotomy j (k + (decide (i ≤ k)).toNat) with hjk | rfl | hjk
  · have H : j < k := (le_or_lt i k).by_cases (lt_of_le_of_lt' · hij)
      (fun h => hjk.trans_eq (by simp_rw [h.not_le, decide_false_eq_false, Bool.toNat_false, add_zero]))
    simp only [hjk.ne', decide_false_eq_false, hjk, decide_true_eq_true, Bool.toNat_true,
      Nat.sub_add_comm (one_le_of_lt H), cond_false, H.ne', H,
      Nat.sub_one_add_one_eq_of_pos (zero_lt_of_lt H)]
  · simp only [decide_true_eq_true, lt_self_iff_false, decide_false_eq_false, Bool.toNat_false, tsub_zero, cond_true,
      self_eq_add_right, Bool.toNat_eq_zero, decide_eq_false_iff_not, not_le,
      (le_self_add).trans_lt hij, add_lt_iff_neg_left, not_lt_zero']
  · have H : k < j := le_self_add.trans_lt hjk
    simp only [gt_iff_lt, H.trans hij, not_le_of_lt, decide_false_eq_false, Bool.toNat_false, add_zero, H,
      not_lt_of_lt, tsub_zero, (succ_lt_of_lt_of_lt H hij)]

theorem testRes_mergeBit_of_lt {p : ℕ} (hij : i < j) :
    (p.mergeBit j b).testRes i = (p.testRes i).mergeBit (j - 1) b := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨j, rfl⟩
  simp only [testBit_ext_iff, testBit_testRes, testBit_mergeBit, add_tsub_cancel_right]
  intro k
  rcases le_or_lt i k with hik | hik
  · simp only [hik, decide_true_eq_true, Bool.toNat_true, add_left_inj, add_lt_add_iff_right]
    rcases lt_trichotomy (i + j) k with hjk | rfl | hjk
    · simp only [hjk.ne', decide_false_eq_false, hjk, decide_true_eq_true, Bool.toNat_true, add_tsub_cancel_right,
      cond_false, (le_add_right _ _).trans (Nat.le_sub_one_of_lt hjk), decide_true_eq_true,
      Bool.toNat_true, Nat.sub_add_cancel (one_le_of_lt hjk)]
    · simp only [decide_true_eq_true, lt_self_iff_false, decide_false_eq_false, Bool.toNat_false, tsub_zero,
      testBit_succ, cond_true, le_add_iff_nonneg_right, _root_.zero_le, Bool.toNat_true]
    · simp only [hjk.ne, decide_false_eq_false, hjk.not_lt, Bool.toNat_false, tsub_zero, testBit_succ,
      cond_false, hik, decide_true_eq_true, Bool.toNat_true]
  · simp only [hik.not_le, decide_false_eq_false, Bool.toNat_false, add_zero, (hik.trans hij).ne,
      (hik.trans hij).not_lt, tsub_zero, cond_false, hik.trans_le (Nat.le_add_right _ _), ne_of_lt,
      not_lt_of_lt]

theorem testRes_mergeBit_of_ne {p : ℕ} (hij : i ≠ j) : (p.mergeBit j b).testRes i =
    (p.testRes (i - (decide (j < i)).toNat)).mergeBit (j - (decide (i < j)).toNat) b := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [testRes_mergeBit_of_lt hij, hij.not_lt, decide_false_eq_false, Bool.toNat_false, tsub_zero,
    hij, decide_true_eq_true, Bool.toNat_true]
  · simp only [testRes_mergeBit_of_gt hij, hij, decide_true_eq_true, Bool.toNat_true, hij.not_lt,
    decide_false_eq_false, Bool.toNat_false, tsub_zero]

theorem testRes_mergeBit {i j p : ℕ} : (p.mergeBit j b).testRes i = bif i = j then p else
    (p.testRes (i - (decide (j < i)).toNat)).mergeBit (j - (decide (i < j)).toNat) b := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testRes_mergeBit_of_eq, decide_true_eq_true, cond_true]
  · simp_rw [hij, testRes_mergeBit_of_ne hij, decide_false_eq_false, cond_false]

theorem testRes_succ_mergeBit_of_ge {p : ℕ} (hij : j ≤ i) :
    (p.mergeBit j b).testRes (i + 1) = (p.testRes i).mergeBit j b := by
  rw [testRes_mergeBit_of_gt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

theorem testRes_mergeBit_succ_of_le {p : ℕ} (hij : i ≤ j) :
    (p.mergeBit (j + 1) b).testRes i = (p.testRes i).mergeBit j b := by
  rw [testRes_mergeBit_of_lt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

-- mergeBit_testRes

theorem mergeBit_testRes_of_le {q : ℕ} (hij : i ≤ j) : (q.testRes j).mergeBit i b =
    (q.mergeBit i b).testRes (j + 1) := (testRes_succ_mergeBit_of_ge hij).symm

theorem mergeBit_testRes_of_ge {q : ℕ} (hij : j ≤ i) :
    (q.testRes j).mergeBit i b = (q.mergeBit (i + 1) b).testRes j :=
  (testRes_mergeBit_succ_of_le hij).symm

theorem mergeBit_testRes_of_ne {q : ℕ} (hij : i ≠ j) :
    (q.testRes j).mergeBit i b =
    (q.mergeBit (i + (decide (j < i)).toNat) b).testRes (j + (decide (i < j)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [mergeBit_testRes_of_le hij.le, hij, not_lt_of_lt, decide_false_eq_false, Bool.toNat_false,
    add_zero, decide_true_eq_true, Bool.toNat_true]
  · simp only [mergeBit_testRes_of_ge hij.le, hij, decide_true_eq_true, Bool.toNat_true, not_lt_of_lt,
    decide_false_eq_false, Bool.toNat_false, add_zero]

theorem mergeBit_not_testBit_testRes_of_eq {q : ℕ} : (q.testRes i).mergeBit i (!q.testBit i) =
  (bif q.testBit i then q - 2^i else q + 2^i) := by
  rw [mergeBit_apply_not, mergeBit_testBit_testRes_of_eq]

theorem mergeBit_testRes_of_eq {i q : ℕ} : (q.testRes i).mergeBit i b =
    bif (q.testBit i).xor !b then q else bif q.testBit i then q - 2^i else q + 2^i := by
  rcases Bool.eq_or_eq_not b (q.testBit i) with rfl | rfl
  · simp_rw [mergeBit_testBit_testRes_of_eq, Bool.bne_not_self, cond_true]
  · simp_rw [Bool.not_not, bne_self_eq_false, mergeBit_not_testBit_testRes_of_eq, cond_false]

theorem mergeBit_testRes {i j : ℕ} : (q.testRes j).mergeBit i b =
    bif i = j then bif (q.testBit i).xor !b then q else (bif q.testBit i then q - 2^i else q + 2^i)
    else (q.mergeBit (i + (decide (j < i)).toNat) b).testRes (j + (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp only [decide_true_eq_true, lt_self_iff_false, decide_false_eq_false, Bool.toNat_false, add_zero,
    testRes_mergeBit_of_eq, cond_true, mergeBit_testRes_of_eq]
  · simp_rw [hij, mergeBit_testRes_of_ne hij, decide_false_eq_false, cond_false]

theorem mergeBit_testRes_pred_of_lt {q : ℕ} (hij : i < j) : (q.testRes (j - 1)).mergeBit i b =
    (q.mergeBit i b).testRes j := (testRes_mergeBit_of_gt hij).symm

theorem mergeBit_pred_testRes_of_gt {q : ℕ} (hij : j < i) : (q.testRes j).mergeBit (i - 1) b =
    (q.mergeBit i b).testRes j := (testRes_mergeBit_of_lt hij).symm

-- testRes_testRes

theorem testRes_testRes_of_lt {i j q : ℕ} (hij : i < j) : (q.testRes j).testRes i =
  (q.testRes i).testRes (j - 1) := by
  simp_rw [testBit_ext_iff, testBit_testRes, tsub_le_iff_right]
  intro k
  rcases lt_or_le k i with (hik | hik)
  · have hkj : k + 1 < j := succ_lt_of_lt_of_lt hik hij
    have hkj' : k < j := lt_of_succ_lt hkj
    simp only [hik.not_le, hkj'.not_le, hkj.not_le, decide_false_eq_false, Bool.toNat_false, add_zero]
  · have h : i ≤ k + (decide (j ≤ k + 1)).toNat := le_add_of_le_left hik
    simp_rw [hik, h, decide_true_eq_true, Bool.toNat_true, add_assoc, add_comm]

theorem testRes_testRes_of_ge {i j q : ℕ} (hij : j ≤ i) :
    (q.testRes j).testRes i = (q.testRes (i + 1)).testRes j := by
  simp_rw [testBit_ext_iff, testBit_testRes]
  intro k
  rcases le_or_lt i k with (hik | hik)
  · have hjk : j ≤ k := hij.trans hik
    have hjk' : j ≤ k + 1 := hjk.trans (le_succ _)
    simp only [hik,  hjk', hjk, decide_true_eq_true, Bool.toNat_true, add_le_add_iff_right]
  · have h : k + (decide (j ≤ k)).toNat < i + 1 := add_lt_add_of_lt_of_le hik (Bool.toNat_le _)
    simp only [hik.not_le, h.not_le, decide_false_eq_false, Bool.toNat_false, add_zero]

theorem testRes_testRes {i j q : ℕ} : (q.testRes j).testRes i =
    (q.testRes (i + (decide (j ≤ i)).toNat)).testRes (j - (!decide (j ≤ i)).toNat) := by
  rcases lt_or_le i j with hij | hij
  · simp_rw [testRes_testRes_of_lt hij, hij.not_le, decide_false_eq_false, Bool.toNat_false,
    add_zero, Bool.not_false, Bool.toNat_true]
  · simp_rw [testRes_testRes_of_ge hij, hij, decide_true_eq_true, Bool.toNat_true,
    Bool.not_true, Bool.toNat_false, tsub_zero]

theorem testRes_testRes_succ_of_le {i j q : ℕ} (hij : i ≤ j) : (q.testRes (j + 1)).testRes i =
    (q.testRes i).testRes j := by
  rw [testRes_testRes_of_lt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

theorem testRes_pred_testRes_of_gt {i j q : ℕ} (hij : j < i) : (q.testRes j).testRes (i - 1) =
    (q.testRes i).testRes j := by
  rw [testRes_testRes_of_ge (Nat.le_sub_one_of_lt hij), Nat.sub_add_cancel (one_le_of_lt hij)]


-- mergeBit_mergeBit

theorem mergeBit_mergeBit_of_le {i j p : ℕ} {b b' : Bool} (hij : i ≤ j) :
    (p.mergeBit j b').mergeBit i b = (p.mergeBit i b).mergeBit (j + 1) b' := by
  simp_rw [mergeBit_eq_iff (i := i), testRes_mergeBit_succ_of_le hij,
  testBit_mergeBit_succ_of_le hij, testBit_mergeBit_of_eq, testRes_mergeBit_of_eq, true_and]

theorem mergeBit_mergeBit_of_gt {i j p : ℕ} {b b' : Bool} (hij : j < i) :
    (p.mergeBit j b').mergeBit i b = (p.mergeBit (i - 1) b).mergeBit j b' := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
  rw [Nat.add_sub_cancel, ← mergeBit_mergeBit_of_le (Nat.le_of_lt_succ hij)]

theorem mergeBit_mergeBit_of_eq {i p : ℕ} {b b' : Bool} :
    (p.mergeBit i b').mergeBit i b = (p.mergeBit i b).mergeBit (i + 1) b' :=
  mergeBit_mergeBit_of_le le_rfl

theorem mergeBit_mergeBit_of_ne {i j p : ℕ} {b b' : Bool} (hij : i ≠ j) :
    (p.mergeBit j b').mergeBit i b =
    (p.mergeBit (i - (decide (j < i)).toNat) b).mergeBit (j + (decide (i < j)).toNat) b' := by
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [mergeBit_mergeBit_of_le hij.le, hij, hij.not_lt, decide_false_eq_false,
    decide_true_eq_true, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero]
  · simp_rw [mergeBit_mergeBit_of_gt hij, hij, hij.not_lt, decide_false_eq_false,
    decide_true_eq_true, Bool.toNat_false, Bool.toNat_true, add_zero]

theorem mergeBit_mergeBit {i j p : ℕ} {b b' : Bool} : (p.mergeBit j b').mergeBit i b  =
    (p.mergeBit (i - (decide (j < i)).toNat) b).mergeBit (j + (decide (i ≤ j)).toNat) b' := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [mergeBit_mergeBit_of_eq, lt_irrefl, le_rfl, decide_false_eq_false,
    decide_true_eq_true, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero]
  · simp_rw [mergeBit_mergeBit_of_ne hij, hij.le_iff_lt]

theorem mergeBit_succ_mergeBit_of_ge {i j p : ℕ} {b b' : Bool} (h : j ≤ i) :
    (p.mergeBit j b).mergeBit (i + 1) b' = (p.mergeBit i b').mergeBit j b :=
  (mergeBit_mergeBit_of_le h).symm

theorem mergeBit_mergeBit_pred_of_lt {i j p : ℕ} {b b' : Bool} (h : i < j) :
    (p.mergeBit (j - 1) b).mergeBit i b' = (p.mergeBit i b').mergeBit j b :=
  (mergeBit_mergeBit_of_gt h).symm

-- mergeBit equalities and inequalities

theorem mergeBit_div_two_pow_eq (h : i ≤ k) : q.mergeBit i b / 2^(k + 1) = q / 2^k := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow, Nat.add_right_comm _ 1,
  testBit_succ_mergeBit_of_ge ((h.trans (Nat.le_add_right _ _))), implies_true]

theorem mergeBit_mod_two_pow_eq (h : k ≤ i) : q.mergeBit i n % 2^k = q % 2^k := by
  simp_rw [testBit_ext_iff, testBit_mod_two_pow]
  intro j
  rcases lt_or_le j k with hjk | hjk
  · simp_rw [hjk, testBit_mergeBit_of_lt (hjk.trans_le h)]
  · simp_rw [hjk.not_lt, decide_False, Bool.false_and]

theorem mergeBit_modEq_two_pow (h : k ≤ i) : q.mergeBit i b ≡ q [MOD 2^k] :=
  mergeBit_mod_two_pow_eq h

theorem mergeBit_lt_iff_lt_div_two (hin : 2^(i + 1) ∣ n) :
    q.mergeBit i b < n ↔ q < n / 2 := by
  rw [← testRes_lt_div_two_iff_lt hin, testRes_mergeBit_of_eq]

theorem mergeBit_lt_two_mul_iff_lt (hin : 2^i ∣ n) :
    q.mergeBit i b < 2 * n ↔ q < n := by
  rw [← testRes_lt_iff_lt_two_mul hin, testRes_mergeBit_of_eq]

theorem mergeBit_lt_two_pow_mul_iff_lt_two_pow_mul (h : i ≤ k) (n : ℕ) :
    q.mergeBit i b < 2^(k + 1) * n ↔ q < 2^k * n := by
  simp_rw [← testRes_lt_two_pow_mul_iff_lt_two_pow_mul h, testRes_mergeBit_of_eq]

theorem mergeBit_lt_two_pow_iff_lt_two_pow (h : i ≤ k) :
    q.mergeBit i b < 2^(k + 1) ↔ q < 2^k := by
  simp_rw [← testRes_lt_two_pow_iff_lt_two_pow h, testRes_mergeBit_of_eq]

theorem mergeBit_testRes_lt_iff_lt (hin : 2^(i + 1) ∣ n) :
    (q.testRes i).mergeBit i b < n ↔ q < n := by
  rw [mergeBit_lt_iff_lt_div_two hin, testRes_lt_div_two_iff_lt hin]

-- zero/succ

theorem testRes_zero : q.testRes 0 = q / 2 := by
  simp only [testRes_apply, pow_zero, zero_add, pow_one, one_mul, mod_one, add_zero]

theorem mergeBit_zero : p.mergeBit 0 b = 2 * p + b.toNat := by
  simp only [mergeBit_apply, zero_add, pow_one, pow_zero, Nat.div_one, mod_one, add_zero, one_mul]

theorem testRes_succ {q : ℕ} : q.testRes (i + 1) = 2 * (q / 2).testRes i + q % 2 := by
  rw [← mergeBit_testBit_testRes_of_eq (i := 0) (q := q.testRes (i + 1)),
  testBit_testRes_succ_of_le (zero_le _), testRes_testRes_succ_of_le (zero_le _),
  testRes_zero, mergeBit_zero, testBit_zero, Bool.decide_mod_two_eq_one_toNat]

theorem mergeBit_succ {q : ℕ} : q.mergeBit (i + 1) b = 2 * (q / 2).mergeBit i b + q % 2 := by
  rw [← mergeBit_testBit_testRes_of_eq (i := 0) (q := q.mergeBit (i + 1) b),
  testRes_mergeBit_succ_of_le (zero_le _), testBit_mergeBit_succ_of_le (zero_le _),
  testRes_zero, mergeBit_zero, testBit_zero, Bool.decide_mod_two_eq_one_toNat]

theorem zero_testRes : (0 : ℕ).testRes i = 0 := by
  rw [testRes_def, zero_shiftRight, zero_shiftLeft, zero_and, or_zero]

theorem zero_mergeBit : (0 : ℕ).mergeBit i b = b.toNat * 2^i := by
  simp_rw [mergeBit_def, zero_shiftRight, zero_shiftLeft, zero_and, or_zero, zero_or, shiftLeft_eq]

theorem zero_mergeBit_true : (0 : ℕ).mergeBit i true = 2^i := by
  simp_rw [zero_mergeBit, Bool.toNat_true, one_mul]

theorem zero_mergeBit_false : (0 : ℕ).mergeBit i false = 0 := by
  simp_rw [zero_mergeBit, Bool.toNat_false, zero_mul]

theorem two_pow_testRes_of_eq : (2 ^ i).testRes i = 0 :=
  zero_mergeBit_true ▸ testRes_mergeBit_of_eq

theorem two_pow_testRes_of_lt (hij : i < j) : (2 ^ i).testRes j = 2 ^ i := by
  rw [← zero_mergeBit_true, testRes_mergeBit_of_gt hij, zero_testRes]

theorem two_pow_testRes_of_gt (hij : j < i) : (2 ^ i).testRes j = 2 ^ (i - 1) := by
  simp_rw [← zero_mergeBit_true, testRes_mergeBit_of_lt hij, zero_testRes]


-- Equivalence family

@[pp_nodot, simps! apply_fst apply_snd symm_apply]
def testBitRes (i : ℕ) : ℕ ≃ Bool × ℕ where
  toFun n := (n.testBit i, n.testRes i)
  invFun bp := bp.2.mergeBit i bp.1
  left_inv _ := mergeBit_testBit_testRes_of_eq
  right_inv _ := Prod.ext testBit_mergeBit_of_eq testRes_mergeBit_of_eq

end BitResiduum

section FlipBit

def flipBit (q i : ℕ) := q ^^^ 1 <<< i

theorem flipBit_def : ∀ (i q : ℕ), q.flipBit i = q ^^^ 1 <<< i := fun _ _ => rfl

-- testBit_flipBit

variable {p q : ℕ}

@[simp]
theorem testBit_flipBit_of_eq : (q.flipBit i).testBit i = !(q.testBit i) := by
  simp_rw [flipBit_def, testBit_xor, testBit_shiftLeft, le_rfl,
    decide_true_eq_true, Bool.true_and, Nat.sub_self, testBit_one_zero, Bool.xor_true]

theorem testBit_flipBit_of_ne {i j : ℕ} (hij : i ≠ j) :
    (q.flipBit j).testBit i = q.testBit i := by
  simp_rw [flipBit_def, testBit_xor, testBit_shiftLeft]
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [hij.not_le, decide_false_eq_false, Bool.false_and, Bool.xor_false]
  · simp_rw [testBit_one, Nat.sub_eq_zero_iff_le, hij.not_le, decide_false_eq_false,
    Bool.and_false, Bool.xor_false]

theorem testBit_flipBit : (q.flipBit j).testBit i = (q.testBit i).xor (i = j) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testBit_flipBit_of_eq, decide_true_eq_true, Bool.xor_true]
  · simp_rw [testBit_flipBit_of_ne hij, hij, decide_false_eq_false, Bool.xor_false]

-- representations of flipBit

theorem flipBit_eq_mergeBit {i : ℕ} :
    q.flipBit i = (q.testRes i).mergeBit i (!(testBit q i))  := by
  simp_rw [testBit_ext_iff]
  intro j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [testBit_flipBit_of_ne hij.ne', testBit_mergeBit_of_gt hij, testBit_pred_testRes_of_gt hij]
  · rw [testBit_flipBit_of_eq, testBit_mergeBit_of_eq]
  · rw [testBit_flipBit_of_ne hij.ne, testBit_mergeBit_of_lt hij, testBit_testRes_of_lt hij]

theorem flipBit_eq_cond {i : ℕ} : q.flipBit i = bif testBit q i then q - 2^i else q + 2^i := by
  rw [flipBit_eq_mergeBit, mergeBit_not_testBit_testRes_of_eq]

-- flipBit equalities and inequalities

theorem flipBit_div_eq {i : ℕ} (h : i < k) : q.flipBit i / 2^k = q / 2^k := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow,
  testBit_flipBit_of_ne (h.trans_le (Nat.le_add_right _ _)).ne', implies_true]

theorem flipBit_mod_two_pow_eq {i : ℕ} (h : k ≤ i) : q.flipBit i % 2^k = q % 2^k := by
  simp_rw [testBit_ext_iff, testBit_mod_two_pow]
  intro j
  rcases eq_or_ne j i with rfl | hji
  · simp_rw [h.not_lt, decide_False, Bool.false_and]
  · simp_rw [testBit_flipBit_of_ne hji]

theorem flipBit_modEq_two_pow (h : k ≤ i) : q.flipBit i ≡ q [MOD 2^k] := flipBit_mod_two_pow_eq h

@[simp]
theorem flipBit_lt_iff_lt (hin : 2^(i + 1) ∣ n) : q.flipBit i < n ↔ q < n := by
  rcases hin with ⟨k, rfl⟩
  simp_rw [mul_comm _ k, ← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),
     flipBit_div_eq i.lt_succ_self]

theorem flipBit_lt_two_pow_mul_iff_lt_two_pow_mul (h : i < k) (n : ℕ) :
    q.flipBit i < 2^k * n ↔ q < 2^k * n :=
  flipBit_lt_iff_lt (dvd_mul_of_dvd_left (pow_dvd_pow _ h) _)

theorem flipBit_lt_two_pow_iff_lt_two_pow {m : ℕ} (h : i < m) :
    q.flipBit i < 2^m ↔ q < 2^m := by
  have H := flipBit_lt_two_pow_mul_iff_lt_two_pow_mul h 1 (q := q)
  simp_rw [mul_one] at H
  exact H

-- flipBit_testRes

theorem flipBit_testRes_of_lt (hij : i < j):
    (q.testRes j).flipBit i = (q.flipBit i).testRes j := by
  simp_rw [flipBit_eq_mergeBit, testRes_testRes_of_lt hij, testBit_testRes_of_lt hij,
  testRes_mergeBit_of_gt hij]

theorem flipBit_testRes_of_ge (hij : j ≤ i):
    (q.testRes j).flipBit i = (q.flipBit (i + 1)).testRes j := by
  simp_rw [flipBit_eq_mergeBit, testRes_testRes_of_ge hij, testBit_testRes_of_ge hij,
  mergeBit_testRes_of_ge hij]

theorem flipBit_testRes :
    (q.testRes j).flipBit i = (q.flipBit (i + (decide (j ≤ i)).toNat)).testRes j := by
  rcases lt_or_le i j with hij | hij
  · simp_rw [flipBit_testRes_of_lt hij, hij.not_le, decide_false_eq_false, Bool.toNat_false, add_zero]
  · simp_rw [flipBit_testRes_of_ge hij, hij, decide_true_eq_true, Bool.toNat_true]

-- testRes_flipBit

theorem testRes_flipBit_of_gt (hij : j < i):
    (q.flipBit j).testRes i = (q.testRes i).flipBit j := (flipBit_testRes_of_lt hij).symm

theorem testRes_flipBit_of_lt (hij : i < j):
    (q.flipBit j).testRes i = (q.testRes i).flipBit (j - 1) := by
  rw [flipBit_testRes_of_ge (Nat.le_sub_one_of_lt hij), Nat.sub_add_cancel (one_le_of_lt hij)]

theorem testRes_flipBit_of_ne (hij : i ≠ j) :
    (q.flipBit j).testRes i = (q.testRes i).flipBit (j - (decide (i < j)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [testRes_flipBit_of_lt hij, hij, not_lt_of_lt, decide_false_eq_false, Bool.toNat_false,
    add_zero, decide_true_eq_true, Bool.toNat_true]
  · simp only [testRes_flipBit_of_gt hij, hij, decide_true_eq_true, Bool.toNat_true, not_lt_of_lt,
    decide_false_eq_false, Bool.toNat_false, Nat.sub_zero]

@[simp]
theorem testRes_flipBit_of_eq : (q.flipBit i).testRes i = q.testRes i := by
  rw [flipBit_eq_mergeBit, testRes_mergeBit_of_eq]

theorem testRes_flipBit : (q.flipBit j).testRes i = bif i = j then q.testRes i else
    (q.testRes i).flipBit (j - (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testRes_flipBit_of_eq, decide_true_eq_true, cond_true]
  · simp_rw [testRes_flipBit_of_ne hij, hij, decide_false_eq_false, cond_false]

-- flipBit_mergeBit

theorem flipBit_mergeBit_of_eq : (p.mergeBit i b).flipBit i = p.mergeBit i (!b) := by
  rw [flipBit_eq_mergeBit, testBit_mergeBit_of_eq, testRes_mergeBit_of_eq]

theorem flipBit_mergeBit_of_lt (hij : i < j) :
    (p.mergeBit j b).flipBit i = (p.flipBit i).mergeBit j b := by
  rw [flipBit_eq_mergeBit, flipBit_eq_mergeBit, testBit_mergeBit_of_lt hij,
  testRes_mergeBit_of_lt hij, mergeBit_mergeBit_pred_of_lt hij]

theorem flipBit_mergeBit_of_gt (hij : j < i) :
    (p.mergeBit j b).flipBit i = (p.flipBit (i - 1)).mergeBit j b := by
  rw [flipBit_eq_mergeBit, flipBit_eq_mergeBit, testBit_mergeBit_of_gt hij,
  testRes_mergeBit_of_gt hij, mergeBit_mergeBit_pred_of_lt hij]

theorem flipBit_mergeBit_of_ne (hij : i ≠ j) :
    (p.mergeBit j b).flipBit i = (p.flipBit (i - (decide (j < i)).toNat)).mergeBit j b := by
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [flipBit_mergeBit_of_lt hij, hij.not_lt, decide_false_eq_false, Bool.toNat_false,
    Nat.sub_zero]
  · simp_rw [flipBit_mergeBit_of_gt hij, hij, decide_true_eq_true, Bool.toNat_true]

theorem flipBit_mergeBitRes :
    (p.mergeBit j b).flipBit i = if i = j then p.mergeBit i (!b) else
    (p.flipBit (i - (decide (j < i)).toNat)).mergeBit j b := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [flipBit_mergeBit_of_eq, if_true]
  · simp_rw [flipBit_mergeBit_of_ne hij, hij, if_false]

-- properties of flipBit

theorem testRes_eq_iff {r : ℕ} :
    q.testRes i = r.testRes i ↔ q = r ∨ q = r.flipBit i := by
  refine ⟨fun h => ?_, ?_⟩
  · simp_rw [testBit_ext_iff] at h ⊢
    have H : ∀ j : ℕ, j ≠ i → q.testBit j = r.testBit j := fun j hji => by
      rcases hji.lt_or_lt with hji | hji
      · have hj := h j
        simp_rw [testBit_testRes_of_lt hji] at hj
        assumption
      · have hj := h (j - 1)
        simp_rw [testBit_pred_testRes_of_gt hji] at hj
        assumption
    refine ((q.testBit i).eq_or_eq_not (r.testBit i)).imp (fun hqr j => ?_) (fun hqr j => ?_) <;>
    rcases eq_or_ne j i with rfl | hji
    · assumption
    · exact H _ hji
    · rw [testBit_flipBit_of_eq, hqr]
    · rw [testBit_flipBit_of_ne hji, H _ hji]
  · rintro (rfl | rfl)
    · rfl
    · rw [testRes_flipBit_of_eq]

@[simp]
theorem flipBit_flipBit_of_eq : (q.flipBit i).flipBit i  = q := by
  simp_rw [flipBit_def, Nat.xor_cancel_right]

@[simp]
theorem flipBit_ne_self : q.flipBit i ≠ q := by
  simp_rw [ne_eq, testBit_ext_iff, not_forall]
  exact ⟨i, by simp_rw [testBit_flipBit_of_eq, Bool.not_eq_self, not_false_eq_true]⟩

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
  rw [← flipBit_div_eq hik, ← flipBit_div_eq (q := r) hik]
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

@[pp_nodot, simps!]
def flipBitPerm (i : ℕ) : Equiv.Perm ℕ :=
  ⟨(flipBit · i), (flipBit · i), xor_cancel_right _, xor_cancel_right _⟩

@[simp]
theorem flipBitPerm_inv_apply : ∀ (x i : ℕ), (flipBitPerm i)⁻¹ x = x.flipBit i := fun _ _ => rfl

theorem flipBitPerm_eq_permCongr (i : ℕ) :
    flipBitPerm i = (testBitRes i).symm.permCongr (boolInversion.prodCongr (Equiv.refl _)) := by
  simp_rw [Equiv.ext_iff, flipBitPerm_apply,
    flipBit_eq_mergeBit, Equiv.permCongr_apply, Equiv.symm_symm, testBitRes_symm_apply,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, boolInversion_apply,
    testBitRes_apply_snd, testBitRes_apply_fst, implies_true]

end FlipBit

section CondFlipBit

def condFlipBit (q : ℕ) (i : ℕ) (c : Array Bool) : ℕ :=
  q ^^^ ((c[q.testRes i]?.getD false).toNat <<< i)

variable {p q : ℕ}

theorem condFlipBit_apply_of_testRes_lt (h : q.testRes i < c.size) :
    q.condFlipBit i c = bif c[q.testRes i] then q.flipBit i else q := by
  unfold condFlipBit
  rw [c.getElem?_lt h, Option.getD_some]
  rcases c[q.testRes i]
  · rw [cond_false, Bool.toNat_false, zero_shiftLeft, xor_zero]
  · rw [cond_true, Bool.toNat_true, flipBit_def]

theorem condFlipBit_apply_of_le_testRes {c : Array Bool} (h : c.size ≤ q.testRes i) :
    q.condFlipBit i c = q := by
  unfold condFlipBit
  rw [c.getElem?_ge h, Option.getD_none, Bool.toNat_false, zero_shiftLeft, xor_zero]

theorem condFlipBit_apply :
    q.condFlipBit i c = bif c[q.testRes i]?.getD false then q.flipBit i else q := by
  rcases lt_or_le (q.testRes i) c.size with h | h
  · rw [condFlipBit_apply_of_testRes_lt h, c.getElem?_lt h, Option.getD_some]
  · rw [condFlipBit_apply_of_le_testRes h, c.getElem?_ge h, Option.getD_none, Bool.cond_false]

theorem testRes_condFlipBit_of_eq : (q.condFlipBit i c).testRes i = q.testRes i := by
  rw [condFlipBit_apply, Bool.apply_cond (testRes · i), testRes_flipBit_of_eq, Bool.cond_self]

theorem testBit_condFlipBit_of_ne (hij : i ≠ j) :
    (q.condFlipBit j c).testBit i = q.testBit i := by
  rw [condFlipBit_apply, Bool.apply_cond (testBit · i), testBit_flipBit_of_ne hij, Bool.cond_self]

theorem testBit_condFlipBit_of_eq :
    (q.condFlipBit i c).testBit i = (c[q.testRes i]?.getD false).xor (q.testBit i) := by
  rw [condFlipBit_apply, Bool.apply_cond (testBit · i), testBit_flipBit_of_eq]
  rcases (c[q.testRes i]?.getD false)
  · rw [cond_false, Bool.xor, Bool.false_xor]
  · rw [cond_true, Bool.xor, Bool.true_xor]

theorem testBit_condFlipBit_of_le_testRes (h : c.size ≤ q.testRes i) :
    (q.condFlipBit i c).testBit j = q.testBit j := by
  rw [condFlipBit_apply_of_le_testRes h]

theorem testBit_condFlipBit_of_testRes_lt_of_eq (h : q.testRes i < c.size) :
  (q.condFlipBit i c).testBit i = (c[q.testRes i]).xor (q.testBit i) := by
  rw [testBit_condFlipBit_of_eq, c.getElem?_lt h, Option.getD_some]

theorem condFlipBit_eq_mergeBit : q.condFlipBit i c =
    (q.testRes i).mergeBit i ((c[q.testRes i]?.getD false).xor (q.testBit i)) := by
  simp_rw [eq_mergeBit_iff, testRes_condFlipBit_of_eq, testBit_condFlipBit_of_eq, true_and]

theorem condFlipBit_eq_mergeBit_of_testRes_lt (h : q.testRes i < c.size) :
    q.condFlipBit i c = (q.testRes i).mergeBit i (c[q.testRes i].xor (q.testBit i)) := by
  simp_rw [eq_mergeBit_iff, testRes_condFlipBit_of_eq, testBit_condFlipBit_of_testRes_lt_of_eq h,
    true_and]

theorem condFlipBit_apply_comm :
(q.condFlipBit i d).condFlipBit i c = (q.condFlipBit i c).condFlipBit i d := by
simp_rw [condFlipBit_eq_mergeBit, testRes_mergeBit_of_eq,
  testBit_mergeBit_of_eq, Bool.xor_left_comm]

theorem condFlipBit_mergeBit :
    (p.mergeBit i b).condFlipBit i c = p.mergeBit i ((c[p]?.getD false).xor b) := by
  rw [condFlipBit_eq_mergeBit, testRes_mergeBit_of_eq, testBit_mergeBit_of_eq]

theorem condFlipBit_eq_dite : q.condFlipBit i c = if h : q.testRes i < c.size then
    bif c[q.testRes i] then q.flipBit i else q else q := by
  symm
  rw [dite_eq_iff']
  exact ⟨fun h => (condFlipBit_apply_of_testRes_lt h).symm,
  fun h => (condFlipBit_apply_of_le_testRes (le_of_not_lt h)).symm⟩

@[simp]
theorem condFlipBit_condFlipBit_of_eq : (q.condFlipBit i c).condFlipBit i c = q := by
  simp_rw [condFlipBit_eq_mergeBit, testRes_mergeBit_of_eq, testBit_mergeBit_of_eq,
    Bool.xor, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor, mergeBit_testBit_testRes_of_eq]

theorem condFlipBit_of_all_of_lt_c.size (hq : q.testRes i < c.size)
    (hc : ∀ (i : ℕ) (h : i < c.size), c[i] = true) :
    q.condFlipBit i c = q.flipBit i := by
  simp_rw [condFlipBit_eq_dite, hq, dite_true, hc _ hq, cond_true]

theorem condFlipBit_of_mkArray_true :
    q.condFlipBit i (mkArray n true) = if q.testRes i < n then q.flipBit i else q := by
  simp_rw [condFlipBit_eq_dite, Array.getElem_mkArray, cond_true, Array.size_mkArray, dite_eq_ite]

theorem condFlipBit_of_all_not (hc : c.all (fun x => !x)) :
    q.condFlipBit i c = q := by
  simp_rw [Array.all_eq_true, Fin.forall_iff, Fin.getElem_fin, Bool.not_eq_true'] at hc
  simp_rw [condFlipBit_eq_dite]
  split_ifs with hq
  · simp_rw [hc _ hq, cond_false]
  · rfl

theorem condFlipBit_of_mkArray_false :
    q.condFlipBit i (mkArray n false) = q := by
  simp_rw [condFlipBit_eq_dite, Array.getElem_mkArray, cond_false, dite_eq_ite, ite_self]

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
def condFlipBitPerm (i : ℕ) (c : Array Bool) : Equiv.Perm ℕ where
  toFun := (condFlipBit · i c)
  invFun := (condFlipBit · i c)
  left_inv _ := condFlipBit_condFlipBit_of_eq
  right_inv _ := condFlipBit_condFlipBit_of_eq

end CondFlipBit

end Nat

namespace Array

section FlipBit

def flipBit_indices (as : Array α) (i : ℕ) : Array α :=
  (Array.range (as.size / 2)).foldr
  (fun k as => as.swap! (k.mergeBit i false) (k.mergeBit i true)) as

@[simp]
theorem size_flipBit_indices (a : Array α) {i : ℕ} :
    (flipBit_indices a i).size = a.size := by
  refine Array.foldr_induction (fun _ (a' : Array α) => a'.size = a.size) rfl (fun _ _ h => ?_)
  simp_rw [size_swap!, h]

theorem getElem_flipBit_indices (a : Array α) (i : ℕ) (ha : 2^(i + 1) ∣ a.size)
    (k : ℕ) (hk : k < (flipBit_indices a i).size) :
    (flipBit_indices a i)[k] = a[k.flipBit i]'((Nat.flipBit_lt_iff_lt ha).mpr
      (hk.trans_eq a.size_flipBit_indices)) := by
  revert k
  suffices h : ∀ (_ : (a.flipBit_indices i).size = a.size) (k : ℕ)
    (hk : k < (a.flipBit_indices i).size), (a.flipBit_indices i)[k] =
    if 0 ≤ k.testRes i then a[k.flipBit i]'((Nat.flipBit_lt_iff_lt ha).mpr
    (hk.trans_eq a.size_flipBit_indices)) else a[k]'(hk.trans_eq a.size_flipBit_indices)
  · simp_rw [zero_le, ite_true] at h
    exact h a.size_flipBit_indices
  · refine Array.foldr_induction (fun n (a' : Array α) =>
    ∀ ha' k (hk : k < a'.size), a'[k] =
    if n ≤ k.testRes i then a[k.flipBit i]'((Nat.flipBit_lt_iff_lt ha).mpr
    (hk.trans_eq ha')) else a[k]'(hk.trans_eq ha')) (fun _ _ hk => ?_) ?_
    · simp_rw [size_range, ← not_lt, Nat.testRes_lt_div_two_iff_lt ha, hk, not_true, if_false]
    · simp_rw [Fin.getElem_fin, size_swap!, Nat.succ_le_iff, getElem_range,
        Fin.forall_iff, size_range]
      intro t ht a' h ha' k hk
      specialize h ha'
      rcases eq_or_ne (k.testRes i) t with htk | htk
      · specialize h (k.flipBit i)
          ((Nat.flipBit_lt_iff_lt (ha.trans (dvd_of_eq ha'.symm))).mpr hk)
        simp_rw [Nat.testRes_flipBit_of_eq, htk, lt_irrefl, if_false] at h
        simp_rw [htk, le_rfl, if_true, ← h, ← htk, Nat.flipBit_eq_mergeBit]
        rcases eq_or_ne (k.testBit i) false with hb | hb
        · simp_rw [hb, Bool.not_false, ← hb, Nat.mergeBit_testBit_testRes_of_eq]
          exact Array.getElem_swap!_left _ _
        · simp_rw [hb, Bool.not_true, ← eq_true_of_ne_false hb, Nat.mergeBit_testBit_testRes_of_eq]
          exact Array.getElem_swap!_right _ _
      · simp_rw [getElem_swap!_of_ne_ne
          (ne_of_apply_ne (Nat.testRes · i) <| htk.trans_eq Nat.testRes_mergeBit_of_eq.symm)
          (ne_of_apply_ne (Nat.testRes · i) <| htk.trans_eq Nat.testRes_mergeBit_of_eq.symm), h,
          htk.symm.le_iff_lt]

def flipBit_vals (as : Array ℕ) (i : ℕ) : Array ℕ := as.map (Nat.flipBit · i)

@[simp]
theorem size_flipBit_vals (as : Array ℕ) (i : ℕ) : (flipBit_vals as i).size = as.size :=
  size_map _ _

theorem getElem_flipBit_vals (as : Array ℕ) (i : ℕ) (k : ℕ)
    (hk : k < (flipBit_vals as i).size) :
    (flipBit_vals as i)[k] = (as[k]'(hk.trans_eq (by simp))).flipBit i := getElem_map _ _ _ _

end FlipBit

section CondFlipBit

def condFlipBit_indices (as : Array α) (i : ℕ) (c : Array Bool) : Array α :=
  c.zipWithIndex.foldr (fun bp as => as.swap! (bp.2.mergeBit i false) (bp.2.mergeBit i bp.1)) as

@[simp]
theorem size_condFlipBit_indices (a : Array α) {i : ℕ} {c : Array Bool} :
    (condFlipBit_indices a i c).size = a.size := by
  refine Array.foldr_induction (fun _ (a' : Array α) => a'.size = a.size) rfl (fun _ _ h => ?_)
  simp_rw [size_swap!, h]

theorem getElem_condFlipBit_indices (a : Array α) (i : ℕ) (ha : 2^(i + 1) ∣ a.size)
    (c : Array Bool) (k : ℕ) (hk : k < (condFlipBit_indices a i c).size) :
    (condFlipBit_indices a i c)[k] = a[k.condFlipBit i c]'((Nat.condFlipBit_lt_iff_lt ha).mpr
      (hk.trans_eq a.size_condFlipBit_indices)) := by
  revert k
  suffices h : ∀ (_ : (a.condFlipBit_indices i c).size = a.size) (k : ℕ)
    (hk : k < (a.condFlipBit_indices i c).size), (a.condFlipBit_indices i c)[k] =
    if 0 ≤ k.testRes i then a[k.condFlipBit i c]'((Nat.condFlipBit_lt_iff_lt ha).mpr
    (hk.trans_eq a.size_condFlipBit_indices)) else a[k]'(hk.trans_eq a.size_condFlipBit_indices)
  · simp_rw [zero_le, ite_true] at h
    exact h a.size_condFlipBit_indices
  · refine Array.foldr_induction (fun n (a' : Array α) =>
    ∀ ha' k (hk : k < a'.size), a'[k] =
    if n ≤ k.testRes i then a[k.condFlipBit i c]'((Nat.condFlipBit_lt_iff_lt ha).mpr
    (hk.trans_eq ha')) else a[k]'(hk.trans_eq ha')) (fun _ _ _ => ?_) ?_
    · split_ifs with hc
      · simp_rw [Nat.condFlipBit_apply_of_le_testRes (c.size_zipWithIndex ▸ hc)]
      · rfl
    · simp_rw [Fin.getElem_fin, size_swap!, Nat.succ_le_iff, getElem_zipWithIndex,
        Fin.forall_iff, c.size_zipWithIndex]
      intro t ht a' h ha' k hk
      specialize h ha'
      rcases eq_or_ne (k.testRes i) t with htk | htk
      · have hki : k.testRes i < c.size := htk ▸ ht
        specialize h (k.condFlipBit i c)
          ((Nat.condFlipBit_lt_iff_lt (ha.trans (dvd_of_eq ha'.symm))).mpr hk)
        simp_rw [Nat.testRes_condFlipBit_of_eq, htk, lt_irrefl, if_false] at h
        simp_rw [htk, le_rfl, if_true, ← h, ← htk, Nat.condFlipBit_eq_mergeBit_of_testRes_lt hki]
        rcases eq_or_ne c[k.testRes i] false with hb | hb
        · simp_rw [hb, getElem_swap!_of_eq, Bool.false_xor, Nat.mergeBit_testBit_testRes_of_eq]
        · simp_rw [hb, Bool.true_xor]
          rcases eq_or_ne (k.testBit i) false with hb | hb
          · simp_rw [hb, Bool.not_false, ← hb, Nat.mergeBit_testBit_testRes_of_eq]
            exact Array.getElem_swap!_left _ _
          · simp_rw [Bool.not_eq_false] at hb
            simp_rw [hb, Bool.not_true, ← hb, Nat.mergeBit_testBit_testRes_of_eq]
            exact Array.getElem_swap!_right _ _
      · simp_rw [getElem_swap!_of_ne_ne
          (ne_of_apply_ne (Nat.testRes · i) <| htk.trans_eq Nat.testRes_mergeBit_of_eq.symm)
          (ne_of_apply_ne (Nat.testRes · i) <| htk.trans_eq Nat.testRes_mergeBit_of_eq.symm), h,
          htk.symm.le_iff_lt]

theorem condFlipBit_indices_of_mkArray_true (a : Array α) (i : ℕ) (ha : 2^(i + 1) ∣ a.size) :
    a.condFlipBit_indices i (mkArray (a.size / 2) true) = a.flipBit_indices i := by
  refine Array.ext _ _ (by simp only [size_condFlipBit_indices, size_flipBit_indices]) ?_
  simp_rw [getElem_condFlipBit_indices _ _ ha, getElem_flipBit_indices _ _ ha,
  Nat.condFlipBit_of_mkArray_true, Nat.testRes_lt_div_two_iff_lt ha, size_condFlipBit_indices]
  intro _ h
  simp_rw [h, if_true, implies_true]

def condFlipBit_vals (as : Array ℕ) (i : ℕ) (c : Array Bool) : Array ℕ :=
  as.map (fun q => q.condFlipBit i c)

@[simp]
theorem size_condFlipBit_vals (as : Array ℕ) (i : ℕ) (c : Array Bool) :
    (condFlipBit_vals as i c).size = as.size := size_map _ _

theorem getElem_condFlipBit_vals (as : Array ℕ) (i : ℕ) (c : Array Bool) (k : ℕ)
    (hk : k < (condFlipBit_vals as i c).size) :
    (condFlipBit_vals as i c)[k] = (as[k]'(hk.trans_eq (by simp))).condFlipBit i c :=
  getElem_map _ _ _ _

end CondFlipBit

end Array

namespace ArrayPerm

section FlipBit

def flipBit (a : ArrayPerm n) {i : ℕ} (hin : 2^(i + 1) ∣ n) : ArrayPerm n where
  toArray := a.toArray.flipBit_indices i
  invArray := a.invArray.flipBit_vals i
  size_toArray' := by simp_rw [Array.size_flipBit_indices, a.size_toArray]
  size_invArray' := by simp_rw [Array.size_flipBit_vals, a.size_invArray]
  getElem_toArray_lt' := fun hk => by
    simp_rw [Array.getElem_flipBit_indices a.toArray i
      (hin.trans (dvd_of_eq a.size_toArray.symm)), getElem_toArray, a.getElem_lt]
  getElem_invArray_lt' := fun hk => by
    simp_rw [Array.getElem_flipBit_vals, Nat.flipBit_lt_iff_lt hin, getElem_invArray, getElem_lt]
  left_inv' := fun hk => by
    simp_rw [Array.getElem_flipBit_vals, Array.getElem_flipBit_indices a.toArray i
      (hin.trans (dvd_of_eq a.size_toArray.symm)), getElem_toArray, getElem_invArray,
      getElem_inv_getElem, Nat.flipBit_flipBit_of_eq]

variable (a b : ArrayPerm n) {i k : ℕ} (hin : 2^(i + 1) ∣ n)

@[simp]
theorem getElem_flipBit (hk : k < n) :
    (a.flipBit hin)[k] = a[k.flipBit i]'((Nat.flipBit_lt_iff_lt hin).mpr hk) :=
  a.toArray.getElem_flipBit_indices _ (hin.trans (dvd_of_eq a.size_toArray.symm)) _ _

@[simp]
theorem getElem_inv_flipBit (hk : k < n) :
    (a.flipBit hin)⁻¹[k] = a⁻¹[k].flipBit i := a.invArray.getElem_flipBit_vals _ _ _

@[simp]
theorem mul_flipBit :
    (a * b).flipBit hin = a * b.flipBit hin := by
  ext
  simp only [getElem_flipBit, getElem_mul]


@[simp]
theorem getElem_flipBit_ne_self (a : ArrayPerm n) (hk : k < n) :
    (a.flipBit hin)[k] ≠ a[k] := by
  simp_rw [getElem_flipBit, getElem_ne_iff]
  exact Nat.flipBit_ne_self

@[simp]
theorem flipBit_flipBit (a : ArrayPerm n) :
    (a.flipBit hin).flipBit hin = a := by
  ext k hk : 1
  simp_rw [getElem_flipBit, Nat.flipBit_flipBit_of_eq]

@[simp]
theorem getElem_one_flipBit {k : ℕ} (hk : k < n) : (flipBit 1 hin)[k] = k.flipBit i := by
  rw [getElem_flipBit, getElem_one]

theorem getElem_one_flipBit_inv {k : ℕ} (hk : k < n) : (flipBit 1 hin)⁻¹[k] = k.flipBit i := by
  rw [getElem_inv_flipBit, inv_one, getElem_one]

@[simp]
theorem one_flipBit_inv : (flipBit 1 hin)⁻¹ = flipBit 1 hin := by
  ext : 1
  simp_rw [getElem_one_flipBit_inv, getElem_one_flipBit]

@[simp]
theorem one_flipBit_mul_self : flipBit 1 hin * flipBit 1 hin = 1 := by
  ext : 1
  simp only [getElem_mul, getElem_flipBit, getElem_one, Nat.flipBit_flipBit_of_eq]


theorem flipBit_eq_mul_one_flipBit (a : ArrayPerm n) : a.flipBit hin = a * flipBit 1 hin := by
  ext k hk : 1
  simp only [getElem_flipBit, getElem_mul, getElem_one]

theorem flipBit_inv_eq_one_swap_mul (a : ArrayPerm n) :
    (a.flipBit hin)⁻¹ = flipBit 1 hin * a⁻¹ := by
  rw [flipBit_eq_mul_one_flipBit, mul_inv_rev, one_flipBit_inv]

open Equiv.Perm in
theorem natPerm_flipBit (a : ArrayPerm n) :
    natPerm (a.flipBit hin) = natPerm a *
    ofSubtype ((Nat.flipBitPerm i).subtypePerm (fun k => (k.flipBit_lt_iff_lt hin).symm)) := by
  ext k : 1
  simp_rw [Equiv.Perm.coe_mul, Function.comp_apply,
  ofSubtype_subtypePerm_apply,  Nat.flipBitPerm_apply, natPerm_apply_apply,
  smul_nat_def, getElem_flipBit]
  by_cases hk : k < n
  · simp_rw [hk, if_true, k.flipBit_lt_iff_lt hin, hk, dite_true]
  · simp_rw [hk, if_false, hk, dite_false]

open Equiv.Perm in
theorem natPerm_one_flipBit :
    natPerm (flipBit 1 hin) =
    ofSubtype ((Nat.flipBitPerm i).subtypePerm (fun k => (k.flipBit_lt_iff_lt hin).symm)) := by
  simp_rw [natPerm_flipBit, map_one, one_mul]

theorem ofPerm_flipBit :
    ofPerm (Nat.flipBitPerm i) (fun k => k.flipBit_lt_iff_lt hin) = flipBit 1 hin := by
  ext k : 1
  simp only [getElem_ofPerm, Nat.flipBitPerm_apply, getElem_flipBit, getElem_one]

end FlipBit

section CondFlipBit

def condFlipBit (a : ArrayPerm n) (hin : 2^(i + 1) ∣ n) (c : Array Bool) : ArrayPerm n where
  toArray := a.toArray.condFlipBit_indices i c
  invArray := a.invArray.condFlipBit_vals i c
  size_toArray' := by simp_rw [Array.size_condFlipBit_indices, a.size_toArray]
  size_invArray' := by simp_rw [Array.size_condFlipBit_vals, a.size_invArray]
  getElem_toArray_lt' := fun hk => by
    simp_rw [Array.getElem_condFlipBit_indices a.toArray i
      (hin.trans (dvd_of_eq a.size_toArray.symm)), getElem_toArray, getElem_lt]
  getElem_invArray_lt' := fun hk => by
    simp_rw [Array.getElem_condFlipBit_vals, Nat.condFlipBit_lt_iff_lt hin, getElem_invArray,
    getElem_lt]
  left_inv' := fun hk => by
    simp_rw [Array.getElem_condFlipBit_vals, Array.getElem_condFlipBit_indices a.toArray i
      (hin.trans (dvd_of_eq a.size_toArray.symm)), getElem_toArray, getElem_invArray,
      a.getElem_inv_getElem, Nat.condFlipBit_condFlipBit_of_eq]

variable (a : ArrayPerm n) {i k : ℕ} (hin : 2^(i + 1) ∣ n)

@[simp]
theorem condFlipBit_getElem {k : ℕ} (hk : k < n) :
    (a.condFlipBit hin c)[k] = a[k.condFlipBit i c]'((Nat.condFlipBit_lt_iff_lt hin).mpr hk) :=
  a.toArray.getElem_condFlipBit_indices _ (hin.trans (dvd_of_eq a.size_toArray.symm)) _ _ _

@[simp]
theorem condFlipBit_inv_getElem {k : ℕ} (hk : k < n) :
    (a.condFlipBit hin c)⁻¹[k] = a⁻¹[k].condFlipBit i c :=
  a.invArray.getElem_condFlipBit_vals _ _ _ _


theorem condFlipBit_smul_eq_ite_smul_condFlipBit :
    (a.condFlipBit hin c) • k = if k < n then a • k.condFlipBit i c else k := by
  split_ifs with hk
  · simp_rw [smul_of_lt hk, smul_of_lt ((k.condFlipBit_lt_iff_lt hin).mpr hk), condFlipBit_getElem]
  · simp_rw [smul_of_ge (le_of_not_lt hk)]

theorem condFlipBit_inv_eq_ite_condFlipBit_inv_smul (a : ArrayPerm n) :
  (a.condFlipBit hin c)⁻¹ • k = if k < n then (a⁻¹ • k).condFlipBit i c else k := by
  split_ifs with hk
  · simp_rw [smul_of_lt hk, condFlipBit_inv_getElem]
  · simp_rw [smul_of_ge (le_of_not_lt hk)]

theorem flipBit_smul_condFlipBit (a : ArrayPerm n) :
    (a.condFlipBit hin c) • (k.condFlipBit i c) = if k < n then a • k else k.condFlipBit i c := by
  simp_rw [condFlipBit_smul_eq_ite_smul_condFlipBit, k.condFlipBit_condFlipBit_of_eq,
  k.condFlipBit_lt_iff_lt hin]

theorem condFlipBit_inv_smul_smul_condFlipBit (a : ArrayPerm n) :
    (a.condFlipBit hin c)⁻¹ • (a • k.condFlipBit i c) = if k < n then k else k.condFlipBit i c := by
  simp_rw [condFlipBit_inv_eq_ite_condFlipBit_inv_smul, inv_smul_smul,
    k.condFlipBit_condFlipBit_of_eq, smul_lt_iff_lt, k.condFlipBit_lt_iff_lt hin]
  split_ifs with hk
  · rfl
  · rw [smul_of_ge (le_of_not_lt ((k.condFlipBit_lt_iff_lt hin).not.mpr hk))]

@[simp]
theorem condFlipBit_condFlipBit (a : ArrayPerm n) :
    (a.condFlipBit hin c).condFlipBit hin c = a := by
  ext k hk : 1
  simp only [condFlipBit_getElem, Nat.condFlipBit_condFlipBit_of_eq]

@[simp]
theorem one_condFlipBit_smul :
    (condFlipBit 1 hin c) • k = if k < n then k.condFlipBit i c else k := by
  rw [condFlipBit_smul_eq_ite_smul_condFlipBit, one_smul]

theorem one_condFlipBit_inv_smul : (condFlipBit 1 hin c)⁻¹ • k =
    if k < n then k.condFlipBit i c else k := by
  simp_rw [condFlipBit_inv_eq_ite_condFlipBit_inv_smul, inv_one, one_smul]

@[simp]
theorem one_condFlipBit_mul_self : condFlipBit 1 hin c * condFlipBit 1 hin c = 1 := by
  ext : 1
  simp only [getElem_mul, condFlipBit_getElem, getElem_one, Nat.condFlipBit_condFlipBit_of_eq]

@[simp]
theorem one_condFlipBit_inverse : (condFlipBit 1 hin c)⁻¹ = condFlipBit 1 hin c := by
  ext : 1
  simp only [condFlipBit_inv_getElem, inv_one, getElem_one, condFlipBit_getElem]

theorem condFlipBit_eq_mul_one_condFlipBit (a : ArrayPerm n) :
    a.condFlipBit hin c = a * condFlipBit 1 hin c := by
  ext k hk : 1
  simp only [condFlipBit_getElem, getElem_mul, getElem_one]

theorem condFlipBit_inv_eq_one_swap_mul (a : ArrayPerm n) :
    (a.condFlipBit hin c)⁻¹ = condFlipBit 1 hin c * a⁻¹ := by
  rw [condFlipBit_eq_mul_one_condFlipBit, mul_inv_rev, one_condFlipBit_inverse]

open Equiv.Perm in
theorem natPerm_condFlipBit (a : ArrayPerm n) :
    natPerm (a.condFlipBit hin c) = natPerm a *
    ofSubtype ((Nat.condFlipBitPerm i c).subtypePerm (fun k => (k.condFlipBit_lt_iff_lt hin).symm)) := by
  ext k : 1
  simp only [natPerm_apply_apply, Equiv.Perm.coe_mul, Function.comp_apply,
  condFlipBit_smul_eq_ite_smul_condFlipBit, ofSubtype_subtypePerm_apply, smul_ite,
  Nat.condFlipBitPerm_apply]
  split_ifs with hk
  · rfl
  · simp_rw [smul_of_ge (le_of_not_lt hk)]

open Equiv.Perm in
theorem natPerm_one_condFlipBit : natPerm (condFlipBit 1 hin c) =
    ofSubtype ((Nat.condFlipBitPerm i c).subtypePerm
    (fun k => (k.condFlipBit_lt_iff_lt hin).symm)) := by
  simp_rw [natPerm_condFlipBit, map_one, one_mul]

theorem ofPerm_condFlipBit : ofPerm (Nat.condFlipBitPerm i c)
    (fun k => k.condFlipBit_lt_iff_lt hin) = condFlipBit 1 hin c := by
  ext
  simp only [getElem_ofPerm, Nat.condFlipBitPerm_apply, condFlipBit_getElem, getElem_one]

end CondFlipBit

section FlipCommutator

def flipBitCommutator (a : ArrayPerm n) (hin : 2^(i + 1) ∣ n) : ArrayPerm n :=
  (a.flipBit hin) * (a⁻¹.flipBit hin)

variable (a : ArrayPerm n) {i k : ℕ} (hin : 2^(i + 1) ∣ n)

@[simp]
theorem getElem_flipBitCommutator (hk : k < n) :
    (a.flipBitCommutator hin)[k] = a[(a⁻¹[k.flipBit i]'
    ((Nat.flipBit_lt_iff_lt hin).mpr hk)).flipBit i]'
    ((Nat.flipBit_lt_iff_lt hin).mpr getElem_lt) := by
  unfold flipBitCommutator
  simp only [getElem_mul, getElem_flipBit]

@[simp]
theorem getElem_inv_flipBitCommutator (hk : k < n) :
    (a.flipBitCommutator hin)⁻¹[k] = (a[(a⁻¹[k]).flipBit i]'
    ((Nat.flipBit_lt_iff_lt hin).mpr getElem_lt)).flipBit i := by
  unfold flipBitCommutator
  simp_rw [mul_inv_rev, getElem_mul, getElem_inv_flipBit, inv_inv]

theorem flipBitCommutator_flipBitCommutator :
    (a.flipBitCommutator hin).flipBitCommutator hin =
      a.flipBitCommutator hin * a.flipBitCommutator hin := by
  ext
  simp only [getElem_flipBitCommutator, getElem_inv_flipBitCommutator, Nat.flipBit_flipBit_of_eq,
    getElem_mul]

theorem flipBit_flipBitCommutator :
    (a.flipBitCommutator hin).flipBit hin = a.flipBit hin * a⁻¹ := by
  ext
  simp only [getElem_flipBit, getElem_flipBitCommutator,  Nat.flipBit_flipBit_of_eq,
  getElem_mul]

theorem flipBit_inv_flipBitCommutator :
    (a.flipBitCommutator hin)⁻¹.flipBit hin = ((a.flipBitCommutator hin)⁻¹.flipBit hin)⁻¹ := by
  ext
  simp_rw [getElem_flipBit, getElem_inv_flipBitCommutator, getElem_inv_flipBit,
  inv_inv, getElem_flipBitCommutator]

@[simp]
theorem flipBitCommutator_smul :
    (a.flipBitCommutator hin) • k = a • ((a⁻¹ • (k.flipBit i)).flipBit i) := by
  rcases lt_or_le k n with hk | hk
  · simp_rw [smul_of_lt hk,
      smul_of_lt <| (Nat.flipBit_lt_iff_lt hin).mpr hk,
      smul_of_lt <| (Nat.flipBit_lt_iff_lt hin).mpr getElem_lt,
      getElem_flipBitCommutator]
  · simp_rw [smul_of_ge hk, smul_of_ge <|
    le_of_not_lt ((Nat.flipBit_lt_iff_lt hin).not.mpr hk.not_lt),
    Nat.flipBit_flipBit_of_eq, smul_of_ge hk]

@[simp]
theorem flipBitCommutator_inv_smul :
    (a.flipBitCommutator hin)⁻¹ • k = (a • ((a⁻¹ • k).flipBit i)).flipBit i := by
  rcases lt_or_le k n with hk | hk
  · simp_rw [smul_of_lt hk,
      smul_of_lt <| (Nat.flipBit_lt_iff_lt hin).mpr getElem_lt,
      getElem_inv_flipBitCommutator]
  · simp_rw [smul_of_ge hk, smul_of_ge <|
    le_of_not_lt ((Nat.flipBit_lt_iff_lt hin).not.mpr hk.not_lt),
    Nat.flipBit_flipBit_of_eq]

theorem flipBitCommutator_eq_commutatorElement : a.flipBitCommutator hin = ⁅a, flipBit 1 hin⁆ := by
  ext
  simp_rw [getElem_flipBitCommutator, commutatorElement_def, one_flipBit_inv, getElem_mul,
    getElem_one_flipBit]

lemma getElem_flipBit_flipBitCommutator (hk : k < n) :
    ((a.flipBitCommutator hin).flipBit hin)[k] =
    (a.flipBitCommutator hin)⁻¹[k].flipBit i := by
  simp_rw [flipBit_flipBitCommutator, getElem_mul, getElem_flipBit, getElem_inv_flipBitCommutator,
  Nat.flipBit_flipBit_of_eq]

lemma getElem_flipBit_flipBitCommutator_inv (hk : k < n) :
    ((a.flipBitCommutator hin)⁻¹.flipBit hin)[k] =
    (a.flipBitCommutator hin)[k].flipBit i := by
  rw [flipBit_inv_flipBitCommutator, getElem_inv_flipBit, inv_inv]

lemma getElem_flipBit_flipBitCommutator_pow_inv (hk : k < n) :
    (((a.flipBitCommutator hin)^p)⁻¹.flipBit hin)[k] =
    ((a.flipBitCommutator hin)^p)[k].flipBit i := by
  induction' p with p IH generalizing k
  · simp_rw [pow_zero, inv_one, getElem_one_flipBit, getElem_one]
  · nth_rewrite 1 [pow_succ']
    simp_rw [pow_succ, mul_inv_rev, getElem_mul, mul_flipBit, getElem_mul,
    getElem_flipBit_flipBitCommutator_inv, ← getElem_flipBit _ hin getElem_lt, IH]

lemma getElem_flipBit_flipBitCommutator_pow (hk : k < n) :
    (((a.flipBitCommutator hin)^p).flipBit hin)[k] =
    ((a.flipBitCommutator hin)^p)⁻¹[k].flipBit i := by
  induction' p with p IH generalizing k
  · simp_rw [pow_zero, inv_one, getElem_one_flipBit, getElem_one]
  · nth_rewrite 1 [pow_succ]
    simp_rw [pow_succ', mul_inv_rev, getElem_mul, mul_flipBit, getElem_mul,
    getElem_flipBit_flipBitCommutator, ← getElem_flipBit _ hin getElem_lt, IH]

lemma getElem_flipBit_flipBitCommutator_zpow {p : ℤ} (hk : k < n) :
    (((a.flipBitCommutator hin)^p).flipBit hin)[k] =
    ((a.flipBitCommutator hin)^p)⁻¹[k].flipBit i := by
  cases p
  · simp only [Int.ofNat_eq_coe, zpow_natCast, zpow_neg, getElem_flipBit_flipBitCommutator_pow]
  · simp only [zpow_negSucc, zpow_neg, inv_inv, getElem_flipBit_flipBitCommutator_pow_inv]

lemma getElem_flipBit_flipBitCommutator_zpow_inv {p : ℤ} (hk : k < n) :
    (((a.flipBitCommutator hin)^p)⁻¹.flipBit hin)[k] =
    ((a.flipBitCommutator hin)^p)[k].flipBit i := by
  rw [← zpow_neg, getElem_flipBit_flipBitCommutator_zpow, zpow_neg, inv_inv]

lemma getElem_flipBitCommutator_ne_flipBit (hk : k < n) :
    (a.flipBitCommutator hin)[k] ≠ k.flipBit i := by
  have hk' : k.flipBit i < n := by rwa [Nat.flipBit_lt_iff_lt hin]
  simp_rw [getElem_flipBitCommutator, ← (a.ne_getElem_inv_iff _ hk')]
  exact Nat.flipBit_ne_self

lemma getElem_flipBitCommutator_flipBit_ne (hk : k < n) :
    (a.flipBitCommutator hin)[k].flipBit i ≠ k := by
  intros H
  apply (getElem_flipBitCommutator_ne_flipBit a hin hk)
  nth_rewrite 2 [← H]
  simp_rw [Nat.flipBit_flipBit_of_eq]

lemma getElem_pow_flipBitCommutator_ne_flipBit (hk : k < n) {p : ℕ} :
    ((a.flipBitCommutator hin) ^ p)[k] ≠ k.flipBit i := by
  induction' p using Nat.twoStepInduction with p IH generalizing k
  · rw [pow_zero, getElem_one]
    exact Nat.flipBit_ne_self.symm
  · rw [pow_one]
    exact a.getElem_flipBitCommutator_ne_flipBit _ _
  · have hk' : k.flipBit i < n := by rwa [Nat.flipBit_lt_iff_lt hin]
    simp_rw [pow_succ (n := p.succ), pow_succ' (n := p), getElem_mul,
    ← (ne_getElem_inv_iff _ _ hk'), getElem_inv_flipBitCommutator, getElem_flipBitCommutator]
    exact IH _

lemma getElem_flipBitCommutator_pow_flipBit_ne (hk : k < n) {p : ℕ} :
    ((a.flipBitCommutator hin) ^ p)[k].flipBit i ≠ k := by
  intros H
  apply (getElem_pow_flipBitCommutator_ne_flipBit a hin hk (p := p))
  nth_rewrite 2 [← H]
  simp_rw [Nat.flipBit_flipBit_of_eq]

lemma getElem_zpow_flipBitCommutator_ne_flipBit (hk : k < n) {p : ℤ} :
    ((a.flipBitCommutator hin) ^ p)[k] ≠ k.flipBit i := by
  cases p
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact getElem_pow_flipBitCommutator_ne_flipBit _ _ _
  · have hk' : k.flipBit i < n := by rwa [Nat.flipBit_lt_iff_lt hin]
    simp_rw [zpow_negSucc, getElem_inv_ne_iff _ _ hk']
    exact (Nat.flipBit_flipBit_of_eq (i := i)).symm.trans_ne
      (getElem_pow_flipBitCommutator_ne_flipBit _ _ _).symm

lemma getElem_flipBitCommutator_zpow_flipBit_ne (hk : k < n) {p : ℤ} :
    ((a.flipBitCommutator hin) ^ p)[k].flipBit i ≠ k := by
  intros H
  apply (getElem_zpow_flipBitCommutator_ne_flipBit a hin hk (p := p))
  nth_rewrite 2 [← H]
  simp_rw [Nat.flipBit_flipBit_of_eq]

theorem getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow (hk : k < n)
    {p q : ℤ} : ((a.flipBitCommutator hin) ^ p)[k] ≠
    ((a.flipBitCommutator hin) ^ q)[k].flipBit i := by
  rw [← sub_add_cancel p q, zpow_add, getElem_mul]
  exact getElem_zpow_flipBitCommutator_ne_flipBit _ _ _

theorem disjoint_flipBitCommutator_cycleOf_map_self_flipBitPerm (k : ℕ) :
    Disjoint ((a.flipBitCommutator hin).cycleOf k)
  (((a.flipBitCommutator hin).cycleOf k).map <| Nat.flipBitPerm i) := by
  simp_rw [Finset.disjoint_iff_ne, Finset.mem_map, Equiv.coe_toEmbedding, Nat.flipBitPerm_apply,
    mem_cycleOf_iff_exists_zpow, forall_exists_index, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff]
  rcases lt_or_le k n with hk | hk
  · simp_rw [smul_of_lt hk]
    exact fun _ _ => getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow _ _ _
  · simp_rw [smul_of_ge hk]
    exact fun _ _ => Nat.flipBit_ne_self.symm

lemma two_mul_filter_sameCycle_card_le_card (s : Finset ℕ)
    (hsy : ∀ q, q ∈ s → q.flipBit i ∈ s) (k : ℕ) (hsc : (a.flipBitCommutator hin).cycleOf k ⊆ s) :
  MulAction.period (a.flipBitCommutator hin) k ≤ s.card / 2 := by
  rw [← card_cycleOf, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  nth_rewrite 2 [← Finset.card_map (Nat.flipBitPerm i).toEmbedding]
  rw [← Finset.card_union_of_disjoint
    (disjoint_flipBitCommutator_cycleOf_map_self_flipBitPerm a hin k)]
  refine Finset.card_le_card (Finset.union_subset hsc ?_)
  simp_rw [Finset.map_subset_iff_subset_preimage, Finset.subset_iff, Finset.mem_preimage,
  Equiv.coe_toEmbedding, Nat.flipBitPerm_apply]
  exact fun _ h => (hsy _ (hsc h))

end FlipCommutator

end ArrayPerm

section BitInvariant

namespace Function

open Nat

def BitInvariant (i : ℕ) (f : ℕ → ℕ) : Prop := (testBit · i) ∘ f = (testBit · i)

variable {f g : ℕ → ℕ} {i : ℕ}

theorem bitInvariant_iff : f.BitInvariant i ↔ ∀ q, (f q).testBit i = q.testBit i := funext_iff

theorem bitInvariant_of_testBit_apply_eq_testBit (h : ∀ q, (f q).testBit i = q.testBit i) :
    f.BitInvariant i := bitInvariant_iff.mpr h

theorem BitInvariant.testBit_apply_eq_testBit (h : f.BitInvariant i) :
    (f q).testBit i = q.testBit i := bitInvariant_iff.mp h _

theorem bitInvariant_id : id.BitInvariant i :=
  bitInvariant_of_testBit_apply_eq_testBit (fun _ => rfl)

theorem forall_bitInvariant_iff_eq_id : (∀ i, f.BitInvariant i) ↔ f = id := by
  simp_rw [funext_iff, id_eq, testBit_ext_iff, bitInvariant_iff]
  exact forall_comm

theorem bitInvariant_flipBit_of_ne (h : i ≠ j) : (flipBit · j).BitInvariant i :=
  bitInvariant_of_testBit_apply_eq_testBit (fun _ => testBit_flipBit_of_ne h)

theorem not_bitInvariant_flipBit_of_eq : ¬ (flipBit · i).BitInvariant i := by
  simp_rw [bitInvariant_iff, testBit_flipBit_of_eq, Bool.not_eq_self,
    forall_const, not_false_eq_true]

theorem bitInvariant_condFlipBit_of_ne (h : i ≠ j) (c : Array Bool) :
    (condFlipBit · j c).BitInvariant i :=
  bitInvariant_of_testBit_apply_eq_testBit (fun _ => testBit_condFlipBit_of_ne h)

theorem BitInvariant.comp (hf : f.BitInvariant i) (hg : g.BitInvariant i) :
    (f ∘ g).BitInvariant i := bitInvariant_of_testBit_apply_eq_testBit <| fun q => by
  simp_rw [Function.comp_apply, hf.testBit_apply_eq_testBit, hg.testBit_apply_eq_testBit]

theorem BitInvariant.of_comp (hf : f.BitInvariant i)
    (hfg : (f ∘ g).BitInvariant i) : g.BitInvariant i :=
  bitInvariant_of_testBit_apply_eq_testBit <| fun _ =>
  hf.testBit_apply_eq_testBit ▸ hfg.testBit_apply_eq_testBit

theorem RightInverse.bitInvariant_of_bitInvariant (hfg : RightInverse g f) (h : f.BitInvariant i) :
  g.BitInvariant i := h.of_comp (hfg.comp_eq_id ▸ bitInvariant_id)

theorem LeftInverse.bitInvariant_of_bitInvariant (hfg : LeftInverse g f) (h : g.BitInvariant i) :
  f.BitInvariant i := RightInverse.bitInvariant_of_bitInvariant hfg h

theorem BitInvariant.bitInvariant_iterate (hf : f.BitInvariant i) {n : ℕ} :
   (f^[n]).BitInvariant i := by
  induction' n with n IH
  · exact bitInvariant_id
  · exact iterate_succ _ _ ▸ IH.comp hf

theorem BitInvariant.mergeBit_testRes_apply_mergeBit {p : ℕ} (hf : f.BitInvariant i) :
    ((f (p.mergeBit i b)).testRes i).mergeBit i b = f (p.mergeBit i b) := by
  simp_rw [mergeBit_eq_iff, hf.testBit_apply_eq_testBit, testBit_mergeBit_of_eq, true_and]

def BitInvariantLT (i : ℕ) (f : ℕ → ℕ) : Prop := ∀ k < i, BitInvariant k f

theorem bitInvariantLT_iff : BitInvariantLT i f ↔ ∀ k < i, f.BitInvariant k := Iff.rfl

theorem bitInvariantLT_iff_mod_two_pow_eq :
    BitInvariantLT i f ↔ ∀ (p : ℕ), f p % 2 ^ i = p % 2 ^ i := by
  simp_rw [testBit_ext_mod_two_pow_iff, bitInvariantLT_iff, bitInvariant_iff,
  imp_forall_iff, forall_swap (α := ℕ)]

@[simp]
theorem bitInvariantLT_zero : BitInvariantLT 0 f := by
  simp_rw [bitInvariantLT_iff, not_lt_zero, false_implies, implies_true]

theorem bitInvariantLT_id : BitInvariantLT i id := fun _ _ => bitInvariant_id

theorem bitInvariantLT_flipBit_of_ge (h : j ≤ i) : BitInvariantLT j (flipBit · i) :=
  fun _ hk => bitInvariant_flipBit_of_ne (hk.trans_le h).ne

theorem bitInvariantLT_flipBit_of_eq : BitInvariantLT i (flipBit · i) :=
  bitInvariantLT_flipBit_of_ge le_rfl

theorem not_bitInvariantLT_flipBit_of_lt (h : i < j) : ¬ BitInvariantLT j (flipBit · i) :=
  not_forall_of_exists_not ⟨i, not_imp_of_and_not ⟨h, not_bitInvariant_flipBit_of_eq⟩⟩

theorem BitInvariantLT.ge (h : BitInvariantLT j (flipBit · i)) : j ≤ i :=
  le_of_not_lt (not_bitInvariantLT_flipBit_of_lt.mt <| not_not_intro h)

theorem bitInvariantLT_flipBit_iff_ge : BitInvariantLT j (flipBit · i) ↔ j ≤ i :=
  ⟨BitInvariantLT.ge, bitInvariantLT_flipBit_of_ge⟩

theorem bitInvariantLT_condFlipBit_of_ge (h : j ≤ i) (c : Array Bool) :
    BitInvariantLT j (condFlipBit · i c) :=
  fun _ hk => bitInvariant_condFlipBit_of_ne (hk.trans_le h).ne c

theorem bitInvariantLT_condFlipBit_of_eq (c : Array Bool) :
    BitInvariantLT i (condFlipBit · i c) :=
  bitInvariantLT_condFlipBit_of_ge le_rfl c

theorem bitInvariantLT_imp_bitInvariantLT_iff_ge :
    (∀ f, BitInvariantLT n f → BitInvariantLT m f) ↔ m ≤ n :=
  ⟨fun h => (h _ bitInvariantLT_flipBit_of_eq).ge, fun hmn _ hf _ hk => hf _ (hk.trans_le hmn)⟩

theorem exists_bitInvariantLT_and_not_bitInvariantLT_iff_lt :
    (∃ f, BitInvariantLT n f ∧ ¬ BitInvariantLT m f) ↔ n < m := not_iff_not.mp <| by
  simp_rw [not_exists, not_lt, not_and_not_right, bitInvariantLT_imp_bitInvariantLT_iff_ge]

def BitInvariantGE (i : ℕ) (f : ℕ → ℕ) : Prop := ∀ k ≥ i, BitInvariant k f

theorem bitInvariantGE_iff : BitInvariantGE i f ↔ ∀ k ≥ i, f.BitInvariant k := Iff.rfl

theorem bitInvariantGE_iff_div_two_pow_eq : BitInvariantGE i f ↔
    ∀ (p : ℕ), f p / 2 ^ i = p / 2 ^ i := by
  simp_rw [testBit_ext_div_two_pow_iff, bitInvariantGE_iff, bitInvariant_iff,
  imp_forall_iff, forall_swap (α := ℕ)]

theorem BitInvariantGE.apply_lt_iff_lt (hf : BitInvariantGE i f) {p : ℕ}:
    f p < 2^i ↔ p < 2^i := by
  rw [bitInvariantGE_iff] at hf
  simp_rw [lt_pow_two_iff_ge_imp_testBit_eq_false]
  exact forall₂_congr (fun _ h => by
    simp_rw [Bool.coe_false_iff_false, Bool.not_inj_iff]
    exact (hf _ h).testBit_apply_eq_testBit)

theorem bitInvariantGE_id : BitInvariantGE i id := fun _ _ => bitInvariant_id

theorem bitInvariantGE_zero_iff_id : BitInvariantGE 0 f ↔ f = id := by
  simp_rw [bitInvariantGE_iff, Nat.zero_le, true_implies, forall_bitInvariant_iff_eq_id]

theorem bitInvariantGE_flipBit_of_lt (h : i < j) : BitInvariantGE j (flipBit · i) :=
  fun _ hk => bitInvariant_flipBit_of_ne (hk.trans_lt' h).ne'

theorem not_bitInvariantGE_flipBit_of_ge (h : j ≤ i) : ¬ BitInvariantGE j (flipBit · i) :=
  not_forall_of_exists_not ⟨i, not_imp_of_and_not ⟨h, not_bitInvariant_flipBit_of_eq⟩⟩

theorem BitInvariantGE.lt (h : BitInvariantGE j (flipBit · i)) : i < j :=
  lt_of_not_le (not_bitInvariantGE_flipBit_of_ge.mt <| not_not_intro h)

theorem not_bitInvariantGE_flipBit_of_eq : ¬ BitInvariantGE i (flipBit · i) :=
  not_bitInvariantGE_flipBit_of_ge le_rfl

theorem bitInvariantGE_flipBit_iff_lt : BitInvariantGE j (flipBit · i) ↔ i < j :=
  ⟨BitInvariantGE.lt, bitInvariantGE_flipBit_of_lt⟩

theorem bitInvariantGE_condFlipBit_of_lt (h : i < j) (c : Array Bool) :
    BitInvariantGE j (condFlipBit · i c) :=
  fun _ hk => bitInvariant_condFlipBit_of_ne (hk.trans_lt' h).ne' c

theorem bitInvariantGE_imp_bitInvariantGE_iff_le :
    (∀ f, BitInvariantGE n f → BitInvariantGE m f) ↔ n ≤ m :=
  ⟨fun h => le_of_not_lt fun hmn =>
    not_bitInvariantGE_flipBit_of_eq (h _ (bitInvariantGE_flipBit_of_lt hmn)),
  fun hmn => fun _ hf _ hk => hf _ (hmn.trans hk)⟩

theorem exists_bitInvariantGE_and_not_bitInvariantGE_iff_gt :
    (∃ f, BitInvariantGE n f ∧ ¬ BitInvariantGE m f) ↔ m < n := not_iff_not.mp <| by
  simp_rw [not_exists, not_lt, not_and_not_right, bitInvariantGE_imp_bitInvariantGE_iff_le]

theorem BitInvariantLT.id_of_bitInvariantGE (hfLT : BitInvariantLT m f)
    (hfGE : BitInvariantGE m f) : f = id :=
  forall_bitInvariant_iff_eq_id.mp <| fun i => (i.lt_or_ge m).by_cases (hfLT i) (hfGE i)

theorem BitInvariantGE.id_of_bitInvariantLT (hfGE : BitInvariantGE m f)
    (hfLT : BitInvariantLT m f) : f = id := hfLT.id_of_bitInvariantGE hfGE

theorem bitInvariantLT_and_bitInvariantGE_iff_id :
    BitInvariantLT m f ∧ BitInvariantGE m f ↔ f = id :=
  ⟨fun h => h.1.id_of_bitInvariantGE h.2, fun h => h ▸ ⟨bitInvariantLT_id, bitInvariantGE_id⟩⟩

end Function

namespace ArrayPerm

theorem getElem_testBit (a : ArrayPerm n) {k : ℕ} (h : n ≤ 2^k) {i : ℕ} (hi : i < n) :
    a[i].testBit k = false :=
  Nat.testBit_eq_false_of_lt <| (a.getElem_lt).trans_le h

open Nat Array

def BitInvariant (i : ℕ) (a : ArrayPerm n) : Prop :=
  a.toArray.map (testBit · i) = (range n).map (testBit · i)

variable {a b : ArrayPerm n}

theorem one_bitInvariant : BitInvariant i (1 : ArrayPerm n) := rfl

theorem bitInvariant_iff_testBit_getElem_eq_testBit : a.BitInvariant i ↔
    ∀ {x} (h : x < n), a[x].testBit i = x.testBit i := by
  unfold BitInvariant
  simp_rw [Array.ext_iff]
  simp only [size_map, size_toArray, size_range, getElem_map, getElem_toArray, getElem_range,
    true_and]
  exact ⟨fun h i hi => h _ hi hi, fun h _ _ => h⟩

theorem bitInvariant_of_ge (h : n ≤ 2^i) : a.BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, a.getElem_testBit h]
  exact fun (hx : _ < n) => (Nat.testBit_eq_false_of_lt (hx.trans_le h)).symm

theorem bitInvariant_of_ge_of_ge (h : n ≤ 2^i) (hk : i ≤ k) : a.BitInvariant k :=
  bitInvariant_of_ge (h.trans (Nat.pow_le_pow_right zero_lt_two hk))

theorem forall_lt_bitInvariant_iff_eq_one_of_ge (hin : n ≤ 2^i) :
    (∀ k < i, a.BitInvariant k) ↔ a = 1 := by
  refine ⟨fun h => ArrayPerm.ext ?_, fun h _ _ => h ▸ one_bitInvariant⟩
  simp only [getElem_one, testBit_ext_iff]
  intro j hj k
  rcases lt_or_le k i with hk | hk
  · simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit] at h
    apply h _ hk
  · have H := a.bitInvariant_of_ge_of_ge hin hk
    simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit] at H
    apply H

@[simp]
theorem BitInvariant.testBit_getElem_toArray_eq_testBit (ha : a.BitInvariant i) {x : ℕ}
    (h : x < n) : a[x].testBit i = x.testBit i :=
  bitInvariant_iff_testBit_getElem_eq_testBit.mp ha h

theorem bitInvariant_of_testBit_getElem_toArray_eq_testBit (h : ∀ {x} (h : x < n),
    a[x].testBit i = x.testBit i) : a.BitInvariant i :=
  bitInvariant_iff_testBit_getElem_eq_testBit.mpr h

@[simp]
theorem BitInvariant.inv (ha : a.BitInvariant i) :
    BitInvariant i a⁻¹ := bitInvariant_of_testBit_getElem_toArray_eq_testBit <| fun hi => by
  rw [← ha.testBit_getElem_toArray_eq_testBit getElem_lt, getElem_getElem_inv]

theorem BitInvariant.of_inv (ha : a⁻¹.BitInvariant i) : BitInvariant i a := ha.inv

theorem bitInvariant_iff_bitInvariant_inv : a⁻¹.BitInvariant i ↔ a.BitInvariant i :=
  ⟨fun h => h.inv, fun h => h.inv⟩

theorem BitInvariant.mul (ha : a.BitInvariant i) (hb : b.BitInvariant i) :
    BitInvariant i (a * b) := bitInvariant_of_testBit_getElem_toArray_eq_testBit <| by
  simp_rw [getElem_mul, ha.testBit_getElem_toArray_eq_testBit,
  hb.testBit_getElem_toArray_eq_testBit, implies_true]

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

theorem bitInvariant_iff_smul_bitInvariant :
    a.BitInvariant i ↔ (a • ·).BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, Function.bitInvariant_iff,
    smul_nat_def, apply_dite (testBit · i), dite_eq_right_iff]

theorem BitInvariant.flipBitCommutator (ha : a.BitInvariant i) {i' : ℕ} (hin : 2 ^ (i' + 1) ∣ n) :
    (a.flipBitCommutator hin).BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, getElem_flipBitCommutator,
  ha.testBit_getElem_toArray_eq_testBit, testBit_flipBit,
  ha.inv.testBit_getElem_toArray_eq_testBit, testBit_flipBit, Bool.xor, Bool.xor_assoc,
  Bool.xor_self, Bool.xor_false, implies_true]

--(hsy : ∀ q, q ∈ s → q.flipBit i ∈ s) (k : ℕ) (hsc : (a.flipBitCommutator hin).cycleOf k ⊆ s)

def BitInvariantEQ (i : ℕ) : Subgroup (ArrayPerm n) where
  carrier := BitInvariant i
  mul_mem' := BitInvariant.mul
  one_mem' := one_bitInvariant
  inv_mem' := BitInvariant.inv

@[simp]
theorem mem_bitInvariantEQ_iff : a ∈ BitInvariantEQ i ↔ a.BitInvariant i := Iff.rfl

theorem mem_bitInvariantEQ_iff_smul_bitInvariant :
  a ∈ BitInvariantEQ i ↔ (a • ·).BitInvariant i := bitInvariant_iff_smul_bitInvariant

def BitInvariantLT (i : ℕ) : Subgroup (ArrayPerm n) :=
  ⨅ (k : ℕ) (_ : k < i), BitInvariantEQ k

theorem mem_bitInvariantLT_iff : a ∈ BitInvariantLT i ↔ ∀ k < i, a ∈ BitInvariantEQ k := by
  unfold BitInvariantLT
  simp_rw [Subgroup.mem_iInf]

theorem mem_bitInvariantLT_iff_smul_bitInvariant :
    a ∈ BitInvariantLT i ↔ (a • ·).BitInvariantLT i := by
  simp_rw [mem_bitInvariantLT_iff, Function.bitInvariantLT_iff,
  mem_bitInvariantEQ_iff_smul_bitInvariant]

def BitInvariantGE (i : ℕ) : Subgroup (ArrayPerm n) :=
  ⨅ (k : ℕ) (_ : i ≤ k), BitInvariantEQ k

theorem mem_bitInvariantGE_iff : a ∈ BitInvariantGE i ↔ ∀ k ≥ i, a ∈ BitInvariantEQ k := by
  unfold BitInvariantGE
  simp_rw [Subgroup.mem_iInf]

theorem mem_bitInvariantGE_iff_smul_bitInvariant :
    a ∈ BitInvariantGE i ↔ (a • ·).BitInvariantGE i := by
  simp_rw [mem_bitInvariantGE_iff, Function.bitInvariantGE_iff,
  mem_bitInvariantEQ_iff_smul_bitInvariant]

theorem mem_bitInvariantGE_of_ge (h : n ≤ 2^i) : a ∈ BitInvariantGE i := by
  simp_rw [mem_bitInvariantGE_iff, mem_bitInvariantEQ_iff]
  exact fun _ => bitInvariant_of_ge_of_ge h

theorem bitInvariantGE_eq_top_of_ge (h : n ≤ 2^i) :
    (BitInvariantGE i : Subgroup (ArrayPerm n)) = ⊤ := by
  ext
  simp_rw [Subgroup.mem_top, iff_true, mem_bitInvariantGE_of_ge h]

theorem bitInvariantLT_iff_eq_one_of_ge (h : n ≤ 2^i) : a ∈ BitInvariantLT i ↔ a = 1 := by
  simp_rw [mem_bitInvariantLT_iff, mem_bitInvariantEQ_iff,
  forall_lt_bitInvariant_iff_eq_one_of_ge h]

theorem bitInvariantLT_eq_bot_of_ge (h : n ≤ 2^i) :
    (BitInvariantLT i : Subgroup (ArrayPerm n)) = ⊥ := by
  ext
  simp_rw [Subgroup.mem_bot, bitInvariantLT_iff_eq_one_of_ge h]

def bitMatchTo (x j i : ℕ) :=
  (Finset.range (2 ^ j)).filter (fun y => ∀ k < i, y.testBit k = x.testBit k)

@[simp]
theorem mem_bitMatchTo_iff {i j x q : ℕ} :
    q ∈ bitMatchTo x j i ↔ q < 2 ^ j ∧ ∀ k < i, q.testBit k = x.testBit k := by
  unfold bitMatchTo
  simp_rw [Finset.mem_filter, Finset.mem_range]

theorem bitMatchTo_antitone {x j : ℕ} : Antitone (bitMatchTo x j) := by
  intro i i' hii' q
  simp_rw [mem_bitMatchTo_iff]
  exact And.imp_right fun H _ h => H _ (h.trans_le hii')

theorem bitMatchTo_monotone {x i : ℕ} : Monotone (bitMatchTo x · i) := by
  intro j j' hjj' q
  simp_rw [mem_bitMatchTo_iff]
  exact And.imp_left fun h => h.trans_le (Nat.pow_le_pow_of_le one_lt_two hjj')

theorem bitMatchTo_zero_right : bitMatchTo x j 0 = Finset.range (2 ^ j) := by
  simp_rw [Finset.ext_iff, mem_bitMatchTo_iff, Finset.mem_range, and_iff_left_iff_imp,
  Nat.not_lt_zero, false_implies, implies_true]

theorem mem_bitMatchTo_self_mod_two_pow_of_mod_two_pow_lt_two_pow_of_le (h : x % 2^k < 2^j)
    (hik : i ≤ k) : x % 2^k ∈ bitMatchTo x j i := by
  simp_rw [mem_bitMatchTo_iff, testBit_mod_two_pow, h, true_and, Bool.and_iff_right_iff_imp,
    decide_eq_true_eq]
  exact fun _ h _ => h.trans_le hik

theorem mem_bitMatchTo_self_mod_two_pow_of_mod_two_pow_lt_two_pow (h : x % 2^i < 2 ^ j) :
    x % 2^i ∈ bitMatchTo x j i :=
  mem_bitMatchTo_self_mod_two_pow_of_mod_two_pow_lt_two_pow_of_le h le_rfl

theorem mem_bitMatchTo_self_mod_two_pow_of_size_mod_two_pow_le (h : (x % 2^i).size ≤ j) :
    x % 2^i ∈ bitMatchTo x j i :=
  mem_bitMatchTo_self_mod_two_pow_of_mod_two_pow_lt_two_pow (Nat.size_le.mp h)

theorem mem_bitMatchTo_self_of_lt_two_pow : x < 2 ^ j → x ∈ bitMatchTo x j i := by
  simp_rw [mem_bitMatchTo_iff, implies_true, and_true, imp_self]

theorem mem_bitMatchTo_self_of_size_le (h : x.size ≤ j) : x ∈ bitMatchTo x j i :=
  mem_bitMatchTo_self_of_lt_two_pow (Nat.size_le.mp h)

theorem mem_bitMatchTo_size_self : x ∈ bitMatchTo x x.size i :=
  mem_bitMatchTo_self_of_size_le le_rfl

lemma card_bitMatchInRange_le (x j i : ℕ) :
    (bitMatchTo x j i).card ≤ 2^(j - i) := by
  rw [← Fintype.card_fin (2^(j - i)), Fintype.card_congr finFunctionFinEquiv.symm,
   ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun m t => finTwoEquiv.symm (m.testBit (t + i)))
    (fun _ _ => Finset.mem_univ _) ?_
  simp_rw [Set.InjOn, Finset.mem_coe, mem_bitMatchTo_iff, and_imp, funext_iff,
    Fin.forall_iff, testBit_ext_iff]
  intros p hp hpx q hq hqx H t
  rcases lt_or_le t j with ht | ht
  · simp_rw [Equiv.apply_eq_iff_eq] at H
    rcases lt_or_le t i with htk | htk
    · rw [hpx _ htk, hqx _ htk]
    · rcases Nat.exists_eq_add_of_le' htk with ⟨_, rfl⟩
      exact H _ (Nat.lt_sub_of_add_lt ht)
  · rw [Nat.testBit_eq_false_of_lt (hq.trans_le (Nat.pow_le_pow_of_le one_lt_two ht)),
    Nat.testBit_eq_false_of_lt (hp.trans_le (Nat.pow_le_pow_of_le one_lt_two ht))]

lemma card_bitMatchInRange_le_one_of_ge (x : ℕ) (hji : j ≤ i) :
    (bitMatchTo x j i).card ≤ 1 := by
  refine (card_bitMatchInRange_le _ _ _).trans_eq ?_
  rw [Nat.sub_eq_zero_of_le hji, pow_zero]

lemma card_bitMatchInRange_eq_of_min_size_le (hj : min x.size i ≤ j) :
    (bitMatchTo x j i).card = 2^(j - i) := by
  rw [← (card_bitMatchInRange_le _ _ _).ge_iff_eq]
  rw [← Fintype.card_fin (2^(j - i)), Fintype.card_congr finFunctionFinEquiv.symm,
    ← Finset.card_univ]
  refine Finset.card_le_card_of_surjOn (fun a t => finTwoEquiv.symm (a.testBit (t + i))) ?_
  simp_rw [Set.SurjOn, Finset.coe_univ, Set.univ_subset_iff, Set.ext_iff,
    Equiv.forall_congr_left finFunctionFinEquiv, Set.mem_image, Finset.mem_coe,
    mem_bitMatchTo_iff, funext_iff, Equiv.symm_apply_eq,
    finTwoEquiv_apply, Fin.forall_iff, Nat.lt_sub_iff_add_lt, Set.mem_univ, iff_true,
    Fin.ext_iff, Fin.val_one, finFunctionFinEquiv_symm_apply_val]
  refine fun b hb => ⟨x % 2^i + 2^i*b, ?_⟩
  simp_rw [testBit_add_mul_two_pow b (Nat.mod_lt _ (Nat.two_pow_pos _)), testBit_mod_two_pow,
  add_lt_iff_neg_right, Nat.not_lt_zero, if_false, Nat.add_sub_cancel, Nat.testBit_to_div_mod,
  implies_true, and_true, ite_eq_iff, Bool.and_iff_right_iff_imp, decide_eq_true_eq,
  (and_iff_left_of_imp fun a _ => a)]
  refine ⟨?_, fun _ h => Or.inl h⟩
  · rcases le_or_lt i j with hij | hij
    · apply Nat.lt_of_div_lt_div (c := 2^i) ?_
      rwa [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)), zero_add,
      Nat.pow_div hij zero_lt_two]
    · simp_rw [min_le_iff, hij.not_le, or_false, Nat.size_le] at hj
      rw [Nat.sub_eq_zero_of_le hij.le, pow_zero, lt_one_iff] at hb
      exact hb ▸ (Nat.mod_le _ _).trans_lt hj

lemma card_bitMatchInRange_eq_of_le (x : ℕ) (hij : i ≤ j) :
    (bitMatchTo x j i).card = 2^(j - i) :=
  card_bitMatchInRange_eq_of_min_size_le (min_le_of_right_le hij)

lemma card_bitMatchInRange_eq_of_size_le (i : ℕ) (hxj : x.size ≤ j) :
    (bitMatchTo x j i).card = 2^(j - i) :=
  card_bitMatchInRange_eq_of_min_size_le (min_le_of_left_le hxj)

lemma card_bitMatchInRange_eq_of_lt_two_pow (i : ℕ) (hxj : x < 2^j) :
    (bitMatchTo x j i).card = 2^(j - i) :=
  card_bitMatchInRange_eq_of_size_le _ (Nat.size_le.mpr hxj)

theorem bitMatchTo_eq_singleton_of_mem_Icc (hj : j ∈ Set.Icc x.size i) :
    bitMatchTo x j i = {x} := by
  have H := card_bitMatchInRange_eq_of_size_le i hj.1
  rw [Nat.sub_eq_zero_of_le hj.2, pow_zero, Finset.card_eq_one] at H
  rcases H with ⟨y, hy⟩
  have HH := mem_bitMatchTo_self_of_size_le hj.1 (i := i)
  rw [hy, Finset.mem_singleton] at HH
  rwa [← HH] at hy

lemma card_bitMatchInRange_size : (bitMatchTo x x.size i).card = 2^(x.size - i) :=
  card_bitMatchInRange_eq_of_min_size_le (min_le_left _ _)

lemma card_bitMatchInRange_self : (bitMatchTo x i i).card = 1 :=
  (card_bitMatchInRange_eq_of_min_size_le (min_le_right _ _)).trans <|
    by simp_rw [Nat.sub_self, pow_zero]

theorem flipBit_mem_bitMatchTo {i j k x : ℕ} (hk : k ∈ Set.Ico i j) (q : ℕ) :
    q ∈ bitMatchTo x j i → q.flipBit k ∈ bitMatchTo x j i := by
  simp_rw [mem_bitMatchTo_iff, Nat.flipBit_lt_iff_lt (Nat.pow_dvd_pow _ hk.2)]
  simp_rw [testBit_flipBit]
  exact And.imp_right (fun hq _ hjk => by
    simp_rw [hq _ hjk, (hjk.trans_le hk.1).ne, decide_False, Bool.xor_false])

theorem cycleOf_subset_bitMatchTo {x : ℕ} (a : ArrayPerm n) (ha : ∀ k < i, a.BitInvariant k)
    (hk : x < n) (hn : n ≤ 2^j) : a.cycleOf x ⊆ bitMatchTo x j i := by
  simp_rw [Finset.subset_iff, mem_cycleOf_iff_exists_zpow, mem_bitMatchTo_iff,
    forall_exists_index, forall_apply_eq_imp_iff, ((smul_lt_iff_lt _).mpr hk).trans_le hn,
    true_and, smul_of_lt hk]
  intros _ _ hk
  simp_rw [((ha _ hk).zpow _).testBit_getElem_toArray_eq_testBit]

theorem period_le_two_pow (a : ArrayPerm n) (k : ℕ) (hin : 2 ^ (i + 1) ∣ n) (hn : n ≤ 2^(j + 1))
    (ha : ∀ k < i, a.BitInvariant k) (hij : i ≤ j) :
    MulAction.period (a.flipBitCommutator hin) k ≤ 2 ^ (j - i) := by
  rcases lt_or_le k n with hk | hk
  · trans ((bitMatchTo k (j + 1) i).card / 2)
    · apply two_mul_filter_sameCycle_card_le_card
      · exact flipBit_mem_bitMatchTo ⟨le_rfl, Nat.lt_succ_of_le hij⟩
      · exact (a.flipBitCommutator hin).cycleOf_subset_bitMatchTo
          (fun _ hl => (ha _ hl).flipBitCommutator hin) hk hn
    · rw [card_bitMatchInRange_eq_of_le _ (hij.trans <| Nat.le_succ _), Nat.succ_sub hij,
      pow_succ, Nat.mul_div_cancel _ (zero_lt_two)]
  · rw [period_eq_one_of_ge _ hk]
    exact Nat.one_le_pow _ _ zero_lt_two

lemma cycleMin_flipBit_eq_flipBit_cycleMin (hin : 2 ^ (i + 1) ∣ n) (hn : n ≤ 2^(j + 1))
    (ha : ∀ k < i, BitInvariant k a) (hij : i ≤ j) :
    (a.flipBitCommutator hin).CycleMin (j - i) (k.flipBit i) =
    ((a.flipBitCommutator hin).CycleMin (j - i) k).flipBit i := by
  rcases lt_or_le k n with hk | hk
  · have hk' := (Nat.flipBit_lt_iff_lt hin).mpr hk
    rw [cycleMin_eq_min'_cycleOf _ _ _ (period_le_two_pow _ k hin hn ha hij),
    cycleMin_eq_min'_cycleOf _ _ _ (period_le_two_pow _ (k.flipBit i) hin hn ha hij)]
    · have H := Finset.min'_mem ((a.flipBitCommutator hin).cycleOf k) nonempty_cycleOf
      simp_rw [mem_cycleOf_iff_exists_zpow, smul_of_lt hk] at H
      rcases H with ⟨p, hp⟩
      refine eq_of_le_of_not_lt ?_ ?_
      · refine Finset.min'_le _ _ ?_
        simp_rw [mem_cycleOf_iff_exists_zpow, smul_of_lt hk']
        exact ⟨-p, by simp_rw [← hp, ← a.getElem_flipBit_flipBitCommutator_zpow_inv hin hk,
          zpow_neg, getElem_flipBit]⟩
      · have H := Finset.min'_mem
          ((a.flipBitCommutator hin).cycleOf (k.flipBit i)) nonempty_cycleOf
        simp_rw [mem_cycleOf_iff_exists_zpow, smul_of_lt hk', ← getElem_flipBit _ hin hk] at H
        rcases H with ⟨q, hq⟩
        simp_rw [a.getElem_flipBit_flipBitCommutator_zpow, ← zpow_neg] at hq
        rcases (Finset.min'_le _ _ ((a.flipBitCommutator hin).getElem_zpow_mem_cycleOf k
          (-q) hk)).eq_or_lt with H | H
        · rw [H, hq]
          exact lt_irrefl _
        · rw [← hq, ← hp]
          rw [← hp] at H
          intro h
          refine getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow
            _ hin hk <| Nat.eq_flipBit_of_lt_of_flipBit_ge_of_lt_testBit_eq H h.le (fun hji => ?_)
          simp_rw [(((ha _ hji).flipBitCommutator hin).zpow p).testBit_getElem_toArray_eq_testBit,
            (((ha _ hji).flipBitCommutator hin).zpow (-(q : ℤ))).testBit_getElem_toArray_eq_testBit]
  · simp_rw [cycleMin_of_ge hk, cycleMin_of_ge <| le_of_not_lt <|
    (Nat.flipBit_lt_iff_lt hin).not.mpr hk.not_lt]


lemma blahjfoo (hin : 2 ^ (i + 1) ∣ n) (hn : n ≤ 2^(j + 1))
    (ha : ∀ k < i, BitInvariant k a) (hij : i ≤ j) :
  (a.flipBitCommutator hin).CycleMin (j - i) (k.flipBit i) =
    ((a.flipBitCommutator hin).CycleMin (j - i) k).flipBit i := by
  rcases lt_or_le k n with hk | hk
  · have hk' := (Nat.flipBit_lt_iff_lt hin).mpr hk
    rcases ((a.flipBitCommutator hin)).exists_lt_cycleMin_eq_pow_apply (j - i) k with
      ⟨p, _, hjq₂⟩
    rw [smul_of_lt hk] at hjq₂
    refine eq_of_le_of_not_lt ?_ ?_
    · rw [hjq₂, ← a.getElem_flipBit_flipBitCommutator_pow_inv, ← zpow_natCast, ← zpow_neg,
      getElem_flipBit, ← smul_of_lt hk']
      refine cycleMin_le_zpow_smul_of_period_le_two_pow _ _ ?_ _
      have H := a.two_mul_filter_sameCycle_card_le_card hin _
        (flipBit_mem_bitMatchTo _ ((j - i) + (i + 1)) _ _ ⟨le_rfl, Nat.lt_add_left _ (Nat.lt_succ_self _)⟩) _
          (blahj _ (fun _ hl => (ha _ hl).flipBitCommutator hin) hk'
          (by rwa [← add_assoc, Nat.sub_add_cancel hij]))
      refine H.trans (Nat.div_le_of_le_mul <| (card_bitMatchInRange_le _ _ _).trans ?_)
      simp_rw [← pow_succ',  Nat.add_sub_assoc (Nat.lt_succ_self _).le, succ_eq_add_one,
      add_tsub_cancel_left, le_rfl]
    · rcases ((a.flipBitCommutator hin)).exists_lt_cycleMin_eq_pow_apply (j - i) (k.flipBit i) with
        ⟨q, _, hkq₂⟩
      rw [smul_of_lt hk', ← getElem_flipBit _ hin hk,
        getElem_flipBit_flipBitCommutator_pow, ← zpow_natCast, ← zpow_neg] at hkq₂
      rcases lt_trichotomy ((a.flipBitCommutator hin) ^ (-(q : ℤ)))[k]
        ((a.flipBitCommutator hin) ^ p)[k] with H | H | H
      · rw [← hjq₂, ← not_le, ← smul_of_lt hk] at H
        refine (H <| cycleMin_le_zpow_smul_of_period_le_two_pow _ _ ?_ _).elim
        have H := a.two_mul_filter_sameCycle_card_le_card hin _
          (flipBit_mem_bitMatchTo _ ((j - i) + (i + 1)) _ _ ⟨le_rfl, Nat.lt_add_left _ (Nat.lt_succ_self _)⟩) _
            (blahj _ (fun _ hl => (ha _ hl).flipBitCommutator hin) hk
            (by rwa [← add_assoc, Nat.sub_add_cancel hij]))
        refine H.trans (Nat.div_le_of_le_mul <| (card_bitMatchInRange_le _ _ _).trans ?_)
        simp_rw [← pow_succ',  Nat.add_sub_assoc (Nat.lt_succ_self _).le, succ_eq_add_one,
        add_tsub_cancel_left, le_rfl]
      · rw [hjq₂, hkq₂, H]
        exact lt_irrefl _
      · rw [hjq₂, hkq₂]
        intro h
        rw [← zpow_natCast] at H
        refine getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow _ hin hk <|
          Nat.eq_flipBit_of_lt_of_flipBit_ge_of_lt_testBit_eq H h.le ?_
        intro j hji
        simp_rw [(((ha _ hji).flipBitCommutator hin).zpow p).testBit_getElem_toArray_eq_testBit,
          (((ha _ hji).flipBitCommutator hin).zpow (-(q : ℤ))).testBit_getElem_toArray_eq_testBit]
  · simp_rw [cycleMin_of_ge hk,
    cycleMin_of_ge (le_of_not_lt <| (Nat.flipBit_lt_iff_lt hin).not.mpr hk.not_lt)]



end ArrayPerm

namespace Submonoid

open Function Nat

def BitInvariant (i : ℕ) : Submonoid (Function.End ℕ) where
  carrier := Function.BitInvariant i
  mul_mem' := BitInvariant.comp
  one_mem' := bitInvariant_id

def BitInvariantLT (i : ℕ) : Submonoid (Function.End ℕ) := ⨅ k : ℕ, ⨅ (_ : k < i), BitInvariant k

variable {f : Function.End ℕ}

@[simp]
theorem mem_bitInvariant_iff : f ∈ BitInvariant i ↔ f.BitInvariant i := Iff.rfl

@[simp]
theorem mem_bitInvariantLT_iff : f ∈ BitInvariantLT i ↔ f.BitInvariantLT i := by
  unfold BitInvariantLT ; simp_rw [mem_iInf] ; exact Iff.rfl

theorem _root_.Function.BitInvariantLT.mem_bitInvariantLT (hf : f.BitInvariantLT i) :
    f ∈ BitInvariantLT i := mem_bitInvariantLT_iff.mpr hf

theorem bitInvariantLT_of_mem_bitInvariantLT (hf : f ∈ BitInvariantLT i) :
    f.BitInvariantLT i := mem_bitInvariantLT_iff.mp hf

@[simp]
theorem bitInvariantLT_zero : BitInvariantLT 0 = ⊤ := by
  simp_rw [Submonoid.eq_top_iff', mem_bitInvariantLT_iff,
  Function.bitInvariantLT_zero, implies_true]

theorem bitInvariantLT_le_iff_le : BitInvariantLT n ≤ BitInvariantLT m ↔ m ≤ n := by
  simp_rw [SetLike.le_def, mem_bitInvariantLT_iff]
  exact bitInvariantLT_imp_bitInvariantLT_iff_ge

theorem bitInvariantLT_strictAnti : StrictAnti BitInvariantLT :=
  strictAnti_of_le_iff_le (fun _ _ => bitInvariantLT_le_iff_le.symm)

theorem bitInvarLT_lt_iff_lt : BitInvariantLT n < BitInvariantLT m ↔ m < n :=
  bitInvariantLT_strictAnti.lt_iff_lt

def BitInvariantGE (i : ℕ) : Submonoid (Function.End ℕ) := ⨅ k : ℕ, ⨅ (_ : i ≤ k), BitInvariant k

@[simp]
theorem mem_bitInvariantGE_iff : f ∈ BitInvariantGE i ↔ f.BitInvariantGE i := by
  unfold BitInvariantGE ; simp_rw [mem_iInf] ; exact Iff.rfl

theorem _root_.Function.bitInvariantGE.mem_bitInvariantGE (hf : f.BitInvariantGE i) :
    f ∈ BitInvariantGE i := mem_bitInvariantGE_iff.mpr hf

theorem bitInvariantGE_of_mem_bitInvariantGE (hf : f ∈ BitInvariantGE i) :
    f.BitInvariantGE i := mem_bitInvariantGE_iff.mp hf

@[simp]
theorem bitInvariantGE_zero :
    BitInvariantGE 0 = ⊥ := by
  simp_rw [Submonoid.eq_bot_iff_forall, mem_bitInvariantGE_iff, bitInvariantGE_zero_iff_id]
  exact fun _ => id

theorem bitInvariantGE_le_iff_le : BitInvariantGE m ≤ BitInvariantGE n ↔ m ≤ n := by
  simp_rw [SetLike.le_def, mem_bitInvariantGE_iff]
  exact bitInvariantGE_imp_bitInvariantGE_iff_le

theorem bitInvariantGE_strictMono : StrictMono BitInvariantGE :=
    strictMono_of_le_iff_le (fun _ _ => bitInvariantGE_le_iff_le.symm)

theorem bitInvariantGE_lt_iff_lt : BitInvariantGE m < BitInvariantGE n ↔ m < n :=
  bitInvariantGE_strictMono.lt_iff_lt

theorem bitInvariantLT_inf_BitInvariantGE_eq_bot : BitInvariantLT m ⊓ BitInvariantGE m = ⊥ :=
    SetLike.ext <| fun f => by
  simp_rw [mem_bot, Submonoid.mem_inf, mem_bitInvariantGE_iff,
  mem_bitInvariantLT_iff, bitInvariantLT_and_bitInvariantGE_iff_id]
  exact Iff.rfl

theorem disjoint_bitInvariantGE_bitInvariantLT :
    Disjoint (BitInvariantLT m) (BitInvariantGE m) := by
  simp_rw [disjoint_iff]
  exact bitInvariantLT_inf_BitInvariantGE_eq_bot

theorem eq_one_of_mem_BitInvariantGE_mem_bitInvarLT (hfLT : f ∈ BitInvariantLT m)
    (hfGE : f ∈ BitInvariantGE m) : f = 1 := Submonoid.mem_bot.mp <| by
  exact bitInvariantLT_inf_BitInvariantGE_eq_bot ▸ Submonoid.mem_inf.mpr ⟨hfLT, hfGE⟩

end Submonoid

namespace Subgroup

open Equiv Function Nat

def BitInvariant (i : ℕ) : Subgroup (Perm ℕ) where
  carrier π := Function.BitInvariant i ⇑π
  mul_mem' := BitInvariant.comp
  one_mem' := bitInvariant_id
  inv_mem' := (rightInverse_symm _).bitInvariant_of_bitInvariant

def BitInvariantLT (i : ℕ) : Subgroup (Perm ℕ) := ⨅ k : ℕ, ⨅ (_ : k < i), BitInvariant k
def BitInvariantGE (i : ℕ) : Subgroup (Perm ℕ) := ⨅ k : ℕ, ⨅ (_ : i ≤ k), BitInvariant k

variable {π : Perm ℕ}

@[simp]
theorem mem_bitInvariant_iff : π ∈ BitInvariant i ↔ (⇑π).BitInvariant i := Iff.rfl

@[simp]
theorem mem_bitInvariantLT_iff : π ∈ BitInvariantLT i ↔ (⇑π).BitInvariantLT i := by
  unfold BitInvariantLT
  simp_rw [mem_iInf, mem_bitInvariant_iff, bitInvariantLT_iff]

@[simp]
theorem mem_bitInvariantGE_iff : π ∈ BitInvariantGE i ↔ (⇑π).BitInvariantGE i:= by
  unfold BitInvariantGE
  simp_rw [mem_iInf, mem_bitInvariant_iff, bitInvariantGE_iff]

theorem mem_bitInvariant_iff_coe_mem_bitInvariant :
  ∀ π, π ∈ BitInvariant i ↔ ⇑π ∈ Submonoid.BitInvariant i := fun _ => Iff.rfl

theorem mem_bitInvariantLT_iff_coe_mem_bitInvariantLT :
    ∀ π, π ∈ BitInvariantLT i ↔ ⇑π ∈ Submonoid.BitInvariantLT i := fun _ =>
  mem_bitInvariantLT_iff.trans Submonoid.mem_bitInvariantLT_iff.symm

theorem mem_bitInvariantGE_iff_coe_mem_bitInvariantGE :
    ∀ π, π ∈ BitInvariantGE i ↔ ⇑π ∈ Submonoid.BitInvariantGE i := fun _ =>
  mem_bitInvariantGE_iff.trans Submonoid.mem_bitInvariantGE_iff.symm

@[simp]
theorem bitInvariantLT_zero : BitInvariantLT 0 = ⊤ := Subgroup.ext fun _ => by
  simp_rw [mem_bitInvariantLT_iff_coe_mem_bitInvariantLT, Submonoid.bitInvariantLT_zero,
  Submonoid.mem_top, mem_top]

theorem bitInvariantLT_le_iff_le : BitInvariantLT n ≤ BitInvariantLT m ↔ m ≤ n := by
  simp_rw [SetLike.le_def, mem_bitInvariantLT_iff]
  exact ⟨fun h => (h (x := flipBitPerm _) bitInvariantLT_flipBit_of_eq).ge,
    fun hmn _ hf _ hk => hf _ (hk.trans_le hmn)⟩

theorem bitInvariantLT_strictAnti : StrictAnti BitInvariantLT :=
  strictAnti_of_le_iff_le (fun _ _ => bitInvariantLT_le_iff_le.symm)

theorem bitInvarLT_lt_iff_lt : BitInvariantLT n < BitInvariantLT m ↔ m < n :=
  bitInvariantLT_strictAnti.lt_iff_lt

@[simp]
theorem bitInvariantGE_zero :
    BitInvariantGE 0 = ⊥ := Subgroup.ext <| fun _ => by
  simp_rw [mem_bitInvariantGE_iff_coe_mem_bitInvariantGE, Submonoid.bitInvariantGE_zero,
  Submonoid.mem_bot, mem_bot, Equiv.Perm.ext_iff, funext_iff]
  exact Iff.rfl

theorem bitInvariantGE_le_iff_le : BitInvariantGE m ≤ BitInvariantGE n ↔ m ≤ n := by
  simp_rw [SetLike.le_def, mem_bitInvariantGE_iff]
  exact   ⟨fun h => le_of_not_lt fun hmn =>
    not_bitInvariantGE_flipBit_of_eq (h (x := flipBitPerm _) (bitInvariantGE_flipBit_of_lt hmn)),
  fun hmn => fun _ hf _ hk => hf _ (hmn.trans hk)⟩

theorem bitInvariantGE_strictMono : StrictMono BitInvariantGE :=
    strictMono_of_le_iff_le (fun _ _ => bitInvariantGE_le_iff_le.symm)

theorem bitInvariantGE_lt_iff_lt : BitInvariantGE m < BitInvariantGE n ↔ m < n :=
  bitInvariantGE_strictMono.lt_iff_lt

theorem bitInvariantLT_inf_BitInvariantGE_eq_bot : BitInvariantLT m ⊓ BitInvariantGE m = ⊥ :=
    SetLike.ext <| fun f => by
  simp_rw [Subgroup.mem_inf, mem_bitInvariantLT_iff_coe_mem_bitInvariantLT,
    mem_bitInvariantGE_iff_coe_mem_bitInvariantGE, ←Submonoid.mem_inf,
    Submonoid.bitInvariantLT_inf_BitInvariantGE_eq_bot (m := m),
  Submonoid.mem_bot, mem_bot, Equiv.Perm.ext_iff, funext_iff]
  exact Iff.rfl

theorem disjoint_bitInvariantGE_bitInvariantLT :
    Disjoint (BitInvariantLT m) (BitInvariantGE m) := by
  simp_rw [disjoint_iff]
  exact bitInvariantLT_inf_BitInvariantGE_eq_bot

theorem eq_one_of_mem_BitInvariantGE_mem_bitInvarLT (hfLT : f ∈ BitInvariantLT m)
    (hfGE : f ∈ BitInvariantGE m) : f = 1 := Subgroup.mem_bot.mp <| by
  exact bitInvariantLT_inf_BitInvariantGE_eq_bot ▸ Subgroup.mem_inf.mpr ⟨hfLT, hfGE⟩

end Subgroup

section Equivs

open Function Equiv Nat

variable {ff : Bool → Function.End ℕ}

def endoOfBoolArrowEndo (i : ℕ) (ff : Bool → ℕ → ℕ) : Function.End ℕ :=
  fun q => (ff (q.testBit i) (q.testRes i)).mergeBit i (q.testBit i)

@[simp]
theorem endoOfBoolArrowEndo_def :
  endoOfBoolArrowEndo i ff q = (ff (q.testBit i) (q.testRes i)).mergeBit i (q.testBit i)  := rfl

theorem endoOfBoolArrowEndo_bitInvar (ff : Bool → ℕ → ℕ) :
  (endoOfBoolArrowEndo i ff).BitInvariant i := by
  simp_rw [bitInvariant_iff, endoOfBoolArrowEndo_def, testBit_mergeBit_of_eq, implies_true]

theorem endoOfBoolArrowEndo_mem_bitInvarEQ
    (f : Bool → ℕ → ℕ) : (endoOfBoolArrowEndo i f) ∈ Submonoid.BitInvariant i :=
  endoOfBoolArrowEndo_bitInvar f

theorem endoOfBoolArrowEndo_comp (f g : Bool → ℕ → ℕ) :
  endoOfBoolArrowEndo i (fun b => (f b) ∘ (g b)) = endoOfBoolArrowEndo i f ∘ endoOfBoolArrowEndo i g
  := by simp_rw [Function.End.ext_iff, Function.comp_apply, endoOfBoolArrowEndo_def,
   testBit_mergeBit_of_eq, testRes_mergeBit_of_eq, Function.comp_apply, implies_true]

theorem endoOfBoolArrowEndo_mul (ff gg : Bool → Function.End ℕ) :
  endoOfBoolArrowEndo i (ff * gg) =
  ((endoOfBoolArrowEndo i ff : Function.End ℕ) * (endoOfBoolArrowEndo i gg : Function.End ℕ)
  : Function.End ℕ) := endoOfBoolArrowEndo_comp _ _

def boolArrowEndoOfEndo (i : ℕ) (ff : ℕ → ℕ) :
  Bool → Function.End ℕ := fun b p => (ff (p.mergeBit i b)).testRes i

@[simp]
theorem boolArrowEndoOfEndo_def {f : ℕ → ℕ} {b : Bool} {p : ℕ} :
  boolArrowEndoOfEndo i f b p = (f (p.mergeBit i b)).testRes i := rfl

theorem endoOfBoolArrowEndo_rightInverse (i : Fin (m + 1)) :
Function.RightInverse (endoOfBoolArrowEndo i) (boolArrowEndoOfEndo i) := fun f => by
  ext ; simp_rw [boolArrowEndoOfEndo_def, endoOfBoolArrowEndo_def, testBit_mergeBit_of_eq,
    testRes_mergeBit_of_eq]

theorem endoOfBoolArrowEndo_leftInvOn (i : Fin (m + 1)) :
  Set.LeftInvOn (endoOfBoolArrowEndo i) (boolArrowEndoOfEndo i) (BitInvariant i) := fun f hf => by
  ext q ; simp_rw [endoOfBoolArrowEndo_def, boolArrowEndoOfEndo_def, mergeBit_testBit_testRes_of_eq,
    mergeBit_testRes_of_eq, hf.testBit_apply_eq_testBit, Bool.xor_not_self, cond_true]

theorem boolArrowEndoOfEndo_leftInverse (i : Fin (m + 1)) :
  Function.LeftInverse (boolArrowEndoOfEndo i) (endoOfBoolArrowEndo i) :=
  endoOfBoolArrowEndo_rightInverse _

theorem boolArrowEndoOfEndo_rightInvOn (i : Fin (m + 1)) :
  Set.RightInvOn (boolArrowEndoOfEndo i) (endoOfBoolArrowEndo i) (BitInvariant i) :=
  endoOfBoolArrowEndo_leftInvOn _

@[simps!]
def bitInvarMulEquivEnd (i : Fin (m + 1)) : (Bool → Function.End ℕ) ≃* Submonoid.BitInvariant i where
  toFun feo := ⟨endoOfBoolArrowEndo i feo, endoOfBoolArrowEndo_mem_bitInvarEQ feo⟩
  invFun f := boolArrowEndoOfEndo i f.val
  left_inv := boolArrowEndoOfEndo_leftInverse i
  right_inv f := Subtype.ext (boolArrowEndoOfEndo_rightInvOn i f.prop)
  map_mul' _ _ := Subtype.ext (endoOfBoolArrowEndo_comp _ _)

def bitInvarMulEquiv (i : Fin (m + 1)) : (Bool → Equiv.Perm ℕ) ≃* Subgroup.BitInvariant i :=
  ((Equiv.Perm.equivUnitsEnd).arrowCongr (Equiv.refl _)).trans <|
  MulEquiv.piUnits.symm.trans <|
  (Units.mapEquiv (bitInvarMulEquivEnd i)).trans <|
  (Equiv.Perm.equivUnitsEnd.subgroupMulEquivUnitsType
    (Subgroup.mem_bitInvariant_iff_coe_mem_bitInvariant)).symm

@[simp]
theorem bitInvarMulEquiv_apply_coe_apply (i : Fin (m + 1))
  (πeo : Bool → Equiv.Perm ℕ) : ⇑((bitInvarMulEquiv i) πeo).val =
  endoOfBoolArrowEndo i fun b => ⇑(πeo b) := rfl

@[simp]
theorem bitInvarMulEquiv_apply_coe_symm_apply (i : Fin (m + 1))
  (πeo : Bool → Equiv.Perm ℕ) : ⇑((bitInvarMulEquiv i) πeo).val.symm =
  endoOfBoolArrowEndo i fun b => ⇑(πeo b)⁻¹ := rfl

@[simp]
theorem bitInvarMulEquiv_symm_apply_apply (i : Fin (m + 1)) (π : ↥(Subgroup.BitInvariant i)):
  ⇑(((bitInvarMulEquiv i).symm) π b) = boolArrowEndoOfEndo i (⇑π.val) b := rfl

@[simp]
theorem bitInvarMulEquiv_symm_apply_symm_apply (i : Fin (m + 1)) (π : ↥(Subgroup.BitInvariant i)):
  ⇑(((bitInvarMulEquiv i).symm) π b).symm = boolArrowEndoOfEndo i (⇑π⁻¹.val) b := rfl

-- Extra theorems

theorem endoOfBoolArrowEndo_leftInverse_apply
  {f g : Bool → ℕ → ℕ}
  (hfg : ∀ b : Bool, (Function.LeftInverse (f b) (g b))) :
  Function.LeftInverse (endoOfBoolArrowEndo i f) (endoOfBoolArrowEndo i g) := fun q => by
  simp_rw [endoOfBoolArrowEndo_def, testBit_mergeBit_of_eq, testRes_mergeBit_of_eq,
    hfg (q.testBit i) (q.testRes i), mergeBit_testBit_testRes_of_eq]

theorem endoOfBoolArrowEndo_rightInverse_apply
  {f g : Bool → ℕ → ℕ}
  (hfg : ∀ b : Bool, (Function.RightInverse (f b) (g b))) :
  Function.RightInverse (endoOfBoolArrowEndo i f) (endoOfBoolArrowEndo i g) :=
  endoOfBoolArrowEndo_leftInverse_apply hfg

theorem boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarLeft
  {f g: Function.End ℕ} (hfg : Function.LeftInverse f g) (hf : f.BitInvariant i)
  {b : Bool} : Function.LeftInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  fun q => by
    simp_rw [boolArrowEndoOfEndo_def,
    (hfg.bitInvariant_of_bitInvariant hf).mergeBit_testRes_apply_mergeBit,
    hfg (q.mergeBit i b), testRes_mergeBit_of_eq]

theorem boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarLeft
  {f g: Function.End ℕ} (hfg : Function.RightInverse f g) (hf : f.BitInvariant i)
  {b : Bool} : Function.RightInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  fun q => by
    simp_rw [boolArrowEndoOfEndo_def, hf.mergeBit_testRes_apply_mergeBit,
    hfg (q.mergeBit i b), testRes_mergeBit_of_eq]

theorem boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarRight
  {f g: Function.End ℕ} (hfg : Function.LeftInverse f g) (hg : g.BitInvariant i)
  {b : Bool} : Function.LeftInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarLeft hfg hg

theorem boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarRight
  {f g: Function.End ℕ} (hfg : Function.RightInverse f g) (hg : g.BitInvariant i)
  {b : Bool} : Function.RightInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarLeft hfg hg

theorem boolArrowEndoOfEndo_comp_ofBitInvarRight
  {f g: Function.End ℕ} (hg : g.BitInvariant i) {b : Bool} :
  boolArrowEndoOfEndo i (f ∘ g) b = boolArrowEndoOfEndo i f b ∘ boolArrowEndoOfEndo i g b := by
  ext ; simp_rw [boolArrowEndoOfEndo_def, Function.comp_apply, boolArrowEndoOfEndo_def,
  hg.mergeBit_testRes_apply_mergeBit]

theorem boolArrowEndoOfEndo_mul_ofBitInvarRight
  {f g: Function.End ℕ} (hg : g.BitInvariant i) :
  boolArrowEndoOfEndo i (f * g) = boolArrowEndoOfEndo i f * boolArrowEndoOfEndo i g := by
  ext : 1 ; exact boolArrowEndoOfEndo_comp_ofBitInvarRight hg

end Equivs

end BitInvariant

section Equivs

open Fin

/-

theorem bitInvarMulEquiv_zero_apply_condFlipBits (c : BV (m + 1) → Bool) (i : Fin (m + 1)) :
    (bitInvarMulEquiv 0) (fun b => condFlipBitPerm (fun p => c (p.mergeBit 0 b)) i) =
    condFlipBit (i.succ) c :=
  Equiv.ext (fun _ => condFlipBit_succ_apply ▸ rfl)

theorem bitInvarMulEquiv_zero_apply_condFlipBits_one (c : BV (m + 1) → Bool) :
    (bitInvarMulEquiv 0) (fun b => condFlipBit 0 (fun p => c (mergeBit 0 b p))) =
    condFlipBit 1 c :=
  bitInvarMulEquiv_zero_apply_condFlipBits _ 0

theorem bitInvarMulEquiv_apply_condFlipBits (c) (i : Fin (m + 1)) (j : Fin (m + 2)) :
    (bitInvarMulEquiv j) (fun b => condFlipBit i (fun p => c (mergeBit (i.predAbove j) b p))) =
    condFlipBit (j.succAbove i) c :=
  Equiv.ext (fun _ => condFlipBit_succAbove_apply ▸ rfl)

theorem bitInvarMulEquiv_last_apply_condFlipBits (c) (i : Fin (m + 1)) :
    (bitInvarMulEquiv (Fin.last _)) (fun b => condFlipBit i
    (fun p => c (mergeBit (Fin.last _) b p))) =
    condFlipBit (i.castSucc) c := by
  rw [← Fin.predAbove_right_last (i := i), bitInvarMulEquiv_apply_condFlipBits, Fin.succAbove_last]
-/

end Equivs

/-



namespace Fin

notation:75 "BV " arg:75  => Fin (2^arg)

section BitRes

variable {m : ℕ} {i : Fin (m + 1)} {q : BV (m + 1)} {p : BV m}

def testBit (q : BV (m + 1)) (i : Fin (m + 1)) := (q : ℕ).testBit i

@[simps!]
def testRes (q : BV (m + 1)) (i : Fin (m + 1)) : BV m where
  val := (q : ℕ).testRes i
  isLt := (Nat.testRes_lt_two_pow_iff_lt_two_pow i.is_le).mpr q.is_lt

@[simps!]
def mergeBit (p : BV m) (i : Fin (m + 1)) (b : Bool) : BV (m + 1) where
  val := (p : ℕ).mergeBit i b
  isLt := (Nat.mergeBit_lt_two_pow_iff_lt_two_pow i.is_le).mpr p.is_lt

@[pp_nodot, simps!]
def testBitRes (i : Fin (m + 1)) : BV (m + 1) ≃ Bool × BV m where
  toFun q := (q.testBit i, q.testRes i)
  invFun bp := bp.2.mergeBit i bp.1
  left_inv _ := Fin.ext Nat.mergeBit_testBit_testRes_of_eq
  right_inv _ := Prod.ext Nat.testBit_mergeBit_of_eq (Fin.ext Nat.testRes_mergeBit_of_eq)

@[simp]
theorem testBit_def : testBit q i = q.val.testBit i := rfl

theorem testRes_def : testRes q i = ⟨(q : ℕ).testRes i, (q.testRes i).2⟩ := rfl

theorem mergeBit_def : mergeBit p i b = ⟨(p : ℕ).mergeBit i b, (mergeBit p i b).2⟩ := rfl

@[simp]
theorem testRes_mergeBit_of_eq : (p.mergeBit i b).testRes i = p := Fin.ext <| by
  rw [testRes_val, mergeBit_val, Nat.testRes_mergeBit_of_eq]

@[simp]
theorem testBit_mergeBit_of_eq : (p.mergeBit i b).testBit i = b := by
  rw [testBit_def, mergeBit_val, Nat.testBit_mergeBit_of_eq]

@[simp]
lemma mergeBit_testBit_testRes_of_eq :
    (q.testRes i).mergeBit i (q.testBit i) = q := Fin.ext <| by
  rw [testBit_def, mergeBit_val, testRes_val, Nat.mergeBit_testBit_testRes_of_eq]

end BitRes

section FlipBit

variable {m : ℕ} {i : Fin m} {q : BV m}

@[simps!]
def flipBit (q : BV m) (i : Fin m) : BV m where
  val := q.val.flipBit i.val
  isLt := (Nat.flipBit_lt_two_pow_iff_lt_two_pow i.isLt).mpr q.isLt

theorem flipBit_base {i} : ∀ q, flipBit (m := 1) q i = Equiv.swap 0 1 q := by
  simp_rw [Fin.ext_iff, flipBit_val, Fin.eq_zero i]
  exact Fin.forall_fin_two.mpr ⟨rfl, rfl⟩

@[pp_nodot, simps! apply symm_apply]
def flipBitPerm (i : Fin m) : Equiv.Perm (BV m) where
  toFun := (flipBit · i)
  invFun := (flipBit · i)
  left_inv _ := by simp_rw [Fin.ext_iff, flipBit_val, Nat.flipBit_flipBit_of_eq]
  right_inv _ := by simp_rw [Fin.ext_iff, flipBit_val, Nat.flipBit_flipBit_of_eq]

theorem flipBitPerm_base {i} : flipBitPerm (m := 1) i = Equiv.swap 0 1 := by
  simp_rw [Equiv.ext_iff, flipBitPerm_apply]
  exact flipBit_base

end FlipBit

section CondFlipBit

@[simps!]
def condFlipBit (q : BV (m + 1)) (i : Fin (m + 1)) (c : BV m → Bool) : BV (m + 1) where
  val := q.val.condFlipBit i.val (Array.ofFn c)
  isLt := (Nat.condFlipBit_lt_two_pow_iff_lt_two_pow i.isLt).mpr q.isLt

variable {m : ℕ} {i : Fin (m + 1)} {q : BV (m + 1)} {p : BV m}

theorem condFlipBit_apply : q.condFlipBit i c = bif c (q.testRes i) then q.flipBit i else q := by
  simp_rw [Fin.ext_iff, Bool.apply_cond (Fin.val), condFlipBit_val, flipBit_val,
    Nat.condFlipBit_apply_of_testRes_lt
    ((testRes_val _ _ ▸ Fin.is_lt _).trans_eq (Array.size_ofFn _).symm), Array.getElem_ofFn]
  congr

theorem condFlipBit_base {i q} : condFlipBit (m := 0) q i c =
    bif c 0 then Equiv.swap 0 1 q else q := by
  simp_rw [condFlipBit_apply, Fin.eq_zero, flipBit_base]

theorem condFlipBit_eq_mergeBit : q.condFlipBit i c =
    (q.testRes i).mergeBit i ((c (q.testRes i)).xor (q.testBit i))  := by
  ext
  simp only [condFlipBit_val, Nat.condFlipBit_eq_mergeBit, testBit_def, mergeBit_val,
    testRes_val]
  refine congrArg _ (congrArg₂ _ ?_ rfl)
  simp_rw [Array.getD_eq_get, Array.size_ofFn,
    Nat.testRes_lt_two_pow_iff_lt_two_pow i.is_le, q.is_lt]
  exact Array.getElem_ofFn _ _ _

theorem condFlipBit_mergeBit : (p.mergeBit i b).condFlipBit i c = p.mergeBit i ((c p).xor b) := by
  simp only [condFlipBit_eq_mergeBit, Fin.ext_iff, testRes_def, mergeBit_val,
    Nat.testRes_mergeBit_of_eq, Fin.eta, testBit_def, Nat.testBit_mergeBit_of_eq]

@[simp]
theorem condFlipBit_condFlipBit : (q.condFlipBit i c).condFlipBit i c = q := by
  simp_rw [Fin.ext_iff, condFlipBit_val, Nat.condFlipBit_condFlipBit_of_eq]

theorem condFlipBit_flipBit_of_all_true : q.flipBit i = q.condFlipBit i (Function.const _ true) := by
  rw [condFlipBit_apply, Function.const_apply, cond_true]

theorem condFlipBit_refl_of_all_false : q = q.condFlipBit i (Function.const _ false) := by
  rw [condFlipBit_apply, Function.const_apply, cond_false]

theorem condFlipBit_apply_comm :
(q.condFlipBit i d).condFlipBit i c = (q.condFlipBit i c).condFlipBit i d := by
simp_rw [condFlipBit_eq_mergeBit, testRes_mergeBit_of_eq,
  testBit_mergeBit_of_eq, Bool.xor_left_comm]

@[pp_nodot, simps! apply symm_apply]
def condFlipBitPerm (c : BV m → Bool) (i : Fin (m + 1)) : Equiv.Perm (BV (m + 1)) where
  toFun := (condFlipBit · i c)
  invFun := (condFlipBit · i c)
  left_inv _ := by simp_rw [Fin.ext_iff, condFlipBit_val, Nat.condFlipBit_condFlipBit_of_eq]
  right_inv _ := by simp_rw [Fin.ext_iff, condFlipBit_val, Nat.condFlipBit_condFlipBit_of_eq]

theorem condFlipBitPerm_base {i} : condFlipBitPerm (m := 0) c i =
    bif c 0 then Equiv.swap 0 1 else 1 := Equiv.ext <| fun _ => by
  simp_rw [condFlipBitPerm_apply, condFlipBit_base]
  rcases (c 0) <;> rfl

@[simp]
theorem condFlipBitPerm_symm : (condFlipBitPerm c i).symm = condFlipBitPerm c i := rfl

@[simp]
theorem condFlipBitPerm_inv : (condFlipBitPerm c i)⁻¹ = condFlipBitPerm c i := rfl

end CondFlipBit

end Fin
-/

/-
theorem condFlipBit_comm :
(condFlipBit i c) * (condFlipBit i d) = (condFlipBit i d) * (condFlipBit i c) := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, condFlipBit_apply_comm]

theorem condFlipBit_apply_comm_flipBit :
  condFlipBit i c (q.flipBit i) = flipBit i (condFlipBit i c q) := by
  rw [condFlipBit_flipBit_of_all_true, condFlipBit_apply_comm]

theorem condFlipBit_comm_flipBit :
  (condFlipBit i c) * (flipBit i) = (flipBit i) * (condFlipBit i c) := by
  rw [condFlipBit_flipBit_of_all_true, condFlipBit_comm]

theorem condFlipBit_apply_flipBit :
condFlipBit i c (q.flipBit i) = bif c (q.testRes i) then q else q.flipBit i := by
  rw [condFlipBit_apply_comm_flipBit]
  rcases (c (q.testRes i)).dichotomy with h | h <;> rw [condFlipBit_apply, h]
  · simp_rw [cond_false]
  · simp_rw [cond_true, flipBit_flipBit]


@[simp]
theorem testRes_condFlipBit : testRes i (condFlipBit i c q) = q.testRes i := by
rcases (c (q.testRes i)).dichotomy with h | h  <;> rw [condFlipBit_apply, h]
· rfl
· rw [cond_true, testRes_flipBit_of_eq]

theorem testBit_condFlipBit : testBit i (condFlipBit i c q) =
bif c (q.testRes i) then !(testBit q i) else testBit q i := by
rcases (c (q.testRes i)).dichotomy with hc | hc <;>
simp only [condFlipBit_apply, cond_false, hc, cond_true, testBit_flipBit_of_eq]

theorem testBit_condFlipBit' : testBit i (condFlipBit i c q) =
xor (c (q.testRes i)) (testBit q i) := by
rcases (c (q.testRes i)).dichotomy with hc | hc <;>
simp only [condFlipBit_apply, hc, cond_false, cond_true,
  Bool.false_xor, Bool.true_xor, testBit_flipBit_of_eq]

theorem testBit_condFlipBit'' : testBit i (condFlipBit i c q) =
bif (testBit q i) then !(c (q.testRes i)) else c (q.testRes i) := by
rcases (testBit q i).dichotomy with hc | hc <;>
simp only [testBit_condFlipBit', hc, Bool.xor_false, Bool.xor_true, cond_true, cond_false]

theorem testBit_condFlipBit_of_ne {i j : Fin (m + 1)} (hij: i ≠ j):
  testBit i ((condFlipBit j c) q) = testBit q i := by
  rw [condFlipBit_apply]
  rcases (c (testRes j q)).dichotomy with (h | h) <;> simp_rw [h]
  · rw [cond_false]
  · rw [cond_true, testBit_flipBit_of_ne hij]

theorem condFlipBit_bitInvar_of_ne {i j : Fin (m + 1)} (h : i ≠ j) : bitInvar i ⇑(condFlipBit j c) :=
  bitInvar_of_testBit_def_eq_testBit (fun _ => testBit_condFlipBit_of_ne h)

theorem condFlipBit_succ_apply {i : Fin (m + 1)} : condFlipBit (Fin.succ i) c q =
    mergeBit 0 (testBit 0 q) ((condFlipBit i fun p =>
    c (mergeBit 0 (testBit 0 q) p)) (testRes 0 q)) := by
    simp_rw [condFlipBit_eq_mergeBit, mergeBit_succ, testRes_succ, testBit_succ,
    testBit_mergeBit, testRes_mergeBit]

theorem condFlipBit_succAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
  condFlipBit (j.succAbove i) c q =
    mergeBit j (testBit j q) ((condFlipBit i fun p =>
    c (mergeBit (i.predAbove j) (testBit j q) p)) (testRes j q)) := by
    simp_rw [condFlipBit_apply, testRes_succAbove,
    Bool.apply_cond (fun x => mergeBit j (testBit j q) x), mergeBit_testBit_testRes,
    flipBit_succAbove]

theorem condFlipBit_zero_apply : condFlipBit 0 c q =
  bif c (q.divNat) then
  finProdFinEquiv (q.divNat, q.modNat.rev)
  else q := by
  rw [condFlipBit_apply, flipBit_zero_apply, testRes_zero]

theorem condFlipBit_zero_mergeBit :
condFlipBit 0 c (mergeBit 0 b p) = finProdFinEquiv (p, bif xor (c p) b then 1 else 0) := by
  simp_rw [condFlipBit_mergeBit, mergeBit_zero]

theorem condFlipBit_zero_mergeBit_true  :
condFlipBit 0 c (mergeBit 0 true p) = finProdFinEquiv (p, bif c p then 0 else 1) := by
  simp_rw [condFlipBit_zero_mergeBit, Bool.xor_true, Bool.cond_not]

theorem condFlipBit_zero_mergeBit_false :
condFlipBit 0 c (mergeBit 0 false p) = finProdFinEquiv (p, bif c p then 1 else 0) := by
  simp_rw [condFlipBit_zero_mergeBit, Bool.xor_false]

/-
@[simp]
theorem condFlipBit_mul_self : (condFlipBit i c) * (condFlipBit i c) = 1 := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply,
  condFlipBit_condFlipBit, Equiv.Perm.coe_one, id_eq]

@[simp]
theorem condFlipBit_mul_cancel_right : ρ * (condFlipBit i c) * (condFlipBit i c) = ρ := by
  rw [mul_assoc, condFlipBit_mul_self, mul_one]

@[simp]
theorem condFlipBit_mul_cancel_left : (condFlipBit i c) * ((condFlipBit i c) * ρ) = ρ := by
  rw [← mul_assoc, condFlipBit_mul_self, one_mul]
-/



-/
