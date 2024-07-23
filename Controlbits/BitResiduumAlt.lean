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

section DivMod

theorem divMod_ext_iff {x y : ℕ} (d : ℕ) : x = y ↔ x / d = y / d ∧ x % d = y % d := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp_rw [Nat.div_zero, mod_zero, true_and]
  · haveI : NeZero d := ⟨hd⟩
    rw [← (Nat.divModEquiv d).apply_eq_iff_eq]
    simp_rw [divModEquiv_apply, Prod.mk.injEq, Fin.ext_iff, Fin.val_natCast]

end DivMod

section TestBit

theorem lt_pow_two_iff_ge_imp_testBit_eq_false {n : Nat} {x : Nat} :
    x < 2 ^ n ↔ ∀ (i : Nat), i ≥ n → x.testBit i = false := by
  refine' ⟨fun h _ hn => testBit_eq_false_of_lt (h.trans_le (Nat.pow_le_pow_of_le one_lt_two hn)),
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
  refine' (nat_eq_testBit_sum_range ha).trans (tsum_eq_sum _).symm
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

-- testRes inequalities

theorem lt_iff_testRes_lt (hi : i ≤ m) : q < 2^(m + 1) ↔ q.testRes i < 2^m := by
  rw [testRes_apply]
  refine' ⟨fun _ => _, lt_imp_lt_of_le_imp_le (fun _ => _)⟩
  · have h : 2 ^ i * (q / 2 ^ (i + 1)) ≤ 2^m - 2^i := by
      rw [← Nat.add_sub_cancel' hi, pow_add _ i (m - i), ← Nat.mul_pred, ]
      refine' Nat.mul_le_mul_left _ (Nat.le_pred_of_lt (Nat.div_lt_of_lt_mul _))
      rwa [mul_comm, ← pow_add, ← add_assoc, Nat.sub_add_cancel hi]
    exact (add_lt_add_of_le_of_lt h (Nat.mod_lt _ (Nat.two_pow_pos _))).trans_eq <|
      Nat.sub_add_cancel (Nat.pow_le_pow_of_le one_lt_two hi)
  · have h : 2 ^ m ≤ 2 ^ i * 2 ^ (m - i) + 0 := by rw [add_zero, ← pow_add, Nat.add_sub_cancel' hi]
    refine' h.trans (Nat.add_le_add (Nat.mul_le_mul_left _
      ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr _)) (Nat.zero_le _))
    rwa [← pow_add, ← add_assoc, Nat.sub_add_cancel hi]

theorem le_testRes_iff_ge (hi : i ≤ m) : 2^m ≤ q.testRes i ↔ 2^(m + 1) ≤ q := by
  simp_rw [← not_lt, lt_iff_testRes_lt hi]

-- testBit_testRes

theorem testBit_testRes_of_lt {i j q : ℕ} (hij : i < j) : (q.testRes j).testBit i = q.testBit i := by
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

-- mergeBit inequalities

theorem lt_iff_mergeBit_lt (hi : i ≤ m) : p < 2^m ↔ p.mergeBit i b < 2^(m + 1) := by
  rw [lt_iff_testRes_lt hi, testRes_mergeBit_of_eq]

theorem le_mergeBit_iff_le (hi : i ≤ m) : 2^(m + 1) ≤ p.mergeBit i b ↔ 2^m ≤ p := by
  rw [← le_testRes_iff_ge hi, testRes_mergeBit_of_eq]

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

@[simp]
theorem testBit_flipBit_of_eq {q : ℕ} : (q.flipBit i).testBit i = !(q.testBit i) := by
  simp_rw [flipBit_def, testBit_xor, testBit_shiftLeft, le_rfl,
    decide_true_eq_true, Bool.true_and, Nat.sub_self, testBit_one_zero, Bool.xor_true]

theorem testBit_flipBit_of_ne {i j q : ℕ} (hij : i ≠ j) :
    (q.flipBit j).testBit i = q.testBit i := by
  simp_rw [flipBit_def, testBit_xor, testBit_shiftLeft]
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [hij.not_le, decide_false_eq_false, Bool.false_and, Bool.xor_false]
  · simp_rw [testBit_one, Nat.sub_eq_zero_iff_le, hij.not_le, decide_false_eq_false,
    Bool.and_false, Bool.xor_false]

theorem testBit_flipBit {q : ℕ} : (q.flipBit j).testBit i = (q.testBit i).xor (i = j) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testBit_flipBit_of_eq, decide_true_eq_true, Bool.xor_true]
  · simp_rw [testBit_flipBit_of_ne hij, hij, decide_false_eq_false, Bool.xor_false]

-- representations of flipBit

theorem flipBit_eq_mergeBit {i q : ℕ} :
    q.flipBit i = (q.testRes i).mergeBit i (!(testBit q i))  := by
  simp_rw [testBit_ext_iff]
  intro j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [testBit_flipBit_of_ne hij.ne', testBit_mergeBit_of_gt hij, testBit_pred_testRes_of_gt hij]
  · rw [testBit_flipBit_of_eq, testBit_mergeBit_of_eq]
  · rw [testBit_flipBit_of_ne hij.ne, testBit_mergeBit_of_lt hij, testBit_testRes_of_lt hij]

theorem flipBit_eq_cond {i q : ℕ} : q.flipBit i = bif testBit q i then q - 2^i else q + 2^i := by
  rw [flipBit_eq_mergeBit, mergeBit_not_testBit_testRes_of_eq]

-- flipBit inequality

theorem lt_iff_flipBit_lt {q m : ℕ} (hi : i < m) : q < 2^m ↔ q.flipBit i < 2^m := by
  cases' m with m
  · exact (not_lt_zero _ hi).elim
  · rw [Nat.lt_succ_iff] at hi
    simp_rw [flipBit_eq_mergeBit, lt_iff_testRes_lt hi, testRes_mergeBit_of_eq]

-- flipBit_testRes

theorem flipBit_testRes_of_lt {q : ℕ} (hij : i < j):
    (q.testRes j).flipBit i = (q.flipBit i).testRes j := by
  simp_rw [flipBit_eq_mergeBit, testRes_testRes_of_lt hij, testBit_testRes_of_lt hij,
  testRes_mergeBit_of_gt hij]

theorem flipBit_testRes_of_ge {q : ℕ} (hij : j ≤ i):
    (q.testRes j).flipBit i = (q.flipBit (i + 1)).testRes j := by
  simp_rw [flipBit_eq_mergeBit, testRes_testRes_of_ge hij, testBit_testRes_of_ge hij,
  mergeBit_testRes_of_ge hij]

theorem flipBit_testRes {q : ℕ} :
    (q.testRes j).flipBit i = (q.flipBit (i + (decide (j ≤ i)).toNat)).testRes j := by
  rcases lt_or_le i j with hij | hij
  · simp_rw [flipBit_testRes_of_lt hij, hij.not_le, decide_false_eq_false, Bool.toNat_false, add_zero]
  · simp_rw [flipBit_testRes_of_ge hij, hij, decide_true_eq_true, Bool.toNat_true]

-- testRes_flipBit

theorem testRes_flipBit_of_gt {q : ℕ} (hij : j < i):
    (q.flipBit j).testRes i = (q.testRes i).flipBit j := (flipBit_testRes_of_lt hij).symm

theorem testRes_flipBit_of_lt {q : ℕ} (hij : i < j):
    (q.flipBit j).testRes i = (q.testRes i).flipBit (j - 1) := by
  rw [flipBit_testRes_of_ge (Nat.le_sub_one_of_lt hij), Nat.sub_add_cancel (one_le_of_lt hij)]

theorem testRes_flipBit_of_ne {q : ℕ} (hij : i ≠ j) :
    (q.flipBit j).testRes i = (q.testRes i).flipBit (j - (decide (i < j)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [testRes_flipBit_of_lt hij, hij, not_lt_of_lt, decide_false_eq_false, Bool.toNat_false,
    add_zero, decide_true_eq_true, Bool.toNat_true]
  · simp only [testRes_flipBit_of_gt hij, hij, decide_true_eq_true, Bool.toNat_true, not_lt_of_lt,
    decide_false_eq_false, Bool.toNat_false, Nat.sub_zero]

@[simp]
theorem testRes_flipBit_of_eq {q : ℕ} :
    (q.flipBit i).testRes i = q.testRes i := by
  rw [flipBit_eq_mergeBit, testRes_mergeBit_of_eq]

theorem testRes_flipBit {q : ℕ} : (q.flipBit j).testRes i = bif i = j then q.testRes i else
    (q.testRes i).flipBit (j - (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testRes_flipBit_of_eq, decide_true_eq_true, cond_true]
  · simp_rw [testRes_flipBit_of_ne hij, hij, decide_false_eq_false, cond_false]

-- flipBit_mergeBit

theorem flipBit_mergeBit_of_eq {p : ℕ} : (p.mergeBit i b).flipBit i = p.mergeBit i (!b) := by
  rw [flipBit_eq_mergeBit, testBit_mergeBit_of_eq, testRes_mergeBit_of_eq]

theorem flipBit_mergeBit_of_lt {p : ℕ} (hij : i < j) :
    (p.mergeBit j b).flipBit i = (p.flipBit i).mergeBit j b := by
  rw [flipBit_eq_mergeBit, flipBit_eq_mergeBit, testBit_mergeBit_of_lt hij,
  testRes_mergeBit_of_lt hij, mergeBit_mergeBit_pred_of_lt hij]

theorem flipBit_mergeBit_of_gt {p : ℕ} (hij : j < i) :
    (p.mergeBit j b).flipBit i = (p.flipBit (i - 1)).mergeBit j b := by
  rw [flipBit_eq_mergeBit, flipBit_eq_mergeBit, testBit_mergeBit_of_gt hij,
  testRes_mergeBit_of_gt hij, mergeBit_mergeBit_pred_of_lt hij]

theorem flipBit_mergeBit_of_ne {p : ℕ} (hij : i ≠ j) :
    (p.mergeBit j b).flipBit i = (p.flipBit (i - (decide (j < i)).toNat)).mergeBit j b := by
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [flipBit_mergeBit_of_lt hij, hij.not_lt, decide_false_eq_false, Bool.toNat_false,
    Nat.sub_zero]
  · simp_rw [flipBit_mergeBit_of_gt hij, hij, decide_true_eq_true, Bool.toNat_true]

theorem flipBit_mergeBitRes {p : ℕ}:
    (p.mergeBit j b).flipBit i = if i = j then p.mergeBit i (!b) else
    (p.flipBit (i - (decide (j < i)).toNat)).mergeBit j b := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [flipBit_mergeBit_of_eq, if_true]
  · simp_rw [flipBit_mergeBit_of_ne hij, hij, if_false]

-- properties of flipBit

@[simp]
theorem flipBit_flipBit_of_eq {q : ℕ} : (q.flipBit i).flipBit i  = q := by
  simp_rw [flipBit_def, Nat.xor_cancel_right]

@[simp]
theorem flipBit_ne_self : ∀ q : ℕ, q.flipBit i ≠ q := by
  simp_rw [ne_eq, testBit_ext_iff, not_forall]
  exact fun _ => ⟨i, by simp_rw [testBit_flipBit_of_eq, Bool.not_eq_self, not_false_eq_true]⟩

theorem testBit_eq_false_true_of_lt_of_flipBit_ge {q r : ℕ} (hrq : r < q)
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

theorem flipBit_div_eq {i q : ℕ} (h : i < k) : q.flipBit i / 2^k = q / 2^k := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow,
  testBit_flipBit_of_ne (h.trans_le (Nat.le_add_right _ _)).ne', implies_true]

theorem testBit_eq_of_le_of_flipBit_lt_ge {q r : ℕ} (hrq : r ≤ q)
    (hf : q.flipBit i ≤ r.flipBit i) (hik : i < k) : r.testBit k = q.testBit k := by
  simp_rw [testBit_to_div_mod, decide_eq_decide]
  suffices hs : r / 2^k = q / 2 ^ k by rw [hs]
  refine' le_antisymm (Nat.div_le_div_right hrq) _
  rw [← flipBit_div_eq hik, ← flipBit_div_eq (q := r) hik]
  exact Nat.div_le_div_right hf

theorem testBit_eq_flipBit_testBit_of_le_of_flipBit_le_ge {q r : ℕ} (hrq : r < q)
    (hf : q.flipBit i ≤ r.flipBit i) (hik : i ≤ k) : r.testBit k = (q.flipBit i).testBit k := by
  rcases hik.lt_or_eq with hik | rfl
  · rw [testBit_flipBit_of_ne hik.ne']
    exact testBit_eq_of_le_of_flipBit_lt_ge hrq.le hf hik
  · simp_rw [testBit_flipBit_of_eq, Bool.eq_not_iff,
    testBit_eq_false_true_of_lt_of_flipBit_ge hrq hf]
    exact Bool.false_ne_true

theorem eq_flipBit_of_lt_of_flipBit_ge_of_lt_testBit_eq {q r : ℕ} (hrq : r < q)
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
theorem flipBitPerm_inv_apply : ∀ (i x : ℕ), (flipBitPerm i)⁻¹ x = x.flipBit i := fun _ _ => rfl

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

theorem condFlipBit_apply_of_testRes_lt {q : ℕ} (h : q.testRes i < c.size) :
    q.condFlipBit i c = bif c[q.testRes i] then q.flipBit i else q := by
  unfold condFlipBit
  rw [c.getElem?_lt h, Option.getD_some]
  rcases c[q.testRes i]
  · rw [cond_false, Bool.toNat_false, zero_shiftLeft, xor_zero]
  · rw [cond_true, Bool.toNat_true, flipBit_def]

theorem condFlipBit_apply_of_le_testRes {q : ℕ} {c : Array Bool} (h : c.size ≤ q.testRes i) :
    q.condFlipBit i c = q := by
  unfold condFlipBit
  rw [c.getElem?_ge h, Option.getD_none, Bool.toNat_false, zero_shiftLeft, xor_zero]

theorem condFlipBit_apply {q : ℕ} :
    q.condFlipBit i c = bif c[q.testRes i]?.getD false then q.flipBit i else q := by
  rcases lt_or_le (q.testRes i) c.size with h | h
  · rw [condFlipBit_apply_of_testRes_lt h, c.getElem?_lt h, Option.getD_some]
  · rw [condFlipBit_apply_of_le_testRes h, c.getElem?_ge h, Option.getD_none, Bool.cond_false]

theorem testRes_condFlipBit_of_eq {q : ℕ} : (q.condFlipBit i c).testRes i = q.testRes i := by
  rw [condFlipBit_apply, Bool.apply_cond (testRes · i), testRes_flipBit_of_eq, Bool.cond_self]

theorem testBit_condFlipBit_of_ne {q : ℕ} (hij : i ≠ j) :
    (q.condFlipBit j c).testBit i = q.testBit i := by
  rw [condFlipBit_apply, Bool.apply_cond (testBit · i), testBit_flipBit_of_ne hij, Bool.cond_self]

theorem testBit_condFlipBit_of_eq {q : ℕ} :
    (q.condFlipBit i c).testBit i = (c[q.testRes i]?.getD false).xor (q.testBit i) := by
  rw [condFlipBit_apply, Bool.apply_cond (testBit · i), testBit_flipBit_of_eq]
  rcases (c[q.testRes i]?.getD false)
  · rw [cond_false, Bool.xor, Bool.false_xor]
  · rw [cond_true, Bool.xor, Bool.true_xor]

theorem testBit_condFlipBit_of_le_testRes {q : ℕ} (h : c.size ≤ q.testRes i) :
    (q.condFlipBit i c).testBit j = q.testBit j := by
  rw [condFlipBit_apply_of_le_testRes h]

theorem testBit_condFlipBit_of_testRes_lt_of_eq {q : ℕ} (h : q.testRes i < c.size) :
  (q.condFlipBit i c).testBit i = (c[q.testRes i]).xor (q.testBit i) := by
  rw [testBit_condFlipBit_of_eq, c.getElem?_lt h, Option.getD_some]

theorem condFlipBit_apply_eq_mergeBit {q : ℕ} : q.condFlipBit i c =
    (q.testRes i).mergeBit i ((c[q.testRes i]?.getD false).xor (q.testBit i)) := by
  simp_rw [eq_mergeBit_iff, testRes_condFlipBit_of_eq, testBit_condFlipBit_of_eq, true_and]

theorem condFlipBit_apply_comm {q : ℕ} :
(q.condFlipBit i d).condFlipBit i c = (q.condFlipBit i c).condFlipBit i d := by
simp_rw [condFlipBit_apply_eq_mergeBit, testRes_mergeBit_of_eq,
  testBit_mergeBit_of_eq, Bool.xor_left_comm]

theorem condFlipBit_mergeBit {p : ℕ} :
    (p.mergeBit i b).condFlipBit i c = p.mergeBit i ((c[p]?.getD false).xor b) := by
  rw [condFlipBit_apply_eq_mergeBit, testRes_mergeBit_of_eq, testBit_mergeBit_of_eq]

theorem condFlipBit_eq_dite {q : ℕ} : q.condFlipBit i c = if h : q.testRes i < c.size then
    bif c[q.testRes i] then q.flipBit i else q else q := by
  symm
  rw [dite_eq_iff']
  exact ⟨fun h => (condFlipBit_apply_of_testRes_lt h).symm,
  fun h => (condFlipBit_apply_of_le_testRes (le_of_not_lt h)).symm⟩

theorem condFlipBit_condFlipBit_of_eq {q : ℕ} : (q.condFlipBit i c).condFlipBit i c = q := by
  simp_rw [condFlipBit_apply_eq_mergeBit, testRes_mergeBit_of_eq, testBit_mergeBit_of_eq,
    Bool.xor, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor, mergeBit_testBit_testRes_of_eq]

theorem condFlipBit_of_all_of_lt_c.size {q : ℕ} (hq : q.testRes i < c.size) (hc : c.all (fun x => x)) :
    q.condFlipBit i c = q.flipBit i := by
  simp_rw [Array.all_eq_true, Fin.forall_iff, Fin.getElem_fin] at hc
  simp_rw [condFlipBit_eq_dite, hq, dite_true, hc _ hq, cond_true]

theorem condFlipBit_of_all_not {q : ℕ} (hc : c.all (fun x => !x)) :
    q.condFlipBit i c = q := by
  simp_rw [Array.all_eq_true, Fin.forall_iff, Fin.getElem_fin, Bool.not_eq_true'] at hc
  simp_rw [condFlipBit_eq_dite]
  split_ifs with hq
  · simp_rw [hc _ hq, cond_false]
  · rfl

theorem lt_iff_condFlipBit_lt {q : ℕ} (hi : i < m) : q < 2^m ↔ q.condFlipBit i c < 2^m := by
  rcases m
  · exact (not_lt_zero _ hi).elim
  · rw [Nat.lt_add_one_iff] at hi
    rw [lt_iff_testRes_lt hi, condFlipBit_apply_eq_mergeBit]
    exact lt_iff_mergeBit_lt hi

@[pp_nodot, simps!]
def condFlipBitPerm (c : Array Bool) (i : ℕ) : Equiv.Perm ℕ where
  toFun := (condFlipBit · i c)
  invFun := (condFlipBit · i c)
  left_inv _ := condFlipBit_condFlipBit_of_eq
  right_inv _ := condFlipBit_condFlipBit_of_eq

end CondFlipBit

end Nat

namespace Fin

notation:75 "BV " arg:75  => Fin (2^arg)

section BitRes

variable {m : ℕ} {i : Fin (m + 1)} {q : BV (m + 1)} {p : BV m}

def testBit (q : BV (m + 1)) (i : Fin (m + 1)) := (q : ℕ).testBit i


@[simps!]
def testRes (q : BV (m + 1)) (i : Fin (m + 1)) : BV m where
  val := (q : ℕ).testRes i
  isLt := (Nat.lt_iff_testRes_lt i.is_le).mp q.is_lt

@[simps!]
def mergeBit (p : BV m) (i : Fin (m + 1)) (b : Bool) : BV (m + 1) where
  val := (p : ℕ).mergeBit i b
  isLt := (Nat.lt_iff_mergeBit_lt i.is_le).mp p.is_lt


@[pp_nodot, simps!]
def testBitRes (i : Fin (m + 1)) : BV (m + 1) ≃ Bool × BV m where
  toFun q := (q.testBit i, q.testRes i)
  invFun bp := bp.2.mergeBit i bp.1
  left_inv _ := ext Nat.mergeBit_testBit_testRes_of_eq
  right_inv _ := Prod.ext Nat.testBit_mergeBit_of_eq (ext Nat.testRes_mergeBit_of_eq)

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
  isLt := (Nat.lt_iff_flipBit_lt i.isLt).mp q.isLt

theorem flipBit_base {i} : ∀ q, flipBit (m := 1) q i = Equiv.swap 0 1 q := by
  simp_rw [Fin.ext_iff, flipBit_val, Fin.eq_zero i]
  exact Fin.forall_fin_two.mpr ⟨rfl, rfl⟩

@[pp_nodot, simps! apply symm_apply]
def flipBitPerm (i : Fin m) : Equiv.Perm (BV m) where
  toFun := (flipBit · i)
  invFun := (flipBit · i)
  left_inv _ := by simp_rw [ext_iff, flipBit_val, Nat.flipBit_flipBit_of_eq]
  right_inv _ := by simp_rw [ext_iff, flipBit_val, Nat.flipBit_flipBit_of_eq]

theorem flipBitPerm_base {i} : flipBitPerm (m := 1) i = Equiv.swap 0 1 := by
  simp_rw [Equiv.ext_iff, flipBitPerm_apply]
  exact flipBit_base

end FlipBit

section CondFlipBit

@[simps!]
def condFlipBit (q : BV (m + 1)) (i : Fin (m + 1)) (c : BV m → Bool) : BV (m + 1) where
  val := q.val.condFlipBit i.val (Array.ofFn c)
  isLt := (Nat.lt_iff_condFlipBit_lt i.isLt).mp q.isLt

variable {m : ℕ} {i : Fin (m + 1)} {q : BV (m + 1)} {p : BV m}

theorem condFlipBit_apply : q.condFlipBit i c = bif c (q.testRes i) then q.flipBit i else q := by
  simp_rw [Fin.ext_iff, Bool.apply_cond (Fin.val), condFlipBit_val, flipBit_val,
    Nat.condFlipBit_apply_of_testRes_lt
    ((testRes_val _ _ ▸ Fin.is_lt _).trans_eq (Array.size_ofFn _).symm), Array.getElem_ofFn]
  congr

theorem condFlipBit_base {i q} : condFlipBit (m := 0) q i c =
    bif c 0 then Equiv.swap 0 1 q else q := by
  simp_rw [condFlipBit_apply, Fin.eq_zero, flipBit_base]

theorem condFlipBit_apply_eq_mergeBit : q.condFlipBit i c =
    (q.testRes i).mergeBit i ((c (q.testRes i)).xor (q.testBit i))  := by
  ext
  simp only [condFlipBit_val, Nat.condFlipBit_apply_eq_mergeBit, testBit_def, mergeBit_val,
    testRes_val]
  refine congrArg _ (congrArg₂ _ ?_ rfl)
  simp_rw [Array.getD_eq_get, Array.size_ofFn, ← Nat.lt_iff_testRes_lt i.is_le, q.is_lt]
  exact Array.getElem_ofFn _ _ _

theorem condFlipBit_mergeBit : (p.mergeBit i b).condFlipBit i c = p.mergeBit i ((c p).xor b) := by
  simp only [condFlipBit_apply_eq_mergeBit, Fin.ext_iff, testRes_def, mergeBit_val,
    Nat.testRes_mergeBit_of_eq, Fin.eta, testBit_def, Nat.testBit_mergeBit_of_eq]

@[simp]
theorem condFlipBit_condFlipBit : (q.condFlipBit i c).condFlipBit i c = q := by
  simp_rw [ext_iff, condFlipBit_val, Nat.condFlipBit_condFlipBit_of_eq]

theorem condFlipBit_flipBit_of_all_true : q.flipBit i = q.condFlipBit i (Function.const _ true) := by
  rw [condFlipBit_apply, Function.const_apply, cond_true]

theorem condFlipBit_refl_of_all_false : q = q.condFlipBit i (Function.const _ false) := by
  rw [condFlipBit_apply, Function.const_apply, cond_false]

theorem condFlipBit_apply_comm :
(q.condFlipBit i d).condFlipBit i c = (q.condFlipBit i c).condFlipBit i d := by
simp_rw [condFlipBit_apply_eq_mergeBit, testRes_mergeBit_of_eq,
  testBit_mergeBit_of_eq, Bool.xor_left_comm]

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
    simp_rw [condFlipBit_apply_eq_mergeBit, mergeBit_succ, testRes_succ, testBit_succ,
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

@[pp_nodot, simps! apply symm_apply]
def condFlipBitPerm (c : BV m → Bool) (i : Fin (m + 1)) : Equiv.Perm (BV (m + 1)) where
  toFun := (condFlipBit · i c)
  invFun := (condFlipBit · i c)
  left_inv _ := by simp_rw [ext_iff, condFlipBit_val, Nat.condFlipBit_condFlipBit_of_eq]
  right_inv _ := by simp_rw [ext_iff, condFlipBit_val, Nat.condFlipBit_condFlipBit_of_eq]

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

theorem BitInvariant.comp_bitInvariant (hf : f.BitInvariant i) (hg : g.BitInvariant i) :
    (f ∘ g).BitInvariant i := bitInvariant_of_testBit_apply_eq_testBit <| fun q => by
  simp_rw [Function.comp_apply, hf.testBit_apply_eq_testBit, hg.testBit_apply_eq_testBit]

theorem BitInvariant.of_comp_bitInvariant (hf : f.BitInvariant i)
    (hfg : (f ∘ g).BitInvariant i) : g.BitInvariant i :=
  bitInvariant_of_testBit_apply_eq_testBit <| fun _ =>
  hf.testBit_apply_eq_testBit ▸ hfg.testBit_apply_eq_testBit

theorem forall_bitInvariant_iff_eq_id : (∀ i, f.BitInvariant i) ↔ f = id := by
  simp_rw [funext_iff, id_eq, testBit_ext_iff, bitInvariant_iff]
  exact forall_comm

theorem id_bitInvariant : id.BitInvariant i := by
  revert i
  rw [forall_bitInvariant_iff_eq_id]

theorem RightInverse.bitInvariant_of_bitInvariant (hfg : RightInverse g f) (h : f.BitInvariant i) :
  g.BitInvariant i := h.of_comp_bitInvariant (hfg.comp_eq_id ▸ id_bitInvariant)

theorem LeftInverse.bitInvariant_of_bitInvariant (hfg : LeftInverse g f) (h : g.BitInvariant i) :
  f.BitInvariant i := RightInverse.bitInvariant_of_bitInvariant hfg h

theorem flipBit_bitInvariant_of_ne (h : i ≠ j) : (flipBit · j).BitInvariant i :=
  bitInvariant_of_testBit_apply_eq_testBit (fun _ => testBit_flipBit_of_ne h)

theorem not_flipBit_bitInvariant_of_eq : ¬ (flipBit · i).BitInvariant i := by
  simp_rw [bitInvariant_iff, testBit_flipBit_of_eq, Bool.not_eq_self,
    forall_const, not_false_eq_true]

theorem flipBitPerm_bitInvariant_of_ne (h : i ≠ j) : (⇑(flipBitPerm j)).BitInvariant i :=
  flipBit_bitInvariant_of_ne h

theorem not_flipBiPerm_bitInvariant_of_eq : ¬ (⇑(flipBitPerm i)).BitInvariant i :=
  not_flipBit_bitInvariant_of_eq

theorem BitInvariant.iterate_bitInvariant (hf : f.BitInvariant i) {n : ℕ} :
   (f^[n]).BitInvariant i := by
  induction' n with n IH
  · exact id_bitInvariant
  · exact iterate_succ _ _ ▸ IH.comp_bitInvariant hf

theorem BitInvariant.mergeBit_testRes_apply_mergeBit {p : ℕ} (hf : f.BitInvariant i) :
    ((f (p.mergeBit i b)).testRes i).mergeBit i b = f (p.mergeBit i b) := by
  simp_rw [mergeBit_eq_iff, hf.testBit_apply_eq_testBit, testBit_mergeBit_of_eq, true_and]

section End

variable {f g : Function.End ℕ}

theorem End.one_bitInvariant : (1 : Function.End ℕ).BitInvariant i := id_bitInvariant

theorem End.forall_bitInvariant_iff_eq_one : (∀ i, f.BitInvariant i) ↔ f = 1 :=
  forall_bitInvariant_iff_eq_id

theorem BitInvariant.mulEnd_bitInvariant  (hf : f.BitInvariant i)
    (hg : g.BitInvariant i) : (f * g).BitInvariant i := hf.comp_bitInvariant hg

theorem BitInvariant.of_mulEnd_bitInvariant (hf : f.BitInvariant i)
    (hfg : (f * g).BitInvariant i) : g.BitInvariant i := hf.of_comp_bitInvariant hfg

theorem BitInvariant.mulEnd_bitInvariant_iff (hf : f.BitInvariant i) :
      (f * g).BitInvariant i ↔ g.BitInvariant i :=
    ⟨hf.of_mulEnd_bitInvariant, hf.mulEnd_bitInvariant⟩

theorem BitInvariant.pow_end_bitInvariant (hf : f.BitInvariant i) {n : ℕ} :
   (f ^ n).BitInvariant i := hf.iterate_bitInvariant

end End

section Equiv

variable {π ρ : Equiv.Perm ℕ}

theorem BitInvariant.symm_bitInvariant (h : (⇑π).BitInvariant i) : (⇑π.symm).BitInvariant i :=
  π.right_inv.bitInvariant_of_bitInvariant h

theorem BitInvariant.of_symm_bitInvariant (h : (⇑π.symm).BitInvariant i) : (⇑π).BitInvariant i :=
  h.symm_bitInvariant

theorem BitInvariant.trans_bitInvariant (hπ : (⇑π).BitInvariant i)
    (hg : (⇑ρ).BitInvariant i) : (⇑(ρ.trans π)).BitInvariant i := hπ.comp_bitInvariant hg

theorem BitInvariant.of_trans_bitInvariant (hπ : (⇑π).BitInvariant i)
    (hπρ : (⇑(ρ.trans π)).BitInvariant i) : (⇑ρ).BitInvariant i := hπ.of_comp_bitInvariant hπρ

theorem BitInvariant.trans_bitInvariant_iff (hπ : (⇑π).BitInvariant i) :
      (⇑(ρ.trans π)).BitInvariant i ↔ (⇑ρ).BitInvariant i :=
    ⟨hπ.of_trans_bitInvariant, hπ.trans_bitInvariant⟩

theorem _root_.Equiv.symm_bitInvar_iff_bitInvar :
    (⇑π.symm).BitInvariant i ↔ (⇑π).BitInvariant i :=
  ⟨BitInvariant.symm_bitInvariant, BitInvariant.symm_bitInvariant⟩

theorem _root_.Equiv.refl_bitInvariant : (⇑(Equiv.refl ℕ)).BitInvariant i := id_bitInvariant

theorem _root_.Equiv.forall_bitInvariant_iff_eq_refl :
    (∀ i, (⇑π).BitInvariant i) ↔ π = Equiv.refl ℕ := by
  rw [DFunLike.ext'_iff]
  exact forall_bitInvariant_iff_eq_id

section Perm

theorem BitInvariant.inv_bitInvariant (h : (⇑π).BitInvariant i) : (⇑π⁻¹).BitInvariant i :=
  h.symm_bitInvariant

theorem BitInvariant.of_inv_bitInvariant (h : (⇑π⁻¹).BitInvariant i) : (⇑π).BitInvariant i :=
  h.symm_bitInvariant

theorem _root_.Equiv.Perm.inv_bitInvar_iff_bitInvar :
    (⇑π⁻¹).BitInvariant i ↔ (⇑π).BitInvariant i :=
  ⟨BitInvariant.inv_bitInvariant, BitInvariant.inv_bitInvariant⟩

theorem BitInvariant.mulPerm_bitInvariant (hπ : (⇑π).BitInvariant i)
    (hg : (⇑ρ).BitInvariant i) : (⇑(π * ρ)).BitInvariant i := hπ.comp_bitInvariant hg

theorem BitInvariant.right_mulPerm_bitInvariant (hπ : (⇑π).BitInvariant i)
    (hπρ : (⇑(π * ρ)).BitInvariant i) : (⇑ρ).BitInvariant i := hπ.of_comp_bitInvariant hπρ

theorem BitInvariant.mulPerm_bitInvariant_iff_right (hπ : (⇑π).BitInvariant i) :
      (⇑(π * ρ)).BitInvariant i ↔ (⇑ρ).BitInvariant i :=
    ⟨hπ.right_mulPerm_bitInvariant, hπ.mulPerm_bitInvariant⟩

theorem BitInvariant.left_mulPerm_bitInvariant (hρ : (⇑ρ).BitInvariant i)
    (hπρ : (⇑(π * ρ)).BitInvariant i) : (⇑π).BitInvariant i :=
  (hρ.inv_bitInvariant.right_mulPerm_bitInvariant
    (mul_inv_rev π ρ ▸ hπρ.inv_bitInvariant)).of_inv_bitInvariant

theorem BitInvariant.mulPerm_bitInvariant_iff_left (hρ : (⇑ρ).BitInvariant i):
    (⇑(π * ρ)).BitInvariant i ↔ (⇑π).BitInvariant i :=
  ⟨hρ.left_mulPerm_bitInvariant, (BitInvariant.mulPerm_bitInvariant · hρ)⟩

theorem BitInvariant.commutatorElement (hπ : (⇑π).BitInvariant i) (hρ : (⇑ρ).BitInvariant i) :
    (⇑⁅π, ρ⁆).BitInvariant i := by
  rw [commutatorElement_def, hρ.inv_bitInvariant.mulPerm_bitInvariant_iff_left,
    hπ.inv_bitInvariant.mulPerm_bitInvariant_iff_left]
  exact hπ.mulPerm_bitInvariant hρ

theorem _root_.Equiv.Perm.one_bitInvariant : (⇑(1 : Equiv.Perm ℕ)).BitInvariant i := id_bitInvariant

theorem _root_.Equiv.Perm.forall_bitInvariant_iff_eq_one : (∀ i, (⇑π).BitInvariant i) ↔ π = 1 :=
  π.forall_bitInvariant_iff_eq_refl

theorem BitInvariant.pow_perm_bitInvariant (hπ : (⇑π).BitInvariant i) {n : ℕ} :
   (⇑(π ^ n)).BitInvariant i := hπ.iterate_bitInvariant

theorem BitInvariant.zpow_perm_bitInvariant (hπ : (⇑π).BitInvariant i) {n : ℤ} :
   (⇑(π ^ n)).BitInvariant i := by
  cases' n with n n
  · exact hπ.pow_perm_bitInvariant
  · exact hπ.pow_perm_bitInvariant.inv_bitInvariant

end Perm

end Equiv

end Function

namespace Submonoid

open Function Nat

def bitInvarEQ (i : ℕ) : Submonoid (Function.End ℕ) where
  carrier := BitInvariant i
  mul_mem' ha hb := BitInvariant.mulEnd_bitInvariant ha hb
  one_mem' := End.one_bitInvariant

def bitInvarLT (i : ℕ) : Submonoid (Function.End ℕ) := ⨅ k : ℕ, ⨅ (_ : k < i), bitInvarEQ k
def bitInvarGE (i : ℕ) : Submonoid (Function.End ℕ) := ⨅ k : ℕ, ⨅ (_ : i ≤ k), bitInvarEQ k

variable {f : Function.End ℕ}

@[simp]
theorem mem_bitInvarEQ_iff : f ∈ bitInvarEQ i ↔ f.BitInvariant i := Iff.rfl

@[simp]
theorem mem_bitInvarLT_iff : f ∈ bitInvarLT i ↔ ∀ k < i, f.BitInvariant k := by
  unfold bitInvarLT
  simp_rw [mem_iInf, mem_bitInvarEQ_iff]

@[simp]
theorem mem_bitInvarGE_iff : f ∈ bitInvarGE i ↔ ∀ k ≥ i, f.BitInvariant k := by
  unfold bitInvarGE
  simp_rw [mem_iInf, mem_bitInvarEQ_iff]

theorem mem_bitInvarLT_iff_mod_two_pow_eq {f : Function.End ℕ} :
    f ∈ bitInvarLT i ↔ ∀ (p : ℕ), f p % 2 ^ i = p % 2 ^ i := by
  simp_rw [testBit_ext_mod_two_pow_iff, mem_bitInvarLT_iff, bitInvariant_iff,
  imp_forall_iff, forall_swap (α := ℕ)]

@[simp]
theorem bitInvarLT_zero : bitInvarLT 0 = ⊤ :=
  le_antisymm le_top (fun _ _ => by
    simp only [mem_bitInvarLT_iff, not_lt_zero', false_implies, implies_true])

theorem bitInvarLT_strictAnti : StrictAnti bitInvarLT := fun m _ h => by
  simp_rw [SetLike.lt_iff_le_and_exists, SetLike.le_def, mem_bitInvarLT_iff,
  not_forall, exists_prop]
  exact ⟨fun _ hf _ hk => hf _ (hk.trans h),
    ⟨(flipBit · m), fun k hk => flipBit_bitInvariant_of_ne hk.ne,
    ⟨m, h, not_flipBit_bitInvariant_of_eq⟩⟩⟩

theorem bitInvarLT_lt_iff_lt : bitInvarLT n < bitInvarLT m ↔ m < n :=
  bitInvarLT_strictAnti.lt_iff_lt

theorem bitInvarLT_le_iff_le : bitInvarLT n ≤ bitInvarLT m ↔ m ≤ n :=
  bitInvarLT_strictAnti.le_iff_le

theorem mem_bitInvarGE_iff_div_two_pow_eq : f ∈ bitInvarGE i ↔
    ∀ (p : ℕ), f p / 2 ^ i = p / 2 ^ i := by
  simp_rw [testBit_ext_div_two_pow_iff, mem_bitInvarGE_iff, bitInvariant_iff,
  imp_forall_iff, forall_swap (α := ℕ)]

theorem lt_iff_apply_lt_of_mem_bitInvarGE (hf : f ∈ bitInvarGE i) {p : ℕ}:
    p < 2^i ↔ f p < 2^i := by
  rw [mem_bitInvarGE_iff] at hf
  simp_rw [lt_pow_two_iff_ge_imp_testBit_eq_false]
  exact forall₂_congr (fun _ h => by
    simp_rw [Bool.coe_false_iff_false, Bool.not_inj_iff]
    exact (hf _ h).testBit_apply_eq_testBit.symm)

@[simp]
theorem bitInvarGE_zero :
    bitInvarGE 0 = ⊥ := le_antisymm (fun _ => by
  simp_rw [mem_bitInvarGE_iff, ge_iff_le, Nat.zero_le, true_implies, mem_bot,
    End.forall_bitInvariant_iff_eq_one, imp_self]) bot_le

theorem bitInvarGE_strictMono : StrictMono bitInvarGE := fun m _ h => by
  refine' ⟨fun _ => _, Set.not_subset.mpr _⟩
  · simp only [SetLike.mem_coe, mem_bitInvarGE_iff, ge_iff_le]
    exact fun hf _ hk => hf _ (h.le.trans hk)
  · simp only [SetLike.mem_coe, mem_bitInvarGE_iff, ge_iff_le, not_forall, Classical.not_imp]
    refine' ⟨(flipBit · m), fun k hk => flipBit_bitInvariant_of_ne (h.trans_le hk).ne', _⟩
    exact ⟨m, le_rfl, not_flipBit_bitInvariant_of_eq⟩

theorem bitInvarGE_lt_iff_lt : bitInvarGE m < bitInvarGE n ↔ m < n :=
  bitInvarGE_strictMono.lt_iff_lt

theorem bitInvarGE_le_iff_le : bitInvarGE m ≤ bitInvarGE n ↔ m ≤ n :=
  bitInvarGE_strictMono.le_iff_le

theorem bitInvarLT_inf_bitInvarGE_eq_bot : bitInvarGE m ⊓ bitInvarLT m = ⊥ :=
    SetLike.ext <| fun f => by
  simp_rw [mem_bot, ← End.forall_bitInvariant_iff_eq_one, Submonoid.mem_inf, mem_bitInvarGE_iff,
  mem_bitInvarLT_iff, ← not_le, ge_iff_le, ← forall_and, _root_.imp_and_neg_imp_iff]

theorem eq_one_of_mem_bitInvarGE_mem_bitInvarLt (hfGE : f ∈ bitInvarGE m) (hfLT : f ∈ bitInvarLT m) :
    f = 1 := by
  rw [← Submonoid.mem_bot]
  exact bitInvarLT_inf_bitInvarGE_eq_bot ▸ Submonoid.mem_inf.mpr ⟨hfGE, hfLT⟩

end Submonoid

namespace Subgroup

open Equiv Function Nat

def bitInvarEQ (i : ℕ) : Subgroup (Perm ℕ) where
  carrier π := BitInvariant i ⇑π
  mul_mem' ha hb := BitInvariant.mulEnd_bitInvariant ha hb
  one_mem' := End.one_bitInvariant
  inv_mem' ha := BitInvariant.inv_bitInvariant ha

def bitInvarLT (i : ℕ) : Subgroup (Perm ℕ) := ⨅ k : ℕ, ⨅ (_ : k < i), bitInvarEQ k
def bitInvarGE (i : ℕ) : Subgroup (Perm ℕ) := ⨅ k : ℕ, ⨅ (_ : i ≤ k), bitInvarEQ k

variable {π : Perm ℕ}

@[simp]
theorem mem_bitInvarEQ_iff : π ∈ bitInvarEQ i ↔ (⇑π).BitInvariant i := Iff.rfl

@[simp]
theorem mem_bitInvarLT_iff : π ∈ bitInvarLT i ↔ ∀ k < i, (⇑π).BitInvariant k := by
  unfold bitInvarLT
  simp_rw [mem_iInf, mem_bitInvarEQ_iff]

@[simp]
theorem mem_bitInvarGE_iff : π ∈ bitInvarGE i ↔ ∀ k ≥ i, (⇑π).BitInvariant k := by
  unfold bitInvarGE
  simp_rw [mem_iInf, mem_bitInvarEQ_iff]

theorem mem_bitInvarEQ_iff_coe_mem_bitInvarEQ :
  ∀ π, π ∈ bitInvarEQ i ↔ ⇑π ∈ Submonoid.bitInvarEQ i := fun _ => Iff.rfl

theorem mem_bitInvarLT_iff_coe_mem_bitInvarLT :
    ∀ π, π ∈ bitInvarLT i ↔ ⇑π ∈ Submonoid.bitInvarLT i := fun _ =>
  mem_bitInvarLT_iff.trans Submonoid.mem_bitInvarLT_iff.symm

theorem mem_bitInvarGE_iff_coe_mem_bitInvarGE :
    ∀ π, π ∈ bitInvarGE i ↔ ⇑π ∈ Submonoid.bitInvarGE i := fun _ =>
  mem_bitInvarGE_iff.trans Submonoid.mem_bitInvarGE_iff.symm

theorem mem_bitInvarLT_iff_mod_two_pow_eq :
    π ∈ bitInvarLT i ↔ ∀ (p : ℕ), π p % 2 ^ i = p % 2 ^ i := by
  simp_rw [mem_bitInvarLT_iff_coe_mem_bitInvarLT]
  exact Submonoid.mem_bitInvarLT_iff_mod_two_pow_eq

@[simp]
theorem bitInvarLT_zero : bitInvarLT 0 = ⊤ := Subgroup.ext fun _ => by
  simp_rw [mem_bitInvarLT_iff_coe_mem_bitInvarLT, Submonoid.bitInvarLT_zero,
  Submonoid.mem_top, mem_top]

theorem bitInvarLT_strictAnti : StrictAnti bitInvarLT := fun m _ h => by
  simp_rw [SetLike.lt_iff_le_and_exists, SetLike.le_def, mem_bitInvarLT_iff,
  not_forall, exists_prop]
  exact ⟨fun _ hf _ hk => hf _ (hk.trans h),
    ⟨flipBitPerm m, fun k hk => flipBit_bitInvariant_of_ne hk.ne,
    ⟨m, h, not_flipBit_bitInvariant_of_eq⟩⟩⟩

theorem bitInvarLT_lt_iff_lt : bitInvarLT n < bitInvarLT m ↔ m < n :=
  bitInvarLT_strictAnti.lt_iff_lt

theorem bitInvarLT_le_iff_le : bitInvarLT n ≤ bitInvarLT m ↔ m ≤ n :=
  bitInvarLT_strictAnti.le_iff_le

theorem mem_bitInvarGE_iff_div_two_pow_eq : π ∈ bitInvarGE i ↔
    ∀ (p : ℕ), π p / 2 ^ i = p / 2 ^ i := by
  simp_rw [testBit_ext_div_two_pow_iff, mem_bitInvarGE_iff, bitInvariant_iff,
  imp_forall_iff, forall_swap (α := ℕ)]

theorem lt_iff_apply_lt_of_mem_bitInvarGE (hf : π ∈ bitInvarGE i) {p : ℕ}:
    p < 2^i ↔ π p < 2^i := by
  rw [mem_bitInvarGE_iff] at hf
  simp_rw [lt_pow_two_iff_ge_imp_testBit_eq_false]
  exact forall₂_congr (fun _ h => by
    simp_rw [Bool.coe_false_iff_false, Bool.not_inj_iff]
    exact (hf _ h).testBit_apply_eq_testBit.symm)

@[simp]
theorem bitInvarGE_zero :
    bitInvarGE 0 = ⊥ := le_antisymm (fun _ => by
  simp_rw [mem_bitInvarGE_iff, ge_iff_le, Nat.zero_le, true_implies, mem_bot,
    Perm.forall_bitInvariant_iff_eq_one, imp_self]) bot_le

theorem bitInvarGE_strictMono : StrictMono bitInvarGE := fun m _ h => by
  refine' ⟨fun _ => _, Set.not_subset.mpr _⟩
  · simp only [SetLike.mem_coe, mem_bitInvarGE_iff, ge_iff_le]
    exact fun hf _ hk => hf _ (h.le.trans hk)
  · simp only [SetLike.mem_coe, mem_bitInvarGE_iff, ge_iff_le, not_forall, Classical.not_imp]
    refine' ⟨flipBitPerm m, fun k hk => flipBit_bitInvariant_of_ne (h.trans_le hk).ne', _⟩
    exact ⟨m, le_rfl, not_flipBit_bitInvariant_of_eq⟩

theorem bitInvarGE_lt_iff_lt : bitInvarGE m < bitInvarGE n ↔ m < n :=
  bitInvarGE_strictMono.lt_iff_lt

theorem bitInvarGE_le_iff_le : bitInvarGE m ≤ bitInvarGE n ↔ m ≤ n :=
  bitInvarGE_strictMono.le_iff_le

theorem bitInvarLT_inf_bitInvarGE_eq_bot : bitInvarGE m ⊓ bitInvarLT m = ⊥ :=
    SetLike.ext <| fun f => by
  simp_rw [mem_bot, ← Perm.forall_bitInvariant_iff_eq_one, Subgroup.mem_inf, mem_bitInvarGE_iff,
  mem_bitInvarLT_iff, ← not_le, ge_iff_le, ← forall_and, _root_.imp_and_neg_imp_iff]

theorem eq_one_of_mem_bitInvarGE_mem_bitInvarLt (hfGE : f ∈ bitInvarGE m) (hfLT : f ∈ bitInvarLT m) :
    f = 1 := by
  rw [← Subgroup.mem_bot]
  exact bitInvarLT_inf_bitInvarGE_eq_bot ▸ Subgroup.mem_inf.mpr ⟨hfGE, hfLT⟩

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
    (f : Bool → ℕ → ℕ) : (endoOfBoolArrowEndo i f) ∈ Submonoid.bitInvarEQ i :=
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
def bitInvarMulEquivEnd (i : Fin (m + 1)) : (Bool → Function.End ℕ) ≃* Submonoid.bitInvarEQ i where
  toFun feo := ⟨endoOfBoolArrowEndo i feo, endoOfBoolArrowEndo_mem_bitInvarEQ feo⟩
  invFun f := boolArrowEndoOfEndo i f.val
  left_inv := boolArrowEndoOfEndo_leftInverse i
  right_inv f := Subtype.ext (boolArrowEndoOfEndo_rightInvOn i f.prop)
  map_mul' _ _ := Subtype.ext (endoOfBoolArrowEndo_comp _ _)

def bitInvarMulEquiv (i : Fin (m + 1)) : (Bool → Equiv.Perm ℕ) ≃* Subgroup.bitInvarEQ i :=
  ((Equiv.Perm.equivUnitsEnd).arrowCongr (Equiv.refl _)).trans <|
  MulEquiv.piUnits.symm.trans <|
  (Units.mapEquiv (bitInvarMulEquivEnd i)).trans <|
  (Equiv.Perm.equivUnitsEnd.subgroupMulEquivUnitsType
    (Subgroup.mem_bitInvarEQ_iff_coe_mem_bitInvarEQ)).symm

@[simp]
theorem bitInvarMulEquiv_apply_coe_apply (i : Fin (m + 1))
  (πeo : Bool → Equiv.Perm ℕ) : ⇑((bitInvarMulEquiv i) πeo).val =
  endoOfBoolArrowEndo i fun b => ⇑(πeo b) := rfl

@[simp]
theorem bitInvarMulEquiv_apply_coe_symm_apply (i : Fin (m + 1))
  (πeo : Bool → Equiv.Perm ℕ) : ⇑((bitInvarMulEquiv i) πeo).val.symm =
  endoOfBoolArrowEndo i fun b => ⇑(πeo b)⁻¹ := rfl

@[simp]
theorem bitInvarMulEquiv_symm_apply_apply (i : Fin (m + 1)) (π : ↥(Subgroup.bitInvarEQ i)):
  ⇑(((bitInvarMulEquiv i).symm) π b) = boolArrowEndoOfEndo i (⇑π.val) b := rfl

@[simp]
theorem bitInvarMulEquiv_symm_apply_symm_apply (i : Fin (m + 1)) (π : ↥(Subgroup.bitInvarEQ i)):
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
