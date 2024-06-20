import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Ring.Defs
import Controlbits.Bool
import Controlbits.Fin
import Controlbits.Equivs
import Controlbits.Submonoid
import Controlbits.FunctionEnd

namespace Fin

lemma val_succAbove {i : Fin m} {j : Fin (m + 1)} :
    (j.succAbove i : ℕ) = i.val + (decide (j.val ≤ i.val)).toNat := by
  rcases le_or_lt j (i.castSucc) with h | h
  · rw [succAbove_of_le_castSucc _ _ h]
    rw [Fin.le_iff_val_le_val, coe_castSucc] at h
    simp_rw [val_succ, h, decide_True, Bool.toNat_true]
  · rw [succAbove_of_castSucc_lt _ _ h]
    rw [Fin.lt_iff_val_lt_val, coe_castSucc] at h
    simp_rw [coe_castSucc, h.not_le, decide_False, Bool.toNat_false, add_zero]

lemma val_predAbove {i : Fin m} {j : Fin (m + 1)} :
    (i.predAbove j : ℕ) = j.val - (decide (i.val < j.val)).toNat := by
  rcases le_or_lt j (i.castSucc) with h | h
  · rw [predAbove_of_le_castSucc _ _ h]
    rw [Fin.le_iff_val_le_val, coe_castSucc] at h
    simp_rw [coe_castPred, h.not_lt, decide_False, Bool.toNat_false, Nat.sub_zero]
  · rw [predAbove_of_castSucc_lt _ _ h]
    rw [Fin.lt_iff_val_lt_val, coe_castSucc] at h
    simp_rw [coe_pred, h, decide_True, Bool.toNat_true]

@[simp]
lemma val_xor {i j : Fin n} : (i ^^^ j).val = (i.val ^^^ j.val) % n := rfl

end Fin

namespace Nat

theorem testBit_one_succ {k : ℕ} : testBit 1 (k + 1) = false := by
  rw [testBit_succ, div_eq_of_lt one_lt_two, zero_testBit]

theorem testBit_one {k : ℕ} : testBit 1 k = decide (k = 0) := by
  cases k
  · exact testBit_one_zero
  · simp_rw [testBit_one_succ, decide_False]

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
  · simp_rw [testBit_two_pow_self, decide_True]
  · simp_rw [testBit_two_pow_of_ne h, h, decide_False]

theorem testBit_add_two_pow_eq (x : Nat) (i : Nat) :
    (x + 2^i).testBit i = !x.testBit i := by rw [add_comm, testBit_two_pow_add_eq]

lemma testBit_add_mul_pow_two (a : Nat) {b : Nat} {i : Nat} (b_lt : b < 2 ^ i) (j : Nat) :
    (b + 2 ^ i * a).testBit j = if j < i then b.testBit j else a.testBit (j - i) := by
  rw [add_comm]
  exact testBit_mul_pow_two_add a b_lt j

lemma testBit_add_mul_two_pow_eq (a : Nat) (b : Nat) (i : Nat) :
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
    Nat.add_div_left _ (Nat.two_pow_pos _), succ_eq_add_one]
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

lemma or_eq_add_two_pow_mul_of_lt_right {a b i: ℕ} (ha : a < 2^i) :
    2^i * b ||| a = 2^i * b + a:= (mul_add_lt_is_or ha _).symm

lemma or_eq_add_two_pow_mul_of_lt_left {a b i: ℕ} (ha : a < 2^i) :
    a ||| 2^i * b = a + 2^i * b := by rw [lor_comm, add_comm, or_eq_add_two_pow_mul_of_lt_right ha]

lemma or_eq_add_two_pow_of_lt_left {a i: ℕ} (ha : a < 2^i) :
    a ||| 2^i = a + 2^i := by
  rw [← (Nat.mul_one (2^i)), or_eq_add_two_pow_mul_of_lt_left ha]

lemma or_eq_add_two_pow_of_lt_right {a i: ℕ} (ha : a < 2^i) :
    2^i ||| a = 2^i + a:= by
  rw [lor_comm, add_comm]
  exact or_eq_add_two_pow_of_lt_left ha

lemma exists_pow_two_mul_of_testBit (b : ℕ) (hb : ∀ i < k, b.testBit i = false) :
    ∃ n, b = 2^k * n := by
  induction' k with k IH generalizing b
  · exact ⟨b, by rw [pow_zero, one_mul]⟩
  · rcases IH _ (fun i hi => hb i  (hi.trans (Nat.lt_succ_self _))) with ⟨b, rfl⟩
    have h := hb k (Nat.lt_succ_self _)
    simp_rw [testBit_mul_pow_two, le_refl, decide_True, Bool.true_and, Nat.sub_self,
      testBit_zero, decide_eq_false_iff_not, mod_two_ne_one, ← Nat.dvd_iff_mod_eq_zero] at h
    rcases h with ⟨b, rfl⟩
    exact ⟨b, by rw [← mul_assoc, pow_succ]⟩

lemma nat_eq_testBit_sum_range {a : ℕ} (ha : a < 2^m) :
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

lemma nat_eq_testBit_tsum {a : ℕ} :
    a = ∑' i, (a.testBit i).toNat * 2^i := by
  rcases pow_unbounded_of_one_lt a one_lt_two with ⟨k, ha⟩
  refine' (nat_eq_testBit_sum_range ha).trans (tsum_eq_sum _).symm
  simp_rw [Finset.mem_range, not_lt, _root_.mul_eq_zero, Bool.toNat_eq_zero, pow_eq_zero_iff',
    false_and, or_false]
  exact fun _ hj => testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_of_le one_lt_two hj))

section BitResiduum

def testRes (q i : ℕ) := ((q >>> (i + 1)) <<< i) ||| (q &&& (2^ i - 1))

def mergeBit (p : ℕ) (i : ℕ) (b : Bool)  :=
  ((p >>> i) <<< (i + 1)) ||| (p &&& (2^ i - 1)) ||| (b.toNat <<< i)

lemma testBit_ext_iff {q q' : ℕ} : q = q' ↔ (∀ i : ℕ, q.testBit i = q'.testBit i) :=
  ⟨fun h _ => h ▸ rfl, Nat.eq_of_testBit_eq⟩

lemma testRes_def : q.testRes i = (q >>> (i + 1)) <<< i ||| q &&& (2^ i - 1) := rfl

lemma mergeBit_def : p.mergeBit i b =
    ((p >>> i) <<< (i + 1)) ||| (p &&& (2^ i - 1)) ||| (b.toNat <<< i) := rfl

lemma toNat_testBit' : (testBit q i).toNat = q / 2^i % 2 := Nat.toNat_testBit _ _

lemma testRes_eq : q.testRes i = 2^i * (q / 2^(i + 1)) + q % 2^i := by
  unfold testRes
  rw [and_pow_two_is_mod, shiftLeft_eq_mul_pow, shiftRight_eq_div_pow,
    mul_comm, or_eq_add_two_pow_mul_of_lt_right (mod_lt _ (Nat.two_pow_pos _))]

lemma mergeBit_eq : p.mergeBit i b =
    2^(i + 1) * (p / 2^i) + p % 2^i + 2^i * bif b then 1 else 0 := by
  unfold mergeBit
  rw [and_pow_two_is_mod]
  cases b
  · simp_rw [cond_false, Bool.toNat_false, Nat.zero_shiftLeft, mul_zero, add_zero,
    Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow, or_zero, mul_comm (p / 2 ^ i),
    pow_succ, mul_assoc]
    rw [or_eq_add_two_pow_mul_of_lt_right (mod_lt _ (Nat.two_pow_pos _))]
  · have h : 2^i < 2^(i + 1) := Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _)
    simp_rw [cond_true, mul_one, Bool.toNat_true, Nat.shiftLeft_eq_mul_pow, one_mul,
    Nat.shiftRight_eq_div_pow, mul_comm (p / 2 ^ i), lor_assoc, add_assoc,
    or_eq_add_two_pow_mul_of_lt_right
      (Nat.or_lt_two_pow ((mod_lt _ (Nat.two_pow_pos _)).trans h) h),
    or_eq_add_two_pow_of_lt_left (mod_lt _ (Nat.two_pow_pos _))]

lemma testBit_testRes {i j q : ℕ} :
    (q.testRes j).testBit i = q.testBit (i + (decide (j ≤ i)).toNat) := by
  simp_rw [testRes_def, testBit_or, testBit_shiftLeft, ge_iff_le,
    testBit_shiftRight, add_right_comm, testBit_and, testBit_two_pow_sub_one, lt_iff_not_le,
    decide_not]
  by_cases ha : (j ≤ i)
  · simp_rw [ha, decide_True, add_tsub_cancel_of_le ha, Bool.true_and, Bool.not_true,
    Bool.and_false, Bool.or_false, Bool.toNat_true]
  · simp_rw [ha, decide_False, Bool.false_and, Bool.false_or, Bool.not_false,
    Bool.and_true, Bool.toNat_false, add_zero]

lemma testBit_testRes_of_lt {i j q : ℕ} (ha : i < j) : (q.testRes j).testBit i = q.testBit i := by
  simp_rw [testBit_testRes, ha.not_le, decide_False, Bool.toNat_false, add_zero]

lemma testBit_testRes_of_ge {i j q : ℕ} (ha : j ≤ i) :
    (q.testRes j).testBit i = q.testBit (i + 1) := by
  simp_rw [testBit_testRes, ha, decide_True, Bool.toNat_true]

lemma testBit_mergeBit {i j p : ℕ} : (p.mergeBit j b).testBit i =
    bif (i = j) then b else p.testBit (i - (decide (j < i)).toNat) := by
  simp_rw [mergeBit_def, and_pow_two_is_mod, testBit_or, testBit_shiftLeft, testBit_shiftRight,
    testBit_mod_two_pow]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp_rw [(lt_succ_of_lt hij).not_le, hij.ne, hij.not_le, hij, hij.le.not_lt, decide_False,
    Bool.false_and, decide_True, Bool.true_and, Bool.false_or, Bool.or_false,
    Bool.toNat_false, tsub_zero, Bool.cond_false]
  · simp_rw [add_le_iff_nonpos_right, zero_lt_one.not_le, lt_irrefl, le_rfl, Nat.sub_self,
    decide_False,  decide_True, Bool.toNat_false, Bool.false_and, Bool.false_or,
    Bool.true_and, Bool.cond_true, testBit_toNat_zero]
  · rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
    simp_rw [← Nat.add_sub_assoc (succ_le_of_lt hij), succ_eq_add_one, Nat.add_sub_add_left,
      succ_le_of_lt hij, hij, hij.le, hij.le.not_lt, add_comm j, Nat.add_right_comm _ j,
      Nat.add_sub_cancel, add_left_eq_self, testBit_toNat_succ, decide_True, decide_False,
      Bool.true_and, Bool.false_and, Bool.or_false, Bool.toNat_true, cond_false]

@[simp]
lemma testBit_mergeBit_of_eq {p : ℕ} : (p.mergeBit i b).testBit i = b := by
  simp_rw [testBit_mergeBit, decide_True, cond_true]

lemma testBit_mergeBit_of_ne {i j p : ℕ} (hij : i ≠ j) : (p.mergeBit j b).testBit i =
    p.testBit (i - (decide (j < i)).toNat) := by
  simp_rw [testBit_mergeBit, hij, decide_False, cond_false]

lemma testBit_mergeBit_of_lt {i j p : ℕ} (hij : i < j) :
    (p.mergeBit j b).testBit i = p.testBit i := by
  simp_rw [testBit_mergeBit_of_ne hij.ne, hij.le.not_lt,
  decide_False, Bool.toNat_false, Nat.sub_zero]

lemma testBit_mergeBit_of_gt {i j p : ℕ} (hij : j < i) :
    (p.mergeBit j b).testBit i = p.testBit (i - 1) := by
  simp_rw [testBit_mergeBit_of_ne hij.ne', hij,
  decide_True, Bool.toNat_true]

lemma testRes_mergeBit_of_gt {p : ℕ} (hij : j < i) :
    (p.mergeBit j b).testRes i = (p.testRes (i - 1)).mergeBit j b := by
  simp only [hij, decide_True, Bool.toNat_true, testBit_ext_iff, testBit_testRes, testBit_mergeBit,
    tsub_le_iff_right]
  intro k
  rcases lt_trichotomy j (k + (decide (i ≤ k)).toNat) with hjk | rfl | hjk
  · have H : j < k := (le_or_lt i k).by_cases (lt_of_le_of_lt' · hij)
      (fun h => hjk.trans_eq (by simp_rw [h.not_le, decide_False, Bool.toNat_false, add_zero]))
    simp only [hjk.ne', decide_False, hjk, decide_True, Bool.toNat_true,
      Nat.sub_add_comm (one_le_of_lt H), cond_false, H.ne', H,
      Nat.sub_one_add_one_eq_of_pos (zero_lt_of_lt H)]
  · simp only [decide_True, lt_self_iff_false, decide_False, Bool.toNat_false, tsub_zero, cond_true,
      self_eq_add_right, Bool.toNat_eq_zero, decide_eq_false_iff_not, not_le,
      (le_self_add).trans_lt hij, add_lt_iff_neg_left, not_lt_zero']
  · have H : k < j := le_self_add.trans_lt hjk
    simp only [gt_iff_lt, H.trans hij, not_le_of_lt, decide_False, Bool.toNat_false, add_zero, H,
      not_lt_of_lt, tsub_zero, (succ_lt_of_lt_of_lt H hij)]

lemma testRes_mergeBit_of_lt {p : ℕ} (hij : i < j) :
    (p.mergeBit j b).testRes i = (p.testRes i).mergeBit (j - 1) b := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨j, rfl⟩
  simp only [testBit_ext_iff, testBit_testRes, testBit_mergeBit, add_tsub_cancel_right]
  intro k
  rcases le_or_lt i k with hik | hik
  · simp only [hik, decide_True, Bool.toNat_true, add_left_inj, add_lt_add_iff_right]
    rcases lt_trichotomy (i + j) k with hjk | rfl | hjk
    · simp only [hjk.ne', decide_False, hjk, decide_True, Bool.toNat_true, add_tsub_cancel_right,
      cond_false, (le_add_right _ _).trans (Nat.le_sub_one_of_lt hjk), decide_True,
      Bool.toNat_true, Nat.sub_add_cancel (one_le_of_lt hjk)]
    · simp only [decide_True, lt_self_iff_false, decide_False, Bool.toNat_false, tsub_zero,
      testBit_succ, cond_true, le_add_iff_nonneg_right, _root_.zero_le, Bool.toNat_true]
    · simp only [hjk.ne, decide_False, hjk.not_lt, Bool.toNat_false, tsub_zero, testBit_succ,
      cond_false, hik, decide_True, Bool.toNat_true]
  · simp only [hik.not_le, decide_False, Bool.toNat_false, add_zero, (hik.trans hij).ne,
      (hik.trans hij).not_lt, tsub_zero, cond_false, hik.trans_le (Nat.le_add_right _ _), ne_of_lt,
      not_lt_of_lt]

lemma testRes_mergeBit_of_ne {p : ℕ} (hij : i ≠ j) : (p.mergeBit j b).testRes i =
    (p.testRes (i - (decide (j < i)).toNat)).mergeBit (j - (decide (i < j)).toNat) b := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [testRes_mergeBit_of_lt hij, hij.not_lt, decide_False, Bool.toNat_false, tsub_zero,
    hij, decide_True, Bool.toNat_true]
  · simp only [testRes_mergeBit_of_gt hij, hij, decide_True, Bool.toNat_true, hij.not_lt,
    decide_False, Bool.toNat_false, tsub_zero]

@[simp]
lemma testRes_mergeBit_of_eq {p : ℕ} : (p.mergeBit i b).testRes i = p := by
  simp only [testBit_ext_iff, testBit_testRes, testBit_mergeBit]
  intro k
  rcases le_or_lt i k with hik | hik
  · simp only [hik, decide_True, Bool.toNat_true, (lt_succ_of_le hik).ne', decide_False,
    lt_succ_of_le hik, add_tsub_cancel_right, cond_false]
  · simp only [gt_iff_lt, hik, not_le_of_lt, decide_False, Bool.toNat_false, add_zero, ne_of_lt,
    not_lt_of_lt, tsub_zero, cond_false]

lemma testRes_mergeBit {i j p : ℕ} : (p.mergeBit j b).testRes i = bif (i = j) then p else
    (p.testRes (i - (decide (j < i)).toNat)).mergeBit (j - (decide (i < j)).toNat) b := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testRes_mergeBit_of_eq, decide_True, cond_true]
  · simp_rw [hij, testRes_mergeBit_of_ne hij, decide_False, cond_false]

lemma mergeBit_testRes_of_le {p : ℕ} (hij : i ≤ j) :
    (p.testRes j).mergeBit i b = (p.mergeBit i b).testRes (j + 1) := by
  rw [testRes_mergeBit_of_gt (Nat.lt_add_one_iff.mpr hij), add_tsub_cancel_right]

lemma mergeBit_testRes_of_ge {p : ℕ} (hij : j ≤ i) :
    (p.testRes j).mergeBit i b = (p.mergeBit (i + 1) b).testRes j := by
  rw [testRes_mergeBit_of_lt (Nat.lt_add_one_iff.mpr hij), add_tsub_cancel_right]

lemma mergeBit_testRes_of_eq_left {p : ℕ} :
    (p.testRes i).mergeBit i b = (p.mergeBit (i + 1) b).testRes i := mergeBit_testRes_of_ge le_rfl

lemma mergeBit_testRes_of_eq_right {p : ℕ} :
    (p.testRes i).mergeBit i b = (p.mergeBit i b).testRes (i + 1) := mergeBit_testRes_of_le le_rfl

lemma mergeBit_testRes_of_ne {p : ℕ} (hij : i ≠ j) :
    (p.testRes j).mergeBit i b =
    (p.mergeBit (i + (decide (j < i)).toNat) b).testRes (j + (decide (i < j)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [mergeBit_testRes_of_le hij.le, hij, not_lt_of_lt, decide_False, Bool.toNat_false,
    add_zero, decide_True, Bool.toNat_true]
  · simp only [mergeBit_testRes_of_ge hij.le, hij, decide_True, Bool.toNat_true, not_lt_of_lt,
    decide_False, Bool.toNat_false, add_zero]

@[simp]
lemma mergeBit_testRes_of_eq_of_testBit {q : ℕ} : (q.testRes i).mergeBit i (q.testBit i) = q := by
  rw [testBit_to_div_mod, testRes_eq, mergeBit_eq]
  simp_rw [Nat.add_mod_mod, Nat.mul_add_mod, Nat.mul_add_div (Nat.two_pow_pos _),
  Nat.mod_div_self, add_zero, Bool.cond_decide]
  have H : (if q / 2 ^ i % 2 = 1 then 1 else 0 : ℕ) = q / 2 ^ i % 2 :=
  (Nat.mod_two_eq_zero_or_one (q / 2 ^ i)).by_cases (fun h => h.symm ▸ rfl) (fun h => h.symm ▸ rfl)
  rw [H, add_assoc, ← Nat.mod_mul, ← pow_succ, Nat.div_add_mod]

lemma testRes_lt_iff_lt (hi : i ≤ m) : q.testRes i < 2^m ↔ q < 2^(m + 1) := by
  rw [testRes_eq]
  refine' ⟨lt_imp_lt_of_le_imp_le (fun _ => _), fun _ => _⟩
  · have h : 2 ^ m ≤ 2 ^ i * 2 ^ (m - i) + 0 := by rw [add_zero, ← pow_add, Nat.add_sub_cancel' hi]
    refine' h.trans (Nat.add_le_add (Nat.mul_le_mul_left _
      ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr _)) (Nat.zero_le _))
    rwa [← pow_add, ← add_assoc, Nat.sub_add_cancel hi]
  · have h : 2 ^ i * (q / 2 ^ (i + 1)) ≤ 2^m - 2^i := by
      rw [← Nat.add_sub_cancel' hi, pow_add _ i (m - i), ← Nat.mul_pred_right, ]
      refine' Nat.mul_le_mul_left _ (Nat.le_pred_of_lt (Nat.div_lt_of_lt_mul _))
      rwa [mul_comm, ← pow_add, ← add_assoc, Nat.sub_add_cancel hi]
    exact (add_lt_add_of_le_of_lt h (Nat.mod_lt _ (Nat.two_pow_pos _))).trans_eq <|
      Nat.sub_add_cancel (Nat.pow_le_pow_of_le one_lt_two hi)

lemma le_testRes_iff_ge (hi : i ≤ m) : 2^m ≤ q.testRes i ↔ 2^(m + 1) ≤ q := by
  simp_rw [← not_lt, testRes_lt_iff_lt hi]

lemma mergeBit_lt_iff_lt (hi : i ≤ m) : p.mergeBit i b < 2^(m + 1) ↔ p < 2^m := by
  rw [← testRes_lt_iff_lt hi, testRes_mergeBit_of_eq]

lemma le_mergeBit_iff_le (hi : i ≤ m) : 2^(m + 1) ≤ p.mergeBit i b ↔ 2^m ≤ p := by
  rw [← le_testRes_iff_ge hi, testRes_mergeBit_of_eq]

lemma testRes_testRes {i j q : ℕ} : (q.testRes j).testRes i =
    (q.testRes (i + (decide (j ≤ i)).toNat)).testRes (j - (!decide (j ≤ i)).toNat) := by
  simp_rw [testBit_ext_iff, testBit_testRes, tsub_le_iff_right]
  intro k
  rcases lt_or_le i j with hij | hij
  · simp_rw [hij.not_le, decide_False, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
    add_zero]
    rcases lt_or_le k i with (hik | hik)
    · have hkj : k + 1 < j := succ_lt_of_lt_of_lt hik hij
      have hkj' : k < j := lt_of_succ_lt hkj
      simp only [hik.not_le, hkj'.not_le, hkj.not_le, decide_False, Bool.toNat_false, add_zero]
    · have h : i ≤ k + (decide (j ≤ k + 1)).toNat := le_add_of_le_left hik
      simp_rw [hik, h, decide_True, Bool.toNat_true, add_assoc, add_comm]
  · simp_rw [hij, decide_True, Bool.not_true, Bool.toNat_false, add_zero, Bool.toNat_true]
    rcases le_or_lt i k with (hik | hik)
    · have hjk : j ≤ k := hij.trans hik
      have hjk' : j ≤ k + 1 := hjk.trans (le_succ _)
      simp only [hik,  hjk', hjk, decide_True, Bool.toNat_true, add_le_add_iff_right]
    · have h : k + (decide (j ≤ k)).toNat < i + 1 := add_lt_add_of_lt_of_le hik (Bool.toNat_le _)
      simp only [hik.not_le, h.not_le, decide_False, Bool.toNat_false, add_zero]

lemma testRes_testRes_of_lt {i j q : ℕ} (ha : i < j) : (q.testRes j).testRes i =
  (q.testRes i).testRes (j - 1) := by
  simp_rw [testRes_testRes (i := i), ha.not_le, decide_False, Bool.not_false,
    Bool.toNat_true, Bool.toNat_false, add_zero]

lemma testRes_testRes_of_ge {i j q : ℕ} (ha : j ≤ i) :
    (q.testRes j).testRes i = (q.testRes (i + 1)).testRes j := by
  simp_rw [testRes_testRes (i := i), ha, decide_True, Bool.not_true, Bool.toNat_false,
    tsub_zero, Bool.toNat_true]

@[simps!]
def testBitRes (i : ℕ) : ℕ ≃ Bool × ℕ :=
  ⟨fun n => (n.testBit i, n.testRes i), fun bp => bp.2.mergeBit i bp.1 ,
  fun _ => mergeBit_testRes_of_eq_of_testBit,
  fun _ => Prod.ext testBit_mergeBit_of_eq testRes_mergeBit_of_eq⟩

end BitResiduum

section FlipBit

def flipBit (q i : ℕ) := q ^^^ 2^i

lemma flipBit_def : ∀ (i q : ℕ), q.flipBit i = q ^^^ 2 ^ i := fun _ _ => rfl

lemma testBit_flipBit {q : ℕ} : (q.flipBit j).testBit i = (q.testBit i).xor (j = i) := by
  simp_rw [flipBit_def, testBit_xor, testBit_two_pow']

@[simp]
lemma testBit_flipBit_of_eq {q : ℕ} : (q.flipBit i).testBit i = !(q.testBit i) := by
  simp_rw [testBit_flipBit, decide_True, Bool.xor_true]

lemma testBit_flipBit_of_ne {i j q : ℕ} (h : i ≠ j) :
    (q.flipBit j).testBit i = q.testBit i := by
  simp_rw [testBit_flipBit, h.symm, decide_False, Bool.xor_false]

lemma flipBit_eq_mergeBit {i q : ℕ} :
    q.flipBit i = (q.testRes i).mergeBit i (!(testBit q i))  := by
  simp_rw [testBit_ext_iff]
  intro j
  rcases eq_or_ne j i with rfl | h
  · rw [testBit_flipBit_of_eq, testBit_mergeBit_of_eq]
  · rw [testBit_flipBit_of_ne h, testBit_mergeBit_of_ne h, testBit_testRes]
    rcases h.lt_or_lt with h | h
    · simp only [h.le.not_lt, h.not_le, decide_False, Bool.toNat_false, tsub_zero, add_zero]
    · simp only [h, decide_True, Bool.toNat_true, le_sub_one_of_lt h,
      Nat.sub_add_cancel (one_le_of_lt h)]

lemma mergeBit_testRes_of_eq {i p : ℕ} : (p.testRes i).mergeBit i b =
    bif (p.testBit i).xor !b then p else p.flipBit i := by
  rcases Bool.eq_or_eq_not b (p.testBit i) with rfl | rfl
  · simp_rw [mergeBit_testRes_of_eq_of_testBit, Bool.bne_not_self, cond_true]
  · simp_rw [Bool.not_not, bne_self_eq_false, flipBit_eq_mergeBit, cond_false]

lemma mergeBit_testRes {i j p : ℕ} : (p.testRes j).mergeBit i b =
    bif i = j then bif (p.testBit i).xor !b then p else p.flipBit i else
    (p.mergeBit (i + (decide (j < i)).toNat) b).testRes (j + (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp only [decide_True, lt_self_iff_false, decide_False, Bool.toNat_false, add_zero,
    testRes_mergeBit_of_eq, cond_true, mergeBit_testRes_of_eq]
  · simp_rw [hij, mergeBit_testRes_of_ne hij, decide_False, cond_false]

lemma testRes_flipBit {q : ℕ} :
    (q.flipBit j).testRes i = (q.testRes (i + (decide (j ≤ i)).toNat)).flipBit j := sorry

lemma flipBit_lt_iff_lt {q m : ℕ} (hi : i < m) : q.flipBit i < 2^m ↔ q < 2^m := by
  cases m
  · exact (not_lt_zero _ hi).elim
  · rw [Nat.lt_succ_iff] at hi
    simp_rw [flipBit_eq_mergeBit, mergeBit_lt_iff_lt hi, testRes_lt_iff_lt hi]

lemma flipBit_eq_of_testBit_true (h : testBit q i = true) :
    q.flipBit i = q - 2^i := by
  simp_rw [testBit_ext_iff]
  intro j
  rcases ne_or_eq i j with hij | rfl
  · rw [testBit_flipBit_of_ne hij.symm, testBit_sub_two_pow_ne_of_testBit_true hij h]
  · rw [testBit_flipBit_of_eq, testBit_sub_two_pow_eq_of_testBit_true h]

lemma flipBit_eq_of_testBit_false {i q : ℕ} (h : testBit q i = false) :
    q.flipBit i = q + 2^i := by
  simp_rw [testBit_ext_iff]
  intro j
  rcases ne_or_eq i j with hij | rfl
  · rw [testBit_flipBit_of_ne hij.symm, testBit_add_two_pow_ne_of_testBit_false hij h]
  · rw [testBit_flipBit_of_eq, testBit_add_two_pow_eq]

lemma flipBit_eq {i q : ℕ} : q.flipBit i = bif testBit q i then q - 2^i else q + 2^i := by
  cases h : testBit q i
  · rw [flipBit_eq_of_testBit_false h, Bool.cond_false]
  · rw [flipBit_eq_of_testBit_true h, Bool.cond_true]

lemma testBit_eq_false_true_of_lt_of_flipBit_ge {q r : ℕ} (hrq : r < q)
    (hf : q.flipBit i ≤ r.flipBit i) : r.testBit i = false ∧ q.testBit i = true := by
  simp_rw [flipBit_eq] at hf
  rcases hr : r.testBit i <;> rcases hq : q.testBit i <;> simp_rw [hr, hq] at hf
  · simp_rw [Bool.cond_false, add_le_add_iff_right] at hf
    exact (hf.not_lt hrq).elim
  · simp_rw [and_self]
  · simp_rw [Bool.cond_true, Bool.cond_false] at hf
    exact ((Nat.sub_le _ _).not_lt ((hrq.trans_le (Nat.le_add_right _ _)).trans_le hf)).elim
  · simp_rw [Bool.cond_true, tsub_le_iff_right, Nat.sub_add_cancel (testBit_implies_ge hr)] at hf
    exact (hf.not_lt hrq).elim

lemma flipBit_div_eq {i q : ℕ} (h : i < k) : q.flipBit i / 2^k = q / 2^k := by
  rcases Nat.exists_eq_add_of_lt h with ⟨k, rfl⟩
  simp_rw [add_assoc, add_comm k, ← add_assoc, pow_add _ _ k, ← Nat.div_div_eq_div_mul]
  suffices h : q.flipBit i / 2 ^ (i + 1) = q / 2 ^ (i + 1) by rw [h]
  simp_rw [flipBit_eq]
  rw [Bool.apply_cond (fun x => x / 2^(i + 1))]
  rcases h : q.testBit i
  · simp_rw [pow_succ, ← Nat.div_div_eq_div_mul]
    rw [testBit_false_iff_mod_two_pow_succ_lt_two_pow, pow_succ] at h
    rw [Bool.cond_false, ← Nat.div_add_mod q (2^i * 2), add_div_right _ (Nat.two_pow_pos _),
    succ_eq_add_one, mul_assoc, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt h, add_zero, Nat.mul_add_div zero_lt_two,
    Nat.mul_div_right _ zero_lt_two, Nat.div_eq_of_lt one_lt_two, add_zero]
  · rw [testBit_true_iff_two_pow_le_mod_two_pow_succ] at h
    rw [Bool.cond_true, ← Nat.div_add_mod q (2^(i + 1)), Nat.add_sub_assoc h,
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.mul_add_div (Nat.two_pow_pos _), Nat.mod_div_self,
    Nat.div_eq_of_lt ((Nat.sub_le _ _).trans_lt (Nat.mod_lt _ (Nat.two_pow_pos _)))]

lemma testBit_gt_eq_testBit_gt_flipBit_of_le_of_flipBit_ge {q r : ℕ} (hrq : r ≤ q)
    (hf : q.flipBit i ≤ r.flipBit i) (hik : i < k) : r.testBit k = (q.flipBit i).testBit k := by
  simp_rw [testBit_flipBit_of_ne hik.ne', testBit_to_div_mod, decide_eq_decide]
  suffices hs : r / 2^k = q / 2 ^ k by rw [hs]
  refine' le_antisymm (Nat.div_le_div_right hrq) _
  rw [← flipBit_div_eq hik, ← flipBit_div_eq (q := r) hik]
  exact Nat.div_le_div_right hf

lemma testBit_gt_eq_testBit_gt_flipBit_of_lt_of_flipBit_ge {q r : ℕ} (hrq : r < q)
    (hf : q.flipBit i ≤ r.flipBit i) (hik : i ≤ k) : r.testBit k = (q.flipBit i).testBit k := by
  rcases hik.lt_or_eq with hik | rfl
  · exact testBit_gt_eq_testBit_gt_flipBit_of_le_of_flipBit_ge hrq.le hf hik
  · have H := testBit_eq_false_true_of_lt_of_flipBit_ge hrq hf
    rw [testBit_flipBit_of_eq, H.1, H.2, Bool.not_true]

lemma eq_of_lowerBits_eq_of_lt_of_flipBit_ge {q r : ℕ} (hrq : r < q)
    (hf : q.flipBit i ≤ r.flipBit i) (h : ∀ {k}, k < i → r.testBit k = q.testBit k) :
    r = q.flipBit i := by
  rw [testBit_ext_iff]
  intros k
  rcases lt_or_le k i with hik | hik
  · rw [testBit_flipBit_of_ne hik.ne, h hik]
  · rw [testBit_gt_eq_testBit_gt_flipBit_of_lt_of_flipBit_ge hrq hf hik]

@[simps!]
def flipBitPerm (i : ℕ) : Equiv.Perm ℕ :=
  ⟨(flipBit · i), (flipBit · i), xor_cancel_right _, xor_cancel_right _⟩

lemma flipBitPerm_eq_permCongr (i : ℕ) :
    flipBitPerm i = (testBitRes i).symm.permCongr (boolInversion.prodCongr (Equiv.refl _)) := by
  simp_rw [Equiv.ext_iff, flipBitPerm_apply,
    flipBit_eq_mergeBit, Equiv.permCongr_apply, Equiv.symm_symm, testBitRes_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod_map, boolInversion_apply, id_eq,
    testBitRes_symm_apply, implies_true]

end FlipBit

end Nat

notation:75 "BV " arg:75  => Fin (2^arg)


lemma val_one_BV_succ : (1 : BV (m + 1)).val = (1 : ℕ) :=
  Nat.one_mod_of_ne_one (Nat.one_lt_two_pow' _).ne'

lemma two_pow_val_BV {i : Fin m} :
    (2^i.val : BV m).val = 2^(i : ℕ) := by
  cases m
  · exact i.elim0
  · induction' i using Fin.induction with i H
    · simp_rw [Fin.val_zero, pow_zero, val_one_BV_succ]
    · simp_rw [Fin.coe_castSucc] at H
      simp_rw [Fin.val_succ, pow_succ, mul_two, Fin.val_add, H]
      refine' Nat.mod_eq_of_lt _
      rw [← Nat.two_pow_succ]
      exact Nat.pow_lt_pow_of_lt one_lt_two (Nat.succ_lt_succ i.isLt)

lemma val_lt_two_pow_BV_succ {i : Fin (m + 1)} {r : BV (m + 1)} (h : r < 2^i.val) :
    r.val < 2^m := by
  rw [Fin.lt_iff_val_lt_val, two_pow_val_BV] at h
  exact h.trans_le (Nat.pow_le_pow_of_le one_lt_two (Nat.le_of_lt_succ i.isLt))

section BitRes

section GetMerge

@[simps! apply apply_fst apply_snd_val symm_apply_val]
def testBitRes (i : Fin (m + 1)) : BV (m + 1) ≃ Bool × BV m :=
⟨fun q => ⟨Nat.testBit q i, ⟨Nat.q.testRes i, (Nat.testRes_lt_iff_lt i.is_le).mpr q.is_lt⟩⟩,
  fun bp => ⟨Nat.mergeBit i bp.1 bp.2, (Nat.mergeBit_lt_iff_lt i.is_le).mpr bp.2.is_lt⟩,
  fun _ => by simp_rw [Nat.mergeBit_testRes_of_eq_of_testBit],
  fun _ => by simp_rw [Nat.testBit_mergeBit_of_eq, Nat.testRes_mergeBit_of_eq]⟩

def testBit (i : Fin (m + 1)) (q : BV (m + 1)) : Bool := (testBitRes i q).1

def testRes (i : Fin (m + 1)) (q : BV (m + 1)) : BV m := (testBitRes i q).2

def mergeBit (i : Fin (m + 1)) (b : Bool) (p : BV m) := (testBitRes i).symm (b, p)

lemma testBit_def : testBit q i = (testBitRes i q).fst := rfl

lemma testRes_def : q.testRes i = (testBitRes i q).snd := rfl

lemma mergeBit_def : p.mergeBit i b = (testBitRes i).symm (b, p) := rfl

@[simp]
lemma testBit_eq : testBit q i = Nat.testBit q i := rfl

@[simp]
lemma testRes_val_eq : (q.testRes i : ℕ) = Nat.q.testRes i := rfl

@[simp]
lemma mergeBit_val_eq : (p.mergeBit i b : ℕ) = Nat.p.mergeBit i b := rfl

lemma ge_of_testBit_true {i : Fin (m + 1)} (h : testBit q i = true) : 2^i.val ≤ q := by
  simp_rw [Fin.le_iff_val_le_val, two_pow_val_BV]
  exact Nat.ge_of_testBit_true h

lemma testBitRes_apply' (j : Fin (m + 1)) (q : BV (m + 1)) : (testBitRes j) q =
  (finTwoEquiv (finFunctionFinEquiv.symm q j),
  finFunctionFinEquiv (fun i => finFunctionFinEquiv.symm q (j.succAbove i))) := by
  simp_rw [testBitRes_apply, Nat.testBit_eq, Nat.testRes_eq, finTwoEquiv_apply, Prod.mk.injEq,
    ← Equiv.symm_apply_eq, decide_eq_decide]
  refine' ⟨_, _⟩
  · rw [Fin.ext_iff, Fin.val_one, finFunctionFinEquiv_symm_apply_val]
  · simp_rw [Function.funext_iff, Fin.ext_iff, finFunctionFinEquiv_symm_apply_val]
    intro a
    rcases lt_or_le a.castSucc j with h | h
    · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.coe_castSucc]
      rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at h
      rw [← Nat.testRes_eq, ← Nat.testBit_toNat, ← Nat.testBit_toNat, Nat.testBit_testRes_of_lt h]
    · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
      rw [Fin.le_iff_val_le_val, Fin.coe_castSucc] at h
      rw [← Nat.testRes_eq, ← Nat.testBit_toNat, ← Nat.testBit_toNat, Nat.testBit_testRes_of_ge h]

lemma testBitRes_reflect : testBitRes (i : Fin (m + 1)) =
    (calc
      _ ≃ (Fin (m + 1) → Fin 2)   := finFunctionFinEquiv.symm
      _ ≃ Fin 2 × (Fin m → Fin 2) := Equiv.piFinSuccAbove _ i
      _ ≃ _                       := finTwoEquiv.prodCongr finFunctionFinEquiv) := by
  simp_rw [Equiv.ext_iff, testBitRes_apply']
  exact fun _ => rfl

lemma testBitRes_symm_apply' (i : Fin (m + 1)) (bp : Bool × BV m) :
    (testBitRes i).symm bp = finFunctionFinEquiv
    (i.insertNth (finTwoEquiv.symm bp.fst) (finFunctionFinEquiv.symm bp.snd)) := by
  simp_rw [Equiv.symm_apply_eq, testBitRes_reflect, Equiv.instTrans_trans,
    finTwoEquiv_symm_apply, cond_eq_if, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.piFinSuccAbove_apply, Fin.extractNth_insertNth, Equiv.prodCongr_apply, Prod_map,
    finTwoEquiv_apply, ite_eq_left_iff, Bool.not_eq_true, zero_ne_one, imp_false, Bool.not_eq_false,
    Bool.decide_eq_true, Equiv.apply_symm_apply]

/-


@[simp]
lemma testBitRes_symm_apply (i : Fin (m + 1)) (bp : Bool × BV m) : (testBitRes i).symm bp =
  finFunctionFinEquiv (i.insertNth (finTwoEquiv.symm bp.fst) (finFunctionFinEquiv.symm bp.snd)) :=
  rfl
-/




/-
lemma testBit_def' : testBit q i = q.val.testBit i := by
  simp_rw [Nat.testBit_to_div_mod, testBit_def, testBitRes_apply, finTwoEquiv_apply,
  Fin.ext_iff, finFunctionFinEquiv_symm_apply_val, Fin.val_one]
-/




/-
lemma testRes_def_of_testBit {i : Fin (m + 1)} (h : testBit q i) :
    q.testRes i =
    ((finCongr (by rw [← pow_add,  ← add_assoc, Nat.sub_add_cancel i.is_le]) q).divNat
    (n := 2^(i.val + 1)) : BV (m - i.val)).castLE ((Nat.pow_le_pow_iff_right (one_lt_two)).mpr
      (by simp_rw [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.zero_le])) +
    ((finCongr (by rw [← pow_add, Nat.sub_add_cancel i.is_le']) q).modNat (n := 2^i.val)).castLE
    ((Nat.pow_le_pow_iff_right (one_lt_two)).mpr i.is_le : 2^i.val ≤ 2^m) := by
  simp_rw [testRes_def, testBitRes_apply, Equiv.apply_eq_iff_eq_symm_apply, Function.funext_iff,
  Fin.ext_iff, finFunctionFinEquiv_symm_apply_val, finCongr_apply, Fin.val_add,
  Fin.coe_castLE, Fin.coe_divNat, Fin.coe_modNat, Fin.coe_cast, Nat.mod_eq_of_lt (smoopy i q.isLt)]
  intro a
  rcases lt_or_le (a.castSucc) i with h | h
  · simp_rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.coe_castSucc]
    sorry
  · simp_rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
  simp_rw [Fin.ext_iff, Fin.val_add, finCongr_apply, Fin.coe_castLE, Fin.coe_divNat,
    Fin.coe_modNat, Fin.coe_cast, Nat.mod_eq_of_lt (smoopy i q.isLt)]

lemma testRes_def_val : q.testRes i = ⟨q / 2^(i.val + 1) + q % 2^i.val, smoopy i q.isLt⟩ := by
  simp_rw [testRes_def, testBitRes_apply, Equiv.apply_eq_iff_eq_symm_apply, Function.funext_iff,
  Fin.ext_iff, finFunctionFinEquiv_symm_apply_val]
  intro a
  rcases lt_or_le (a.castSucc) i with h | h
  · simp_rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.coe_castSucc]
    sorry
  · simp_rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
  rcases h : (testBit q i) with (_ | _)
  · rw [cond_false, tsub_zero, testRes_def]
    simp_rw [testBitRes_apply, finTwoEquiv_apply, Fin.isValue, finFunctionFinEquiv_apply_val,
      finFunctionFinEquiv_symm_apply_val]
-/



lemma testBitRes_apply_zero : testBitRes i 0 = (false, 0) := by
ext <;> simp only [testBitRes_apply', finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply,
  Fin.val_zero', Nat.zero_div, Nat.zero_mod, Fin.zero_eta, finTwoEquiv_apply, zero_ne_one,
  decide_False, Equiv.ofRightInverseOfCardLE_apply, Fin.val_zero, zero_mul, Finset.sum_const_zero]

lemma testBit_def_zero : testBit i 0 = false := by
rw [testBit_def, testBitRes_apply_zero]

lemma testRes_def_zero : testRes i 0 = 0 := by
rw [testRes_def, testBitRes_apply_zero]

lemma mergeBit_apply_false_zero : mergeBit i false 0 = 0 := by
rw [mergeBit_def, ← testBitRes_apply_zero (i := i), Equiv.symm_apply_apply]

lemma testBitRes_apply_two_pow {i : Fin (m + 1)} : testBitRes i (2^i.val) = (true, 0) := by
  ext
  · simp only [testBitRes_apply', finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply,
    two_pow_val_BV, gt_iff_lt, Nat.ofNat_pos, pow_pos, Nat.div_self, Nat.mod_succ, Fin.mk_one,
    Fin.isValue, finTwoEquiv_apply, decide_True, Equiv.ofRightInverseOfCardLE_apply]
  · simp only [testBitRes_apply', finTwoEquiv_apply, Fin.isValue, finFunctionFinEquiv_apply_val,
    finFunctionFinEquiv_symm_apply_val, two_pow_val_BV, Fin.val_zero', Finset.sum_eq_zero_iff,
    Finset.mem_univ, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false,
    true_implies]
    intro x
    rcases (Fin.succAbove_ne i x).lt_or_lt with h | h <;> rw [Fin.lt_iff_val_lt_val] at h
    · rw [Nat.pow_div h.le zero_lt_two, Nat.pow_mod, Nat.mod_self,
        Nat.zero_pow (Nat.sub_pos_of_lt h), Nat.zero_mod]
    · rw [Nat.div_eq_of_lt (pow_lt_pow_right one_lt_two h), Nat.zero_mod]

lemma testBit_def_two_pow {i : Fin (m + 1)} : testBit i (2^i.val) = true := by
  rw [testBit_def, testBitRes_apply_two_pow]

lemma testBit_def_zero_one : testBit 0 (1 : BV (m + 1)) = true := testBit_def_two_pow

lemma testRes_def_two_pow {i : Fin (m + 1)} : testRes i (2^i.val) = 0 := by
  rw [testRes_def, testBitRes_apply_two_pow]

lemma mergeBit_apply_true_zero {i : Fin (m + 1)} :
  mergeBit i true 0 = 2^i.val := by
  rw [mergeBit_def, ← testBitRes_apply_two_pow (i := i), Equiv.symm_apply_apply]

lemma testBitRes_lt {i : Fin (m + 1)} {r : BV (m + 1)} (h : r < 2^i.val) :
    testBitRes i r = (false, r.castLT (val_lt_two_pow_BV_succ h)) := by
  rw [Fin.lt_iff_val_lt_val, two_pow_val_BV] at h
  ext : 1
  · simp_rw [testBitRes_apply', Equiv.apply_eq_iff_eq_symm_apply, finTwoEquiv_symm_apply, cond_false,
    Fin.ext_iff, finFunctionFinEquiv_symm_apply_val,
    Nat.div_eq_of_lt h, Nat.zero_mod, Fin.val_zero]
  · simp_rw [testBitRes_apply', Equiv.apply_eq_iff_eq_symm_apply, Function.funext_iff, Fin.ext_iff,
    finFunctionFinEquiv_symm_apply_val, Fin.coe_castLT]
    intro x
    rcases lt_or_le x.castSucc i with h' | h'
    · simp_rw [Fin.succAbove_of_castSucc_lt _ _ h', Fin.coe_castSucc]
    · simp_rw [Fin.succAbove_of_le_castSucc _ _ h', Fin.val_succ]
      rw [Fin.le_iff_val_le_val, Fin.coe_castSucc] at h'
      rw [Nat.div_eq_of_lt (h.trans_le (Nat.pow_le_pow_of_le one_lt_two h')),
      Nat.div_eq_of_lt (h.trans_le (Nat.pow_le_pow_of_le one_lt_two (h'.trans (Nat.le_succ x))))]

lemma testBit_lt {i : Fin (m + 1)} {r : BV (m + 1)} (h : r < 2^i.val) :
    testBit i r = false := by rw [testBit_def, testBitRes_lt h]

lemma testRes_lt {i : Fin (m + 1)} {r : BV (m + 1)} (h : r < 2^i.val) :
    testRes i r = r.castLT (val_lt_two_pow_BV_succ h) :=
  by rw [testRes_def, testBitRes_lt h]

def testBitResSucc (i : Fin (m + 1)) : BV (m + 2) ≃ Bool × BV (m + 1) :=
calc
  _ ≃ _ := testBitRes 0
  _ ≃ _ := (Equiv.refl _).prodCongr (testBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (testBitRes 0).symm

lemma testBitResSucc_apply {i : Fin (m + 1)} :
    testBitResSucc i q = (((testBitRes i) ((testBitRes 0) q).2).1,
    (testBitRes 0).symm (((testBitRes 0) q).1, ((testBitRes i) ((testBitRes 0) q).2).2)) := rfl

lemma testBitResSucc_symm_apply {i : Fin (m + 1)} : (testBitResSucc i).symm (b, p) =
    (testBitRes 0).symm ((testBitRes 0 p).1, (testBitRes i).symm (b, (testBitRes 0 p).2)) := rfl

lemma testBitRes_succ {i : Fin (m + 1)} : testBitRes (i.succ) = testBitResSucc i := by
  simp_rw [Equiv.ext_iff, testBitResSucc_apply,
    testBitRes_apply', testBitRes_symm_apply', Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_zero, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_succ, true_and, implies_true]

lemma testBitRes_succ_apply {i : Fin (m + 1)} : testBitRes (i.succ) q =
    (((testBitRes i) ((testBitRes 0) q).2).1,
    (testBitRes 0).symm (((testBitRes 0) q).1, ((testBitRes i) ((testBitRes 0) q).2).2)) := by
  rw [testBitRes_succ, testBitResSucc_apply]

lemma testBitRes_succ_symm_apply {i : Fin (m + 1)} : (testBitRes (i.succ)).symm (b, p) =
    (testBitRes 0).symm ((testBitRes 0 p).1, (testBitRes i).symm (b, (testBitRes 0 p).2)) := by
  rw [testBitRes_succ, testBitResSucc_symm_apply]

lemma testRes_succ (i : Fin (m + 1)) : testRes (i.succ) q =
    mergeBit 0 (testBit 0 q) (testRes i (testRes 0 q)) := by
  simp_rw [testRes_def, mergeBit_def, testBit_def, testBitRes_succ_apply]

lemma testBit_succ (i : Fin (m + 1)) :
    testBit (i.succ) q = testBit i (testRes 0 q) := by
  simp_rw [testRes_def, testBit_def, testBitRes_succ_apply]

lemma mergeBit_succ (i : Fin (m + 1)) : mergeBit i.succ b q =
    mergeBit 0 (testBit 0 q) (mergeBit i b (testRes 0 q)) := by
  simp_rw [mergeBit_def, testBit_def, testRes_def, testBitRes_succ_symm_apply]

def testBitResCastSucc (i : Fin (m + 1)) : BV (m + 2) ≃ Bool × BV (m + 1) :=
calc
  _ ≃ _ := testBitRes (Fin.last _)
  _ ≃ _ := (Equiv.refl _).prodCongr (testBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (testBitRes (Fin.last _)).symm

lemma testBitResCastSucc_apply {i : Fin (m + 1)} :
    testBitResCastSucc i q = (((testBitRes i) ((testBitRes (Fin.last _)) q).2).1,
    (testBitRes (Fin.last _)).symm (((testBitRes (Fin.last _)) q).1,
    ((testBitRes i) ((testBitRes (Fin.last _)) q).2).2)) := rfl

lemma testBitResCastSucc_symm_apply {i : Fin (m + 1)} : (testBitResCastSucc i).symm (b, p) =
    (testBitRes (Fin.last _)).symm ((testBitRes (Fin.last _) p).1,
    (testBitRes i).symm (b, (testBitRes (Fin.last _) p).2)) := rfl

lemma testBitRes_castSucc {i : Fin (m + 1)} : testBitRes (i.castSucc) = testBitResCastSucc i := by
  simp_rw [Equiv.ext_iff, testBitResCastSucc_apply,
    testBitRes_apply', testBitRes_symm_apply', Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_last, Fin.castSucc_succAbove_last,
    Fin.castSucc_succAbove_castSucc, true_and, implies_true]

lemma testBitRes_castSucc_apply {i : Fin (m + 1)} : testBitRes (i.castSucc) q =
    (((testBitRes i) ((testBitRes (Fin.last _)) q).2).1,
    (testBitRes (Fin.last _)).symm (((testBitRes (Fin.last _)) q).1,
    ((testBitRes i) ((testBitRes (Fin.last _)) q).2).2)) := by
  rw [testBitRes_castSucc, testBitResCastSucc_apply]

lemma testBitRes_castSucc_symm_apply {i : Fin (m + 1)} : (testBitRes (i.castSucc)).symm (b, p) =
    (testBitRes (Fin.last _)).symm ((testBitRes (Fin.last _) p).1,
    (testBitRes i).symm (b, (testBitRes (Fin.last _) p).2)) := by
  rw [testBitRes_castSucc, testBitResCastSucc_symm_apply]

lemma testRes_castSucc (i : Fin (m + 1)) : testRes (i.castSucc) q =
    mergeBit (Fin.last _) (testBit (Fin.last _) q) (testRes i (testRes (Fin.last _) q)) := by
  simp_rw [testRes_def, mergeBit_def, testBit_def, testBitRes_castSucc_apply]

lemma testBit_castSucc (i : Fin (m + 1)) :
    testBit (i.castSucc) q = testBit i (testRes (Fin.last _) q) := by
  simp_rw [testRes_def, testBit_def, testBitRes_castSucc_apply]

lemma mergeBit_castSucc (i : Fin (m + 1)) : mergeBit i.castSucc b q =
    mergeBit (Fin.last _) (testBit (Fin.last _) q) (mergeBit i b (testRes (Fin.last _) q)) := by
  simp_rw [mergeBit_def, testBit_def, testRes_def, testBitRes_castSucc_symm_apply]

def testBitResZero : BV (m + 1) ≃ Bool × BV m :=
 calc
  _ ≃ _ := finProdFinEquiv.symm
  _ ≃ _ := Equiv.prodComm ..
  _ ≃ _ := finTwoEquiv.prodCongr (Equiv.refl _)

lemma testBitResZero_apply : testBitResZero q = (finTwoEquiv q.modNat, q.divNat) := rfl

lemma testBitResZero_symm_apply : testBitResZero.symm (b, p) =
  finProdFinEquiv (p, bif b then 1 else 0) := by cases b <;> rfl

lemma testBitRes_zero : testBitRes (0 : Fin (m + 1)) = testBitResZero := by
  ext q : 1
  simp_rw [testBitRes_apply', testBitResZero_apply, Fin.zero_succAbove, finFunctionFinEquiv,
    Equiv.ofRightInverseOfCardLE_symm_apply, Fin.val_zero, pow_zero, Nat.div_one,
    finTwoEquiv_apply, Fin.val_succ, Equiv.ofRightInverseOfCardLE_apply,
    Nat.pow_eq, Prod.mk.injEq, decide_eq_decide, Fin.ext_iff, Fin.val_one, Fin.coe_modNat,
    Finset.sum_fin_eq_sum_range, dite_eq_ite, Fin.coe_divNat, true_and]
  rw [Finset.sum_ite_of_true (h := fun _ H => (Finset.mem_range.mp H))]
  refine' Nat.eq_of_mul_eq_mul_left (zero_lt_two)
    (add_right_cancel (b := (q : ℕ) / 2 ^ 0 % 2 * 2 ^ 0) _)
  simp_rw [Finset.mul_sum, mul_left_comm (2 : ℕ), ← Nat.pow_succ', Nat.succ_eq_add_one,
  ← Finset.sum_range_succ' (fun x => (q : ℕ) / 2 ^ x % 2 * 2 ^ x), pow_zero, Nat.div_one,
    mul_one, Nat.div_add_mod, Finset.sum_range, ← finFunctionFinEquiv_symm_apply_val,
    ← finFunctionFinEquiv_apply_val, Equiv.apply_symm_apply]

lemma testBitRes_zero_apply : testBitRes (0 : Fin (m + 1)) q = (finTwoEquiv q.modNat, q.divNat) := by
  simp_rw [testBitRes_zero, testBitResZero_apply]

lemma testBitRes_zero_symm_apply : (testBitRes (0 : Fin (m + 1))).symm (b, p) =
  finProdFinEquiv (p, bif b then 1 else 0) := by simp_rw [testBitRes_zero, testBitResZero_symm_apply]

lemma testBit_zero : testBit 0 q = finTwoEquiv q.modNat := by
  simp_rw [testBit_def, testBitRes_zero_apply]

lemma testRes_zero : testRes 0 q = q.divNat := by
  simp_rw [testRes_def, testBitRes_zero_apply]

lemma mergeBit_zero : mergeBit 0 b p = finProdFinEquiv (p, (bif b then 1 else 0)) := by
  simp_rw [mergeBit_def, testBitRes_zero_symm_apply]

lemma mergeBit_zero_divNat_modNat : ((mergeBit 0 b p).divNat, (mergeBit 0 b p).modNat) =
  (p, (bif b then 1 else 0)) := by
  simp_rw [← finProdFinEquiv_symm_apply, Equiv.symm_apply_eq]
  exact mergeBit_zero

lemma mergeBit_zero_divNat : (mergeBit 0 b p).divNat = p :=
(Prod.ext_iff.mp (mergeBit_zero_divNat_modNat (b := b) (p := p))).1

lemma mergeBit_zero_modNat : (mergeBit 0 b p).modNat = bif b then 1 else 0 :=
(Prod.ext_iff.mp (mergeBit_zero_divNat_modNat (b := b) (p := p))).2

lemma mergeBit_zero_apply_true_zero_eq_one : mergeBit (0 : Fin (m + 1)) true 0 = 1 := by
  simp_rw [mergeBit_zero, Fin.ext_iff, finProdFinEquiv_apply_val, Fin.val_zero', mul_zero,
  add_zero, Bool.cond_true, Fin.val_one, Fin.val_one', ← Nat.pow_succ,
  Nat.mod_eq_of_lt (Nat.one_lt_pow' _ _ )]


def testBitResLast : BV (m + 1) ≃ Bool × BV m :=
 calc
  _ ≃ _ := finCongr (mul_comm _ _)
  _ ≃ _ := finProdFinEquiv.symm
  _ ≃ _ := finTwoEquiv.prodCongr (Equiv.refl _)

lemma testBitResLast_apply {q : BV (m + 1)} :
  testBitResLast q =
  (finTwoEquiv (finCongr (mul_comm _ _) q).divNat, (finCongr (mul_comm _ _) q).modNat) := rfl

lemma testBitResLast_symm_apply {p : BV m} : testBitResLast.symm (b, p) =
  finCongr (mul_comm _ _) (finProdFinEquiv (bif b then 1 else 0, p)) := by cases b <;> rfl

lemma mergeBit_base_true : mergeBit (m := 0) i true p = 1 := by
rw [Fin.eq_zero p, Fin.eq_zero i] ; exact mergeBit_zero_apply_true_zero_eq_one

lemma mergeBit_base_false : mergeBit (m := 0) i false p = 0 := by
rw [Fin.eq_zero p] ; exact mergeBit_apply_false_zero

lemma mergeBit_base : mergeBit (m := 0) i b p = if b then 1 else 0 :=
  b.rec mergeBit_base_false mergeBit_base_true

lemma testBit_base : testBit (m := 0) i q = decide (q = 1) := by
  rw [Fin.eq_zero i]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

lemma testRes_base : testRes (m := 0) i q = 0 := by
  rw [Fin.eq_zero i]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

def testBitResSuccAbove (j : Fin (m + 2)) (i : Fin (m + 1)) :
  BV (m + 2) ≃ Bool × BV (m + 1) :=
calc
  _ ≃ _ := testBitRes j
  _ ≃ _ := (Equiv.refl _).prodCongr (testBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (testBitRes (i.predAbove j)).symm

lemma testBitResSuccAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
    testBitResSuccAbove j i q = (((testBitRes i) ((testBitRes j) q).2).1,
    (testBitRes (i.predAbove j)).symm (((testBitRes j) q).1,
    ((testBitRes i) ((testBitRes j) q).2).2)) := rfl

lemma testBitResSuccAbove_symm_apply : (testBitResSuccAbove j i).symm (b, p) =
    (testBitRes j).symm ((testBitRes (i.predAbove j) p).1,
    (testBitRes i).symm (b, (testBitRes (i.predAbove j) p).2)) := rfl

lemma testBitRes_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} :
  testBitRes (j.succAbove i) = testBitResSuccAbove j i := by
  simp_rw [Equiv.ext_iff, testBitResSuccAbove_apply,
    testBitRes_apply', testBitRes_symm_apply', Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_succAbove_predAbove,
    Fin.succAbove_succAbove_predAbove_succAbove, true_and, implies_true]

lemma testBitRes_succAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} : testBitRes (j.succAbove i) q =
    (((testBitRes i) ((testBitRes j) q).2).1,
    (testBitRes (i.predAbove j)).symm (((testBitRes j) q).1,
    ((testBitRes i) ((testBitRes j) q).2).2)) := by
  rw [testBitRes_succAbove, testBitResSuccAbove_apply]

lemma testBitRes_succAbove_symm_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
    (testBitRes (j.succAbove i)).symm (b, p) =
    (testBitRes j).symm ((testBitRes (i.predAbove j) p).1,
    (testBitRes i).symm (b, (testBitRes (i.predAbove j) p).2)) := by
  rw [testBitRes_succAbove, testBitResSuccAbove_symm_apply]

lemma testRes_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} : testRes (j.succAbove i) q =
    mergeBit (i.predAbove j) (testBit j q) (testRes i (testRes j q)) := by
  simp_rw [testRes_def, mergeBit_def, testBit_def, testBitRes_succAbove_apply]

lemma testBit_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} :
    testBit (j.succAbove i) q = testBit i (testRes j q) := by
  simp_rw [testBit_eq, testRes_val_eq, Nat.testBit_testRes, Fin.val_succAbove]

lemma mergeBit_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} : mergeBit (j.succAbove i) b q =
    mergeBit j (testBit (i.predAbove j) q) (mergeBit i b (testRes (i.predAbove j) q)) := by
  simp_rw [mergeBit_def, testBit_def, testRes_def, testBitRes_succAbove_symm_apply]

@[simp]
lemma testBit_mergeBit : testBit i (p.mergeBit i b) = b := by
simp_rw [testBit_def, mergeBit_def, Equiv.apply_symm_apply]

@[simp]
lemma testRes_mergeBit  : testRes i (p.mergeBit i b) = p := by
simp_rw [testRes_def, mergeBit_def, Equiv.apply_symm_apply]

@[simp]
lemma mergeBit_testBit_testRes : mergeBit i (testBit q i) (q.testRes i) = q := by
simp_rw [testRes_def, mergeBit_def, testBit_def, Prod.mk.eta, Equiv.symm_apply_apply]

lemma mergeBit_surj (i : Fin (m + 1)) (q : BV (m + 1)) :
  ∃ b p, p.mergeBit i b = q :=
  ⟨testBit q i, q.testRes i, mergeBit_testBit_testRes⟩

lemma mergeBit_Bool_inj (i : Fin (m + 1)) (h : mergeBit i b₁ p₁ = mergeBit i b₂ p₂) :
  b₁ = b₂ := by
  have h₂ := (congrArg (testBit i) h) ; simp only [testBit_mergeBit] at h₂ ; exact h₂

lemma mergeBit_Fin_inj (i : Fin (m + 1)) (h : mergeBit i b₁ p₁ = mergeBit i b₂ p₂) :
  p₁ = p₂ := by
  have h₂ := (congrArg (testRes i) h) ; simp_rw [testRes_mergeBit] at h₂ ; exact h₂

lemma mergeBit_inj (i : Fin (m + 1)) (h : mergeBit i b₁ p₁ = mergeBit i b₂ p₂) :
  b₁ = b₂ ∧ p₁ = p₂ :=
  ⟨mergeBit_Bool_inj i h, mergeBit_Fin_inj i h⟩

lemma mergeBit_inj_iff (i : Fin (m + 1)) : mergeBit i b₁ p₁ = mergeBit i b₂ p₂ ↔
  b₁ = b₂ ∧ p₁ = p₂ :=
  ⟨mergeBit_inj i, by rintro ⟨rfl, rfl⟩ ; rfl⟩

lemma mergeBit_ne_inj_iff (i : Fin (m + 1)) : mergeBit i b₁ p₁ ≠ mergeBit i b₂ p₂ ↔
  b₁ ≠ b₂ ∨ p₁ ≠ p₂ := by rw [ne_eq, mergeBit_inj_iff, not_and_or]

lemma testRes_testBit_inj (i : Fin (m + 1)) (h₁ : testBit q i₁ = testBit q i₂)
  (h₂ : q.testRes i₁ = q.testRes i₂) : q₁ = q₂ :=
  by rw [← mergeBit_testBit_testRes (i := i) (q := q₁), h₁, h₂, mergeBit_testBit_testRes]

lemma testRes_testBit_inj_iff (i : Fin (m + 1)) :
q₁ = q₂ ↔ testBit q i₁ = testBit q i₂ ∧ q.testRes i₁ = q.testRes i₂ :=
⟨by rintro rfl ; exact ⟨rfl, rfl⟩, and_imp.mpr (testRes_testBit_inj i)⟩

lemma mergeBit_eq_iff :
  p.mergeBit i b = q ↔ (testBit q i = b) ∧ (q.testRes i = p) :=
⟨fun H => H ▸ ⟨testBit_mergeBit, testRes_mergeBit⟩, fun ⟨rfl, rfl⟩ => mergeBit_testBit_testRes⟩

lemma eq_mergeBit_iff :
    q = p.mergeBit i b ↔ (testBit q i = b) ∧ (q.testRes i = p) := by
    rw [← mergeBit_eq_iff, eq_comm]

lemma mergeBit_ne_iff :
    p.mergeBit i b ≠ q ↔ (testBit q i ≠ b) ∨ (q.testRes i ≠ p) := by
    simp_rw [ne_eq, mergeBit_eq_iff, Decidable.not_and_iff_or_not]

lemma ne_mergeBit_iff :
    q ≠ p.mergeBit i b ↔ (testBit q i ≠ b) ∨ (q.testRes i ≠ p) := by
    rw [← mergeBit_ne_iff, ne_comm]

lemma mergeBit_testRes_of_testBit_eq (h : testBit q i = b) : mergeBit i b (q.testRes i) = q := by
simp_rw [← h, mergeBit_testBit_testRes]

lemma mergeBit_testRes_cases (i : Fin (m + 1)) (q : BV (m + 1)) :
(testBit q i = false ∧ mergeBit i false (q.testRes i) = q) ∨
(testBit q i = true ∧ mergeBit i true (q.testRes i) = q) := by
  rcases (testBit q i).dichotomy with (h | h) <;>
  simp_rw [h, mergeBit_testRes_of_testBit_eq h, false_and, and_self]
  · simp_rw [or_false]
  · simp_rw [or_true]

lemma mergeBit_testBit_of_testRes_eq (h : q.testRes i = p) : mergeBit i (testBit q i) p = q := by
simp_rw [← h, mergeBit_testBit_testRes]

lemma mergeBit_inv (h₁ : testBit q i = b) (h₂ : q.testRes i = p) : p.mergeBit i b = q := by
simp_rw [← h₁, ← h₂, mergeBit_testBit_testRes]

lemma testRes_inv (i : Fin (m + 1)) (h : mergeBit i (testBit q i) p = q) : q.testRes i = p := by
  rcases mergeBit_surj i q with ⟨b, p', rfl⟩ ; rw [testRes_mergeBit]
  exact (mergeBit_Fin_inj i h).symm

lemma testBit_inv (i : Fin (m + 1)) (h : mergeBit i b (q.testRes i) = q) : testBit q i = b := by
  rcases mergeBit_surj i q with ⟨b', p', rfl⟩ ; rw [testBit_mergeBit]
  exact (mergeBit_Bool_inj i h).symm

lemma forall_iff_forall_mergeBit (i : Fin (m + 1)) {pr : BV (m + 1) → Prop} :
  (∀ (q : BV (m + 1)), pr q) ↔ (∀ b p, pr (p.mergeBit i b)) :=
  ⟨fun h _ _ => h _, fun h q => by rcases mergeBit_surj i q with ⟨b, p, rfl⟩ ; exact h _ _⟩

lemma forall_iff_forall_mergeBit_bool (i : Fin (m + 1)) {pr : BV (m + 1) → Prop} :
  (∀ (q : BV (m + 1)), pr q) ↔
  (∀ p, pr (mergeBit i false p)) ∧ (∀ p, pr (mergeBit i true p)) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩,
    fun h q => by rcases mergeBit_surj i q with ⟨(h|h), p, rfl⟩
                  · exact h.1 _
                  · exact h.2 _⟩

lemma exists_iff_exists_mergeBit (i : Fin (m + 1)) {pr : BV (m + 1) → Prop} :
(∃ (q : BV (m + 1)), pr q) ↔ (∃ b p, pr (p.mergeBit i b)) :=
⟨ fun ⟨q, hq⟩ => ⟨testBit q i, q.testRes i, mergeBit_testBit_testRes ▸ hq⟩,
  fun ⟨b, p, hbp⟩ => ⟨p.mergeBit i b, hbp⟩⟩

lemma testBit_surj (i : Fin (m + 1)) (q : BV (m + 1)) :
  ∃ p, mergeBit i (testBit q i) p = q :=
  ⟨q.testRes i, mergeBit_testBit_testRes⟩

lemma testRes_surj (i : Fin (m + 1)) (q : BV (m + 1)) :
  ∃ b, mergeBit i b (q.testRes i) = q :=
  ⟨testBit q i, mergeBit_testBit_testRes⟩

lemma ne_iff_testBit_ne_or_testRes_ne (i : Fin (m + 1)) :
q₁ ≠ q₂ ↔ testBit q i₁ ≠ testBit q i₂ ∨ q.testRes i₁ ≠ q.testRes i₂ := by
rw [ne_eq q₁, testRes_testBit_inj_iff i, not_and_or]

lemma ne_of_testBit_ne (i : Fin (m + 1)) (h : testBit q i₁ ≠ testBit q i₂) :
q₁ ≠ q₂ := (ne_iff_testBit_ne_or_testRes_ne i).mpr (Or.inl h)

lemma ne_of_testRes_ne (i : Fin (m + 1)) (h : q.testRes i₁ ≠ q.testRes i₂) :
q₁ ≠ q₂ := (ne_iff_testBit_ne_or_testRes_ne i).mpr (Or.inr h)

lemma testBit_ext_iff {q q' : BV (m + 1)} :
    q = q' ↔ (∀ i : Fin (m + 1), testBit q i = testBit q i') := by
  refine' ⟨fun h _ => h ▸ rfl, fun h => _⟩
  induction' m with m IH
  · simp_rw [testRes_testBit_inj_iff 0, Fin.eq_zero, and_true, h]
  · simp_rw [Fin.forall_fin_succ (P := fun i => testBit q i = testBit q i'), testBit_succ] at h
    exact (testRes_testBit_inj_iff 0).mpr ⟨h.1, IH h.2⟩

lemma testBit_ext {q q' : BV (m + 1)} (h : ∀ i : Fin (m + 1), testBit q i = testBit q i') :
    q = q' := testBit_ext_iff.mpr h

end GetMerge

section bitInvar

def bitInvar (i : Fin (m + 1)) (f : Function.End (BV (m + 1))) : Prop :=
∀ q, testBit i (f q) = testBit q i

lemma bitInvar_iff_testBit_apply_eq_testBit :
  bitInvar i f ↔ ∀ q, testBit i (f q) = testBit q i := Iff.rfl

lemma bitInvar_of_testBit_def_eq_testBit {f : Function.End (BV (m + 1))}
  (h : ∀ q, testBit i (f q) = testBit q i) : bitInvar i f :=
  bitInvar_iff_testBit_apply_eq_testBit.mpr h

lemma testBit_def_eq_testBit_of_bitInvar (h : bitInvar i f) : testBit i (f q) = testBit q i :=
bitInvar_iff_testBit_apply_eq_testBit.mp h _

lemma bitInvar_comp_of_bitInvar (hf : bitInvar i f) (hg : bitInvar i g) : bitInvar i (f ∘ g) :=
  fun q => by simp_rw [Function.comp_apply, hf (g q), hg q]

lemma bitInvar_mul_of_bitInvar (hf : bitInvar i f) (hg : bitInvar i g) : bitInvar i (f * g) :=
  bitInvar_comp_of_bitInvar hf hg

lemma bitInvar_of_comp_bitInvar_bitInvar (hfg : bitInvar i (f ∘ g)) (h : bitInvar i f) :
  bitInvar i g := fun q => by rw [← h (g q), ← hfg q, Function.comp_apply]

lemma bitInvar_of_mul_bitInvar_bitInvar (hfg : bitInvar i (f * g)) (h : bitInvar i f) :
  bitInvar i g := bitInvar_of_comp_bitInvar_bitInvar hfg h

lemma id_bitInvar : bitInvar i id := fun _ => rfl

lemma one_bitInvar : bitInvar i 1 := id_bitInvar

lemma bitInvar_of_rightInverse_bitInvar (hfg : Function.RightInverse g f) (h : bitInvar i f) :
  bitInvar i g := bitInvar_of_comp_bitInvar_bitInvar (hfg.comp_eq_id ▸ id_bitInvar) h

lemma bitInvar_of_leftInverse_bitInvar (hfg : Function.LeftInverse g f) (h : bitInvar i g) :
  bitInvar i f := bitInvar_of_rightInverse_bitInvar hfg h

lemma mergeBit_testBit_testRes_def_eq_apply_of_bitinvar (h : bitInvar i f) :
mergeBit i (testBit q i) (testRes i (f q)) = f q := by
  rw [← h q, mergeBit_testBit_testRes]

@[simp]
lemma mergeBit_testRes_def_mergeBit_of_bitinvar (h : bitInvar i f) :
mergeBit i b (testRes i (f (p.mergeBit i b))) = f (p.mergeBit i b) := by
  convert (testBit_mergeBit ▸ mergeBit_testBit_testRes_def_eq_apply_of_bitinvar h)

lemma symm_bitInvar_iff_bitInvar {π : Equiv.Perm (BV (m + 1))} :
  bitInvar i ⇑π.symm ↔ bitInvar i ⇑π :=
  ⟨bitInvar_of_leftInverse_bitInvar π.left_inv, bitInvar_of_rightInverse_bitInvar π.right_inv⟩

lemma symm_bitInvar_of_bitInvar {π : Equiv.Perm (BV (m + 1))} (h : bitInvar i ⇑π) :
  bitInvar i ⇑π.symm := symm_bitInvar_iff_bitInvar.mpr h

lemma bitInvar_of_symm_bitInvar {π : Equiv.Perm (BV (m + 1))} (h : bitInvar i ⇑π.symm) :
bitInvar i ⇑π := symm_bitInvar_iff_bitInvar.mp h

lemma inv_bitInvar_iff_bitInvar {π : Equiv.Perm (BV (m + 1))} :
  bitInvar i (⇑π⁻¹) ↔ bitInvar i ⇑π := symm_bitInvar_iff_bitInvar

lemma inv_bitInvar_of_bitInvar {π : Equiv.Perm (BV (m + 1))} (h : bitInvar i ⇑π) :
  bitInvar i (⇑π⁻¹) := symm_bitInvar_of_bitInvar h

lemma bitInvar_of_inv_bitInvar {π : Equiv.Perm (BV (m + 1))}
  (h : bitInvar i (⇑π⁻¹)) : bitInvar i ⇑π := bitInvar_of_symm_bitInvar h

lemma bitInvar_mulPerm_of_bitInvar {π ρ : Equiv.Perm (BV (m + 1))} (hπ : bitInvar i ⇑π)
  (hρ : bitInvar i ⇑ρ) : bitInvar i ⇑(π*ρ) :=
  Equiv.Perm.coe_mul _ _ ▸ bitInvar_mul_of_bitInvar hπ hρ

lemma bitInvar_of_mulPerm_bitInvar_bitInvar {π ρ : Equiv.Perm (BV (m + 1))}
  (hfg : bitInvar i ⇑(π*ρ : Equiv.Perm (BV (m + 1)))) (h : bitInvar i ⇑π) : bitInvar i ⇑ρ :=
  bitInvar_of_mul_bitInvar_bitInvar hfg h

lemma onePerm_bitInvar {i : Fin (m + 1)} : bitInvar i ⇑(1 : Equiv.Perm (BV (m + 1))) :=
one_bitInvar

section Submonoid

def bitInvarSubmonoid (i : Fin (m + 1)) : Submonoid (Function.End (BV (m + 1))) where
  carrier f := bitInvar i f
  mul_mem' ha hb := bitInvar_mul_of_bitInvar ha hb
  one_mem' := one_bitInvar

@[simp]
lemma mem_bitInvarSubmonoid {i : Fin (m + 1)} : f ∈ bitInvarSubmonoid i ↔ bitInvar i f := Iff.rfl

lemma mem_bitInvarSubmonoid_of_bitInvar {i : Fin (m + 1)} (h : bitInvar i f) :
  f ∈ bitInvarSubmonoid i := h

lemma bitInvar_of_mem_bitInvarSubmonoid {i : Fin (m + 1)} (h : f ∈ bitInvarSubmonoid i) :
  bitInvar i f := h

end Submonoid

section Subgroup

def bitInvarSubgroup (i : Fin (m + 1)) : Subgroup (Equiv.Perm (BV (m + 1))) where
  carrier π := bitInvar i ⇑π
  mul_mem' ha hb := bitInvar_mulPerm_of_bitInvar ha hb
  one_mem' := one_bitInvar
  inv_mem' ha := inv_bitInvar_of_bitInvar ha

@[simp]
lemma mem_bitInvarSubgroup {i : Fin (m + 1)} : π ∈ bitInvarSubgroup i ↔ bitInvar i ⇑π := Iff.rfl

@[simp]
lemma mem_bitInvarSubgroup_iff_coe_mem_bitInvarSubmonoid {i : Fin (m + 1)} :
  ∀ π, π ∈ bitInvarSubgroup i ↔ ⇑π ∈ bitInvarSubmonoid i := fun _ => Iff.rfl

lemma mem_bitInvarSubgroup_of_coe_mem_bitInvarSubmonoid {i : Fin (m + 1)}
  {π : Equiv.Perm (BV (m + 1))} (h : ⇑π ∈ bitInvarSubmonoid i) : π ∈ bitInvarSubgroup i := h

lemma coe_mem_bitInvarSubmonoid_of_mem_bitInvarSubgroup {i : Fin (m + 1)}
  {π : Equiv.Perm (BV (m + 1))} (h : π ∈ bitInvarSubgroup i) : ⇑π ∈ bitInvarSubmonoid i := h

lemma mem_bitInvarSubgroup_iff_coe_unit_mem {i : Fin (m + 1)}: ∀ π, π ∈ bitInvarSubgroup i ↔
  (Equiv.Perm.equivUnitsEnd π).val ∈ bitInvarSubmonoid i :=
  mem_bitInvarSubgroup_iff_coe_mem_bitInvarSubmonoid

end Subgroup

section Equivs

def endoOfBoolArrowEndo (i : Fin (m + 1)) (f : Bool → Function.End (BV m)) :
  Function.End (BV (m + 1)) :=
  fun q => mergeBit i (testBit q i) (f (testBit q i) (q.testRes i))

@[simp]
lemma endoOfBoolArrowEndo_def {i : Fin (m + 1)} {f : Bool → Function.End (BV m)}
  {q : BV (m + 1)} :
  endoOfBoolArrowEndo i f q = mergeBit i (testBit q i) (f (testBit q i) (q.testRes i)) := rfl

lemma endoOfBoolArrowEndo_bitInvar {i : Fin (m + 1)} (f : Bool → Function.End (BV m)) :
  bitInvar i (endoOfBoolArrowEndo i f) := by
  simp_rw [bitInvar_iff_testBit_apply_eq_testBit, endoOfBoolArrowEndo_def,
    testBit_mergeBit, implies_true]

lemma endoOfBoolArrowEndo_mem_bitInvarSubmonoid {i : Fin (m + 1)}
  (f : Bool → Function.End (BV m)) : (endoOfBoolArrowEndo i f) ∈ bitInvarSubmonoid i :=
  endoOfBoolArrowEndo_bitInvar f

lemma endoOfBoolArrowEndo_comp {i : Fin (m + 1)} (f g : Bool → Function.End (BV m)) :
  endoOfBoolArrowEndo i (fun b => (f b) ∘ (g b)) = endoOfBoolArrowEndo i f ∘ endoOfBoolArrowEndo i g
  := by simp_rw [Function.End.ext_iff, Function.comp_apply, endoOfBoolArrowEndo_def,  testBit_mergeBit,
    testRes_mergeBit, Function.comp_apply, implies_true]

lemma endoOfBoolArrowEndo_mul {i : Fin (m + 1)} (f g : Bool → Function.End (BV m)) :
  endoOfBoolArrowEndo i (f * g) = endoOfBoolArrowEndo i f * endoOfBoolArrowEndo i g
  := endoOfBoolArrowEndo_comp _ _

def boolArrowEndoOfEndo (i : Fin (m + 1)) (f : Function.End (BV (m + 1))) :
  Bool → Function.End (BV m) := fun b p => testRes i (f (p.mergeBit i b))

@[simp]
lemma boolArrowEndoOfEndo_def {i : Fin (m + 1)} {f : Function.End (BV (m + 1))}
{b : Bool} {p : BV m} : boolArrowEndoOfEndo i f b p = testRes i (f (p.mergeBit i b)) := rfl

lemma endoOfBoolArrowEndo_rightInverse (i : Fin (m + 1)) :
Function.RightInverse (endoOfBoolArrowEndo i) (boolArrowEndoOfEndo i) := fun f => by
  ext ; simp_rw [boolArrowEndoOfEndo_def, endoOfBoolArrowEndo_def, testBit_mergeBit,
    testRes_mergeBit]

lemma endoOfBoolArrowEndo_leftInvOn (i : Fin (m + 1)) :
  Set.LeftInvOn (endoOfBoolArrowEndo i) (boolArrowEndoOfEndo i) (bitInvar i) := fun f hf => by
  ext q ; simp_rw [endoOfBoolArrowEndo_def, boolArrowEndoOfEndo_def, mergeBit_testBit_testRes,
    mergeBit_testRes_of_testBit_eq (hf q)]

lemma boolArrowEndoOfEndo_leftInverse (i : Fin (m + 1)) :
  Function.LeftInverse (boolArrowEndoOfEndo i) (endoOfBoolArrowEndo i) :=
  endoOfBoolArrowEndo_rightInverse _

lemma boolArrowEndoOfEndo_rightInvOn (i : Fin (m + 1)) :
  Set.RightInvOn (boolArrowEndoOfEndo i) (endoOfBoolArrowEndo i) (bitInvar i) :=
  endoOfBoolArrowEndo_leftInvOn _

@[simps!]
def bitInvarMulEquivEnd (i : Fin (m + 1)) :
(Bool → Function.End (BV m)) ≃* bitInvarSubmonoid i where
  toFun feo := ⟨endoOfBoolArrowEndo i feo, endoOfBoolArrowEndo_mem_bitInvarSubmonoid feo⟩
  invFun f := boolArrowEndoOfEndo i f.val
  left_inv := boolArrowEndoOfEndo_leftInverse i
  right_inv f := Subtype.ext (boolArrowEndoOfEndo_rightInvOn i f.prop)
  map_mul' _ _ := Subtype.ext (endoOfBoolArrowEndo_mul _ _)

def bitInvarMulEquiv (i : Fin (m + 1)) : (Bool → Equiv.Perm (BV m)) ≃* bitInvarSubgroup i :=
  ((Equiv.Perm.equivUnitsEnd).arrowCongr (Equiv.refl _)).trans <|
  MulEquiv.piUnits.symm.trans <|
  (Units.mapEquiv (bitInvarMulEquivEnd i)).trans <|
  (Equiv.Perm.equivUnitsEnd.subgroupMulEquivUnitsType (mem_bitInvarSubgroup_iff_coe_unit_mem)).symm

@[simp]
lemma bitInvarMulEquiv_apply_coe_apply (i : Fin (m + 1))
  (πeo : Bool → Equiv.Perm (BV m)) : ⇑((bitInvarMulEquiv i) πeo).val =
  endoOfBoolArrowEndo i fun b => ⇑(πeo b) := rfl

@[simp]
lemma bitInvarMulEquiv_apply_coe_symm_apply (i : Fin (m + 1))
  (πeo : Bool → Equiv.Perm (BV m)) : ⇑((bitInvarMulEquiv i) πeo).val.symm =
  endoOfBoolArrowEndo i fun b => ⇑(πeo b)⁻¹ := rfl

@[simp]
lemma bitInvarMulEquiv_symm_apply_apply (i : Fin (m + 1)) (π : ↥(bitInvarSubgroup i)):
  ⇑(((bitInvarMulEquiv i).symm) π b) = boolArrowEndoOfEndo i (⇑π.val) b := rfl

@[simp]
lemma bitInvarMulEquiv_symm_apply_symm_apply (i : Fin (m + 1)) (π : ↥(bitInvarSubgroup i)):
  ⇑(((bitInvarMulEquiv i).symm) π b).symm = boolArrowEndoOfEndo i (⇑π⁻¹.val) b := rfl

-- Extra lemmas

lemma endoOfBoolArrowEndo_leftInverse_apply {i : Fin (m + 1)}
  {f g : Bool → Function.End (BV m)}
  (hfg : ∀ b : Bool, (Function.LeftInverse (f b) (g b))) :
  Function.LeftInverse (endoOfBoolArrowEndo i f) (endoOfBoolArrowEndo i g) := fun q => by
  simp_rw [endoOfBoolArrowEndo_def, testBit_mergeBit, testRes_mergeBit,
    hfg (testBit q i) (q.testRes i), mergeBit_testBit_testRes]

lemma endoOfBoolArrowEndo_rightInverse_apply {i : Fin (m + 1)}
  {f g : Bool → Function.End (BV m)}
  (hfg : ∀ b : Bool, (Function.RightInverse (f b) (g b))) :
  Function.RightInverse (endoOfBoolArrowEndo i f) (endoOfBoolArrowEndo i g) :=
  endoOfBoolArrowEndo_leftInverse_apply hfg

lemma boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarLeft {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hfg : Function.LeftInverse f g) (hf : bitInvar i f)
  {b : Bool} : Function.LeftInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  fun q => by simp_rw [boolArrowEndoOfEndo_def,
    mergeBit_testRes_def_mergeBit_of_bitinvar (bitInvar_of_leftInverse_bitInvar hfg hf),
    hfg (mergeBit i b q), testRes_mergeBit]

lemma boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarLeft {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hfg : Function.RightInverse f g) (hf : bitInvar i f)
  {b : Bool} : Function.RightInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  fun q => by simp_rw [boolArrowEndoOfEndo_def, mergeBit_testRes_def_mergeBit_of_bitinvar hf,
    hfg (mergeBit i b q), testRes_mergeBit]

lemma boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hfg : Function.LeftInverse f g) (hg : bitInvar i g)
  {b : Bool} : Function.LeftInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarLeft hfg hg

lemma boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hfg : Function.RightInverse f g) (hg : bitInvar i g)
  {b : Bool} : Function.RightInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarLeft hfg hg

lemma boolArrowEndoOfEndo_comp_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hg : bitInvar i g) {b : Bool} :
  boolArrowEndoOfEndo i (f ∘ g) b = boolArrowEndoOfEndo i f b ∘ boolArrowEndoOfEndo i g b := by
  ext ; simp_rw [boolArrowEndoOfEndo_def, Function.comp_apply, boolArrowEndoOfEndo_def,
    mergeBit_testRes_def_mergeBit_of_bitinvar hg]

lemma boolArrowEndoOfEndo_mul_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hg : bitInvar i g) :
  boolArrowEndoOfEndo i (f * g) = boolArrowEndoOfEndo i f * boolArrowEndoOfEndo i g := by
  ext : 1 ; exact boolArrowEndoOfEndo_comp_ofBitInvarRight hg

end Equivs

end bitInvar

section FlipBit

@[simps!]
def flipBit (i : Fin (m + 1)) : Equiv.Perm (BV (m + 1)) :=
  ⟨fun q => ⟨Nat.flipBit i.val q.val,
  (Nat.flipBit_lt_iff_lt i.is_lt).mpr q.isLt⟩,
  fun q => ⟨(Nat.flipBit i.val).symm q.val,
  (Nat.flipBit_lt_iff_lt i.is_lt).mpr q.isLt⟩,
  fun q => by simp_rw [Equiv.symm_apply_apply],
  fun q => by simp_rw [Equiv.apply_symm_apply]⟩

lemma testBit_flipBit : testBit i (flipBit j q) = (testBit q i).xor (j = i) := by
  simp only [testBit_eq, flipBit_apply_val, Nat.testBit_flipBit, Fin.ext_iff]

-- TODO: testRes_flipBit

@[simp]
lemma testBit_flipBit_of_eq : testBit i (q.flipBit i) = !(testBit q i) := by
  simp_rw [testBit_flipBit, decide_True, Bool.xor_true]

lemma testBit_flipBit_of_ne {i j : Fin (m + 1)} (h : i ≠ j) :
    testBit i (flipBit j q) = testBit q i := by
  simp_rw [testBit_flipBit, h.symm, decide_False, Bool.xor_false]

lemma flipBit_eq_mergeBit {i : Fin (m + 1)} :
    q.flipBit i = mergeBit i (!(testBit q i)) (q.testRes i) := by
  simp_rw [Fin.ext_iff, flipBit_apply_val, testBit_eq, mergeBit_val_eq, testRes_val_eq,
  Nat.flipBit_eq_mergeBit]

lemma flipBit_eq_permCongr (i : Fin (m + 1)) :
    flipBit i = (testBitRes i).symm.permCongr (boolInversion.prodCongr (Equiv.refl _)) := by
  simp_rw [Equiv.ext_iff, Fin.ext_iff, flipBit_apply_val, Nat.flipBit_eq_permCongr] ;
  simp_rw [Equiv.permCongr_apply, Equiv.symm_symm, Nat.testBitRes_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod_map, boolInversion_apply, id_eq, Nat.testBitRes_symm_apply, testBitRes_apply,
    testBitRes_symm_apply_val, implies_true]

lemma flipBit_base : flipBit (m := 0) i = Equiv.swap 0 1 := by
  simp_rw [Equiv.ext_iff, flipBit_eq_mergeBit, Fin.eq_zero i]
  exact Fin.forall_fin_two.mpr ⟨rfl, rfl⟩

lemma flipBit_zero_apply : flipBit 0 q = finProdFinEquiv (q.divNat, q.modNat.rev) := by
  simp_rw [flipBit_eq_mergeBit, testBit_zero, Nat.pow_eq, finTwoEquiv_apply,
    testRes_zero, mergeBit_zero, Bool.cond_not, Bool.cond_decide]
  rcases Fin.modNat_two_eq_zero_or_one q with (h | h) <;> simp_rw [h] <;> rfl

@[simp]
lemma flipBit_mergeBit : flipBit i (p.mergeBit i b) = mergeBit i (!b) p := by
rw [flipBit_eq_mergeBit, testBit_mergeBit, testRes_mergeBit]

lemma flipBit_mergeBit_false : flipBit i (mergeBit i false k) = mergeBit i true k :=
flipBit_mergeBit (b := false)

lemma flipBit_mergeBit_true : flipBit i (mergeBit i true k) = mergeBit i false k :=
flipBit_mergeBit (b := true)

lemma flipBit_mergeBit_zero : flipBit 0 (mergeBit 0 b p) =
  finProdFinEquiv (p, bif b then 0 else 1) := by
  simp_rw [flipBit_zero_apply, mergeBit_zero_divNat,
    mergeBit_zero_modNat, Bool.apply_cond (Fin.rev)]
  rfl

lemma flipBit_mergeBit_zero_true : flipBit 0 (mergeBit 0 true p) = finProdFinEquiv (p, 0) :=
flipBit_mergeBit_zero (b := true)

lemma flipBit_mergeBit_zero_false : flipBit 0 (mergeBit 0 false p) = finProdFinEquiv (p, 1) :=
flipBit_mergeBit_zero (b := false)

lemma mergeBit_testRes_of_testBit_not (h : testBit q i = !b) :
mergeBit i b (q.testRes i) = q.flipBit i := by
simp_rw [flipBit_eq_mergeBit, h, Bool.not_not]

lemma mergeBit_testRes_cases_flipBit (i : Fin (m + 1)) (q) (b) :
  (testBit q i = b ∧ mergeBit i b (q.testRes i) = q) ∨
  ((testBit q i = !b) ∧ mergeBit i b (q.testRes i) = q.flipBit i) :=
  (Bool.eq_or_eq_not (testBit q i) b).elim
    (fun h => Or.inl (And.intro h (mergeBit_testRes_of_testBit_eq h)))
    (fun h => Or.inr (And.intro h (mergeBit_testRes_of_testBit_not h)))

lemma flipBit_succ : flipBit (i.succ) q = mergeBit 0 (testBit 0 q) (flipBit i (testRes 0 q)) := by
  simp_rw [flipBit_eq_mergeBit, testBit_succ, testRes_succ, mergeBit_succ,
  testBit_mergeBit, testRes_mergeBit]

lemma flipBit_castSucc : flipBit (i.castSucc) q =
  mergeBit (Fin.last _) (testBit (Fin.last _) q) (flipBit i (testRes (Fin.last _) q)) := by
  simp_rw [flipBit_eq_mergeBit, testBit_castSucc, testRes_castSucc, mergeBit_castSucc,
  testBit_mergeBit, testRes_mergeBit]

lemma flipBit_succAbove {j : Fin (m + 2)} : flipBit (j.succAbove i) q =
  mergeBit j (testBit j q) (flipBit i (testRes j q)) := by
  simp_rw [flipBit_eq_mergeBit, testBit_succAbove, testRes_succAbove, mergeBit_succAbove,
  testBit_mergeBit, testRes_mergeBit]

lemma eq_flipBit_iff : q = flipBit i r ↔ testBit q i = (!testBit i r) ∧
    q.testRes i = testRes i r := by
  rcases mergeBit_surj i q with ⟨bq, pq, rfl⟩;
  rcases mergeBit_surj i r with ⟨br, pr, rfl⟩
  simp_rw [flipBit_mergeBit, testBit_mergeBit, testRes_mergeBit,
    mergeBit_inj_iff]

@[simp]
lemma flipBit_flipBit : flipBit i (q.flipBit i) = q := by
  simp_rw [flipBit_eq_mergeBit (q := q), flipBit_mergeBit,
    Bool.not_not, mergeBit_testBit_testRes]

@[simp]
lemma flipBit_symm : (flipBit i).symm = flipBit i := rfl

@[simp]
lemma flipBit_inv : (flipBit i)⁻¹ = flipBit i := rfl

@[simp]
lemma flipBit_mul_self : (flipBit i) * (flipBit i) = 1 := by
  rw [mul_eq_one_iff_inv_eq]
  exact flipBit_inv

@[simp]
lemma flipBit_mul_cancel_right : ρ * (flipBit i) * (flipBit i) = ρ := by
  rw [mul_assoc, flipBit_mul_self, mul_one]

@[simp]
lemma flipBit_mul_cancel_left : (flipBit i) * ((flipBit i) * ρ)  = ρ := by
  rw [← mul_assoc, flipBit_mul_self, one_mul]

@[simp]
lemma testRes_flipBit_of_eq : testRes i (q.flipBit i) = q.testRes i := by
  rw [flipBit_eq_mergeBit, testRes_mergeBit]

lemma flipBit_bitInvar_of_ne {i j : Fin (m + 1)} (h : i ≠ j) : bitInvar i ⇑(flipBit j) :=
  bitInvar_of_testBit_def_eq_testBit (fun _ => testBit_flipBit_of_ne h)

lemma testBit_zero_flipBit_succ {i : Fin m} :
    testBit 0 (flipBit (i.succ) q) = testBit 0 q := by
  cases m
  · exact i.elim0
  · rw [flipBit_succ, testBit_mergeBit]

lemma testBit_succ_flipBit_zero {i : Fin m} :
    testBit (i.succ) (flipBit 0 q) = testBit (i.succ) q := by
  cases m
  · exact i.elim0
  · simp_rw [testBit_succ, testRes_flipBit_of_eq]

lemma flipBit_succ_bitInvar_zero {i : Fin m} : bitInvar 0 ⇑(flipBit (i.succ)) :=
  bitInvar_of_testBit_def_eq_testBit (fun _ => testBit_zero_flipBit_succ)

lemma flipBit_zero_bitInvar_succ {i : Fin m} : bitInvar (i.succ) ⇑(flipBit 0) :=
  bitInvar_of_testBit_def_eq_testBit (fun _ => testBit_succ_flipBit_zero)

@[simp]
lemma flipBit_ne_self (q) : q.flipBit i ≠ q := by
  apply ne_of_testBit_ne i
  rw [testBit_flipBit_of_eq, ne_eq, Bool.not_not_eq]

lemma testRes_zero_eq_and_testBit_zero_opp_of_lt_of_flipBit_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) :
testBit 0 r = false ∧ testBit 0 q = true ∧ testRes 0 r = testRes 0 q := by
rcases mergeBit_surj 0 q with ⟨bq, pq, rfl⟩; rcases mergeBit_surj 0 r with ⟨br, pr, rfl⟩
simp_rw [flipBit_mergeBit, testBit_mergeBit, testRes_mergeBit,
  Fin.lt_iff_val_lt_val, mergeBit_zero, finProdFinEquiv_apply_val, Bool.cond_not, add_comm,
  Bool.apply_cond (Fin.val), Fin.val_one, Fin.val_zero] at hf h ⊢
rcases Nat.eq_false_true_of_cond_succ_lt_of_cond_succ_lt h hf with ⟨hr, hq, he⟩
exact ⟨hr, hq, Fin.ext (Nat.eq_of_mul_eq_mul_left zero_lt_two he)⟩

lemma eq_flipBit_zero_of_lt_of_flipBit_zero_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) : r = flipBit 0 q := by
rcases testRes_zero_eq_and_testBit_zero_opp_of_lt_of_flipBit_gt h hf with ⟨hr, hq, hrq⟩
simp only [eq_flipBit_iff, hr, hq, hrq, Bool.not_true, and_self]

lemma testBit_gt_eq_testBit_gt_flipBit_of_lt_of_flipBit_ge (h : r < q)
    (hf : q.flipBit i ≤ flipBit i r) (hik : i ≤ k) : testBit k r = testBit k (q.flipBit i) := by
  rw [Fin.lt_iff_val_lt_val] at h
  rw [Fin.le_iff_val_le_val] at hf hik
  simp_rw [testBit_eq, flipBit_apply_val] at hf ⊢
  exact Nat.testBit_gt_eq_testBit_gt_flipBit_of_lt_of_flipBit_ge h hf hik

lemma eq_of_lowerBits_eq_of_lt_of_flipBit_ge (hrq : r < q) (hf : q.flipBit i ≤ flipBit i r)
    (h : ∀ {k}, k < i → testBit k r = testBit k q) : r = q.flipBit i := by
  rw [testBit_ext_iff]
  intros k
  rcases lt_or_le k i with hik | hik
  · rw [testBit_flipBit_of_ne hik.ne, h hik]
  · rw [testBit_gt_eq_testBit_gt_flipBit_of_lt_of_flipBit_ge hrq hf hik]

end FlipBit

section CondFlipBit

def condFlipBitCore (i : Fin (m + 1)) (c : BV m → Bool) : Function.End (BV (m + 1)) :=
  fun q => bif c (q.testRes i) then q.flipBit i else q

lemma condFlipBitCore_condFlipBitCore : condFlipBitCore i c (condFlipBitCore i c q) = q := by
rcases (c (q.testRes i)).dichotomy with h | h <;>
simp only [condFlipBitCore, h, cond_true, cond_false, testRes_flipBit_of_eq, flipBit_flipBit]

def condFlipBit (i : Fin (m + 1)) (c : BV m → Bool) : Equiv.Perm (BV (m + 1)) where
  toFun := condFlipBitCore i c
  invFun := condFlipBitCore i c
  left_inv _ := condFlipBitCore_condFlipBitCore
  right_inv _ := condFlipBitCore_condFlipBitCore

lemma condFlipBit_apply :
condFlipBit i c q = bif c (q.testRes i) then q.flipBit i else q := rfl

lemma condFlipBit_def :
condFlipBit i c = fun q => bif c (q.testRes i) then q.flipBit i else q := rfl

lemma condFlipBit_apply_eq_mergeBit : condFlipBit i c q =
mergeBit i (xor (c (q.testRes i)) (testBit q i)) (q.testRes i) := by
  rw [condFlipBit_apply] ; cases (c (q.testRes i))
  · rw [cond_false, Bool.false_xor, mergeBit_testBit_testRes]
  · rw [cond_true, Bool.true_xor, flipBit_eq_mergeBit]

lemma condFlipBit_apply_eq_swap_apply : condFlipBit i c q =
      Equiv.swap q (mergeBit i (xor (c (q.testRes i)) (testBit q i)) (q.testRes i)) q := by
  exact condFlipBit_apply_eq_mergeBit.trans (Equiv.swap_apply_left _ _).symm

lemma condFlipBit_base : condFlipBit (m := 0) i c = bif c 0 then Equiv.swap 0 1 else 1 := by
  ext q : 1
  rw [condFlipBit_apply, Fin.eq_zero (q.testRes i), flipBit_base]
  cases (c 0) <;> rfl

lemma condFlipBit_mergeBit : condFlipBit i c (p.mergeBit i b) =
mergeBit i (xor (c p) b) p := by
rw [condFlipBit_apply_eq_mergeBit, testRes_mergeBit, testBit_mergeBit]

@[simp]
lemma condFlipBit_symm : (condFlipBit i c).symm = condFlipBit i c := rfl

@[simp]
lemma condFlipBit_inv : (condFlipBit i c)⁻¹ = condFlipBit i c := rfl

@[simp]
lemma condFlipBit_condFlipBit : condFlipBit i c (condFlipBit i c q) = q :=
  (condFlipBit i c).left_inv _

@[simp]
lemma condFlipBit_mul_self : (condFlipBit i c) * (condFlipBit i c) = 1 := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply,
  condFlipBit_condFlipBit, Equiv.Perm.coe_one, id_eq]

@[simp]
lemma condFlipBit_mul_cancel_right : ρ * (condFlipBit i c) * (condFlipBit i c) = ρ := by
  rw [mul_assoc, condFlipBit_mul_self, mul_one]

@[simp]
lemma condFlipBit_mul_cancel_left : (condFlipBit i c) * ((condFlipBit i c) * ρ) = ρ := by
  rw [← mul_assoc, condFlipBit_mul_self, one_mul]

lemma condFlipBit_flipBit_of_all_true : flipBit i = condFlipBit i (Function.const _ true) := by
  ext
  rw [condFlipBit_apply]
  rfl

lemma condFlipBit_refl_of_all_false : Equiv.refl _ = condFlipBit i (Function.const _ false) := rfl

lemma condFlipBit_apply_comm :
condFlipBit i c (condFlipBit i d q) = condFlipBit i d (condFlipBit i c q) := by
simp_rw [condFlipBit_apply_eq_mergeBit, testRes_mergeBit,
  testBit_mergeBit, Bool.xor_left_comm]

lemma condFlipBit_comm :
(condFlipBit i c) * (condFlipBit i d) = (condFlipBit i d) * (condFlipBit i c) := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, condFlipBit_apply_comm]

lemma condFlipBit_apply_comm_flipBit :
  condFlipBit i c (q.flipBit i) = flipBit i (condFlipBit i c q) := by
  rw [condFlipBit_flipBit_of_all_true, condFlipBit_apply_comm]

lemma condFlipBit_comm_flipBit :
  (condFlipBit i c) * (flipBit i) = (flipBit i) * (condFlipBit i c) := by
  rw [condFlipBit_flipBit_of_all_true, condFlipBit_comm]

lemma condFlipBit_apply_flipBit :
condFlipBit i c (q.flipBit i) = bif c (q.testRes i) then q else q.flipBit i := by
  rw [condFlipBit_apply_comm_flipBit]
  rcases (c (q.testRes i)).dichotomy with h | h <;> rw [condFlipBit_apply, h]
  · simp_rw [cond_false]
  · simp_rw [cond_true, flipBit_flipBit]

@[simp]
lemma testRes_condFlipBit : testRes i (condFlipBit i c q) = q.testRes i := by
rcases (c (q.testRes i)).dichotomy with h | h  <;> rw [condFlipBit_apply, h]
· rfl
· rw [cond_true, testRes_flipBit_of_eq]

lemma testBit_condFlipBit : testBit i (condFlipBit i c q) =
bif c (q.testRes i) then !(testBit q i) else testBit q i := by
rcases (c (q.testRes i)).dichotomy with hc | hc <;>
simp only [condFlipBit_apply, cond_false, hc, cond_true, testBit_flipBit_of_eq]

lemma testBit_condFlipBit' : testBit i (condFlipBit i c q) =
xor (c (q.testRes i)) (testBit q i) := by
rcases (c (q.testRes i)).dichotomy with hc | hc <;>
simp only [condFlipBit_apply, hc, cond_false, cond_true,
  Bool.false_xor, Bool.true_xor, testBit_flipBit_of_eq]

lemma testBit_condFlipBit'' : testBit i (condFlipBit i c q) =
bif (testBit q i) then !(c (q.testRes i)) else c (q.testRes i) := by
rcases (testBit q i).dichotomy with hc | hc <;>
simp only [testBit_condFlipBit', hc, Bool.xor_false, Bool.xor_true, cond_true, cond_false]

lemma testBit_condFlipBit_of_ne {i j : Fin (m + 1)} (hij: i ≠ j):
  testBit i ((condFlipBit j c) q) = testBit q i := by
  rw [condFlipBit_apply]
  rcases (c (testRes j q)).dichotomy with (h | h) <;> simp_rw [h]
  · rw [cond_false]
  · rw [cond_true, testBit_flipBit_of_ne hij]

lemma condFlipBit_bitInvar_of_ne {i j : Fin (m + 1)} (h : i ≠ j) : bitInvar i ⇑(condFlipBit j c) :=
  bitInvar_of_testBit_def_eq_testBit (fun _ => testBit_condFlipBit_of_ne h)

lemma condFlipBit_succ_apply {i : Fin (m + 1)} : condFlipBit (Fin.succ i) c q =
    mergeBit 0 (testBit 0 q) ((condFlipBit i fun p =>
    c (mergeBit 0 (testBit 0 q) p)) (testRes 0 q)) := by
    simp_rw [condFlipBit_apply_eq_mergeBit, mergeBit_succ, testRes_succ, testBit_succ,
    testBit_mergeBit, testRes_mergeBit]

lemma condFlipBit_succAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
  condFlipBit (j.succAbove i) c q =
    mergeBit j (testBit j q) ((condFlipBit i fun p =>
    c (mergeBit (i.predAbove j) (testBit j q) p)) (testRes j q)) := by
    simp_rw [condFlipBit_apply, testRes_succAbove,
    Bool.apply_cond (fun x => mergeBit j (testBit j q) x), mergeBit_testBit_testRes,
    flipBit_succAbove]

lemma condFlipBit_zero_apply : condFlipBit 0 c q =
  bif c (q.divNat) then
  finProdFinEquiv (q.divNat, q.modNat.rev)
  else q := by
  rw [condFlipBit_apply, flipBit_zero_apply, testRes_zero]

lemma condFlipBit_zero_mergeBit :
condFlipBit 0 c (mergeBit 0 b p) = finProdFinEquiv (p, bif xor (c p) b then 1 else 0) := by
  simp_rw [condFlipBit_mergeBit, mergeBit_zero]

lemma condFlipBit_zero_mergeBit_true  :
condFlipBit 0 c (mergeBit 0 true p) = finProdFinEquiv (p, bif c p then 0 else 1) := by
  simp_rw [condFlipBit_zero_mergeBit, Bool.xor_true, Bool.cond_not]

lemma condFlipBit_zero_mergeBit_false :
condFlipBit 0 c (mergeBit 0 false p) = finProdFinEquiv (p, bif c p then 1 else 0) := by
  simp_rw [condFlipBit_zero_mergeBit, Bool.xor_false]

end CondFlipBit

section Equivs

lemma bitInvarMulEquiv_zero_apply_condFlipBits (c : BV (m + 1) → Bool) (i : Fin (m + 1)) :
    (bitInvarMulEquiv 0) (fun b => condFlipBit i (fun p => c (mergeBit 0 b p))) =
    condFlipBit (i.succ) c :=
  Equiv.ext (fun _ => condFlipBit_succ_apply ▸ rfl)

lemma bitInvarMulEquiv_zero_apply_condFlipBits_one (c : BV (m + 1) → Bool) :
    (bitInvarMulEquiv 0) (fun b => condFlipBit 0 (fun p => c (mergeBit 0 b p))) =
    condFlipBit 1 c :=
  bitInvarMulEquiv_zero_apply_condFlipBits _ 0

lemma bitInvarMulEquiv_apply_condFlipBits (c) (i : Fin (m + 1)) (j : Fin (m + 2)) :
    (bitInvarMulEquiv j) (fun b => condFlipBit i (fun p => c (mergeBit (i.predAbove j) b p))) =
    condFlipBit (j.succAbove i) c :=
  Equiv.ext (fun _ => condFlipBit_succAbove_apply ▸ rfl)

lemma bitInvarMulEquiv_last_apply_condFlipBits (c) (i : Fin (m + 1)) :
    (bitInvarMulEquiv (Fin.last _)) (fun b => condFlipBit i
    (fun p => c (mergeBit (Fin.last _) b p))) =
    condFlipBit (i.castSucc) c := by
  rw [← Fin.predAbove_right_last (i := i), bitInvarMulEquiv_apply_condFlipBits, Fin.succAbove_last]

end Equivs

end BitRes
