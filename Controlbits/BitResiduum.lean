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

end Fin

namespace Nat

@[simp]
theorem testBit_one_succ {k : ℕ} : testBit 1 (k.succ) = false := by
  rw [testBit_succ, div_eq_of_lt one_lt_two, zero_testBit]

theorem testBit_one {k : ℕ} : testBit 1 k = decide (k = 0) := by
  cases k
  · exact testBit_one_zero
  · simp_rw [testBit_one_succ, decide_False]

theorem testBit_two_pow' (n : ℕ) (m : ℕ) : (2 ^ n).testBit m = decide (n = m) := by
  rcases eq_or_ne n m with rfl | h
  · simp_rw [testBit_two_pow_self, decide_True]
  · simp_rw [testBit_two_pow_of_ne h, h, decide_False]

lemma shiftLeft'_true {m : ℕ} (n : ℕ ) : m.shiftLeft' true n = (m <<< n) ||| (2^n - 1) := by
  apply eq_of_testBit_eq
  simp_rw [testBit_or, testBit_shiftLeft, testBit_two_pow_sub_one]
  intro j
  induction' n with n IH generalizing m j
  · simp_rw [shiftLeft', zero_le, decide_True, Bool.true_and, not_lt_zero, decide_False,
    Bool.or_false, Nat.sub_zero]
  · cases' j with j
    · simp_rw [shiftLeft', testBit_bit_zero, nonpos_iff_eq_zero, decide_False, Bool.false_and,
      Bool.false_or, zero_lt_succ, decide_True]
    · simp_rw [shiftLeft', testBit_bit_succ, IH, Nat.add_sub_add_right,
      add_lt_add_iff_right, add_le_add_iff_right]

lemma shiftLeft'_true_zero : shiftLeft' true 0 n = 2^n - 1 := by
  rw [shiftLeft'_true, zero_shiftLeft, zero_or]

lemma shiftLeft'_testBit {x : ℕ} : (x.shiftLeft' b i).testBit j =
  ((j ≥ i) && x.testBit (j - i) || (j < i) && b) := by
  cases b
  · simp_rw [shiftLeft'_false, testBit_shiftLeft, Bool.and_false,
    Bool.or_false]
  · simp_rw [shiftLeft'_true, testBit_or, testBit_shiftLeft,
    testBit_two_pow_sub_one, Bool.and_true]

lemma shiftLeft'_true_zero_testBit {x : ℕ} : (shiftLeft' true 0 x).testBit j = decide (j < x) := by
  rw [shiftLeft'_true_zero, testBit_two_pow_sub_one]

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

lemma testBit_add_mul_pow_two (a : Nat) {b : Nat} {i : Nat} (b_lt : b < 2 ^ i) (j : Nat) :
    (b + 2 ^ i * a).testBit j = if j < i then b.testBit j else a.testBit (j - i) := by
  rw [add_comm]
  exact testBit_mul_pow_two_add a b_lt j

theorem testBit_two_pow_add_gt' {i j : Nat} (j_lt_i : j < i) (x : Nat) :
    testBit (2^i + x) j = testBit x j := by
  have i_def : i = j + (i-j) := (Nat.add_sub_cancel' (Nat.le_of_lt j_lt_i)).symm
  rw [i_def]
  simp only [testBit_to_div_mod, Nat.pow_add,
        Nat.add_comm x, Nat.mul_add_div (Nat.two_pow_pos _)]
  match i_sub_j_eq : i - j with
  | 0 =>
    exfalso
    rw [Nat.sub_eq_zero_iff_le] at i_sub_j_eq
    exact Nat.not_le_of_gt j_lt_i i_sub_j_eq
  | d+1 =>
    simp [Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_add_mod]

lemma testBit_add_mul_two_pow_eq (a : Nat) (b : Nat) (i : Nat) :
    (b + 2 ^ i * a).testBit i = (decide (a % 2 = 1)).xor (b.testBit i) := by
  rw [add_comm]
  exact testBit_mul_two_pow_add_eq a b i

theorem testBit_two_pow_add_lt_testBit_false {i : Nat} {j : Nat} (i_lt_j : i < j) (x : Nat)
    (hx : x.testBit i = false) : (2 ^ i + x).testBit j = x.testBit j := by
  rw [testBit_to_div_mod, decide_eq_false_iff_not, mod_two_ne_one] at hx
  rw [← div_add_mod x (2^j)] at hx
  rcases Nat.exists_eq_add_of_lt i_lt_j with ⟨k, rfl⟩
  nth_rewrite 1 [add_assoc, Nat.pow_add, mul_assoc, mul_add_div (Nat.pow_pos zero_lt_two),
  Nat.pow_succ', mul_assoc, Nat.mul_add_mod] at hx
  rw [testBit_to_div_mod, Nat.add_div (Nat.pow_pos zero_lt_two),
    div_eq_of_lt (Nat.pow_lt_pow_of_lt one_lt_two i_lt_j), zero_add,
    mod_eq_of_lt (Nat.pow_lt_pow_of_lt one_lt_two i_lt_j)]
  have h : 2 ^ i + x % 2 ^ (i + k + 1) < 2^(i + k + 1) := by
    nth_rewrite 2 [add_assoc, Nat.pow_add]
    rw [mul_comm]
    refine' lt_mul_of_div_lt _ (Nat.pow_pos zero_lt_two)
    rw [add_div_left _ (Nat.pow_pos zero_lt_two), succ_eq_add_one]
    refine' lt_of_le_of_ne (Nat.div_lt_of_lt_mul _) (fun H => Nat.zero_ne_one _)
    · simp_rw [← pow_add, add_assoc, mod_lt _ (Nat.pow_pos zero_lt_two)]
    · rw [← hx, ← succ_mod_two_eq_zero_iff, H, pow_succ', mul_mod_right]
  · simp_rw [h.not_le, if_false, add_zero, testBit_to_div_mod]

theorem testBit_add_two_pow_lt_testBit_false {i : Nat} {j : Nat} (i_lt_j : i < j) (x : Nat)
    (hx : x.testBit i = false) : (x + 2^i).testBit j = x.testBit j := by
  rw [add_comm, testBit_two_pow_add_lt_testBit_false i_lt_j _ hx]

lemma or_eq_add_two_pow_mul_of_lt_left {a b i: ℕ} (ha : a < 2^i) :
    a ||| 2^i * b = a + 2^i * b := by
  apply Nat.eq_of_testBit_eq
  intros j
  simp_rw [testBit_or, testBit_add_mul_pow_two _ ha, Nat.testBit_mul_pow_two]
  rcases lt_or_le j i with hji | hji
  · simp_rw [hji, if_true, hji.not_le, decide_False, Bool.false_and, Bool.or_false]
  · simp_rw [hji, decide_True, hji.not_lt, if_false, Bool.true_and,
    Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_of_le one_lt_two hji)), Bool.false_or]

lemma or_eq_add_two_pow_mul_of_lt_right {a b i: ℕ} (ha : a < 2^i) :
    2^i * b ||| a = 2^i * b + a:= by
  rw [lor_comm, add_comm]
  exact or_eq_add_two_pow_mul_of_lt_left ha

lemma or_eq_add_two_pow_of_lt_left {a i: ℕ} (ha : a < 2^i) :
    a ||| 2^i = a + 2^i := by
  rw [← (Nat.mul_one (2^i)), or_eq_add_two_pow_mul_of_lt_left ha]

lemma or_eq_add_two_pow_of_lt_right {a i: ℕ} (ha : a < 2^i) :
    2^i ||| a = 2^i + a:= by
  rw [lor_comm, add_comm]
  exact or_eq_add_two_pow_of_lt_left ha

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

def getBit (i q : ℕ) := q.testBit i

def getRes (i q : ℕ) := ((q >>> (i + 1)) <<< i) ||| (q &&& (2^ i - 1))

def mergeBitRes (i : ℕ) (b : Bool) (p : ℕ) :=
  ((p >>> i) <<< (i + 1)) ||| (p &&& (2^ i - 1)) ||| (b.toNat <<< i)

lemma getBit_def : getBit i q = q.testBit i := rfl

lemma ge_of_getBit_true (h : getBit i q = true) : 2^i ≤ q := testBit_implies_ge h

theorem getBit_two_pow_add_gt {i : ℕ} {j : ℕ} (j_lt_i : j < i) (x : ℕ) :
  j.getBit (2^i + x) = j.getBit x := testBit_two_pow_add_gt j_lt_i _

theorem getBit_add_two_pow_gt {i : ℕ} {j : ℕ} (j_lt_i : j < i) (x : ℕ) :
  j.getBit (x + 2^i) = j.getBit x := Nat.add_comm _ _ ▸ testBit_two_pow_add_gt j_lt_i _

theorem getBit_two_pow_add_eq (x : ℕ) (i : ℕ) :
    i.getBit (2^i + x) = !i.getBit x := testBit_two_pow_add_eq _ _

theorem getBit_add_two_pow_eq (x : ℕ) (i : ℕ) :
    i.getBit (x + 2^i) = !i.getBit x := Nat.add_comm _ _ ▸ testBit_two_pow_add_eq _ _

theorem getBit_two_pow_add_lt_getBit_false {i : Nat} {j : Nat} (i_lt_j : i < j) (x : Nat)
    (hx : i.getBit x = false) : j.getBit (2 ^ i + x) = j.getBit x :=
  testBit_two_pow_add_lt_testBit_false i_lt_j _ hx

theorem getBit_add_two_pow_lt_getBit_false {i : Nat} {j : Nat} (i_lt_j : i < j) (x : Nat)
    (hx : i.getBit x = false) : j.getBit (x + 2^i) = j.getBit x :=
  testBit_add_two_pow_lt_testBit_false i_lt_j _ hx

lemma getBit_ext (h : ∀ i : ℕ, getBit i q = getBit i q') : q = q' := Nat.eq_of_testBit_eq h

lemma getBit_ext_iff : q = q' ↔ (∀ i : ℕ, getBit i q = getBit i q') :=
  ⟨fun h _ => h ▸ rfl, getBit_ext⟩

lemma getRes_def : getRes i q = (q >>> (i + 1)) <<< i ||| q &&& (2^ i - 1) := rfl
lemma mergeBitRes_def : mergeBitRes i b p =
    ((p >>> i) <<< (i + 1)) ||| (p &&& (2^ i - 1)) ||| (b.toNat <<< i) := rfl

lemma getBit_eq : getBit i q = decide (q / 2^i % 2 = 1) := Nat.testBit_to_div_mod

lemma getBit_toNat : (getBit i q).toNat = q / 2^i % 2 := Nat.toNat_testBit _ _

lemma getRes_eq : getRes i q = 2^i * (q / 2^(i + 1)) + q % 2^i := by
  unfold getRes
  rw [and_pow_two_is_mod, shiftLeft_eq_mul_pow, shiftRight_eq_div_pow,
    mul_comm, or_eq_add_two_pow_mul_of_lt_right (mod_lt _ (Nat.pow_pos zero_lt_two))]

lemma mergeBitRes_eq : mergeBitRes i b p =
    2^(i + 1) * (p / 2^i) + p % 2^i + 2^i * bif b then 1 else 0 := by
  unfold mergeBitRes
  rw [and_pow_two_is_mod]
  cases b
  · simp_rw [cond_false, Bool.toNat_false, Nat.zero_shiftLeft, mul_zero, add_zero,
    Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow, or_zero, mul_comm (p / 2 ^ i),
    pow_succ, mul_assoc]
    rw [or_eq_add_two_pow_mul_of_lt_right (mod_lt _ (Nat.pow_pos zero_lt_two))]
  · have h : 2^i < 2^(i + 1) := Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _)
    simp_rw [cond_true, mul_one, Bool.toNat_true, Nat.shiftLeft_eq_mul_pow, one_mul,
    Nat.shiftRight_eq_div_pow, mul_comm (p / 2 ^ i), lor_assoc, add_assoc,
    or_eq_add_two_pow_mul_of_lt_right
      (Nat.or_lt_two_pow ((mod_lt _ (Nat.pow_pos zero_lt_two)).trans h) h),
    or_eq_add_two_pow_of_lt_left (mod_lt _ (Nat.pow_pos zero_lt_two))]

@[simp]
lemma getBit_mergeBitRes_of_eq : getBit i (mergeBitRes i b p) = b := by
  rw [getBit_eq, mergeBitRes_eq]
  cases b
  · simp_rw [cond_false, decide_eq_false_iff_not, Nat.mod_two_ne_one, mul_zero, add_zero,
    Nat.pow_add, pow_one, mul_assoc, Nat.mul_add_div (Nat.pow_pos zero_lt_two),
    Nat.mod_div_self, add_zero, Nat.mul_mod_right]
  · simp_rw [cond_true, decide_eq_true_eq, pow_succ, mul_one,
    Nat.add_div_right _ (Nat.pow_pos zero_lt_two), mul_assoc,
    Nat.mul_add_div (Nat.pow_pos zero_lt_two), Nat.mod_div_self, add_zero, Nat.succ_eq_add_one,
    Nat.succ_mod_two_eq_one_iff, Nat.mul_mod_right]

@[simp]
lemma getRes_mergeBitRes_of_eq : getRes i (mergeBitRes i b p) = p := by
  rw [getRes_eq, mergeBitRes_eq]
  cases b
  · simp_rw [cond_false, mul_zero, add_zero, Nat.add_mod_mod,
    Nat.mul_add_div (Nat.pow_pos zero_lt_two), mul_add, Nat.div_eq_of_lt (a := p % 2 ^ i)
      ((Nat.mod_lt _ (Nat.pow_pos zero_lt_two)).trans
      (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _))),
    pow_succ, mul_assoc, Nat.mul_add_mod, mul_zero, add_zero, Nat.div_add_mod]
  · simp_rw [cond_true, mul_one, Nat.add_mod_right, Nat.add_mod_mod, add_assoc,
    Nat.mul_add_div (Nat.pow_pos zero_lt_two), pow_succ, mul_assoc, mul_two,
    Nat.div_eq_of_lt (Nat.add_lt_add_right (Nat.mod_lt _ (Nat.pow_pos zero_lt_two)) _),
    add_zero, Nat.mul_add_mod, Nat.div_add_mod]

@[simp]
lemma mergeBitRes_getBit_getRes_of_eq : mergeBitRes i (getBit i q) (getRes i q) = q := by
  rw [getBit_eq, getRes_eq, mergeBitRes_eq]
  simp_rw [Nat.add_mod_mod, Nat.mul_add_mod, Nat.mul_add_div (Nat.pow_pos zero_lt_two),
  Nat.mod_div_self, add_zero, Bool.cond_decide]
  have H : (if q / 2 ^ i % 2 = 1 then 1 else 0 : ℕ) = q / 2 ^ i % 2 :=
  (Nat.mod_two_eq_zero_or_one (q / 2 ^ i)).by_cases (fun h => h.symm ▸ rfl) (fun h => h.symm ▸ rfl)
  rw [H, add_assoc, ← Nat.mod_mul, ← pow_succ, Nat.div_add_mod]

@[simps!]
def getBitRes (i : ℕ) : ℕ ≃ Bool × ℕ :=
  ⟨fun n => (getBit i n, getRes i n), fun bp => mergeBitRes i bp.1 bp.2,
  fun _ => mergeBitRes_getBit_getRes_of_eq,
  fun _ => Prod.ext getBit_mergeBitRes_of_eq getRes_mergeBitRes_of_eq⟩

lemma getRes_lt_iff_lt (hi : i ≤ m) : getRes i q < 2^m ↔ q < 2^(m + 1) := by
  rw [getRes_eq]
  refine' ⟨lt_imp_lt_of_le_imp_le (fun _ => _), fun _ => _⟩
  · have h : 2 ^ m ≤ 2 ^ i * 2 ^ (m - i) + 0 := by rw [add_zero, ← pow_add, Nat.add_sub_cancel' hi]
    refine' h.trans (Nat.add_le_add (Nat.mul_le_mul_left _
      ((Nat.le_div_iff_mul_le (Nat.pow_pos zero_lt_two)).mpr _)) (Nat.zero_le _))
    rwa [← pow_add, ← add_assoc, Nat.sub_add_cancel hi]
  · have h : 2 ^ i * (q / 2 ^ (i + 1)) ≤ 2^m - 2^i := by
      rw [← Nat.add_sub_cancel' hi, pow_add _ i (m - i), ← Nat.mul_pred_right, ]
      refine' Nat.mul_le_mul_left _ (Nat.le_pred_of_lt (Nat.div_lt_of_lt_mul _))
      rwa [mul_comm, ← pow_add, ← add_assoc, Nat.sub_add_cancel hi]
    exact (add_lt_add_of_le_of_lt h (Nat.mod_lt _ (Nat.pow_pos zero_lt_two))).trans_eq <|
      Nat.sub_add_cancel (Nat.pow_le_pow_of_le one_lt_two hi)

lemma le_getRes_iff_ge (hi : i ≤ m) : 2^m ≤ getRes i q ↔ 2^(m + 1) ≤ q := by
  simp_rw [← not_lt, getRes_lt_iff_lt hi]

lemma mergeBitRes_lt_iff_lt (hi : i ≤ m) : mergeBitRes i b p < 2^(m + 1) ↔ p < 2^m := by
  rw [← getRes_lt_iff_lt hi, getRes_mergeBitRes_of_eq]

lemma le_mergeBitRes_iff_le (hi : i ≤ m) : 2^(m + 1) ≤ mergeBitRes i b p ↔ 2^m ≤ p := by
  rw [← le_getRes_iff_ge hi, getRes_mergeBitRes_of_eq]

lemma getBit_getRes {i j q : ℕ} :
    i.getBit (j.getRes q) = (i + (decide (j ≤ i)).toNat).getBit q := by
  simp_rw [getBit_def, getRes_def, testBit_or, testBit_shiftLeft, ge_iff_le,
    testBit_shiftRight, add_right_comm, testBit_and, testBit_two_pow_sub_one, lt_iff_not_le,
    decide_not]
  by_cases ha : (j ≤ i)
  · simp_rw [ha, decide_True, add_tsub_cancel_of_le ha, Bool.true_and, Bool.not_true,
    Bool.and_false, Bool.or_false, Bool.toNat_true]
  · simp_rw [ha, decide_False, Bool.false_and, Bool.false_or, Bool.not_false,
    Bool.and_true, Bool.toNat_false, add_zero]

lemma getBit_getRes_of_lt {i j q : ℕ} (ha : i < j) : i.getBit (j.getRes q) = i.getBit q := by
  simp_rw [getBit_getRes, ha.not_le, decide_False, Bool.toNat_false, add_zero]

lemma getBit_getRes_of_ge {i j q : ℕ} (ha : j ≤ i) : i.getBit (j.getRes q) = (i + 1).getBit q := by
  simp_rw [getBit_getRes, ha, decide_True, Bool.toNat_true]

lemma getRes_getRes {i j q : ℕ} : i.getRes (j.getRes q) =
    (j - (!decide (j ≤ i)).toNat).getRes ((i + (decide (j ≤ i)).toNat).getRes q) := by
  simp_rw [getBit_ext_iff, getBit_getRes, tsub_le_iff_right]
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

lemma getRes_getRes_of_lt {i j q : ℕ} (ha : i < j) : i.getRes (j.getRes q) =
  (j - 1).getRes (getRes i q) := by
  simp_rw [getRes_getRes (i := i), ha.not_le, decide_False, Bool.not_false,
    Bool.toNat_true, Bool.toNat_false, add_zero]

lemma getRes_getRes_of_ge {i j q : ℕ} (ha : j ≤ i) :
    i.getRes (j.getRes q) = j.getRes ((i + 1).getRes q) := by
  simp_rw [getRes_getRes (i := i), ha, decide_True, Bool.not_true, Bool.toNat_false,
    tsub_zero, Bool.toNat_true]

lemma getBit_mergeBitRes_of_ne {i j : ℕ} (hij : i ≠ j) : i.getBit (j.mergeBitRes b p) =
    (i - (decide (j < i)).toNat).getBit p := by
  simp_rw [getBit_def, mergeBitRes_def]
  simp_rw [testBit_or, testBit_and, testBit_shiftLeft, ge_iff_le, testBit_shiftRight,
    testBit_two_pow_sub_one]
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [(lt_succ_of_lt hij).not_le, hij.not_le, hij, hij.le.not_lt, decide_False,
    Bool.false_and, decide_True, Bool.and_true, Bool.false_or, Bool.or_false,
    Bool.toNat_false, tsub_zero]
  · rw [← Nat.add_sub_assoc (succ_le_of_lt hij), succ_eq_add_one, Nat.add_sub_add_left]
    simp_rw [succ_le_of_lt hij, hij, hij.le, hij.le.not_lt, decide_True, decide_False,
      Bool.true_and, Bool.and_false, Bool.or_false, Bool.toNat_true]
    cases b
    · simp_rw [Bool.toNat_false, zero_testBit, Bool.or_false]
    · simp_rw [Bool.toNat_true, testBit_one, Nat.sub_eq_zero_iff_le, hij.not_le,
      decide_False, Bool.or_false]


def flipBit (i : ℕ) : Equiv.Perm ℕ :=
  ⟨fun q => q ^^^ 2^i, fun q => q ^^^ 2^i, xor_cancel_right _, xor_cancel_right _⟩

lemma flipBit_apply : ∀ (i q : ℕ), i.flipBit q = q ^^^ 2 ^ i := fun _ _ => rfl

lemma flipBit_symm_apply : ∀ (i q : ℕ), (Equiv.symm i.flipBit) q = q ^^^ 2 ^ i := fun _ _ => rfl

lemma getBit_flipBit : getBit i (flipBit j q) = (getBit i q).xor (j = i) := by
  simp_rw [flipBit_apply, getBit_def, testBit_xor, testBit_two_pow']

-- TODO: getRes_flipBit

@[simp]
lemma getBit_flipBit_of_eq : getBit i (flipBit i q) = !(getBit i q) := by
  simp_rw [getBit_flipBit, decide_True, Bool.xor_true]

lemma getBit_flipBit_of_ne {i j : ℕ} (h : i ≠ j) :
    getBit i (flipBit j q) = getBit i q := by
  simp_rw [getBit_flipBit, h.symm, decide_False, Bool.xor_false]

lemma flipBit_eq_of_getBit_true (h : getBit i q = true) :
    flipBit i q = q - 2^i := by
  refine' Nat.eq_sub_of_add_eq _
  simp_rw [getBit_ext_iff]
  intro j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [getBit_add_two_pow_lt_getBit_false hij _ (by rw [getBit_flipBit_of_eq, h, Bool.not_true]),
      getBit_flipBit_of_ne hij.ne']
  · exact (getBit_add_two_pow_eq _ _).trans (by rw [getBit_flipBit_of_eq, Bool.not_not])
  · rw [getBit_add_two_pow_gt hij, getBit_flipBit_of_ne hij.ne]

lemma flipBit_eq_of_getBit_false {i q : ℕ} (h : getBit i q = false) :
    flipBit i q = q + 2^i := by
  simp_rw [getBit_ext_iff]
  intro j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [getBit_add_two_pow_lt_getBit_false hij _ h, getBit_flipBit_of_ne hij.ne']
  · rw [getBit_add_two_pow_eq, getBit_flipBit_of_eq]
  · rw [getBit_add_two_pow_gt hij, getBit_flipBit_of_ne hij.ne]

lemma flipBit_eq {i q : ℕ} : flipBit i q = bif getBit i q then q - 2^i else q + 2^i := by
  cases h : getBit i q
  · rw [flipBit_eq_of_getBit_false h, Bool.cond_false]
  · rw [flipBit_eq_of_getBit_true h, Bool.cond_true]

lemma flipBit_eq_mergeBitRes {i q : ℕ} :
    flipBit i q = mergeBitRes i (!(getBit i q)) (getRes i q) := by
  simp_rw [getBit_ext_iff]
  intro j
  rcases eq_or_ne j i with rfl | h
  · rw [getBit_flipBit_of_eq, getBit_mergeBitRes_of_eq]
  · rw [getBit_flipBit_of_ne h, getBit_mergeBitRes_of_ne h, getBit_getRes]
    rcases h.lt_or_lt with h | h
    · simp only [h.le.not_lt, h.not_le, decide_False, Bool.toNat_false, tsub_zero, add_zero]
    · simp only [h, decide_True, Bool.toNat_true, le_sub_one_of_lt h,
      Nat.sub_add_cancel (one_le_of_lt h)]

lemma flipBit_eq_permCongr (i : ℕ) :
    flipBit i = (getBitRes i).symm.permCongr (boolInversion.prodCongr (Equiv.refl _)) := by
  simp_rw [Equiv.ext_iff, flipBit_eq_mergeBitRes, Equiv.permCongr_apply, Equiv.symm_symm,
    getBitRes_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod_map, boolInversion_apply,
    id_eq, getBitRes_symm_apply, implies_true]

lemma getBit_flipBit_eq (h : r < q) (hf : flipBit i q < flipBit i r) :
    ∀ k ≥ i, getBit k r = getBit k (flipBit i q) := by
  intros k hk
  rcases eq_or_ne k i with rfl | h
  · rw [getBit_flipBit_of_eq]
    sorry
  · rw [getBit_flipBit_of_ne h]


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

@[simps!]
def getBitRes (i : Fin (m + 1)) : BV (m + 1) ≃ Bool × BV m :=
⟨fun q => ⟨Nat.getBit i q, ⟨Nat.getRes i q, (Nat.getRes_lt_iff_lt i.is_le).mpr q.is_lt⟩⟩,
  fun bp => ⟨Nat.mergeBitRes i bp.1 bp.2, (Nat.mergeBitRes_lt_iff_lt i.is_le).mpr bp.2.is_lt⟩,
  fun _ => by simp_rw [Nat.mergeBitRes_getBit_getRes_of_eq],
  fun _ => by simp_rw [Nat.getBit_mergeBitRes_of_eq, Nat.getRes_mergeBitRes_of_eq]⟩

def getBit (i : Fin (m + 1)) (q : BV (m + 1)) : Bool := (getBitRes i q).1

def getRes (i : Fin (m + 1)) (q : BV (m + 1)) : BV m := (getBitRes i q).2

def mergeBitRes (i : Fin (m + 1)) (b : Bool) (p : BV m) := (getBitRes i).symm (b, p)

lemma getBit_def : getBit i q = (getBitRes i q).fst := rfl

lemma getRes_def : getRes i q = (getBitRes i q).snd := rfl

lemma mergeBitRes_def : mergeBitRes i b p = (getBitRes i).symm (b, p) := rfl

@[simp]
lemma getBit_eq : getBit i q = Nat.getBit i q := rfl

@[simp]
lemma getRes_val_eq : (getRes i q : ℕ) = Nat.getRes i q := rfl

@[simp]
lemma mergeBitRes_val_eq : (mergeBitRes i b p : ℕ) = Nat.mergeBitRes i b p := rfl

lemma ge_of_getBit_true {i : Fin (m + 1)} (h : getBit i q = true) : 2^i.val ≤ q := by
  simp_rw [Fin.le_iff_val_le_val, two_pow_val_BV]
  exact Nat.ge_of_getBit_true h

@[simp]
lemma getBitRes_apply' (j : Fin (m + 1)) (q : BV (m + 1)) : (getBitRes j) q =
  (finTwoEquiv (finFunctionFinEquiv.symm q j),
  finFunctionFinEquiv (fun i => finFunctionFinEquiv.symm q (j.succAbove i))) := by
  simp_rw [getBitRes_apply, Nat.getBit_eq, Nat.getRes_eq, finTwoEquiv_apply, Prod.mk.injEq,
    ← Equiv.symm_apply_eq, decide_eq_decide]
  refine' ⟨_, _⟩
  · rw [Fin.ext_iff, Fin.val_one, finFunctionFinEquiv_symm_apply_val]
  · simp_rw [Function.funext_iff, Fin.ext_iff, finFunctionFinEquiv_symm_apply_val]
    intro a
    rcases lt_or_le a.castSucc j with h | h
    · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.coe_castSucc]
      rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] at h
      rw [← Nat.getRes_eq, ← Nat.getBit_toNat, ← Nat.getBit_toNat, Nat.getBit_getRes_of_lt h]
    · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
      rw [Fin.le_iff_val_le_val, Fin.coe_castSucc] at h
      rw [← Nat.getRes_eq, ← Nat.getBit_toNat, ← Nat.getBit_toNat, Nat.getBit_getRes_of_ge h]

lemma getBitRes_reflect : getBitRes (i : Fin (m + 1)) =
    (calc
      _ ≃ (Fin (m + 1) → Fin 2)   := finFunctionFinEquiv.symm
      _ ≃ Fin 2 × (Fin m → Fin 2) := Equiv.piFinSuccAbove _ i
      _ ≃ _                       := finTwoEquiv.prodCongr finFunctionFinEquiv) := by
  simp_rw [Equiv.ext_iff, getBitRes_apply']
  exact fun _ => rfl

@[simp]
lemma getBitRes_symm_apply' (i : Fin (m + 1)) (bp : Bool × BV m) :
    (getBitRes i).symm bp = finFunctionFinEquiv
    (i.insertNth (finTwoEquiv.symm bp.fst) (finFunctionFinEquiv.symm bp.snd)) := by
  simp_rw [Equiv.symm_apply_eq, getBitRes_reflect, Equiv.instTrans_trans,
    finTwoEquiv_symm_apply, cond_eq_if, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.piFinSuccAbove_apply, Fin.extractNth_insertNth, Equiv.prodCongr_apply, Prod_map,
    finTwoEquiv_apply, ite_eq_left_iff, Bool.not_eq_true, zero_ne_one, imp_false, Bool.not_eq_false,
    Bool.decide_eq_true, Equiv.apply_symm_apply]

/-


@[simp]
lemma getBitRes_symm_apply (i : Fin (m + 1)) (bp : Bool × BV m) : (getBitRes i).symm bp =
  finFunctionFinEquiv (i.insertNth (finTwoEquiv.symm bp.fst) (finFunctionFinEquiv.symm bp.snd)) :=
  rfl
-/




/-
lemma getBit_def' : getBit i q = q.val.testBit i := by
  simp_rw [Nat.testBit_to_div_mod, getBit_def, getBitRes_apply, finTwoEquiv_apply,
  Fin.ext_iff, finFunctionFinEquiv_symm_apply_val, Fin.val_one]
-/




/-
lemma getRes_def_of_getBit {i : Fin (m + 1)} (h : getBit i q) :
    getRes i q =
    ((finCongr (by rw [← pow_add,  ← add_assoc, Nat.sub_add_cancel i.is_le]) q).divNat
    (n := 2^(i.val + 1)) : BV (m - i.val)).castLE ((Nat.pow_le_pow_iff_right (one_lt_two)).mpr
      (by simp_rw [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.zero_le])) +
    ((finCongr (by rw [← pow_add, Nat.sub_add_cancel i.is_le']) q).modNat (n := 2^i.val)).castLE
    ((Nat.pow_le_pow_iff_right (one_lt_two)).mpr i.is_le : 2^i.val ≤ 2^m) := by
  simp_rw [getRes_def, getBitRes_apply, Equiv.apply_eq_iff_eq_symm_apply, Function.funext_iff,
  Fin.ext_iff, finFunctionFinEquiv_symm_apply_val, finCongr_apply, Fin.val_add,
  Fin.coe_castLE, Fin.coe_divNat, Fin.coe_modNat, Fin.coe_cast, Nat.mod_eq_of_lt (smoopy i q.isLt)]
  intro a
  rcases lt_or_le (a.castSucc) i with h | h
  · simp_rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.coe_castSucc]
    sorry
  · simp_rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
  simp_rw [Fin.ext_iff, Fin.val_add, finCongr_apply, Fin.coe_castLE, Fin.coe_divNat,
    Fin.coe_modNat, Fin.coe_cast, Nat.mod_eq_of_lt (smoopy i q.isLt)]

lemma getRes_def_val : getRes i q = ⟨q / 2^(i.val + 1) + q % 2^i.val, smoopy i q.isLt⟩ := by
  simp_rw [getRes_def, getBitRes_apply, Equiv.apply_eq_iff_eq_symm_apply, Function.funext_iff,
  Fin.ext_iff, finFunctionFinEquiv_symm_apply_val]
  intro a
  rcases lt_or_le (a.castSucc) i with h | h
  · simp_rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.coe_castSucc]
    sorry
  · simp_rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.val_succ]
  rcases h : (getBit i q) with (_ | _)
  · rw [cond_false, tsub_zero, getRes_def]
    simp_rw [getBitRes_apply, finTwoEquiv_apply, Fin.isValue, finFunctionFinEquiv_apply_val,
      finFunctionFinEquiv_symm_apply_val]
-/



lemma getBitRes_apply_zero : getBitRes i 0 = (false, 0) := by
ext <;> simp only [getBitRes_apply', finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply,
  Fin.val_zero', Nat.zero_div, Nat.zero_mod, Fin.zero_eta, finTwoEquiv_apply, zero_ne_one,
  decide_False, Equiv.ofRightInverseOfCardLE_apply, Fin.val_zero, zero_mul, Finset.sum_const_zero]

lemma getBit_def_zero : getBit i 0 = false := by
rw [getBit_def, getBitRes_apply_zero]

lemma getRes_def_zero : getRes i 0 = 0 := by
rw [getRes_def, getBitRes_apply_zero]

lemma mergeBitRes_apply_false_zero : mergeBitRes i false 0 = 0 := by
rw [mergeBitRes_def, ← getBitRes_apply_zero (i := i), Equiv.symm_apply_apply]

lemma getBitRes_apply_two_pow {i : Fin (m + 1)} : getBitRes i (2^i.val) = (true, 0) := by
  ext
  · simp only [getBitRes_apply', finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply,
    two_pow_val_BV, gt_iff_lt, Nat.ofNat_pos, pow_pos, Nat.div_self, Nat.mod_succ, Fin.mk_one,
    Fin.isValue, finTwoEquiv_apply, decide_True, Equiv.ofRightInverseOfCardLE_apply]
  · simp only [getBitRes_apply', finTwoEquiv_apply, Fin.isValue, finFunctionFinEquiv_apply_val,
    finFunctionFinEquiv_symm_apply_val, two_pow_val_BV, Fin.val_zero', Finset.sum_eq_zero_iff,
    Finset.mem_univ, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false,
    true_implies]
    intro x
    rcases (Fin.succAbove_ne i x).lt_or_lt with h | h <;> rw [Fin.lt_iff_val_lt_val] at h
    · rw [Nat.pow_div h.le zero_lt_two, Nat.pow_mod, Nat.mod_self,
        Nat.zero_pow (Nat.sub_pos_of_lt h), Nat.zero_mod]
    · rw [Nat.div_eq_of_lt (pow_lt_pow_right one_lt_two h), Nat.zero_mod]

lemma getBit_def_two_pow {i : Fin (m + 1)} : getBit i (2^i.val) = true := by
  rw [getBit_def, getBitRes_apply_two_pow]

lemma getBit_def_zero_one : getBit 0 (1 : BV (m + 1)) = true := getBit_def_two_pow

lemma getRes_def_two_pow {i : Fin (m + 1)} : getRes i (2^i.val) = 0 := by
  rw [getRes_def, getBitRes_apply_two_pow]

lemma mergeBitRes_apply_true_zero {i : Fin (m + 1)} :
  mergeBitRes i true 0 = 2^i.val := by
  rw [mergeBitRes_def, ← getBitRes_apply_two_pow (i := i), Equiv.symm_apply_apply]

lemma getBitRes_lt {i : Fin (m + 1)} {r : BV (m + 1)} (h : r < 2^i.val) :
    getBitRes i r = (false, r.castLT (val_lt_two_pow_BV_succ h)) := by
  rw [Fin.lt_iff_val_lt_val, two_pow_val_BV] at h
  ext : 1
  · simp_rw [getBitRes_apply', Equiv.apply_eq_iff_eq_symm_apply, finTwoEquiv_symm_apply, cond_false,
    Fin.ext_iff, finFunctionFinEquiv_symm_apply_val,
    Nat.div_eq_of_lt h, Nat.zero_mod, Fin.val_zero]
  · simp_rw [getBitRes_apply', Equiv.apply_eq_iff_eq_symm_apply, Function.funext_iff, Fin.ext_iff,
    finFunctionFinEquiv_symm_apply_val, Fin.coe_castLT]
    intro x
    rcases lt_or_le x.castSucc i with h' | h'
    · simp_rw [Fin.succAbove_of_castSucc_lt _ _ h', Fin.coe_castSucc]
    · simp_rw [Fin.succAbove_of_le_castSucc _ _ h', Fin.val_succ]
      rw [Fin.le_iff_val_le_val, Fin.coe_castSucc] at h'
      rw [Nat.div_eq_of_lt (h.trans_le (Nat.pow_le_pow_of_le one_lt_two h')),
      Nat.div_eq_of_lt (h.trans_le (Nat.pow_le_pow_of_le one_lt_two (h'.trans (Nat.le_succ x))))]

lemma getBit_lt {i : Fin (m + 1)} {r : BV (m + 1)} (h : r < 2^i.val) :
    getBit i r = false := by rw [getBit_def, getBitRes_lt h]

lemma getRes_lt {i : Fin (m + 1)} {r : BV (m + 1)} (h : r < 2^i.val) :
    getRes i r = r.castLT (val_lt_two_pow_BV_succ h) :=
  by rw [getRes_def, getBitRes_lt h]

def getBitResSucc (i : Fin (m + 1)) : BV (m + 2) ≃ Bool × BV (m + 1) :=
calc
  _ ≃ _ := getBitRes 0
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes 0).symm

lemma getBitResSucc_apply {i : Fin (m + 1)} :
    getBitResSucc i q = (((getBitRes i) ((getBitRes 0) q).2).1,
    (getBitRes 0).symm (((getBitRes 0) q).1, ((getBitRes i) ((getBitRes 0) q).2).2)) := rfl

lemma getBitResSucc_symm_apply {i : Fin (m + 1)} : (getBitResSucc i).symm (b, p) =
    (getBitRes 0).symm ((getBitRes 0 p).1, (getBitRes i).symm (b, (getBitRes 0 p).2)) := rfl

lemma getBitRes_succ {i : Fin (m + 1)} : getBitRes (i.succ) = getBitResSucc i := by
  simp_rw [Equiv.ext_iff, getBitResSucc_apply,
    getBitRes_apply', getBitRes_symm_apply', Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_zero, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_succ, true_and, implies_true]

lemma getBitRes_succ_apply {i : Fin (m + 1)} : getBitRes (i.succ) q =
    (((getBitRes i) ((getBitRes 0) q).2).1,
    (getBitRes 0).symm (((getBitRes 0) q).1, ((getBitRes i) ((getBitRes 0) q).2).2)) := by
  rw [getBitRes_succ, getBitResSucc_apply]

lemma getBitRes_succ_symm_apply {i : Fin (m + 1)} : (getBitRes (i.succ)).symm (b, p) =
    (getBitRes 0).symm ((getBitRes 0 p).1, (getBitRes i).symm (b, (getBitRes 0 p).2)) := by
  rw [getBitRes_succ, getBitResSucc_symm_apply]

lemma getRes_succ (i : Fin (m + 1)) : getRes (i.succ) q =
    mergeBitRes 0 (getBit 0 q) (getRes i (getRes 0 q)) := by
  simp_rw [getRes_def, mergeBitRes_def, getBit_def, getBitRes_succ_apply]

lemma getBit_succ (i : Fin (m + 1)) :
    getBit (i.succ) q = getBit i (getRes 0 q) := by
  simp_rw [getRes_def, getBit_def, getBitRes_succ_apply]

lemma mergeBitRes_succ (i : Fin (m + 1)) : mergeBitRes i.succ b q =
    mergeBitRes 0 (getBit 0 q) (mergeBitRes i b (getRes 0 q)) := by
  simp_rw [mergeBitRes_def, getBit_def, getRes_def, getBitRes_succ_symm_apply]

def getBitResCastSucc (i : Fin (m + 1)) : BV (m + 2) ≃ Bool × BV (m + 1) :=
calc
  _ ≃ _ := getBitRes (Fin.last _)
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes (Fin.last _)).symm

lemma getBitResCastSucc_apply {i : Fin (m + 1)} :
    getBitResCastSucc i q = (((getBitRes i) ((getBitRes (Fin.last _)) q).2).1,
    (getBitRes (Fin.last _)).symm (((getBitRes (Fin.last _)) q).1,
    ((getBitRes i) ((getBitRes (Fin.last _)) q).2).2)) := rfl

lemma getBitResCastSucc_symm_apply {i : Fin (m + 1)} : (getBitResCastSucc i).symm (b, p) =
    (getBitRes (Fin.last _)).symm ((getBitRes (Fin.last _) p).1,
    (getBitRes i).symm (b, (getBitRes (Fin.last _) p).2)) := rfl

lemma getBitRes_castSucc {i : Fin (m + 1)} : getBitRes (i.castSucc) = getBitResCastSucc i := by
  simp_rw [Equiv.ext_iff, getBitResCastSucc_apply,
    getBitRes_apply', getBitRes_symm_apply', Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_last, Fin.castSucc_succAbove_last,
    Fin.castSucc_succAbove_castSucc, true_and, implies_true]

lemma getBitRes_castSucc_apply {i : Fin (m + 1)} : getBitRes (i.castSucc) q =
    (((getBitRes i) ((getBitRes (Fin.last _)) q).2).1,
    (getBitRes (Fin.last _)).symm (((getBitRes (Fin.last _)) q).1,
    ((getBitRes i) ((getBitRes (Fin.last _)) q).2).2)) := by
  rw [getBitRes_castSucc, getBitResCastSucc_apply]

lemma getBitRes_castSucc_symm_apply {i : Fin (m + 1)} : (getBitRes (i.castSucc)).symm (b, p) =
    (getBitRes (Fin.last _)).symm ((getBitRes (Fin.last _) p).1,
    (getBitRes i).symm (b, (getBitRes (Fin.last _) p).2)) := by
  rw [getBitRes_castSucc, getBitResCastSucc_symm_apply]

lemma getRes_castSucc (i : Fin (m + 1)) : getRes (i.castSucc) q =
    mergeBitRes (Fin.last _) (getBit (Fin.last _) q) (getRes i (getRes (Fin.last _) q)) := by
  simp_rw [getRes_def, mergeBitRes_def, getBit_def, getBitRes_castSucc_apply]

lemma getBit_castSucc (i : Fin (m + 1)) :
    getBit (i.castSucc) q = getBit i (getRes (Fin.last _) q) := by
  simp_rw [getRes_def, getBit_def, getBitRes_castSucc_apply]

lemma mergeBitRes_castSucc (i : Fin (m + 1)) : mergeBitRes i.castSucc b q =
    mergeBitRes (Fin.last _) (getBit (Fin.last _) q) (mergeBitRes i b (getRes (Fin.last _) q)) := by
  simp_rw [mergeBitRes_def, getBit_def, getRes_def, getBitRes_castSucc_symm_apply]

def getBitResZero : BV (m + 1) ≃ Bool × BV m :=
 calc
  _ ≃ _ := finProdFinEquiv.symm
  _ ≃ _ := Equiv.prodComm ..
  _ ≃ _ := finTwoEquiv.prodCongr (Equiv.refl _)

lemma getBitResZero_apply : getBitResZero q = (finTwoEquiv q.modNat, q.divNat) := rfl

lemma getBitResZero_symm_apply : getBitResZero.symm (b, p) =
  finProdFinEquiv (p, bif b then 1 else 0) := by cases b <;> rfl

lemma getBitRes_zero : getBitRes (0 : Fin (m + 1)) = getBitResZero := by
  ext q : 1
  simp_rw [getBitRes_apply', getBitResZero_apply, Fin.zero_succAbove, finFunctionFinEquiv,
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

lemma getBitRes_zero_apply : getBitRes (0 : Fin (m + 1)) q = (finTwoEquiv q.modNat, q.divNat) := by
  simp_rw [getBitRes_zero, getBitResZero_apply]

lemma getBitRes_zero_symm_apply : (getBitRes (0 : Fin (m + 1))).symm (b, p) =
  finProdFinEquiv (p, bif b then 1 else 0) := by simp_rw [getBitRes_zero, getBitResZero_symm_apply]

lemma getBit_zero : getBit 0 q = finTwoEquiv q.modNat := by
  simp_rw [getBit_def, getBitRes_zero_apply]

lemma getRes_zero : getRes 0 q = q.divNat := by
  simp_rw [getRes_def, getBitRes_zero_apply]

lemma mergeBitRes_zero : mergeBitRes 0 b p = finProdFinEquiv (p, (bif b then 1 else 0)) := by
  simp_rw [mergeBitRes_def, getBitRes_zero_symm_apply]

lemma mergeBitRes_zero_divNat_modNat : ((mergeBitRes 0 b p).divNat, (mergeBitRes 0 b p).modNat) =
  (p, (bif b then 1 else 0)) := by
  simp_rw [← finProdFinEquiv_symm_apply, Equiv.symm_apply_eq]
  exact mergeBitRes_zero

lemma mergeBitRes_zero_divNat : (mergeBitRes 0 b p).divNat = p :=
(Prod.ext_iff.mp (mergeBitRes_zero_divNat_modNat (b := b) (p := p))).1

lemma mergeBitRes_zero_modNat : (mergeBitRes 0 b p).modNat = bif b then 1 else 0 :=
(Prod.ext_iff.mp (mergeBitRes_zero_divNat_modNat (b := b) (p := p))).2

lemma mergeBitRes_zero_apply_true_zero_eq_one : mergeBitRes (0 : Fin (m + 1)) true 0 = 1 := by
  simp_rw [mergeBitRes_zero, Fin.ext_iff, finProdFinEquiv_apply_val, Fin.val_zero', mul_zero,
  add_zero, Bool.cond_true, Fin.val_one, Fin.val_one', ← Nat.pow_succ,
  Nat.mod_eq_of_lt (Nat.one_lt_pow' _ _ )]


def getBitResLast : BV (m + 1) ≃ Bool × BV m :=
 calc
  _ ≃ _ := finCongr (mul_comm _ _)
  _ ≃ _ := finProdFinEquiv.symm
  _ ≃ _ := finTwoEquiv.prodCongr (Equiv.refl _)

lemma getBitResLast_apply {q : BV (m + 1)} :
  getBitResLast q =
  (finTwoEquiv (finCongr (mul_comm _ _) q).divNat, (finCongr (mul_comm _ _) q).modNat) := rfl

lemma getBitResLast_symm_apply {p : BV m} : getBitResLast.symm (b, p) =
  finCongr (mul_comm _ _) (finProdFinEquiv (bif b then 1 else 0, p)) := by cases b <;> rfl

lemma mergeBitRes_base_true : mergeBitRes (m := 0) i true p = 1 := by
rw [Fin.eq_zero p, Fin.eq_zero i] ; exact mergeBitRes_zero_apply_true_zero_eq_one

lemma mergeBitRes_base_false : mergeBitRes (m := 0) i false p = 0 := by
rw [Fin.eq_zero p] ; exact mergeBitRes_apply_false_zero

lemma mergeBitRes_base : mergeBitRes (m := 0) i b p = if b then 1 else 0 :=
  b.rec mergeBitRes_base_false mergeBitRes_base_true

lemma getBit_base : getBit (m := 0) i q = decide (q = 1) := by
  rw [Fin.eq_zero i]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

lemma getRes_base : getRes (m := 0) i q = 0 := by
  rw [Fin.eq_zero i]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

def getBitResSuccAbove (j : Fin (m + 2)) (i : Fin (m + 1)) :
  BV (m + 2) ≃ Bool × BV (m + 1) :=
calc
  _ ≃ _ := getBitRes j
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes (i.predAbove j)).symm

lemma getBitResSuccAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
    getBitResSuccAbove j i q = (((getBitRes i) ((getBitRes j) q).2).1,
    (getBitRes (i.predAbove j)).symm (((getBitRes j) q).1,
    ((getBitRes i) ((getBitRes j) q).2).2)) := rfl

lemma getBitResSuccAbove_symm_apply : (getBitResSuccAbove j i).symm (b, p) =
    (getBitRes j).symm ((getBitRes (i.predAbove j) p).1,
    (getBitRes i).symm (b, (getBitRes (i.predAbove j) p).2)) := rfl

lemma getBitRes_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} :
  getBitRes (j.succAbove i) = getBitResSuccAbove j i := by
  simp_rw [Equiv.ext_iff, getBitResSuccAbove_apply,
    getBitRes_apply', getBitRes_symm_apply', Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_succAbove_predAbove,
    Fin.succAbove_succAbove_predAbove_succAbove, true_and, implies_true]

lemma getBitRes_succAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} : getBitRes (j.succAbove i) q =
    (((getBitRes i) ((getBitRes j) q).2).1,
    (getBitRes (i.predAbove j)).symm (((getBitRes j) q).1,
    ((getBitRes i) ((getBitRes j) q).2).2)) := by
  rw [getBitRes_succAbove, getBitResSuccAbove_apply]

lemma getBitRes_succAbove_symm_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
    (getBitRes (j.succAbove i)).symm (b, p) =
    (getBitRes j).symm ((getBitRes (i.predAbove j) p).1,
    (getBitRes i).symm (b, (getBitRes (i.predAbove j) p).2)) := by
  rw [getBitRes_succAbove, getBitResSuccAbove_symm_apply]

lemma getRes_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} : getRes (j.succAbove i) q =
    mergeBitRes (i.predAbove j) (getBit j q) (getRes i (getRes j q)) := by
  simp_rw [getRes_def, mergeBitRes_def, getBit_def, getBitRes_succAbove_apply]

lemma getBit_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} :
    getBit (j.succAbove i) q = getBit i (getRes j q) := by
  simp_rw [getBit_eq, getRes_val_eq, Nat.getBit_getRes, Fin.val_succAbove]

lemma mergeBitRes_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} : mergeBitRes (j.succAbove i) b q =
    mergeBitRes j (getBit (i.predAbove j) q) (mergeBitRes i b (getRes (i.predAbove j) q)) := by
  simp_rw [mergeBitRes_def, getBit_def, getRes_def, getBitRes_succAbove_symm_apply]

@[simp]
lemma getBit_mergeBitRes : getBit i (mergeBitRes i b p) = b := by
simp_rw [getBit_def, mergeBitRes_def, Equiv.apply_symm_apply]

@[simp]
lemma getRes_mergeBitRes  : getRes i (mergeBitRes i b p) = p := by
simp_rw [getRes_def, mergeBitRes_def, Equiv.apply_symm_apply]

@[simp]
lemma mergeBitRes_getBit_getRes : mergeBitRes i (getBit i q) (getRes i q) = q := by
simp_rw [getRes_def, mergeBitRes_def, getBit_def, Prod.mk.eta, Equiv.symm_apply_apply]

lemma mergeBitRes_surj (i : Fin (m + 1)) (q : BV (m + 1)) :
  ∃ b p, mergeBitRes i b p = q :=
  ⟨getBit i q, getRes i q, mergeBitRes_getBit_getRes⟩

lemma mergeBitRes_Bool_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) :
  b₁ = b₂ := by
  have h₂ := (congrArg (getBit i) h) ; simp only [getBit_mergeBitRes] at h₂ ; exact h₂

lemma mergeBitRes_Fin_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) :
  p₁ = p₂ := by
  have h₂ := (congrArg (getRes i) h) ; simp_rw [getRes_mergeBitRes] at h₂ ; exact h₂

lemma mergeBitRes_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) :
  b₁ = b₂ ∧ p₁ = p₂ :=
  ⟨mergeBitRes_Bool_inj i h, mergeBitRes_Fin_inj i h⟩

lemma mergeBitRes_inj_iff (i : Fin (m + 1)) : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂ ↔
  b₁ = b₂ ∧ p₁ = p₂ :=
  ⟨mergeBitRes_inj i, by rintro ⟨rfl, rfl⟩ ; rfl⟩

lemma mergeBitRes_ne_inj_iff (i : Fin (m + 1)) : mergeBitRes i b₁ p₁ ≠ mergeBitRes i b₂ p₂ ↔
  b₁ ≠ b₂ ∨ p₁ ≠ p₂ := by rw [ne_eq, mergeBitRes_inj_iff, not_and_or]

lemma getRes_getBit_inj (i : Fin (m + 1)) (h₁ : getBit i q₁ = getBit i q₂)
  (h₂ : getRes i q₁ = getRes i q₂) : q₁ = q₂ :=
  by rw [← mergeBitRes_getBit_getRes (i := i) (q := q₁), h₁, h₂, mergeBitRes_getBit_getRes]

lemma getRes_getBit_inj_iff (i : Fin (m + 1)) :
q₁ = q₂ ↔ getBit i q₁ = getBit i q₂ ∧ getRes i q₁ = getRes i q₂ :=
⟨by rintro rfl ; exact ⟨rfl, rfl⟩, and_imp.mpr (getRes_getBit_inj i)⟩

lemma mergeBitRes_eq_iff :
  mergeBitRes i b p = q ↔ (getBit i q = b) ∧ (getRes i q = p) :=
⟨fun H => H ▸ ⟨getBit_mergeBitRes, getRes_mergeBitRes⟩, fun ⟨rfl, rfl⟩ => mergeBitRes_getBit_getRes⟩

lemma eq_mergeBitRes_iff :
    q = mergeBitRes i b p ↔ (getBit i q = b) ∧ (getRes i q = p) := by
    rw [← mergeBitRes_eq_iff, eq_comm]

lemma mergeBitRes_ne_iff :
    mergeBitRes i b p ≠ q ↔ (getBit i q ≠ b) ∨ (getRes i q ≠ p) := by
    simp_rw [ne_eq, mergeBitRes_eq_iff, Decidable.not_and_iff_or_not]

lemma ne_mergeBitRes_iff :
    q ≠ mergeBitRes i b p ↔ (getBit i q ≠ b) ∨ (getRes i q ≠ p) := by
    rw [← mergeBitRes_ne_iff, ne_comm]

lemma mergeBitRes_getRes_of_getBit_eq (h : getBit i q = b) : mergeBitRes i b (getRes i q) = q := by
simp_rw [← h, mergeBitRes_getBit_getRes]

lemma mergeBitRes_getRes_cases (i : Fin (m + 1)) (q : BV (m + 1)) :
(getBit i q = false ∧ mergeBitRes i false (getRes i q) = q) ∨
(getBit i q = true ∧ mergeBitRes i true (getRes i q) = q) := by
  rcases (getBit i q).dichotomy with (h | h) <;>
  simp_rw [h, mergeBitRes_getRes_of_getBit_eq h, false_and, and_self]
  · simp_rw [or_false]
  · simp_rw [or_true]

lemma mergeBitRes_getBit_of_getRes_eq (h : getRes i q = p) : mergeBitRes i (getBit i q) p = q := by
simp_rw [← h, mergeBitRes_getBit_getRes]

lemma mergeBitRes_inv (h₁ : getBit i q = b) (h₂ : getRes i q = p) : mergeBitRes i b p = q := by
simp_rw [← h₁, ← h₂, mergeBitRes_getBit_getRes]

lemma getRes_inv (i : Fin (m + 1)) (h : mergeBitRes i (getBit i q) p = q) : getRes i q = p := by
  rcases mergeBitRes_surj i q with ⟨b, p', rfl⟩ ; rw [getRes_mergeBitRes]
  exact (mergeBitRes_Fin_inj i h).symm

lemma getBit_inv (i : Fin (m + 1)) (h : mergeBitRes i b (getRes i q) = q) : getBit i q = b := by
  rcases mergeBitRes_surj i q with ⟨b', p', rfl⟩ ; rw [getBit_mergeBitRes]
  exact (mergeBitRes_Bool_inj i h).symm

lemma forall_iff_forall_mergeBitRes (i : Fin (m + 1)) {pr : BV (m + 1) → Prop} :
  (∀ (q : BV (m + 1)), pr q) ↔ (∀ b p, pr (mergeBitRes i b p)) :=
  ⟨fun h _ _ => h _, fun h q => by rcases mergeBitRes_surj i q with ⟨b, p, rfl⟩ ; exact h _ _⟩

lemma forall_iff_forall_mergeBitRes_bool (i : Fin (m + 1)) {pr : BV (m + 1) → Prop} :
  (∀ (q : BV (m + 1)), pr q) ↔
  (∀ p, pr (mergeBitRes i false p)) ∧ (∀ p, pr (mergeBitRes i true p)) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩,
    fun h q => by rcases mergeBitRes_surj i q with ⟨(h|h), p, rfl⟩
                  · exact h.1 _
                  · exact h.2 _⟩

lemma exists_iff_exists_mergeBitRes (i : Fin (m + 1)) {pr : BV (m + 1) → Prop} :
(∃ (q : BV (m + 1)), pr q) ↔ (∃ b p, pr (mergeBitRes i b p)) :=
⟨ fun ⟨q, hq⟩ => ⟨getBit i q, getRes i q, mergeBitRes_getBit_getRes ▸ hq⟩,
  fun ⟨b, p, hbp⟩ => ⟨mergeBitRes i b p, hbp⟩⟩

lemma getBit_surj (i : Fin (m + 1)) (q : BV (m + 1)) :
  ∃ p, mergeBitRes i (getBit i q) p = q :=
  ⟨getRes i q, mergeBitRes_getBit_getRes⟩

lemma getRes_surj (i : Fin (m + 1)) (q : BV (m + 1)) :
  ∃ b, mergeBitRes i b (getRes i q) = q :=
  ⟨getBit i q, mergeBitRes_getBit_getRes⟩

lemma ne_iff_getBit_ne_or_getRes_ne (i : Fin (m + 1)) :
q₁ ≠ q₂ ↔ getBit i q₁ ≠ getBit i q₂ ∨ getRes i q₁ ≠ getRes i q₂ := by
rw [ne_eq q₁, getRes_getBit_inj_iff i, not_and_or]

lemma ne_of_getBit_ne (i : Fin (m + 1)) (h : getBit i q₁ ≠ getBit i q₂) :
q₁ ≠ q₂ := (ne_iff_getBit_ne_or_getRes_ne i).mpr (Or.inl h)

lemma ne_of_getRes_ne (i : Fin (m + 1)) (h : getRes i q₁ ≠ getRes i q₂) :
q₁ ≠ q₂ := (ne_iff_getBit_ne_or_getRes_ne i).mpr (Or.inr h)

lemma getBit_ext_iff {q q' : BV (m + 1)} :
    q = q' ↔ (∀ i : Fin (m + 1), getBit i q = getBit i q') := by
  refine' ⟨fun h _ => h ▸ rfl, fun h => _⟩
  induction' m with m IH
  · simp_rw [getRes_getBit_inj_iff 0, Fin.eq_zero, and_true, h]
  · simp_rw [Fin.forall_fin_succ (P := fun i => getBit i q = getBit i q'), getBit_succ] at h
    exact (getRes_getBit_inj_iff 0).mpr ⟨h.1, IH h.2⟩

lemma getBit_ext {q q' : BV (m + 1)} (h : ∀ i : Fin (m + 1), getBit i q = getBit i q') :
    q = q' := getBit_ext_iff.mpr h

end GetMerge

section bitInvar

def bitInvar (i : Fin (m + 1)) (f : Function.End (BV (m + 1))) : Prop :=
∀ q, getBit i (f q) = getBit i q

lemma bitInvar_iff_getBit_apply_eq_getBit :
  bitInvar i f ↔ ∀ q, getBit i (f q) = getBit i q := Iff.rfl

lemma bitInvar_of_getBit_def_eq_getBit {f : Function.End (BV (m + 1))}
  (h : ∀ q, getBit i (f q) = getBit i q) : bitInvar i f :=
  bitInvar_iff_getBit_apply_eq_getBit.mpr h

lemma getBit_def_eq_getBit_of_bitInvar (h : bitInvar i f) : getBit i (f q) = getBit i q :=
bitInvar_iff_getBit_apply_eq_getBit.mp h _

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

lemma mergeBitRes_getBit_getRes_def_eq_apply_of_bitinvar (h : bitInvar i f) :
mergeBitRes i (getBit i q) (getRes i (f q)) = f q := by
  rw [← h q, mergeBitRes_getBit_getRes]

@[simp]
lemma mergeBitRes_getRes_def_mergeBitRes_of_bitinvar (h : bitInvar i f) :
mergeBitRes i b (getRes i (f (mergeBitRes i b p))) = f (mergeBitRes i b p) := by
  convert (getBit_mergeBitRes ▸ mergeBitRes_getBit_getRes_def_eq_apply_of_bitinvar h)

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
  fun q => mergeBitRes i (getBit i q) (f (getBit i q) (getRes i q))

@[simp]
lemma endoOfBoolArrowEndo_def {i : Fin (m + 1)} {f : Bool → Function.End (BV m)}
  {q : BV (m + 1)} :
  endoOfBoolArrowEndo i f q = mergeBitRes i (getBit i q) (f (getBit i q) (getRes i q)) := rfl

lemma endoOfBoolArrowEndo_bitInvar {i : Fin (m + 1)} (f : Bool → Function.End (BV m)) :
  bitInvar i (endoOfBoolArrowEndo i f) := by
  simp_rw [bitInvar_iff_getBit_apply_eq_getBit, endoOfBoolArrowEndo_def,
    getBit_mergeBitRes, implies_true]

lemma endoOfBoolArrowEndo_mem_bitInvarSubmonoid {i : Fin (m + 1)}
  (f : Bool → Function.End (BV m)) : (endoOfBoolArrowEndo i f) ∈ bitInvarSubmonoid i :=
  endoOfBoolArrowEndo_bitInvar f

lemma endoOfBoolArrowEndo_comp {i : Fin (m + 1)} (f g : Bool → Function.End (BV m)) :
  endoOfBoolArrowEndo i (fun b => (f b) ∘ (g b)) = endoOfBoolArrowEndo i f ∘ endoOfBoolArrowEndo i g
  := by simp_rw [Function.End.ext_iff, Function.comp_apply, endoOfBoolArrowEndo_def,  getBit_mergeBitRes,
    getRes_mergeBitRes, Function.comp_apply, implies_true]

lemma endoOfBoolArrowEndo_mul {i : Fin (m + 1)} (f g : Bool → Function.End (BV m)) :
  endoOfBoolArrowEndo i (f * g) = endoOfBoolArrowEndo i f * endoOfBoolArrowEndo i g
  := endoOfBoolArrowEndo_comp _ _

def boolArrowEndoOfEndo (i : Fin (m + 1)) (f : Function.End (BV (m + 1))) :
  Bool → Function.End (BV m) := fun b p => getRes i (f (mergeBitRes i b p))

@[simp]
lemma boolArrowEndoOfEndo_def {i : Fin (m + 1)} {f : Function.End (BV (m + 1))}
{b : Bool} {p : BV m} : boolArrowEndoOfEndo i f b p = getRes i (f (mergeBitRes i b p)) := rfl

lemma endoOfBoolArrowEndo_rightInverse (i : Fin (m + 1)) :
Function.RightInverse (endoOfBoolArrowEndo i) (boolArrowEndoOfEndo i) := fun f => by
  ext ; simp_rw [boolArrowEndoOfEndo_def, endoOfBoolArrowEndo_def, getBit_mergeBitRes,
    getRes_mergeBitRes]

lemma endoOfBoolArrowEndo_leftInvOn (i : Fin (m + 1)) :
  Set.LeftInvOn (endoOfBoolArrowEndo i) (boolArrowEndoOfEndo i) (bitInvar i) := fun f hf => by
  ext q ; simp_rw [endoOfBoolArrowEndo_def, boolArrowEndoOfEndo_def, mergeBitRes_getBit_getRes,
    mergeBitRes_getRes_of_getBit_eq (hf q)]

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
  simp_rw [endoOfBoolArrowEndo_def, getBit_mergeBitRes, getRes_mergeBitRes,
    hfg (getBit i q) (getRes i q), mergeBitRes_getBit_getRes]

lemma endoOfBoolArrowEndo_rightInverse_apply {i : Fin (m + 1)}
  {f g : Bool → Function.End (BV m)}
  (hfg : ∀ b : Bool, (Function.RightInverse (f b) (g b))) :
  Function.RightInverse (endoOfBoolArrowEndo i f) (endoOfBoolArrowEndo i g) :=
  endoOfBoolArrowEndo_leftInverse_apply hfg

lemma boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarLeft {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hfg : Function.LeftInverse f g) (hf : bitInvar i f)
  {b : Bool} : Function.LeftInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  fun q => by simp_rw [boolArrowEndoOfEndo_def,
    mergeBitRes_getRes_def_mergeBitRes_of_bitinvar (bitInvar_of_leftInverse_bitInvar hfg hf),
    hfg (mergeBitRes i b q), getRes_mergeBitRes]

lemma boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarLeft {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hfg : Function.RightInverse f g) (hf : bitInvar i f)
  {b : Bool} : Function.RightInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  fun q => by simp_rw [boolArrowEndoOfEndo_def, mergeBitRes_getRes_def_mergeBitRes_of_bitinvar hf,
    hfg (mergeBitRes i b q), getRes_mergeBitRes]

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
    mergeBitRes_getRes_def_mergeBitRes_of_bitinvar hg]

lemma boolArrowEndoOfEndo_mul_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (BV (m + 1))} (hg : bitInvar i g) :
  boolArrowEndoOfEndo i (f * g) = boolArrowEndoOfEndo i f * boolArrowEndoOfEndo i g := by
  ext : 1 ; exact boolArrowEndoOfEndo_comp_ofBitInvarRight hg

end Equivs

end bitInvar

section FlipBit

def flipBit (i : Fin (m + 1)) : Equiv.Perm (BV (m + 1)) :=
(getBitRes i).symm.permCongr <| boolInversion.prodCongr (Equiv.refl _)

lemma flipBit_apply {i : Fin (m + 1)} :
flipBit i q  = mergeBitRes i (!(getBit i q)) (getRes i q) := rfl

lemma flipBit_base : flipBit (m := 0) i = Equiv.swap 0 1 := by
  simp_rw [Equiv.ext_iff, flipBit_apply, Fin.eq_zero i]
  exact Fin.forall_fin_two.mpr ⟨rfl, rfl⟩

lemma flipBit_zero_apply : flipBit 0 q = finProdFinEquiv (q.divNat, q.modNat.rev) := by
  simp_rw [flipBit_apply, getBit_zero, Nat.pow_eq, finTwoEquiv_apply,
    getRes_zero, mergeBitRes_zero, Bool.cond_not, Bool.cond_decide]
  rcases Fin.modNat_two_eq_zero_or_one q with (h | h) <;> simp_rw [h] <;> rfl

@[simp]
lemma flipBit_mergeBitRes : flipBit i (mergeBitRes i b p) = mergeBitRes i (!b) p := by
rw [flipBit_apply, getBit_mergeBitRes, getRes_mergeBitRes]

lemma flipBit_mergeBitRes_false : flipBit i (mergeBitRes i false k) = mergeBitRes i true k :=
flipBit_mergeBitRes (b := false)

lemma flipBit_mergeBitRes_true : flipBit i (mergeBitRes i true k) = mergeBitRes i false k :=
flipBit_mergeBitRes (b := true)

lemma flipBit_mergeBitRes_zero : flipBit 0 (mergeBitRes 0 b p) =
  finProdFinEquiv (p, bif b then 0 else 1) := by
  simp_rw [flipBit_zero_apply, mergeBitRes_zero_divNat,
    mergeBitRes_zero_modNat, Bool.apply_cond (Fin.rev)]
  rfl

lemma flipBit_mergeBitRes_zero_true : flipBit 0 (mergeBitRes 0 true p) = finProdFinEquiv (p, 0) :=
flipBit_mergeBitRes_zero (b := true)

lemma flipBit_mergeBitRes_zero_false : flipBit 0 (mergeBitRes 0 false p) = finProdFinEquiv (p, 1) :=
flipBit_mergeBitRes_zero (b := false)

lemma mergeBitRes_getRes_of_getBit_not (h : getBit i q = !b) :
mergeBitRes i b (getRes i q) = flipBit i q := by
simp_rw [flipBit_apply, h, Bool.not_not]

lemma mergeBitRes_getRes_cases_flipBit (i : Fin (m + 1)) (q) (b) :
  (getBit i q = b ∧ mergeBitRes i b (getRes i q) = q) ∨
  ((getBit i q = !b) ∧ mergeBitRes i b (getRes i q) = flipBit i q) :=
  (Bool.eq_or_eq_not (getBit i q) b).elim
    (fun h => Or.inl (And.intro h (mergeBitRes_getRes_of_getBit_eq h)))
    (fun h => Or.inr (And.intro h (mergeBitRes_getRes_of_getBit_not h)))

lemma flipBit_succ : flipBit (i.succ) q = mergeBitRes 0 (getBit 0 q) (flipBit i (getRes 0 q)) := by
  simp_rw [flipBit_apply, getBit_succ, getRes_succ, mergeBitRes_succ,
  getBit_mergeBitRes, getRes_mergeBitRes]

lemma flipBit_castSucc : flipBit (i.castSucc) q =
  mergeBitRes (Fin.last _) (getBit (Fin.last _) q) (flipBit i (getRes (Fin.last _) q)) := by
  simp_rw [flipBit_apply, getBit_castSucc, getRes_castSucc, mergeBitRes_castSucc,
  getBit_mergeBitRes, getRes_mergeBitRes]

lemma flipBit_succAbove {j : Fin (m + 2)} : flipBit (j.succAbove i) q =
  mergeBitRes j (getBit j q) (flipBit i (getRes j q)) := by
  simp_rw [flipBit_apply, getBit_succAbove, getRes_succAbove, mergeBitRes_succAbove,
  getBit_mergeBitRes, getRes_mergeBitRes]

lemma eq_flipBit_iff : q = flipBit i r ↔ getBit i q = (!getBit i r) ∧
    getRes i q = getRes i r := by
  rcases mergeBitRes_surj i q with ⟨bq, pq, rfl⟩;
  rcases mergeBitRes_surj i r with ⟨br, pr, rfl⟩
  simp_rw [flipBit_mergeBitRes, getBit_mergeBitRes, getRes_mergeBitRes,
    mergeBitRes_inj_iff]

@[simp]
lemma flipBit_flipBit : flipBit i (flipBit i q) = q := by
  simp_rw [flipBit_apply (q := q), flipBit_mergeBitRes,
    Bool.not_not, mergeBitRes_getBit_getRes]

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
lemma getBit_flipBit : getBit i (flipBit i q) = !(getBit i q) := by
  simp_rw [flipBit_apply, getBit_mergeBitRes]

@[simp]
lemma getRes_flipBit : getRes i (flipBit i q) = getRes i q := by
  rw [flipBit_apply, getRes_mergeBitRes]

lemma getBit_flipBit_of_ne {i j : Fin (m + 1)} (h : i ≠ j) :
    getBit i (flipBit j q) = getBit i q := by
  cases m
  · exact (h ((Fin.subsingleton_one).elim i j)).elim
  · rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
    simp_rw [getBit_succAbove, getRes_flipBit]

lemma flipBit_bitInvar_of_ne {i j : Fin (m + 1)} (h : i ≠ j) : bitInvar i ⇑(flipBit j) :=
  bitInvar_of_getBit_def_eq_getBit (fun _ => getBit_flipBit_of_ne h)

lemma getBit_zero_flipBit_succ {i : Fin m} :
    getBit 0 (flipBit (i.succ) q) = getBit 0 q := by
  cases m
  · exact i.elim0
  · rw [flipBit_succ, getBit_mergeBitRes]

lemma getBit_succ_flipBit_zero {i : Fin m} :
    getBit (i.succ) (flipBit 0 q) = getBit (i.succ) q := by
  cases m
  · exact i.elim0
  · simp_rw [getBit_succ, getRes_flipBit]

lemma flipBit_succ_bitInvar_zero {i : Fin m} : bitInvar 0 ⇑(flipBit (i.succ)) :=
  bitInvar_of_getBit_def_eq_getBit (fun _ => getBit_zero_flipBit_succ)

lemma flipBit_zero_bitInvar_succ {i : Fin m} : bitInvar (i.succ) ⇑(flipBit 0) :=
  bitInvar_of_getBit_def_eq_getBit (fun _ => getBit_succ_flipBit_zero)

@[simp]
lemma flipBit_ne_self (q) : flipBit i q ≠ q := by
  apply ne_of_getBit_ne i
  rw [getBit_flipBit, ne_eq, Bool.not_not_eq]

lemma getRes_zero_eq_and_getBit_zero_opp_of_lt_of_flipBit_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) :
getBit 0 r = false ∧ getBit 0 q = true ∧ getRes 0 r = getRes 0 q := by
rcases mergeBitRes_surj 0 q with ⟨bq, pq, rfl⟩; rcases mergeBitRes_surj 0 r with ⟨br, pr, rfl⟩
simp_rw [flipBit_mergeBitRes, getBit_mergeBitRes, getRes_mergeBitRes,
  Fin.lt_iff_val_lt_val, mergeBitRes_zero, finProdFinEquiv_apply_val, Bool.cond_not, add_comm,
  Bool.apply_cond (Fin.val), Fin.val_one, Fin.val_zero] at hf h ⊢
rcases Nat.eq_false_true_of_cond_succ_lt_of_cond_succ_lt h hf with ⟨hr, hq, he⟩
exact ⟨hr, hq, Fin.ext (Nat.eq_of_mul_eq_mul_left zero_lt_two he)⟩

lemma eq_flipBit_zero_of_lt_of_flipBit_zero_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) : r = flipBit 0 q := by
rcases getRes_zero_eq_and_getBit_zero_opp_of_lt_of_flipBit_gt h hf with ⟨hr, hq, hrq⟩
simp only [eq_flipBit_iff, hr, hq, hrq, Bool.not_true, and_self]

lemma eq_flipBit_zero_of_lt_of_flipBit_zero_gt' (h : r < q) (hf : flipBit i q < flipBit i r) :
    ∀ k ≥ i, getBit k r = getBit k (flipBit i q) := sorry

end FlipBit

section CondFlipBit

def condFlipBitCore (i : Fin (m + 1)) (c : BV m → Bool) : Function.End (BV (m + 1)) :=
  fun q => bif c (getRes i q) then flipBit i q else q

lemma condFlipBitCore_condFlipBitCore : condFlipBitCore i c (condFlipBitCore i c q) = q := by
rcases (c (getRes i q)).dichotomy with h | h <;>
simp only [condFlipBitCore, h, cond_true, cond_false, getRes_flipBit, flipBit_flipBit]

def condFlipBit (i : Fin (m + 1)) (c : BV m → Bool) : Equiv.Perm (BV (m + 1)) where
  toFun := condFlipBitCore i c
  invFun := condFlipBitCore i c
  left_inv _ := condFlipBitCore_condFlipBitCore
  right_inv _ := condFlipBitCore_condFlipBitCore

lemma condFlipBit_apply :
condFlipBit i c q = bif c (getRes i q) then flipBit i q else q := rfl

lemma condFlipBit_def :
condFlipBit i c = fun q => bif c (getRes i q) then flipBit i q else q := rfl

lemma condFlipBit_apply_eq_mergeBitRes : condFlipBit i c q =
mergeBitRes i (xor (c (getRes i q)) (getBit i q)) (getRes i q) := by
  rw [condFlipBit_apply] ; cases (c (getRes i q))
  · rw [cond_false, Bool.false_xor, mergeBitRes_getBit_getRes]
  · rw [cond_true, Bool.true_xor, flipBit_apply]

lemma condFlipBit_apply_eq_swap_apply : condFlipBit i c q =
      Equiv.swap q (mergeBitRes i (xor (c (getRes i q)) (getBit i q)) (getRes i q)) q := by
  exact condFlipBit_apply_eq_mergeBitRes.trans (Equiv.swap_apply_left _ _).symm

lemma condFlipBit_base : condFlipBit (m := 0) i c = bif c 0 then Equiv.swap 0 1 else 1 := by
  ext q : 1
  rw [condFlipBit_apply, Fin.eq_zero (getRes i q), flipBit_base]
  cases (c 0) <;> rfl

lemma condFlipBit_mergeBitRes : condFlipBit i c (mergeBitRes i b p) =
mergeBitRes i (xor (c p) b) p := by
rw [condFlipBit_apply_eq_mergeBitRes, getRes_mergeBitRes, getBit_mergeBitRes]

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
simp_rw [condFlipBit_apply_eq_mergeBitRes, getRes_mergeBitRes,
  getBit_mergeBitRes, Bool.xor_left_comm]

lemma condFlipBit_comm :
(condFlipBit i c) * (condFlipBit i d) = (condFlipBit i d) * (condFlipBit i c) := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, condFlipBit_apply_comm]

lemma condFlipBit_apply_comm_flipBit :
  condFlipBit i c (flipBit i q) = flipBit i (condFlipBit i c q) := by
  rw [condFlipBit_flipBit_of_all_true, condFlipBit_apply_comm]

lemma condFlipBit_comm_flipBit :
  (condFlipBit i c) * (flipBit i) = (flipBit i) * (condFlipBit i c) := by
  rw [condFlipBit_flipBit_of_all_true, condFlipBit_comm]

lemma condFlipBit_apply_flipBit :
condFlipBit i c (flipBit i q) = bif c (getRes i q) then q else flipBit i q := by
  rw [condFlipBit_apply_comm_flipBit]
  rcases (c (getRes i q)).dichotomy with h | h <;> rw [condFlipBit_apply, h]
  · simp_rw [cond_false]
  · simp_rw [cond_true, flipBit_flipBit]

@[simp]
lemma getRes_condFlipBit : getRes i (condFlipBit i c q) = getRes i q := by
rcases (c (getRes i q)).dichotomy with h | h  <;> rw [condFlipBit_apply, h]
· rfl
· rw [cond_true, getRes_flipBit]

lemma getBit_condFlipBit : getBit i (condFlipBit i c q) =
bif c (getRes i q) then !(getBit i q) else getBit i q := by
rcases (c (getRes i q)).dichotomy with hc | hc <;>
simp only [condFlipBit_apply, cond_false, hc, cond_true, getBit_flipBit]

lemma getBit_condFlipBit' : getBit i (condFlipBit i c q) =
xor (c (getRes i q)) (getBit i q) := by
rcases (c (getRes i q)).dichotomy with hc | hc <;>
simp only [condFlipBit_apply, hc, cond_false, cond_true,
  Bool.false_xor, Bool.true_xor, getBit_flipBit]

lemma getBit_condFlipBit'' : getBit i (condFlipBit i c q) =
bif (getBit i q) then !(c (getRes i q)) else c (getRes i q) := by
rcases (getBit i q).dichotomy with hc | hc <;>
simp only [getBit_condFlipBit', hc, Bool.xor_false, Bool.xor_true, cond_true, cond_false]

lemma getBit_condFlipBit_of_ne {i j : Fin (m + 1)} (hij: i ≠ j):
  getBit i ((condFlipBit j c) q) = getBit i q := by
  rw [condFlipBit_apply]
  rcases (c (getRes j q)).dichotomy with (h | h) <;> simp_rw [h]
  · rw [cond_false]
  · rw [cond_true, getBit_flipBit_of_ne hij]

lemma condFlipBit_bitInvar_of_ne {i j : Fin (m + 1)} (h : i ≠ j) : bitInvar i ⇑(condFlipBit j c) :=
  bitInvar_of_getBit_def_eq_getBit (fun _ => getBit_condFlipBit_of_ne h)

lemma condFlipBit_succ_apply {i : Fin (m + 1)} : condFlipBit (Fin.succ i) c q =
    mergeBitRes 0 (getBit 0 q) ((condFlipBit i fun p =>
    c (mergeBitRes 0 (getBit 0 q) p)) (getRes 0 q)) := by
    simp_rw [condFlipBit_apply_eq_mergeBitRes, mergeBitRes_succ, getRes_succ, getBit_succ,
    getBit_mergeBitRes, getRes_mergeBitRes]

lemma condFlipBit_succAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
  condFlipBit (j.succAbove i) c q =
    mergeBitRes j (getBit j q) ((condFlipBit i fun p =>
    c (mergeBitRes (i.predAbove j) (getBit j q) p)) (getRes j q)) := by
    simp_rw [condFlipBit_apply, getRes_succAbove,
    Bool.apply_cond (fun x => mergeBitRes j (getBit j q) x), mergeBitRes_getBit_getRes,
    flipBit_succAbove]

lemma condFlipBit_zero_apply : condFlipBit 0 c q =
  bif c (q.divNat) then
  finProdFinEquiv (q.divNat, q.modNat.rev)
  else q := by
  rw [condFlipBit_apply, flipBit_zero_apply, getRes_zero]

lemma condFlipBit_zero_mergeBitRes :
condFlipBit 0 c (mergeBitRes 0 b p) = finProdFinEquiv (p, bif xor (c p) b then 1 else 0) := by
  simp_rw [condFlipBit_mergeBitRes, mergeBitRes_zero]

lemma condFlipBit_zero_mergeBitRes_true  :
condFlipBit 0 c (mergeBitRes 0 true p) = finProdFinEquiv (p, bif c p then 0 else 1) := by
  simp_rw [condFlipBit_zero_mergeBitRes, Bool.xor_true, Bool.cond_not]

lemma condFlipBit_zero_mergeBitRes_false :
condFlipBit 0 c (mergeBitRes 0 false p) = finProdFinEquiv (p, bif c p then 1 else 0) := by
  simp_rw [condFlipBit_zero_mergeBitRes, Bool.xor_false]

end CondFlipBit

section Equivs

lemma bitInvarMulEquiv_zero_apply_condFlipBits (c : BV (m + 1) → Bool) (i : Fin (m + 1)) :
    (bitInvarMulEquiv 0) (fun b => condFlipBit i (fun p => c (mergeBitRes 0 b p))) =
    condFlipBit (i.succ) c :=
  Equiv.ext (fun _ => condFlipBit_succ_apply ▸ rfl)

lemma bitInvarMulEquiv_zero_apply_condFlipBits_one (c : BV (m + 1) → Bool) :
    (bitInvarMulEquiv 0) (fun b => condFlipBit 0 (fun p => c (mergeBitRes 0 b p))) =
    condFlipBit 1 c :=
  bitInvarMulEquiv_zero_apply_condFlipBits _ 0

lemma bitInvarMulEquiv_apply_condFlipBits (c) (i : Fin (m + 1)) (j : Fin (m + 2)) :
    (bitInvarMulEquiv j) (fun b => condFlipBit i (fun p => c (mergeBitRes (i.predAbove j) b p))) =
    condFlipBit (j.succAbove i) c :=
  Equiv.ext (fun _ => condFlipBit_succAbove_apply ▸ rfl)

lemma bitInvarMulEquiv_last_apply_condFlipBits (c) (i : Fin (m + 1)) :
    (bitInvarMulEquiv (Fin.last _)) (fun b => condFlipBit i
    (fun p => c (mergeBitRes (Fin.last _) b p))) =
    condFlipBit (i.castSucc) c := by
  rw [← Fin.predAbove_right_last (i := i), bitInvarMulEquiv_apply_condFlipBits, Fin.succAbove_last]

end Equivs

end BitRes
