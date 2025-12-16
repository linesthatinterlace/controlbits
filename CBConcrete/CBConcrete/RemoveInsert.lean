import CBConcrete.Lib.Bool
import CBConcrete.Lib.Equiv
import CBConcrete.Lib.Finset
import CBConcrete.PermOf.MulAction

namespace Nat

section RemoveInsert

variable {p q i j k m n : ℕ} {b b' : Bool}

/-- `removeBit q i` returns the number that remains if the
  `(i+1)` least significant bit is erased from `q`.-/
def removeBit (q i : ℕ) := ((q >>> (i + 1)) <<< i) ||| (q &&& (2^i - 1))

/-- `insertBit b p i` returns the number that arises if the bit `b` is
inserted into `p` such that it is the `(i+1)` least significant bit in the result.-/

def insertBit (b : Bool) (p : ℕ) (i : ℕ) :=
  ((p >>> i) <<< (i + 1)) ||| (b.toNat <<< i) ||| (p &&& (2^i - 1))

theorem removeBit_def : q.removeBit i = (q >>> (i + 1)) <<< i ||| q &&& (2^i - 1) := rfl

theorem insertBit_def : p.insertBit b i =
    ((p >>> i) <<< (i + 1)) ||| (b.toNat <<< i) ||| (p &&& (2^i - 1)) := rfl

-- inductive definition
@[grind =]
theorem removeBit_zero : q.removeBit 0 = q / 2 := eq_of_testBit_eq <| by grind [removeBit]
@[grind =]
theorem insertBit_zero : q.insertBit b 0 = q.bit b := eq_of_testBit_eq <| by grind [insertBit]

@[grind =]
theorem removeBit_succ {q i : ℕ} : q.removeBit (i + 1) = ((q / 2).removeBit i).bit (q.testBit 0) :=
    eq_of_testBit_eq <| by grind [removeBit]

@[grind =]
theorem insertBit_succ {q i : ℕ} :
    q.insertBit b (i + 1) = ((q / 2).insertBit b i).bit (q.testBit 0) := eq_of_testBit_eq <| by
  rintro (_ | j) <;> grind [insertBit]

-- basic combination eq theorems

@[simp, grind =]
theorem testBit_insertBit_of_eq {p i : ℕ} : (p.insertBit b i).testBit i = b := by
  induction i generalizing p b <;> grind

@[simp, grind =]
theorem removeBit_insertBit_of_eq {p i : ℕ} : (p.insertBit b i).removeBit i = p := by
  induction i generalizing p b <;> grind

@[simp, grind =]
theorem insertBit_testBit_removeBit_of_eq {q i : ℕ} :
    (q.removeBit i).insertBit (q.testBit i) i = q := by
  induction i generalizing q <;> grind

-- testBit_removeBit

@[grind =]
theorem testBit_removeBit {i j q : ℕ} :
    (q.removeBit j).testBit i = q.testBit (i + (decide (j ≤ i)).toNat) := by
  induction j generalizing q i <;> grind [cases Nat]

theorem testBit_removeBit_of_lt {i j q : ℕ} (hij : i < j) :
    (q.removeBit j).testBit i = q.testBit i := by grind

theorem testBit_removeBit_of_ge {i j q : ℕ} (hij : j ≤ i) :
    (q.removeBit j).testBit i = q.testBit (i + 1) := by grind

theorem testBit_pred_removeBit_of_gt {i j q : ℕ} (hij : j < i) :
    (q.removeBit j).testBit (i - 1) = q.testBit i := by grind

theorem testBit_removeBit_succ_of_le {i j q : ℕ} (hij : i ≤ j) :
    (q.removeBit (j + 1)).testBit i = q.testBit i := by grind

-- testBit_insertBit

theorem testBit_insertBit_of_lt {i j p : ℕ} (hij : i < j) :
    (p.insertBit b j).testBit i = p.testBit i := by
  induction j generalizing i b p <;> grind

theorem testBit_insertBit_of_gt {i j p : ℕ} (hij : j < i) :
    (p.insertBit b j).testBit i = p.testBit (i - 1) := by
  induction j generalizing i b p <;> grind

@[grind =]
theorem testBit_insertBit {i j p : ℕ} : (p.insertBit b j).testBit i =
    if (i = j) then b else p.testBit (i - (decide (j < i)).toNat) := by
  split <;> grind [testBit_insertBit_of_lt, testBit_insertBit_of_gt]

theorem testBit_insertBit_of_ne {i j p : ℕ} (hij : i ≠ j) : (p.insertBit b j).testBit i =
    p.testBit (i - (decide (j < i)).toNat) := by
  rcases hij.lt_or_gt with hij | hij
  · simp_rw [testBit_insertBit_of_lt hij, Bool.toNat_neg (hij.not_gt), tsub_zero] ;
  · simp only [testBit_insertBit_of_gt hij, Bool.toNat_pos hij]

theorem testBit_insertBit_succ_of_le {i j p : ℕ} (hij : i ≤ j) :
    (p.insertBit b (j + 1)).testBit i = p.testBit i := by
  rw [testBit_insertBit_of_lt (Nat.lt_succ_of_le hij)]

theorem testBit_succ_insertBit_of_ge {i j p : ℕ} (hij : j ≤ i) :
    (p.insertBit b j).testBit (i + 1) = p.testBit i := by
  rw [testBit_insertBit_of_gt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

-- Equivalence family

section InsertBitEquiv

open Equiv

@[pp_nodot, simps! symm_apply  apply]
def insertBitEquiv (i : ℕ) : Bool × ℕ ≃ ℕ where
  toFun bp := bp.2.insertBit bp.1 i
  invFun n := (n.testBit i, n.removeBit i)
  left_inv _ := by grind
  right_inv _ := by grind

theorem insertBitEquiv_zero : insertBitEquiv 0 = boolProdNatEquivNat := Equiv.ext <| fun _ => by
  simp_rw [Equiv.boolProdNatEquivNat_apply, Function.uncurry_def,
    insertBitEquiv_apply, insertBit_zero]

theorem insertBitEquiv_succ : insertBitEquiv (i + 1) =
  (prodCongrRight (fun _ => (insertBitEquiv 0).symm)).trans (
    (Equiv.prodAssoc _ _ _).symm.trans (
      (prodCongrLeft (fun _ => Equiv.prodComm _ _)).trans (
        (Equiv.prodAssoc _ _ _).trans ((prodCongrRight (fun _ => insertBitEquiv i)).trans
        (insertBitEquiv 0))))) := by
  simp_rw [Equiv.ext_iff, trans_apply, prodAssoc_symm_apply, prodCongrLeft_apply, prodComm_apply,
    Prod.swap_prod_mk, prodAssoc_apply, insertBitEquiv_apply, Prod.forall,
    prodCongrRight_apply, insertBitEquiv_symm_apply, insertBitEquiv_apply,
    insertBit_succ, insertBit_zero, removeBit_zero, implies_true]

end InsertBitEquiv

-- basic application theorems

theorem removeBit_apply : q.removeBit i = 2^i * (q / 2^(i + 1)) + q % 2^i := by
  induction i generalizing q with | zero | succ _ IH
  · grind
  · simp_rw [removeBit_succ, IH]
    grind [Nat.div_div_eq_div_mul, mod_mul]

theorem insertBit_apply : p.insertBit b i = p + 2^i * ((p / 2^i) + b.toNat) := by
  induction i generalizing p b with | zero | succ _ IH
  · grind
  · simp_rw [insertBit_succ, IH, bit_val, toNat_testBit_zero, pow_succ', mul_add, mul_assoc,
      Nat.div_div_eq_div_mul, add_right_comm, Nat.div_add_mod]

-- apply lemmas

theorem insertBit_apply_false {p : ℕ} : p.insertBit false i = p + (2^i) * (p / 2^i) := by
  simp_rw [insertBit_apply, Bool.toNat_false, add_zero]

theorem insertBit_apply_false_of_lt_two_pow {p : ℕ} (hp : p < 2^i) :
    p.insertBit false i = p := by
  simp_rw [insertBit_apply_false, Nat.div_eq_of_lt hp, mul_zero, add_zero]

theorem insertBit_apply_true {p : ℕ} : p.insertBit true i = p + (2^i) * (p / 2^i) + (2^i) := by
  simp_rw [insertBit_apply, Bool.toNat_true, mul_add, mul_one, add_assoc]

theorem insertBit_apply_false_add_pow_two {p : ℕ} :
    p.insertBit false i + 2^i = p.insertBit true i := by
  simp_rw [insertBit_apply_false, insertBit_apply_true]

theorem insertBit_apply_true_sub_pow_two {p : ℕ} :
    p.insertBit true i - 2^i = p.insertBit false i := by
  simp_rw [insertBit_apply_false, insertBit_apply_true, Nat.add_sub_cancel]

theorem insertBit_apply_not {p : ℕ} : p.insertBit (!b) i =
    (bif b then p.insertBit b i - 2^i else p.insertBit b i + 2^i) := by
  cases b
  · rw [Bool.not_false, cond_false, insertBit_apply_false_add_pow_two]
  · rw [Bool.not_true, cond_true, insertBit_apply_true_sub_pow_two]

-- removeBit equalities and inequalities

theorem removeBit_div_two_pow_eq (h : i ≤ k) : q.removeBit i / 2^k = q / 2^(k + 1) := by
  simp_rw [testBit_eq_iff, testBit_div_two_pow,
  testBit_removeBit_of_ge (h.trans (Nat.le_add_left _ _)), Nat.add_assoc, implies_true]

theorem removeBit_mod_two_pow_eq (h : k ≤ i) : q.removeBit i % 2^k = q % 2^k := by
  simp_rw [testBit_eq_iff, testBit_mod_two_pow]
  intro j
  rcases lt_or_ge j k with hjk | hjk
  · simp_rw [hjk, testBit_removeBit_of_lt (hjk.trans_le h)]
  · simp_rw [hjk.not_gt, decide_false, Bool.false_and]

theorem removeBit_modEq_two_pow (h : k ≤ i) : q.removeBit i ≡ q [MOD 2^k] :=
  removeBit_mod_two_pow_eq h

theorem removeBit_lt_iff_lt_two_mul (hin : 2^i ∣ n) : q.removeBit i < n ↔ q < 2 * n := by
  rcases hin with ⟨k, rfl⟩
  simp_rw [← mul_assoc, ← pow_succ', mul_comm _ k,
  ← Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), removeBit_div_two_pow_eq le_rfl]

theorem removeBit_lt_div_two_iff_lt (hin : 2^(i + 1) ∣ n) : q.removeBit i < n / 2 ↔ q < n := by
  rcases hin with ⟨k, rfl⟩
  rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ (zero_lt_two),
    ← removeBit_lt_iff_lt_two_mul (dvd_mul_right _ _)]

theorem removeBit_lt_two_pow_mul_iff_lt_two_pow_mul (h : i ≤ k) (n : ℕ) :
    q.removeBit i < 2^k * n ↔ q < 2^(k + 1) * n := by
  rw [removeBit_lt_iff_lt_two_mul (dvd_mul_of_dvd_left (pow_dvd_pow _ h) _), pow_succ', mul_assoc]

theorem removeBit_lt_two_pow_iff_lt_two_pow (h : i ≤ m) : q.removeBit i < 2^m ↔ q < 2^(m + 1) := by
  have H := removeBit_lt_two_pow_mul_iff_lt_two_pow_mul h 1 (q := q)
  simp_rw [mul_one] at H
  exact H

-- Remaining of_eq theorems

theorem insertBit_eq_iff : p.insertBit b i = q ↔ (b = testBit q i) ∧ (p = q.removeBit i) :=
  ⟨fun H => H ▸ ⟨testBit_insertBit_of_eq.symm, removeBit_insertBit_of_eq.symm⟩,
    fun h => by simp_rw [h, insertBit_testBit_removeBit_of_eq]⟩

@[grind =]
theorem insertBit_eq_insertBit_iff {r : ℕ} :
    q.insertBit b i = r.insertBit b' i ↔ b = b' ∧ q = r := by
  rw [insertBit_eq_iff, testBit_insertBit_of_eq, removeBit_insertBit_of_eq]

theorem insertBit_inj {p q : ℕ} : p.insertBit b i = q.insertBit b i ↔ p = q := by
  simp_rw [insertBit_eq_insertBit_iff, true_and]

theorem insertBit_inj_right {p : ℕ} : p.insertBit b i = p.insertBit b' i ↔ b = b' := by
  simp_rw [insertBit_eq_insertBit_iff, and_true]

theorem eq_insertBit_iff : p = q.insertBit b i ↔ (testBit p i = b) ∧ (p.removeBit i = q) := by
  simp_rw [eq_comm (a := p), insertBit_eq_iff, eq_comm]

theorem removeBit_eq_iff : p.removeBit i = q ↔ p = q.insertBit (p.testBit i) i := by
  simp_rw [eq_insertBit_iff, true_and]

theorem eq_removeBit_iff : p = q.removeBit i ↔ p.insertBit (q.testBit i) i = q := by
  simp_rw [insertBit_eq_iff, true_and]

theorem insertBit_injective : (insertBit b · i).Injective := fun _ _ => by
  simp_rw [insertBit_inj, imp_self]

theorem insertBit_right_injective : (insertBit · p i).Injective := fun _ _ => by
  simp_rw [insertBit_inj_right, imp_self]

-- inequalities

theorem insertBit_strictMono : StrictMono (insertBit b · i) := by
  refine Monotone.strictMono_of_injective
    (fun p q hpq => ?_) insertBit_injective
  simp_rw [insertBit_apply, mul_add, ← add_assoc]
  exact Nat.add_le_add_right (Nat.add_le_add hpq (Nat.mul_le_mul_left _
    (Nat.div_le_div_right hpq))) _

@[grind! .]
theorem insertBit_false_lt_insertBit_true {q : ℕ} :
    q.insertBit false i < q.insertBit true i :=
  insertBit_apply_false_add_pow_two ▸ Nat.lt_add_of_pos_right (Nat.two_pow_pos _)

theorem insertBit_strictMono_right : StrictMono (insertBit · p i) := by
  refine Monotone.strictMono_of_injective
    (fun b b' => b.rec (fun _ => b'.rec le_rfl insertBit_false_lt_insertBit_true.le)
    (fun hbb' => hbb' rfl ▸ le_rfl)) insertBit_right_injective

theorem insertBit_false_le_insertBit_true {q : ℕ} {b : Bool} :
    q.insertBit false i ≤ q.insertBit b i := by
  cases b <;> grind

theorem insertBit_lt_insertBit_iff_lt {r : ℕ} :
    q.insertBit b i < r.insertBit b i ↔ q < r :=
  insertBit_strictMono.lt_iff_lt

theorem insertBit_le_insertBit_iff_le {r : ℕ} :
    q.insertBit b i ≤ r.insertBit b i ↔ q ≤ r :=
  insertBit_strictMono.le_iff_le

@[grind =]
theorem lt_removeBit_iff {p : ℕ} : q < p.removeBit i ↔ q.insertBit (p.testBit i) i < p := by
  rw [← insertBit_lt_insertBit_iff_lt (r := p.removeBit i) (b := p.testBit i) (i := i),
    insertBit_testBit_removeBit_of_eq]

@[grind =]
theorem removeBit_lt_iff {p : ℕ} : p.removeBit i < q ↔ p < q.insertBit (p.testBit i) i := by
  nth_rewrite 2 [← insertBit_testBit_removeBit_of_eq (q := p) (i := i)]
  rw [insertBit_lt_insertBit_iff_lt]

theorem removeBit_lt_removeBit_iff_lt_of_testBit_eq_iff {p q : ℕ} (h : p.testBit i = q.testBit i) :
    p.removeBit i < q.removeBit i ↔ p < q := by
  rw [lt_removeBit_iff, ← h, insertBit_testBit_removeBit_of_eq]

theorem le_removeBit_iff {p : ℕ} : q ≤ p.removeBit i ↔ q.insertBit (p.testBit i) i ≤ p := by
  nth_rewrite 3 [← insertBit_testBit_removeBit_of_eq (q := p) (i := i)]
  rw [insertBit_le_insertBit_iff_le]

theorem removeBit_le_iff {p : ℕ} : p.removeBit i ≤ q ↔ p ≤ q.insertBit (p.testBit i) i := by
  nth_rewrite 2 [← insertBit_testBit_removeBit_of_eq (q := p) (i := i)]
  rw [insertBit_le_insertBit_iff_le]

theorem removeBit_le_removeBit_iff_lt_of_testBit_eq {p q : ℕ} (h : p.testBit i = q.testBit i) :
    q.removeBit i ≤ p.removeBit i ↔ q ≤ p := by
  rw [le_removeBit_iff, h, insertBit_testBit_removeBit_of_eq]

-- removeBit_insertBit

theorem removeBit_insertBit_of_gt {p : ℕ} (hij : j < i) :
    (p.insertBit b j).removeBit i = (p.removeBit (i - 1)).insertBit b j := by
  simp only [testBit_eq_iff, testBit_removeBit, testBit_insertBit, tsub_le_iff_right]
  intro k
  rcases lt_trichotomy j (k + (decide (i ≤ k)).toNat) with hjk | rfl | hjk
  · have H : j < k := (le_or_gt i k).by_cases (lt_of_le_of_lt' · hij)
      (fun h => hjk.trans_eq (by simp_rw [h.not_ge, decide_false, Bool.toNat_false, add_zero]))
    grind
  · grind
  · have hkj : k < j := le_self_add.trans_lt hjk
    have hik' : ¬ i ≤ k := lt_asymm hkj ∘ hij.trans_le
    simp only [hkj.not_gt, hik']
    grind

theorem removeBit_insertBit_of_lt {p : ℕ} (hij : i < j) :
    (p.insertBit b j).removeBit i = (p.removeBit i).insertBit b (j - 1) := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨j, rfl⟩
  simp only [testBit_eq_iff, testBit_removeBit, testBit_insertBit, add_tsub_cancel_right]
  intro k
  rcases le_or_gt i k with hik | hik
  · simp only [hik, decide_true, Bool.toNat_true]
    rcases lt_trichotomy (i + j) k <;> grind
  · grind

theorem removeBit_insertBit_of_ne {p : ℕ} (hij : i ≠ j) : (p.insertBit b j).removeBit i =
    (p.removeBit (i - (decide (j < i)).toNat)).insertBit b (j - (decide (i < j)).toNat) := by
  rcases hij.lt_or_gt
  · grind [removeBit_insertBit_of_lt]
  · grind [removeBit_insertBit_of_gt]

@[grind =]
theorem removeBit_insertBit {i j p : ℕ} : (p.insertBit b j).removeBit i = bif i = j then p else
    (p.removeBit (i - (decide (j < i)).toNat)).insertBit b (j - (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [removeBit_insertBit_of_eq, decide_true, cond_true]
  · simp_rw [hij, removeBit_insertBit_of_ne hij, decide_false, cond_false]

theorem removeBit_succ_insertBit_of_ge {p : ℕ} (hij : j ≤ i) :
    (p.insertBit b j).removeBit (i + 1) = (p.removeBit i).insertBit b j := by
  rw [removeBit_insertBit_of_gt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

theorem removeBit_insertBit_succ_of_le {p : ℕ} (hij : i ≤ j) :
    (p.insertBit b (j + 1)).removeBit i = (p.removeBit i).insertBit b j := by
  rw [removeBit_insertBit_of_lt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

-- insertBit_removeBit

theorem insertBit_removeBit_of_le {q : ℕ} (hij : i ≤ j) : (q.removeBit j).insertBit b i =
    (q.insertBit b i).removeBit (j + 1) := (removeBit_succ_insertBit_of_ge hij).symm

theorem insertBit_removeBit_of_ge {q : ℕ} (hij : j ≤ i) :
    (q.removeBit j).insertBit b i = (q.insertBit b (i + 1)).removeBit j :=
  (removeBit_insertBit_succ_of_le hij).symm

theorem insertBit_removeBit_of_ne {q : ℕ} (hij : i ≠ j) :
    (q.removeBit j).insertBit b i =
    (q.insertBit b (i + (decide (j < i)).toNat)).removeBit (j + (decide (i < j)).toNat) := by
  rcases hij.lt_or_gt with hij | hij
  · simp only [insertBit_removeBit_of_le hij.le, hij, not_lt_of_gt, decide_false, Bool.toNat_false,
    add_zero, decide_true, Bool.toNat_true]
  · simp only [insertBit_removeBit_of_ge hij.le, hij, decide_true, Bool.toNat_true, not_lt_of_gt,
    decide_false, Bool.toNat_false, add_zero]

theorem insertBit_not_testBit_removeBit_of_eq {q : ℕ} :
    (q.removeBit i).insertBit (!q.testBit i) i =
  (bif q.testBit i then q - 2^i else q + 2^i) := by
  rw [insertBit_apply_not, insertBit_testBit_removeBit_of_eq]

theorem insertBit_removeBit_of_eq {i q : ℕ} : (q.removeBit i).insertBit b i =
    bif (q.testBit i).xor !b then q else bif q.testBit i then q - 2^i else q + 2^i := by
  rcases Bool.eq_or_eq_not b (q.testBit i) with rfl | rfl
  · simp_rw [insertBit_testBit_removeBit_of_eq, Bool.bne_not_self, cond_true]
  · simp_rw [Bool.not_not, bne_self_eq_false, insertBit_not_testBit_removeBit_of_eq, cond_false]

@[grind =]
theorem insertBit_removeBit {i j : ℕ} : (q.removeBit j).insertBit b i =
    bif i = j then bif (q.testBit i).xor !b then q else (bif q.testBit i then q - 2^i else q + 2^i)
    else (q.insertBit b (i + (decide (j < i)).toNat)).removeBit (j + (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp only [decide_true, lt_self_iff_false, decide_false, Bool.toNat_false, add_zero,
    removeBit_insertBit_of_eq, cond_true, insertBit_removeBit_of_eq]
  · simp_rw [hij, insertBit_removeBit_of_ne hij, decide_false, cond_false]

theorem insertBit_removeBit_pred_of_lt {q : ℕ} (hij : i < j) :
    (q.removeBit (j - 1)).insertBit b i =
    (q.insertBit b i).removeBit j := (removeBit_insertBit_of_gt hij).symm

theorem insertBit_pred_removeBit_of_gt {q : ℕ} (hij : j < i) :
    (q.removeBit j).insertBit b (i - 1) =
    (q.insertBit b i).removeBit j := (removeBit_insertBit_of_lt hij).symm

-- removeBit_removeBit

theorem removeBit_removeBit_of_lt {i j q : ℕ} (hij : i < j) : (q.removeBit j).removeBit i =
  (q.removeBit i).removeBit (j - 1) := by
  simp_rw [testBit_eq_iff, testBit_removeBit, tsub_le_iff_right]
  intro k
  rcases lt_or_ge k i with (hik | hik)
  · have hkj : k + 1 < j := (Nat.succ_le_of_lt hik).trans_lt hij
    have hkj' : k < j := lt_of_succ_lt hkj
    simp only [hik.not_ge, hkj'.not_ge, hkj.not_ge, decide_false, Bool.toNat_false, add_zero]
  · have h : i ≤ k + (decide (j ≤ k + 1)).toNat := le_add_of_le_left hik
    simp_rw [hik, h, decide_true, Bool.toNat_true, add_assoc, add_comm]

theorem removeBit_removeBit_of_ge {i j q : ℕ} (hij : j ≤ i) :
    (q.removeBit j).removeBit i = (q.removeBit (i + 1)).removeBit j := by
  simp_rw [testBit_eq_iff, testBit_removeBit]
  intro k
  rcases le_or_gt i k with (hik | hik)
  · have hjk : j ≤ k := hij.trans hik
    have hjk' : j ≤ k + 1 := hjk.trans (le_succ _)
    simp only [hik,  hjk', hjk, decide_true, Bool.toNat_true, add_le_add_iff_right]
  · have h : k + (decide (j ≤ k)).toNat < i + 1 := add_lt_add_of_lt_of_le hik (Bool.toNat_le _)
    simp only [hik.not_ge, h.not_ge, decide_false, Bool.toNat_false, add_zero]

@[grind =]
theorem removeBit_removeBit {i j q : ℕ} : (q.removeBit j).removeBit i =
    (q.removeBit (i + (decide (j ≤ i)).toNat)).removeBit (j - (!decide (j ≤ i)).toNat) := by
  rcases lt_or_ge i j with hij | hij
  · simp_rw [removeBit_removeBit_of_lt hij, hij.not_ge, decide_false, Bool.toNat_false,
    add_zero, Bool.not_false, Bool.toNat_true]
  · simp_rw [removeBit_removeBit_of_ge hij, hij, decide_true, Bool.toNat_true,
    Bool.not_true, Bool.toNat_false, tsub_zero]

theorem removeBit_removeBit_succ_of_le {i j q : ℕ} (hij : i ≤ j) : (q.removeBit (j + 1)).removeBit i =
    (q.removeBit i).removeBit j := by
  rw [removeBit_removeBit_of_lt (Nat.lt_succ_of_le hij), succ_eq_add_one, add_tsub_cancel_right]

theorem removeBit_pred_removeBit_of_gt {i j q : ℕ} (hij : j < i) : (q.removeBit j).removeBit (i - 1) =
    (q.removeBit i).removeBit j := by
  rw [removeBit_removeBit_of_ge (Nat.le_sub_one_of_lt hij), Nat.sub_add_cancel (one_le_of_lt hij)]


-- insertBit_insertBit

theorem insertBit_insertBit_of_le {i j p : ℕ} {b b' : Bool} (hij : i ≤ j) :
    (p.insertBit b' j).insertBit b i = (p.insertBit b i).insertBit b' (j + 1) := by
  simp_rw [insertBit_eq_iff (i := i), removeBit_insertBit_succ_of_le hij,
  testBit_insertBit_succ_of_le hij, testBit_insertBit_of_eq, removeBit_insertBit_of_eq, true_and]

theorem insertBit_insertBit_of_gt {i j p : ℕ} {b b' : Bool} (hij : j < i) :
    (p.insertBit b' j).insertBit b i = (p.insertBit b (i - 1)).insertBit b' j := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
  rw [Nat.add_sub_cancel, ← insertBit_insertBit_of_le (Nat.le_of_lt_succ hij)]

theorem insertBit_insertBit_of_eq {i p : ℕ} {b b' : Bool} :
    (p.insertBit b' i).insertBit b i = (p.insertBit b i).insertBit b' (i + 1) :=
  insertBit_insertBit_of_le le_rfl

theorem insertBit_insertBit_of_ne {i j p : ℕ} {b b' : Bool} (hij : i ≠ j) :
    (p.insertBit b' j).insertBit b i =
    (p.insertBit b (i - (decide (j < i)).toNat)).insertBit b' (j + (decide (i < j)).toNat) := by
  rcases hij.lt_or_gt with hij | hij
  · simp_rw [insertBit_insertBit_of_le hij.le, hij, hij.not_gt, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero]
  · simp_rw [insertBit_insertBit_of_gt hij, hij, hij.not_gt, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, add_zero]

@[grind =]
theorem insertBit_insertBit {i j p : ℕ} {b b' : Bool} : (p.insertBit b' j).insertBit b i  =
    (p.insertBit b (i - (decide (j < i)).toNat)).insertBit b' (j + (decide (i ≤ j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [insertBit_insertBit_of_eq, lt_irrefl, le_rfl, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero]
  · simp_rw [insertBit_insertBit_of_ne hij, hij.le_iff_lt]

theorem insertBit_succ_insertBit_of_ge {i j p : ℕ} {b b' : Bool} (h : j ≤ i) :
    (p.insertBit b j).insertBit b' (i + 1) = (p.insertBit b' i).insertBit b j :=
  (insertBit_insertBit_of_le h).symm

theorem insertBit_insertBit_pred_of_lt {i j p : ℕ} {b b' : Bool} (h : i < j) :
    (p.insertBit b (j - 1) ).insertBit b' i = (p.insertBit b' i).insertBit b j :=
  (insertBit_insertBit_of_gt h).symm

-- insertBit equalities and inequalities

theorem insertBit_div_two_pow_eq (h : i ≤ k) : q.insertBit b i / 2^(k + 1) = q / 2^k := by
  simp_rw [testBit_eq_iff, testBit_div_two_pow, ← Nat.add_assoc,
  testBit_succ_insertBit_of_ge ((h.trans (Nat.le_add_left _ _))), implies_true]

theorem insertBit_mod_two_pow_eq (h : k ≤ i) : q.insertBit b i % 2^k = q % 2^k := by
  simp_rw [testBit_eq_iff, testBit_mod_two_pow]
  intro j
  rcases lt_or_ge j k with hjk | hjk
  · simp_rw [hjk, testBit_insertBit_of_lt (hjk.trans_le h)]
  · simp_rw [hjk.not_gt, decide_false, Bool.false_and]

theorem insertBit_modEq_two_pow (h : k ≤ i) : q.insertBit b i ≡ q [MOD 2^k] :=
  insertBit_mod_two_pow_eq h

theorem insertBit_lt_iff_lt_div_two (hin : 2^(i + 1) ∣ n) :
    q.insertBit b i < n ↔ q < n / 2 := by
  rw [← removeBit_lt_div_two_iff_lt hin, removeBit_insertBit_of_eq]

theorem insertBit_lt_two_mul_iff_lt (hin : 2^i ∣ n) :
    q.insertBit b i < 2 * n ↔ q < n := by
  rw [← removeBit_lt_iff_lt_two_mul hin, removeBit_insertBit_of_eq]

theorem insertBit_lt_two_pow_mul_iff_lt_two_pow_mul (h : i ≤ k) (n : ℕ) :
    q.insertBit b i < 2^(k + 1) * n ↔ q < 2^k * n := by
  simp_rw [← removeBit_lt_two_pow_mul_iff_lt_two_pow_mul h, removeBit_insertBit_of_eq]

theorem insertBit_lt_two_pow_iff_lt_two_pow (h : i ≤ k) :
    q.insertBit b i < 2^(k + 1) ↔ q < 2^k := by
  simp_rw [← removeBit_lt_two_pow_iff_lt_two_pow h, removeBit_insertBit_of_eq]

theorem insertBit_removeBit_lt_iff_lt (hin : 2^(i + 1) ∣ n) :
    (q.removeBit i).insertBit b i < n ↔ q < n := by
  rw [insertBit_lt_iff_lt_div_two hin, removeBit_lt_div_two_iff_lt hin]

theorem zero_removeBit : (0 : ℕ).removeBit i = 0 := by
  induction i <;> grind

theorem zero_insertBit : (0 : ℕ).insertBit b i = b.toNat * 2^i := by
  induction i <;> grind

theorem zero_insertBit_true : (0 : ℕ).insertBit true i = 2^i := by
  simp_rw [zero_insertBit, Bool.toNat_true, one_mul]

theorem zero_insertBit_false : (0 : ℕ).insertBit false i = 0 := by
  simp_rw [zero_insertBit, Bool.toNat_false, zero_mul]

theorem two_pow_removeBit_of_eq : (2 ^ i).removeBit i = 0 :=
  zero_insertBit_true ▸ removeBit_insertBit_of_eq

theorem two_pow_removeBit_of_lt (hij : i < j) : (2 ^ i).removeBit j = 2 ^ i := by
  rw [← zero_insertBit_true, removeBit_insertBit_of_gt hij, zero_removeBit]

theorem two_pow_removeBit_of_gt (hij : j < i) : (2 ^ i).removeBit j = 2 ^ (i - 1) := by
  simp_rw [← zero_insertBit_true, removeBit_insertBit_of_lt hij, zero_removeBit]

theorem removeBit_eq_mod_of_lt (hq : q < 2^(i + 1)) : q.removeBit i = q % 2^i := by
  cases q using Nat.bitCasesOn with | bit b q => _
  simp_rw [Nat.bit_lt_two_pow_succ_iff] at hq
  simp_rw [testBit_eq_iff]
  grind

theorem removeBit_eq_of_lt (hq : q < 2^i) : q.removeBit i = q := by
  rw [removeBit_eq_mod_of_lt (hq.trans (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _))),
    mod_eq_of_lt hq]

theorem two_pow_insertBit_false (hq : q < 2^j) : q.insertBit false j = q := by
  simp_rw [insertBit_eq_iff, removeBit_eq_of_lt hq, Nat.testBit_lt_two_pow hq, true_and]

end RemoveInsert

end Nat

namespace Fin

end Fin

namespace BitVec
open Nat

variable {w} {b : Bool} {q : BitVec (w + 1)} {p : BitVec w} {i : Fin (w + 1)}

@[simps!]
def insertLsb (b : Bool) (p : BitVec w) (i : Fin (w + 1)) : BitVec (w + 1) :=
  BitVec.ofNatLT (p.toNat.insertBit b i) <|
  (Nat.insertBit_lt_two_pow_iff_lt_two_pow i.is_le).mpr p.isLt

@[grind =]
theorem toNat_insertLsb : (p.insertLsb b i).toNat = p.toNat.insertBit b i := rfl

@[simp]
theorem getElem_insertLsb_of_val_self : (p.insertLsb b i)[i.val] = b := Nat.testBit_insertBit_of_eq

@[simp]
theorem getElem_insertLsb_of_gt_val {j : ℕ} (hj : j < w + 1) :
    ∀ (hij : i < j), (p.insertLsb b i)[j] = p[j - 1] := Nat.testBit_insertBit_of_gt
@[simp]
theorem getElem_insertLsb_of_lt_val {j : ℕ} (hj : j < w + 1) :
    ∀ (hij : j < i), (p.insertLsb b i)[j] = p[j] := Nat.testBit_insertBit_of_lt

@[grind =]
theorem getElem_insertLsb {j : ℕ} (hj : j < w + 1) :
    (p.insertLsb b i)[j] = if hij : i < j then p[j - 1] else if hij : j < i then p[j] else b := by
  grind [getElem_insertLsb_of_val_self, getElem_insertLsb_of_gt_val, getElem_insertLsb_of_lt_val]

@[grind =]
theorem getElem?_insertLsb {j : ℕ} :
    (p.insertLsb b i)[j]? = if hij : i < j then p[j - 1]? else if hij : j < i then p[j] else b := by
  grind

@[simps!]
def removeLsb (q : BitVec (w + 1)) (i : Fin (w + 1)) : BitVec w :=
  BitVec.ofNatLT (q.toNat.removeBit i) <|
  (Nat.removeBit_lt_two_pow_iff_lt_two_pow i.is_le).mpr q.isLt

variable {b : Bool} {q : BitVec (w + 1)} {p : BitVec w} {i : Fin (w + 1)}

@[grind =]
theorem toNat_removeLsb : (q.removeLsb i).toNat = q.toNat.removeBit i := rfl

@[simp]
theorem getElem_removeLsb_of_ge {j : ℕ} (hj : j < w) :
    i ≤ j → (q.removeLsb i)[j] = q[j + 1] := Nat.testBit_removeBit_of_ge

@[simp]
theorem getElem_removeLsb_of_lt {j : ℕ} (hj : j < w) :
    j < i → (q.removeLsb i)[j] = q[j] := Nat.testBit_removeBit_of_lt

@[grind =]
theorem getElem_removeLsb {j : ℕ} (hj : j < w) :
    (q.removeLsb i)[j] = if i ≤ j then q[j + 1] else q[j] := by
  grind [getElem_removeLsb_of_ge, getElem_removeLsb_of_lt]

@[grind =]
theorem getElem?_removeLsb {j : ℕ} :
    (q.removeLsb i)[j]? = if hij : i ≤ j then q[j + 1]? else q[j] := by grind

@[simp, grind =]
theorem insertLsb_getElem_val_removeLsb_of_eq : (q.removeLsb i).insertLsb q[i.val] i = q :=
  eq_of_toNat_eq Nat.insertBit_testBit_removeBit_of_eq

@[simp, grind =]
theorem removeLsb_insertLsb_of_eq : (p.insertLsb b i).removeLsb i = p :=
  eq_of_toNat_eq Nat.removeBit_insertBit_of_eq

@[simps! apply symm_apply]
def insertLsbEquiv (i : Fin (w + 1)) : Bool × BitVec w ≃ BitVec (w + 1) where
  toFun bp := bp.2.insertLsb bp.1 i
  invFun n := (n[i.val], n.removeLsb i)
  left_inv _ := by grind
  right_inv _ := by grind

theorem insertLsbEquiv_apply_toNat {bp} : ((insertLsbEquiv i) bp).toNat =
    i.val.insertBitEquiv (bp.1, bp.2.toNat) := rfl

theorem insertLsbEquiv_symm_apply_snd_toNat : ((insertLsbEquiv i).symm q).2.toNat =
    (i.val.insertBitEquiv.symm q.toNat).2 := rfl

end BitVec
