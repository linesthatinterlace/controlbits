import Mathlib.Tactic.SimpRw
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import CBConcrete.Lib.Bool

namespace Nat

universe u

example {p : Nat → Prop} : p 0 ∧ (∀ n, p (n + 1)) ↔ ∀ n, p n := by grind [cases Nat]

example {p : Nat → Prop} : p 0 ∨ (Exists fun n => p (n + 1)) ↔ Exists p := by grind [cases Nat]

theorem forall_add_right {p : Nat → Prop} {n : Nat} :
    (∀ (i : ℕ), p (i + n)) ↔ ∀ i ≥ n, p i := by grind [Nat.add_sub_of_le]

theorem forall_add_left {p : Nat → Prop} {n : Nat} :
    (∀ (i : ℕ), p (n + i)) ↔ ∀ i ≥ n, p i := by grind [Nat.add_sub_of_le]

theorem forall_sub {p : Nat → Prop} {n : Nat} :
    (∀ (i : ℕ), p (n - i)) ↔ ∀ i ≤ n, p i := by grind [Nat.sub_sub_self]

theorem exists_add_right {p : Nat → Prop} {n : Nat} :
    (∃ (i : ℕ), p (i + n)) ↔ ∃ i ≥ n, p i := by
  convert (forall_add_right (p := (¬ p ·)) (n := n)).not <;> grind

theorem exists_add_left {p : Nat → Prop} {n : Nat} :
    (∃ (i : ℕ), p (n + i)) ↔ ∃ i ≥ n, p i := by
  convert (forall_add_left (p := (¬ p ·)) (n := n)).not <;> grind

theorem exists_sub {p : Nat → Prop} {n : Nat} :
    (∃ (i : ℕ), p (n - i)) ↔ ∃ i ≤ n, p i := by
  convert (forall_sub (p := (¬ p ·)) (n := n)).not <;> grind

theorem mod_div_injective {a b n : Nat} (meq : a % n = b % n)
    (deq : a / n = b / n) :
    a = b := by grind [Nat.div_add_mod]

theorem mod_div_inj (a b n : Nat) : a = b ↔ a % n = b % n ∧ a / n = b / n := by grind [Nat.div_add_mod]

section Fold

theorem fold_succ_zero {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    fold (n + 1) f init = (fold n (fun i h => f (i + 1) (by omega)) (f 0 (by omega) init)) := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [fold_succ, fold_zero]
  · rw [fold_succ, IH, fold_succ]

theorem foldRev_succ_zero {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    foldRev (n + 1) f init = f 0 (by omega)
    (foldRev n (fun i hi => f (i + 1) (by omega)) init) := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_succ, foldRev_zero]
  · rw [foldRev_succ, IH, foldRev_succ]

theorem foldRev_eq_fold_of_apply_eq_apply_pred_sub' {α : Type u} (n : Nat)
    (f g : (i : Nat) → i < n → α → α)
    (hfg : ∀ i (hi : i < n) , f i hi = g ((n - i) - 1) (by omega)) (init : α) :
    foldRev n f init = fold n g init := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_zero, fold_zero]
  · simp_rw [foldRev_succ_zero, fold_succ, hfg 0, Nat.sub_zero, Nat.add_one_sub_one]
    exact congrArg _ (IH _ _ (fun i hi => (hfg (i + 1) (Nat.succ_lt_succ hi)).trans
      (funext (fun _ => by simp_rw [Nat.add_sub_add_right]))) _)

theorem foldRev_eq_fold_of_apply_eq_apply_pred_sub {α : Type u} (n : Nat)
    (f g : (i : Nat) → i < n → α → α)
    (hfg : ∀ i j (hi : i < n) (hj : j < n), i + j = n - 1 → f i hi = g j hj) (init : α) :
    foldRev n f init = fold n g init := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_zero, fold_zero]
  · rw [foldRev_succ_zero, fold_succ, hfg 0 n (by omega) (by omega) (by omega)]
    congr
    refine IH _ _ (fun x y hx hy hxy => hfg _ _ _ _ ?_) _
    omega

theorem foldRev_eq_fold {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n → α → α) (init : α) :
    foldRev n f init = fold n (fun i (hi : i < n) => f ((n - 1) - i) (by omega)) init := by
  refine foldRev_eq_fold_of_apply_eq_apply_pred_sub _ _ _ (fun i j hi hj hij => ?_) _
  conv =>
    lhs
    congr
    rw [Nat.eq_sub_of_add_eq hij]

theorem fold_eq_foldRev {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n → α → α) (init : α) :
    fold n f init = foldRev n (fun i (hi : i < n) => f ((n - 1) - i) (by omega)) init := by
  refine (foldRev_eq_fold_of_apply_eq_apply_pred_sub _ _ _ (fun i j hi hj hij => ?_) _).symm
  conv =>
    rhs
    congr
    rw [Nat.eq_sub_of_add_eq' hij]

def foldRecOn {α : Type u} {motive : α → Sort*} : (n : Nat) → (f : (i : Nat) → i < n → α → α) →
  {a : α} → motive a → (∀ a, motive a → (i : Nat) → (hi : i < n) → motive (f i hi a)) →
    motive (n.fold f a)
  | 0, _, _, zro, _ => zro
  | _ + 1, _, _, zro, scc => scc _ (foldRecOn _ _ zro (fun _ H _ _ => scc _ H _ _)) _ _

section FoldRecOn

variable {α : Type u} {n : Nat} {motive : α → Sort*} {init : α} (zro : motive init)

@[simp]
theorem foldRecOn_zero (f : (i : Nat) → i < 0 → α → α)
    (scc : ∀ a, motive a → (i : Nat) → (hi : i < 0) → motive (f i hi a)) :
    foldRecOn 0 f zro scc = zro := rfl

@[simp]
theorem foldRecOn_succ (f : (i : Nat) → i < n + 1 → α → α)
    (scc : ∀ a, motive a → (i : Nat) → (hi : i < n + 1) → motive (f i hi a)) :
    foldRecOn (n + 1) f zro scc = scc _ (foldRecOn _ _ zro (fun _ H _ _ => scc _ H _ _)) _ _ := rfl

end FoldRecOn

end Fold

section Size

@[simp]
theorem size_succ {x : ℕ} : x.succ.size ≠ 0 := by
  simp_rw [ne_eq, Nat.size_eq_zero, Nat.succ_ne_zero, not_false_eq_true]

theorem size_le_self {n : ℕ} (hn : n ≠ 0) : 2^(n.size - 1) ≤ n := by
  rw [← Nat.lt_size]
  exact Nat.sub_one_lt (by simp_rw [Nat.size_eq_zero.not, hn, not_false_eq_true])

end Size

section Bit

attribute [grind =] bit_val bit_div_two

lemma bit_true_zero : bit true 0 = 1 := rfl

end Bit

section BOdd

@[simp]
theorem bodd_toNat {m : ℕ} : m.bodd.toNat = m % 2 := (mod_two_of_bodd _).symm

end BOdd

section TestBit

@[grind =]
theorem toNat_testBit_zero {x : ℕ} : (x.testBit 0).toNat = x % 2 := by grind

theorem mod_two_eq_mod_two_iff {x y : ℕ} :
    x % 2 = y % 2 ↔ x.testBit 0 = y.testBit 0 := by
  grind only [testBit_zero, Nat.mod_two_eq_zero_or_one]

theorem testBit_eq_iff {x y : ℕ} : x = y ↔ ∀ (i : ℕ), x.testBit i = y.testBit i := by
  by_cases hxy : x = 0 ∧ y = 0
  · grind
  · simp_rw [mod_div_inj x y 2, testBit_eq_iff (x := x / 2) (y := y / 2),
      mod_two_eq_mod_two_iff, testBit_div_two]
    exact Nat.and_forall_add_one (p := fun i => x.testBit i = y.testBit i)
  termination_by x + y

theorem testBit_ne_iff {x y : ℕ} : x ≠ y ↔ ∃ (i : ℕ), x.testBit i ≠ y.testBit i := by
  simp [testBit_eq_iff]

theorem eq_zero_iff_forall_testBit_false {x : ℕ} : x = 0 ↔ ∀ (i : ℕ), x.testBit i = false := by
  simp_rw [testBit_eq_iff, zero_testBit]

theorem ne_zero_iff_exists_testBit_true {x : ℕ} : x ≠ 0 ↔ ∃ (i : ℕ), x.testBit i := by
  simp_rw [testBit_ne_iff, zero_testBit, Bool.ne_false_iff]

@[grind =]
theorem lt_pow_two_iff {n : Nat} {x : Nat} :
    x < 2 ^ n ↔ ∀ (i : Nat), i ≥ n → x.testBit i = false := by
  simp_rw [← Nat.div_lt_one_iff (Nat.two_pow_pos n), Nat.lt_one_iff,
    eq_zero_iff_forall_testBit_false, testBit_div_two_pow, ← forall_add_right]

@[grind =]
theorem ge_pow_two_iff {n : Nat} {x : Nat} :
    2 ^ n ≤ x ↔ ∃ i ≥ n, x.testBit i := by
  simp_rw [← Nat.one_le_div_iff (Nat.two_pow_pos n), Nat.one_le_iff_ne_zero,
    ne_zero_iff_exists_testBit_true, testBit_div_two_pow, ← exists_add_right]

theorem testBit_eq_bool {x i : ℕ} {b} : x.testBit i = b ↔ x / 2^i % 2 = b.toNat := by grind

theorem testBit_eq_false {x i : ℕ} : x.testBit i = false ↔ x / 2^i % 2 = 0 := by grind

theorem testBit_eq_true {x i : ℕ} : x.testBit i = true ↔ x / 2^i % 2 = 1 := by grind

theorem testBit_eq_iff_div_pow_mod_eq {x y i j : ℕ} :
    x.testBit i = y.testBit j ↔ x / 2^i % 2 = y / 2^j % 2 := by grind

@[grind _=_]
theorem bodd_eq_testBit_zero (m : ℕ) : m.bodd = m.testBit 0 := Nat.bodd_eq_one_and_ne_zero _

@[grind =]
theorem testBit_div2 (m i : ℕ) : m.div2.testBit i = m.testBit (i + 1) := by grind

alias testBit_apply := testBit_eq_decide_div_mod_eq

attribute [grind =] testBit_bit_zero testBit_bit_succ

@[grind =]
theorem testBit_bit (m : ℕ) (b : Bool) (n : ℕ) :
    (Nat.bit b n).testBit m = if m = 0 then b else n.testBit (m - 1) := by cases m <;> grind

-- deprecate testBit_eq_false_of_lt

@[simp]
theorem testBit_size_self {x : ℕ} : x.testBit x.size = false :=
  Nat.testBit_lt_two_pow x.lt_size_self

theorem testBit_pred_size_self {x : ℕ} : x ≠ 0 → x.testBit (x.size - 1) = true := by
  induction x using Nat.binaryRec with | zero | bit b n IH
  · simp_rw [ne_eq, not_true_eq_false, false_implies]
  · intros H
    rw [Nat.size_bit H, succ_eq_add_one, Nat.add_sub_cancel, testBit_bit]
    rw [Nat.bit_ne_zero_iff] at H
    cases n
    · simp_rw [size_zero, if_true]
      exact H rfl
    · simp_rw [size_succ, if_false]
      exact IH (succ_ne_zero _)

alias testBit_ext := Nat.eq_of_testBit_eq

@[grind =]
theorem testBit_mod_two (x i : Nat) :
    (x % 2).testBit i = (decide (i = 0) && x.testBit 0) := by grind [mod_div_self, cases Nat]

attribute [grind =] testBit_mod_two_pow testBit_div_two_pow testBit_succ
  testBit_two_pow_mul_add

theorem testBit_ext_div_two_pow_iff {q q' m : ℕ} : q / 2^m = q' / 2^m ↔
  (∀ i ≥ m, q.testBit i = q'.testBit i) := by
  simp_rw [testBit_eq_iff, testBit_div_two_pow]
  grind [Nat.exists_eq_add_of_le]

theorem testBit_ext_mod_two_pow_iff {q q' m : ℕ} : q % 2^m = q' % 2^m ↔
  (∀ i < m, q.testBit i = q'.testBit i) := by
  simp_rw [testBit_eq_iff, testBit_mod_two_pow]
  grind

theorem testBit_one_succ {k : ℕ} : testBit 1 (k + 1) = false := by grind

@[grind =]
theorem testBit_one {k : ℕ} : testBit 1 k = decide (k = 0) := by grind [cases Nat]

@[grind =]
theorem testBit_two {k : ℕ} : testBit 2 k = decide (k = 1) := by grind [cases Nat]

@[grind =]
theorem testBit_toNat_zero {b : Bool} : b.toNat.testBit 0 = b := by grind

theorem testBit_toNat_succ {b : Bool} {k : ℕ} : b.toNat.testBit (k + 1) = false := by grind

theorem testBit_toNat {b : Bool} {k : ℕ} : b.toNat.testBit k = (decide (k = 0) && b) := by grind

theorem testBit_true_iff_two_pow_le_mod_two_pow_succ {i k : ℕ} :
    testBit k i = true ↔ 2^i ≤ k % 2^(i + 1) := by
  simp_rw [ge_pow_two_iff, testBit_mod_two_pow]
  grind

theorem testBit_false_iff_mod_two_pow_succ_lt_two_pow {i k : ℕ} :
    testBit k i = false ↔ k % 2^(i + 1) < 2^i := by
  simp_rw [lt_pow_two_iff, testBit_mod_two_pow]
  grind

@[grind =]
theorem testBit_two_mul (x : Nat) (j : Nat) :
    (2 * x).testBit j = (decide (j ≥ 1) && x.testBit (j - 1)):= by
  rw [← pow_one 2, testBit_two_pow_mul]

theorem testBit_two_pow_mul_add' (a : Nat) {b i : Nat} (j : Nat) :
    testBit (2 ^ i * a + b) j = if j < i then b.testBit j else  (a + b / 2^i).testBit (j - i) := by
  trans ((2 ^ i * (a + b / 2 ^ i) + b % 2 ^ i).testBit j) <;> grind [div_add_mod]

@[grind =]
theorem testBit_two_mul_add (x y i : Nat) :
    (2 * x + y).testBit i = if i = 0 then y.testBit 0 else (x + y / 2).testBit (i - 1) := by
  rw [← pow_one 2, testBit_two_pow_mul_add']
  grind

theorem testBit_add_two_pow_eq (x : Nat) (i : Nat) :
    (x + 2^i).testBit i = !x.testBit i := by grind [testBit_two_pow_add_eq]

theorem testBit_add_mul_two_pow (a : Nat) {b : Nat} {i : Nat} (j : Nat) :
    (b + 2 ^ i * a).testBit j = if j < i then b.testBit j else  (b / 2^i + a).testBit (j - i) := by
  simp_rw [b.add_comm, add_comm _ a, testBit_two_pow_mul_add']

theorem testBit_add_mul_two_pow_eq (a : Nat) (b : Nat) (i : Nat) :
    (b + 2 ^ i * a).testBit i = (decide (a % 2 = 1)).xor (b.testBit i) := by
  grind [testBit_mul_two_pow_add_eq]

theorem testBit_two_pow_add_ne_of_testBit_false {i : Nat} {j : Nat} (hij : i ≠ j) {x : Nat}
    (hx : x.testBit i = false) : (2 ^ i + x).testBit j = x.testBit j := by
  rcases hij.lt_or_gt with hij | hij
  · rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
    simp_rw [testBit_eq_iff_div_pow_mod_eq, add_assoc, pow_add _ i,  pow_succ',
      ← Nat.div_div_eq_div_mul, Nat.add_div_left _ (Nat.two_pow_pos _)]
    rw [← div_add_mod (x / 2^i) 2]
    simp_rw [testBit_eq_false.mp hx, add_assoc, Nat.mul_add_div Nat.zero_lt_two,
      Nat.zero_div, zero_add]
  · grind [testBit_two_pow_add_gt]

theorem testBit_add_two_pow_ne_of_testBit_false {i : Nat} {j : Nat} (hij : i ≠ j) {x : Nat}
    (hx : x.testBit i = false)  : (x + 2^i).testBit j = x.testBit j := by
  grind [testBit_two_pow_add_ne_of_testBit_false]

theorem testBit_sub_two_pow_ne_of_testBit_true {i : Nat} {j : Nat} (hij : i ≠ j) {x : Nat}
    (hx : x.testBit i = true) : (x - 2^i).testBit j = x.testBit j := by
  rcases Nat.exists_eq_add_of_le' (Nat.ge_two_pow_of_testBit hx) with ⟨x, rfl⟩
  rw [testBit_add_two_pow_eq, Bool.not_eq_true'] at hx
  exact Nat.add_sub_cancel _ _ ▸ (testBit_add_two_pow_ne_of_testBit_false hij hx).symm

theorem testBit_sub_two_pow_eq_of_testBit_true {i : Nat} {x : Nat}
    (hx : x.testBit i = true) : (x - 2^i).testBit i = !x.testBit i := by
  rcases Nat.exists_eq_add_of_le' (Nat.ge_two_pow_of_testBit hx) with ⟨x, rfl⟩
  rw [testBit_add_two_pow_eq, Bool.not_eq_true'] at hx
  rw [Nat.add_sub_cancel, testBit_add_two_pow_eq, Bool.not_not]

attribute [grind =] Nat.sub_add_eq_max Nat.sub_sub_eq_min

theorem exists_pow_two_mul_of_testBit {k : ℕ} (b : ℕ) (hb : ∀ i < k, b.testBit i = false) :
    ∃ n, b = 2^k * n := ⟨b / 2^k, eq_of_testBit_eq <| by grind⟩

/-
theorem nat_eq_testBit_sum_range {a m : ℕ} (ha : a < 2^m) :
    a = ∑ i ∈ Finset.range m, (a.testBit i).toNat * 2^i := by
  induction m generalizing a with | zero | succ m IH
  · grind [Finset.range_zero]
  · rw [Finset.sum_range_succ]
    rcases lt_or_ge a (2^m) with h | h
    · grind
    · rcases (Nat.exists_eq_add_of_le h) with ⟨a, rfl⟩
      rw [pow_succ', two_mul, add_lt_add_iff_left] at ha
      rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow ha,
      Bool.not_false, Bool.toNat_true, one_mul]
      nth_rewrite 1 [add_comm, add_left_inj, IH ha]
      apply Finset.sum_equiv (Equiv.refl _) (by simp_rw [Equiv.refl_apply, implies_true])
      simp_rw [Finset.mem_range, Equiv.refl_apply, mul_eq_mul_right_iff, pow_eq_zero_iff',
        two_ne_zero, false_and, or_false]
      exact fun _ hi => (Nat.testBit_two_pow_add_gt hi _) ▸ rfl
-/

end TestBit

section Lor

theorem or_one {a : ℕ} : a ||| 1 = bit true a.div2 := by
  simp_rw [testBit_eq_iff, testBit_or, testBit_one, testBit_bit]
  grind

theorem or_eq_add_two_pow_mul_of_lt_right {a b i : ℕ} (ha : a < 2^i) :
    2^i * b ||| a = 2^i * b + a := (two_pow_add_eq_or_of_lt ha _).symm

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
  rw [testBit_eq_iff]
  simp only [testBit_or, testBit_shiftLeft]
  intros j
  rcases lt_or_ge j i with hji | hji
  · simp_rw [hji.not_ge, decide_false, Bool.false_and, Bool.false_or]
  · simp_rw [hji, decide_true, Bool.true_and]

theorem or_shiftRight {a b i : ℕ} : (a ||| b) >>> i = (a >>> i) ||| (b >>> i) := by
  simp only [testBit_eq_iff, testBit_or, testBit_shiftRight, implies_true]

end Lor

section Land

theorem and_shiftLeft {a b i : ℕ} : (a &&& b) <<< i = (a <<< i) &&& (b <<< i) := by
  rw [testBit_eq_iff]
  simp only [testBit_and, testBit_shiftLeft]
  intros j
  rcases lt_or_ge j i with hji | hji
  · simp_rw [hji.not_ge, decide_false, Bool.false_and]
  · simp_rw [hji, decide_true, Bool.true_and]

theorem and_shiftRight {a b i : ℕ} : (a &&& b) >>> i = (a >>> i) &&& (b >>> i) := by
  simp only [testBit_eq_iff, testBit_and, testBit_shiftRight, implies_true]

end Land

section Lxor

theorem xor_shiftLeft {a b i : ℕ} : (a ^^^ b) <<< i = (a <<< i) ^^^ (b <<< i) := by
  rw [testBit_eq_iff]
  simp only [testBit_xor, testBit_shiftLeft]
  intros j
  rcases lt_or_ge j i with hji | hji
  · simp_rw [hji.not_ge, decide_false, Bool.false_and, Bool.false_xor]
  · simp_rw [hji, decide_true, Bool.true_and]

theorem xor_shiftRight {a b i : ℕ} : (a ^^^ b) >>> i = (a >>> i) ^^^ (b >>> i) := by
  simp only [testBit_eq_iff, testBit_xor, testBit_shiftRight, implies_true]

end Lxor

section ShiftLeft

attribute [grind =] shiftLeft_eq

theorem shiftLeft_one {m : ℕ} : m <<< 1 = 2 * m := rfl

end ShiftLeft

section ShiftLeft'

@[grind =]
theorem shiftLeft'_zero {b : Bool} {m : ℕ}  : shiftLeft' b m 0 = m := rfl

@[grind =]
theorem shiftLeft'_succ {b : Bool} {m i: ℕ} :
    (shiftLeft' b m i.succ) = bit b (shiftLeft' b m i) := rfl

theorem shiftLeft'_true {m : ℕ} (n : ℕ) :
    shiftLeft' true m n = (m <<< n) ^^^ (1 <<< n - 1) := eq_of_testBit_eq <| by
  induction n  <;> grind

theorem shiftLeft'_eq_shiftLeft_xor_shiftLeft_sub_one {m : ℕ} {b : Bool} (n : ℕ) :
    shiftLeft' b m n = (m <<< n) ^^^ (b.toNat <<< n - 1) := by
  cases b
  · rw [shiftLeft'_false, Bool.toNat_false, zero_shiftLeft, Nat.zero_sub, xor_zero]
  · rw [shiftLeft'_true, Bool.toNat_true]

theorem testBit_shiftLeft' {b : Bool} {m i j : ℕ}  :
    (shiftLeft' b m i).testBit j = bif j < i then b else m.testBit (j - i) := by
  induction i generalizing j with | zero | succ i IH
  · grind [shiftLeft']
  · simp_rw [shiftLeft'_succ, Nat.lt_succ_iff]
    cases b
    · simp_rw [bit_false]
      rw [← pow_one 2, testBit_two_pow_mul]
      grind
    · simp_rw [bit_true, Bool.cond_true_left]
      rw [← pow_one 2, testBit_two_pow_mul_add _ Nat.one_lt_two, IH]
      simp only [Bool.cond_true_left]
      cases j
      · simp_rw [Nat.zero_lt_one, if_true, zero_le, decide_true, Bool.true_or,
          testBit_zero, decide_true]
      · simp_rw [Nat.add_sub_cancel, Nat.add_sub_add_right, Nat.succ_le_iff, Nat.succ_lt_succ_iff,
        Nat.not_lt_zero, if_false]

theorem testBit_shiftLeft'_true {m i j : ℕ}  :
    (shiftLeft' true m i).testBit j = ((j < i) || m.testBit (j - i)) := by
  rw [testBit_shiftLeft']
  rcases lt_or_ge j i with hji | hji
  · simp_rw [hji, decide_true, cond_true, Bool.true_or]
  · simp_rw [hji.not_gt, decide_false, cond_false, Bool.false_or]

theorem testBit_shiftLeft'_false {m i j : ℕ}  :
    (shiftLeft' false m i).testBit j = (!(j < i) && m.testBit (j - i)) := by
  rw [testBit_shiftLeft']
  rcases lt_or_ge j i with hji | hji
  · simp_rw [hji, decide_true, cond_true, Bool.not_true, Bool.false_and]
  · simp_rw [hji.not_gt, decide_false, cond_false, Bool.not_false, Bool.true_and]




end ShiftLeft'



theorem testBit_shiftLeft_shiftRight {x n m j : ℕ} : (x <<< n >>> m).testBit j =
    if n ≤ m + j then x.testBit (m + j - n) else false := by grind

theorem testBit_shiftRight_shiftLeft {x n m j : ℕ} : (x >>> n <<< m).testBit j =
    if m ≤ j then x.testBit (n + (j - m)) else false := by grind

@[grind =]
theorem testBit_shiftRight_shiftLeft_add {n j k : ℕ} (x : ℕ) : (x >>> n <<< (n + k)).testBit j =
    (decide (n + k ≤ j) && x.testBit (j - k)) := by
  rw [testBit_shiftRight_shiftLeft]
  grind

end Nat
