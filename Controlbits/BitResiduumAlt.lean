import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Ring.Defs
import Controlbits.Fin
import Controlbits.Equivs
import Controlbits.Submonoid
import Controlbits.FunctionEnd
import Controlbits.VectorPerm

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
  simp_rw [p, decide_true, toNat_true]

@[simp]
theorem toNat_neg {P : Prop} [Decidable P] (p : ¬P) : toNat P = 0 := by
  simp_rw [p, _root_.decide_false, toNat_false]

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

section TestBit

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

theorem testBit_div_two_pow (x i j : ℕ) : testBit (x/2^i) j = testBit x (i + j) := by
  induction' i with i IH generalizing x j
  · rw [pow_zero, Nat.div_one, zero_add]
  · rw [pow_succ, ← Nat.div_div_eq_div_mul, testBit_div_two, IH,
      add_comm j, add_assoc]

theorem testBit_ext_iff {q q' : ℕ} : q = q' ↔ (∀ i : ℕ, q.testBit i = q'.testBit i) :=
  ⟨fun h _ => h ▸ rfl, Nat.eq_of_testBit_eq⟩

theorem testBit_ne_iff {q q' : ℕ} : q ≠ q' ↔ (∃ i : ℕ, q.testBit i ≠ q'.testBit i) := by
  simp_rw [ne_eq, testBit_ext_iff, not_forall]

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


theorem exists_pow_two_mul_of_testBit (b : ℕ) (hb : ∀ i < k, b.testBit i = false) :
    ∃ n, b = 2^k * n := by
  induction' k with k IH generalizing b
  · exact ⟨b, by rw [pow_zero, one_mul]⟩
  · rcases IH _ (fun i hi => hb i  (hi.trans (Nat.lt_succ_self _))) with ⟨b, rfl⟩
    have h := hb k (Nat.lt_succ_self _)
    simp_rw [testBit_mul_pow_two, le_refl, decide_true, Bool.true_and, Nat.sub_self,
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

section BitMatchTo

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

end BitMatchTo

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

section ShiftLeft'

theorem shiftLeft'_zero {b : Bool} {m : ℕ}  : shiftLeft' b m 0 = m := rfl
theorem shiftLeft'_succ {b : Bool} {m  i: ℕ} :
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

theorem shiftLeft'_eq_shiftLeft_xor_shiftLeft_sub_one {m : ℕ} (n : ℕ) :
    shiftLeft' b m n = (m <<< n) ^^^ (b.toNat <<< n - 1) := by
  cases b
  · rw [shiftLeft'_false, Bool.toNat_false, zero_shiftLeft, Nat.zero_sub, xor_zero]
  · rw [shiftLeft'_true, Bool.toNat_true]

end ShiftLeft'

section BitResiduum

def testRes (q i : ℕ) := ((q >>> (i + 1)) <<< i) ||| (q &&& (2^i - 1))

def mergeBit (p : ℕ) (i : ℕ) (b : Bool)  :=
  ((p >>> i) <<< (i + 1)) ||| (p &&& (2^i - 1)) ||| (b.toNat <<< i)

theorem testRes_def : q.testRes i = (q >>> (i + 1)) <<< i ||| q &&& (2^i - 1) := rfl

theorem mergeBit_def : p.mergeBit i b =
    ((p >>> i) <<< (i + 1)) ||| (p &&& (2^i - 1)) ||| (b.toNat <<< i) := rfl

-- application theorems

theorem testRes_apply : q.testRes i = 2^i * (q / 2^(i + 1)) + q % 2^i := by
  rw [testRes_def, and_pow_two_sub_one_eq_mod, shiftLeft_eq_mul_pow, shiftRight_eq_div_pow,
    mul_comm, or_eq_add_two_pow_mul_of_lt_right (mod_lt _ (Nat.two_pow_pos _))]

theorem mergeBit_apply : p.mergeBit i b =
    p + (2^i) * ((p / 2^i) + b.toNat) := by
  rw [mergeBit_def, and_pow_two_sub_one_eq_mod]
  cases b
  · simp_rw [Bool.toNat_false, zero_shiftLeft, or_zero, add_zero,
    Nat.shiftLeft_eq_mul_pow, Nat.shiftRight_eq_div_pow, pow_succ, mul_comm (p / 2 ^ i),
    mul_assoc, or_eq_add_two_pow_mul_of_lt_right (mod_lt _ (Nat.two_pow_pos _)),
    Nat.mul_left_comm, two_mul, add_assoc, add_comm _ (p % 2 ^ i), mod_add_div, add_comm]
  · have h : 2^i < 2^(i + 1) := Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _)
    simp_rw [Bool.toNat_true, Nat.shiftLeft_eq_mul_pow, one_mul,
    Nat.shiftRight_eq_div_pow, mul_comm (p / 2 ^ i), lor_assoc,
    or_eq_add_two_pow_mul_of_lt_right
      (Nat.or_lt_two_pow ((mod_lt _ (Nat.two_pow_pos _)).trans h) h),
    or_eq_add_two_pow_of_lt_left (mod_lt _ (Nat.two_pow_pos _)), mul_add, mul_one, pow_succ',
    mul_assoc, two_mul, add_assoc, ← add_assoc _ _ (2^i), add_comm _ (p % 2 ^ i), mod_add_div,
    Nat.add_right_comm p, add_assoc _ _ (2^i), add_comm]

theorem mergeBit_apply_false {p : ℕ} : p.mergeBit i false = p + (2^i) * (p / 2^i) := by
  simp_rw [mergeBit_apply, Bool.toNat_false, add_zero]

theorem mergeBit_apply_true {p : ℕ} : p.mergeBit i true = p + (2^i) * (p / 2^i) + (2^i) := by
  simp_rw [mergeBit_apply, Bool.toNat_true, mul_add, mul_one, add_assoc]

theorem mergeBit_apply_false_add_pow_two {p : ℕ} : p.mergeBit i false + 2^i = p.mergeBit i true := by
  simp_rw [mergeBit_apply_false, mergeBit_apply_true]

theorem mergeBit_apply_true_sub_pow_two {p : ℕ} : p.mergeBit i true - 2^i = p.mergeBit i false := by
  simp_rw [mergeBit_apply_false, mergeBit_apply_true, Nat.add_sub_cancel]

theorem mergeBit_apply_not {p : ℕ} : p.mergeBit i (!b) =
    (bif b then p.mergeBit i b - 2^i else p.mergeBit i b + 2^i) := by
  cases b
  · rw [Bool.not_false, cond_false, mergeBit_apply_false_add_pow_two]
  · rw [Bool.not_true, cond_true, mergeBit_apply_true_sub_pow_two]

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
  testBit_testRes_of_ge (h.trans (Nat.le_add_right _ _)), Nat.add_right_comm, implies_true]

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

/-
theorem lt_of_testRes_le (hq : q.testRes i ≤ n) : q < 2 * n + 2 ^ (i + 1) := by
  have H := hq.trans_lt <| Nat.lt_mul_div_succ n (Nat.two_pow_pos i)
  rw [testRes_lt_iff_lt_two_mul (dvd_mul_right _ _), mul_succ, mul_add,
    ← pow_succ'] at H
  exact H.trans_le (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)) _)

theorem testRes_lt_of_le (hq : q ≤ n) : q.testRes i < n / 2 + 2 ^ i := by
  have H := hq.trans_lt <| Nat.lt_mul_div_succ n (Nat.two_pow_pos (i + 1))
  rw [pow_succ', mul_assoc, ← testRes_lt_iff_lt_two_mul (dvd_mul_right _ _), mul_succ] at H
  refine H.trans_le (Nat.add_le_add_right ?_ _)
  rw [Nat.le_div_iff_mul_le (zero_lt_two), mul_comm, ← mul_assoc]
  exact (Nat.mul_div_le _ _)-/

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
  simp only [mergeBit_def, and_pow_two_sub_one_eq_mod, testBit_or, testBit_shiftLeft, ge_iff_le,
    add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, decide_false,
    le_add_iff_nonneg_right, _root_.zero_le, tsub_eq_zero_of_le, testBit_zero, Bool.false_and,
    testBit_mod_two_pow, lt_self_iff_false, Bool.or_self, le_refl, decide_true,
    Bool.decide_toNat_mod_two_eq_one, Bool.true_and, Bool.false_or]

theorem testBit_mergeBit_of_lt {i j p : ℕ} (hij : i < j) :
    (p.mergeBit j b).testBit i = p.testBit i := by
  simp only [mergeBit_def, and_pow_two_sub_one_eq_mod, testBit_or, testBit_shiftLeft, ge_iff_le,
    (lt_succ_of_lt hij).not_le, decide_false, testBit_shiftRight, Bool.false_and,
    testBit_mod_two_pow, hij, decide_true, Bool.true_and, Bool.false_or, hij.not_le, Bool.or_false]

theorem testBit_mergeBit_of_gt {i j p : ℕ} (hij : j < i) :
    (p.mergeBit j b).testBit i = p.testBit (i - 1) := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
  simp_rw [mergeBit_def, and_pow_two_sub_one_eq_mod, testBit_or, testBit_shiftLeft,
    testBit_shiftRight,
    testBit_mod_two_pow, ← Nat.add_sub_assoc (succ_le_of_lt hij), succ_eq_add_one,
    Nat.add_sub_add_left, succ_le_of_lt hij, add_comm j, Nat.add_right_comm _ j,
    Nat.add_sub_cancel, testBit_toNat_succ, (Nat.le_add_left j _).not_lt, decide_true,
    Bool.true_and, decide_false, Bool.false_and, Bool.and_false, Bool.or_false]

theorem testBit_mergeBit_of_ne {i j p : ℕ} (hij : i ≠ j) : (p.mergeBit j b).testBit i =
    p.testBit (i - (decide (j < i)).toNat) := by
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [testBit_mergeBit_of_lt hij, Bool.toNat_neg (hij.not_lt), tsub_zero] ;
  · simp only [testBit_mergeBit_of_gt hij, Bool.toNat_pos hij]

theorem testBit_mergeBit {i j p : ℕ} : (p.mergeBit j b).testBit i =
    bif (i = j) then b else p.testBit (i - (decide (j < i)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testBit_mergeBit_of_eq, decide_true, cond_true]
  · simp_rw [hij, testBit_mergeBit_of_ne hij, decide_false, cond_false]

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
  · simp only [hik, decide_true, Bool.toNat_true, (lt_succ_of_le hik).ne',
    decide_false, lt_succ_of_le hik, add_tsub_cancel_right, cond_false]
  · simp only [gt_iff_lt, hik, not_le_of_lt, decide_false, Bool.toNat_false,
    add_zero, ne_of_lt, not_lt_of_lt, tsub_zero, cond_false]

theorem mergeBit_eq_iff : p.mergeBit i b = q ↔ (b = testBit q i) ∧ (p = q.testRes i) :=
  ⟨fun H => H ▸ ⟨testBit_mergeBit_of_eq.symm, testRes_mergeBit_of_eq.symm⟩,
    fun h => by simp_rw [h, mergeBit_testBit_testRes_of_eq]⟩

theorem eq_mergeBit_iff : p = q.mergeBit i b ↔ (testBit p i = b) ∧ (p.testRes i = q) := by
  simp_rw [eq_comm (a := p), mergeBit_eq_iff, eq_comm]

theorem testRes_eq_iff : p.testRes i = q ↔ p = mergeBit q i (p.testBit i) := by
  simp_rw [eq_mergeBit_iff, true_and]

theorem eq_testRes_iff : p = q.testRes i ↔ mergeBit p i (q.testBit i) = q := by
  simp_rw [mergeBit_eq_iff, true_and]

theorem mergeBit_inj {p q : ℕ} : p.mergeBit i b = q.mergeBit i b ↔ p = q := by
  simp_rw [mergeBit_eq_iff, testRes_mergeBit_of_eq, testBit_mergeBit_of_eq, true_and]

theorem mergeBit_inj_right {p : ℕ} : p.mergeBit i b = p.mergeBit i b' ↔ b = b' := by
  simp_rw [mergeBit_eq_iff, testRes_mergeBit_of_eq, testBit_mergeBit_of_eq, and_true]

theorem mergeBit_injective : (mergeBit · i b).Injective := fun _ _ => by
  simp_rw [mergeBit_inj, imp_self]

theorem mergeBit_right_injective : (mergeBit p i · ).Injective := fun _ _ => by
  simp_rw [mergeBit_inj_right, imp_self]

theorem mergeBit_strictMono : StrictMono (mergeBit · i b) := by
  refine Monotone.strictMono_of_injective
    (fun p q hpq => ?_) mergeBit_injective
  simp_rw [mergeBit_apply, mul_add, ← add_assoc]
  exact Nat.add_le_add_right (Nat.add_le_add hpq (Nat.mul_le_mul_left _
    (Nat.div_le_div_right hpq))) _

theorem mergeBit_false_lt_mergeBit_true {q : ℕ} :
    q.mergeBit i false < q.mergeBit i true :=
  mergeBit_apply_false_add_pow_two ▸ Nat.lt_add_of_pos_right (Nat.two_pow_pos _)

theorem mergeBit_strictMono_right : StrictMono (mergeBit p i ·) := by
  refine Monotone.strictMono_of_injective
    (fun b b' => b.rec (fun _ => b'.rec le_rfl mergeBit_false_lt_mergeBit_true.le)
    (fun hbb' => hbb' rfl ▸ le_rfl)) mergeBit_right_injective

theorem mergeBit_lt_mergeBit_iff_lt {r : ℕ} : q.mergeBit i b < r.mergeBit i b ↔ q < r :=
  mergeBit_strictMono.lt_iff_lt

theorem mergeBit_le_mergeBit_iff_le {r : ℕ} : q.mergeBit i b ≤ r.mergeBit i b ↔ q ≤ r :=
  mergeBit_strictMono.le_iff_le

theorem lt_testRes_iff {p : ℕ} : q < p.testRes i ↔ q.mergeBit i (p.testBit i) < p := by
  nth_rewrite 3 [← mergeBit_testBit_testRes_of_eq (q := p) (i := i)]
  rw [mergeBit_lt_mergeBit_iff_lt]

theorem testRes_lt_iff {p : ℕ} : p.testRes i < q ↔ p < q.mergeBit i (p.testBit i) := by
  nth_rewrite 2 [← mergeBit_testBit_testRes_of_eq (q := p) (i := i)]
  rw [mergeBit_lt_mergeBit_iff_lt]

theorem testRes_lt_testRes_iff_lt_of_testBit_eq_testBit {p q : ℕ} (h : p.testBit i = q.testBit i) :
    p.testRes i < q.testRes i ↔ p < q := by rw [lt_testRes_iff, ← h, mergeBit_testBit_testRes_of_eq]

theorem le_testRes_iff {p : ℕ} : q ≤ p.testRes i ↔ q.mergeBit i (p.testBit i) ≤ p := by
  nth_rewrite 3 [← mergeBit_testBit_testRes_of_eq (q := p) (i := i)]
  rw [mergeBit_le_mergeBit_iff_le]

theorem testRes_le_iff {p : ℕ} : p.testRes i ≤ q ↔ p ≤ q.mergeBit i (p.testBit i) := by
  nth_rewrite 2 [← mergeBit_testBit_testRes_of_eq (q := p) (i := i)]
  rw [mergeBit_le_mergeBit_iff_le]

theorem testRes_le_testRes_iff_lt_of_testBit_eq {p q : ℕ} (h : p.testBit i = q.testBit i) :
    q.testRes i ≤ p.testRes i ↔ q ≤ p := by rw [le_testRes_iff, h, mergeBit_testBit_testRes_of_eq]

-- testRes_mergeBit

theorem testRes_mergeBit_of_gt {p : ℕ} (hij : j < i) :
    (p.mergeBit j b).testRes i = (p.testRes (i - 1)).mergeBit j b := by
  simp only [hij, decide_true, Bool.toNat_true, testBit_ext_iff, testBit_testRes, testBit_mergeBit,
    tsub_le_iff_right]
  intro k
  rcases lt_trichotomy j (k + (decide (i ≤ k)).toNat) with hjk | rfl | hjk
  · have H : j < k := (le_or_lt i k).by_cases (lt_of_le_of_lt' · hij)
      (fun h => hjk.trans_eq (by simp_rw [h.not_le, decide_false, Bool.toNat_false, add_zero]))
    simp only [hjk.ne', decide_false, hjk, decide_true, Bool.toNat_true,
      Nat.sub_add_comm (one_le_of_lt H), cond_false, H.ne', H,
      Nat.sub_one_add_one_eq_of_pos (zero_lt_of_lt H)]
  · simp only [decide_true, lt_self_iff_false, decide_false, Bool.toNat_false, tsub_zero, cond_true,
      self_eq_add_right, Bool.toNat_eq_zero, decide_eq_false_iff_not, not_le,
      (le_self_add).trans_lt hij, add_lt_iff_neg_left, not_lt_zero']
  · have H : k < j := le_self_add.trans_lt hjk
    simp only [gt_iff_lt, H.trans hij, not_le_of_lt, decide_false, Bool.toNat_false, add_zero, H,
      not_lt_of_lt, tsub_zero, (succ_lt_of_lt_of_lt H hij)]

theorem testRes_mergeBit_of_lt {p : ℕ} (hij : i < j) :
    (p.mergeBit j b).testRes i = (p.testRes i).mergeBit (j - 1) b := by
  rcases Nat.exists_eq_add_of_lt hij with ⟨j, rfl⟩
  simp only [testBit_ext_iff, testBit_testRes, testBit_mergeBit, add_tsub_cancel_right]
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

theorem testRes_mergeBit_of_ne {p : ℕ} (hij : i ≠ j) : (p.mergeBit j b).testRes i =
    (p.testRes (i - (decide (j < i)).toNat)).mergeBit (j - (decide (i < j)).toNat) b := by
  rcases hij.lt_or_lt with hij | hij
  · simp only [testRes_mergeBit_of_lt hij, hij.not_lt, decide_false, Bool.toNat_false, tsub_zero,
    hij, decide_true, Bool.toNat_true]
  · simp only [testRes_mergeBit_of_gt hij, hij, decide_true, Bool.toNat_true, hij.not_lt,
    decide_false, Bool.toNat_false, tsub_zero]

theorem testRes_mergeBit {i j p : ℕ} : (p.mergeBit j b).testRes i = bif i = j then p else
    (p.testRes (i - (decide (j < i)).toNat)).mergeBit (j - (decide (i < j)).toNat) b := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testRes_mergeBit_of_eq, decide_true, cond_true]
  · simp_rw [hij, testRes_mergeBit_of_ne hij, decide_false, cond_false]

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
  · simp only [mergeBit_testRes_of_le hij.le, hij, not_lt_of_lt, decide_false, Bool.toNat_false,
    add_zero, decide_true, Bool.toNat_true]
  · simp only [mergeBit_testRes_of_ge hij.le, hij, decide_true, Bool.toNat_true, not_lt_of_lt,
    decide_false, Bool.toNat_false, add_zero]

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
  · simp only [decide_true, lt_self_iff_false, decide_false, Bool.toNat_false, add_zero,
    testRes_mergeBit_of_eq, cond_true, mergeBit_testRes_of_eq]
  · simp_rw [hij, mergeBit_testRes_of_ne hij, decide_false, cond_false]

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
  · simp_rw [mergeBit_mergeBit_of_le hij.le, hij, hij.not_lt, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero]
  · simp_rw [mergeBit_mergeBit_of_gt hij, hij, hij.not_lt, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, add_zero]

theorem mergeBit_mergeBit {i j p : ℕ} {b b' : Bool} : (p.mergeBit j b').mergeBit i b  =
    (p.mergeBit (i - (decide (j < i)).toNat) b).mergeBit (j + (decide (i ≤ j)).toNat) b' := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [mergeBit_mergeBit_of_eq, lt_irrefl, le_rfl, decide_false,
    decide_true, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero]
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
  · simp_rw [hjk.not_lt, decide_false, Bool.false_and]

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

theorem testRes_zero : q.testRes 0 = q / 2 := by
  simp_rw [testRes_def, zero_add, shiftLeft_zero, pow_zero, Nat.sub_self, and_zero, or_zero,
    shiftRight_succ, shiftRight_zero]

theorem mergeBit_zero : p.mergeBit 0 b = 2 * p + b.toNat := by
  simp_rw [mergeBit_apply, two_mul, pow_zero, one_mul, Nat.div_one, add_assoc]

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

theorem testRes_eq_mod_of_lt (hq : q < 2^(i + 1)) : q.testRes i = q % 2^i := by
  rw [testRes_apply, Nat.div_eq_of_lt hq, mul_zero, zero_add]

theorem testRes_eq_of_lt (hq : q < 2^i) : q.testRes i = q := by
  rw [testRes_eq_mod_of_lt (hq.trans (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _))),
    mod_eq_of_lt hq]

theorem two_pow_mergeBit_false (hq : q < 2^j) : q.mergeBit j false = q := by
  simp_rw [mergeBit_eq_iff, testRes_eq_of_lt hq, Nat.testBit_eq_false_of_lt hq, true_and]

theorem blahj (hij : i < j) : (2 ^ i).mergeBit j false = 2^i := by
  simp_rw [mergeBit_eq_iff, two_pow_testRes_of_lt hij, testBit_two_pow_of_ne hij.ne, true_and]

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
    decide_true, Bool.true_and, Nat.sub_self, testBit_one_zero, Bool.xor_true]

theorem testBit_flipBit_of_ne {i j : ℕ} (hij : i ≠ j) :
    (q.flipBit j).testBit i = q.testBit i := by
  simp_rw [flipBit_def, testBit_xor, testBit_shiftLeft]
  rcases hij.lt_or_lt with hij | hij
  · simp_rw [hij.not_le, decide_false, Bool.false_and, Bool.xor_false]
  · simp_rw [testBit_one, Nat.sub_eq_zero_iff_le, hij.not_le, decide_false,
    Bool.and_false, Bool.xor_false]

theorem testBit_flipBit : (q.flipBit j).testBit i = (q.testBit i).xor (i = j) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testBit_flipBit_of_eq, decide_true, Bool.xor_true]
  · simp_rw [testBit_flipBit_of_ne hij, hij, decide_false, Bool.xor_false]

-- representations of flipBit

theorem flipBit_eq_mergeBit {i : ℕ} :
    q.flipBit i = (q.testRes i).mergeBit i (!(testBit q i)) := by
  simp_rw [testBit_ext_iff]
  intro j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [testBit_flipBit_of_ne hij.ne', testBit_mergeBit_of_gt hij, testBit_pred_testRes_of_gt hij]
  · rw [testBit_flipBit_of_eq, testBit_mergeBit_of_eq]
  · rw [testBit_flipBit_of_ne hij.ne, testBit_mergeBit_of_lt hij, testBit_testRes_of_lt hij]

theorem flipBit_eq_of_testBit_false {i : ℕ} (hqi : q.testBit i = false) :
    q.flipBit i = (q.testRes i).mergeBit i true := by
  rw [flipBit_eq_mergeBit, hqi, Bool.not_false]

theorem flipBit_eq_of_testBit_true {i : ℕ} (hqi : q.testBit i = true) :
    q.flipBit i = (q.testRes i).mergeBit i false := by
  rw [flipBit_eq_mergeBit, hqi, Bool.not_true]

theorem flipBit_eq_cond {i : ℕ} : q.flipBit i = bif testBit q i then q - 2^i else q + 2^i := by
  rw [flipBit_eq_mergeBit, mergeBit_not_testBit_testRes_of_eq]

-- flipBit equalities and inequalities

theorem flipBit_div_two_pow_eq {i : ℕ} (h : i < k) : q.flipBit i / 2^k = q / 2^k := by
  simp_rw [testBit_ext_iff, testBit_div_two_pow,
  testBit_flipBit_of_ne (h.trans_le (Nat.le_add_right _ _)).ne', implies_true]

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

theorem flipBit_mem_bitMatchTo {i j k x : ℕ} (hk : k ∈ Set.Ico i j) (q : ℕ) :
    q ∈ bitMatchTo x j i → q.flipBit k ∈ bitMatchTo x j i := by
  simp_rw [mem_bitMatchTo_iff, Nat.flipBit_lt_iff_lt (Nat.pow_dvd_pow _ hk.2)]
  simp_rw [testBit_flipBit]
  exact And.imp_right (fun hq _ hjk => by
    simp_rw [hq _ hjk, (hjk.trans_le hk.1).ne, decide_false, Bool.xor_false])

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
  rw [flipBit_eq_mergeBit, testRes_mergeBit_of_eq]

theorem testRes_flipBit : (q.flipBit j).testRes i = bif i = j then q.testRes i else
    (q.testRes i).flipBit (j - (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [testRes_flipBit_of_eq, decide_true, cond_true]
  · simp_rw [testRes_flipBit_of_ne hij, hij, decide_false, cond_false]

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
  · simp_rw [flipBit_mergeBit_of_lt hij, hij.not_lt, decide_false, Bool.toNat_false,
    Nat.sub_zero]
  · simp_rw [flipBit_mergeBit_of_gt hij, hij, decide_true, Bool.toNat_true]

theorem flipBit_mergeBitRes :
    (p.mergeBit j b).flipBit i = if i = j then p.mergeBit i (!b) else
    (p.flipBit (i - (decide (j < i)).toNat)).mergeBit j b := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [flipBit_mergeBit_of_eq, if_true]
  · simp_rw [flipBit_mergeBit_of_ne hij, hij, if_false]

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

theorem testRes_eq_testRes_iff {r : ℕ} :
    q.testRes i = r.testRes i ↔ q = r ∨ q = r.flipBit i := by
  rw [testRes_eq_iff]
  rcases Bool.eq_or_eq_not (q.testBit i) (r.testBit i) with hqr | hqr
  · simp_rw [hqr, mergeBit_testBit_testRes_of_eq, ne_flipBit_of_testBit_eq hqr, or_false]
  · simp_rw [hqr, flipBit_eq_mergeBit, ne_of_testBit_eq_not_testBit i hqr, false_or]

theorem flipBit_lt_iff_lt_flipBit_of_testBit_eq_not_testBit {r : ℕ}
    (h : q.testBit i = !r.testBit i) : q.flipBit i < r ↔ q < r.flipBit i := by
  simp_rw [flipBit_eq_mergeBit, h, Bool.not_not, ← h, ← testRes_lt_iff, ← lt_testRes_iff]

theorem flipBit_lt_iff_lt_flipBit_of_not_testBit_eq_testBit {r : ℕ}
    (h : (!q.testBit i) = r.testBit i) : q.flipBit i < r ↔ q < r.flipBit i := by
  simp_rw [flipBit_eq_mergeBit, ← h, Bool.not_not, h, ← testRes_lt_iff, ← lt_testRes_iff]

theorem testRes_lt_testRes_iff_flipBit_lt_of_not_testBit_eq_testBit
    (h : (!q.testBit i) = r.testBit i) : q.testRes i < r.testRes i ↔ q.flipBit i < r := by
  rw [flipBit_eq_mergeBit, h, ← lt_testRes_iff]

theorem testRes_lt_testRes_iff_flipBit_lt_of_testBit_eq_not_testBit
    (h : q.testBit i = !r.testBit i) : q.testRes i < r.testRes i ↔ q.flipBit i < r :=
  testRes_lt_testRes_iff_flipBit_lt_of_not_testBit_eq_testBit  (h ▸ Bool.not_not _)

theorem testRes_lt_testRes_iff_lt_flipBit_of_testBit_eq_not_testBit {r : ℕ}
    (h : q.testBit i = !r.testBit i) : q.testRes i < r.testRes i ↔ q < r.flipBit i := by
  rw [testRes_lt_testRes_iff_flipBit_lt_of_testBit_eq_not_testBit h,
  flipBit_lt_iff_lt_flipBit_of_testBit_eq_not_testBit h]

theorem testRes_lt_testRes_iff_lt_flipBit_of_not_testBit_eq_testBit {r : ℕ}
    (h : (!q.testBit i) = r.testBit i) : q.testRes i < r.testRes i ↔ q < r.flipBit i := by
  rw [testRes_lt_testRes_iff_flipBit_lt_of_not_testBit_eq_testBit h,
  flipBit_lt_iff_lt_flipBit_of_not_testBit_eq_testBit h]

theorem flipBit_lt_flipBit_iff_lt_of_testBit_eq_testBit {q r : ℕ}
    (h : q.testBit i = r.testBit i) : q.flipBit i < r.flipBit i ↔ q < r := by
  rw [← testRes_lt_testRes_iff_lt_flipBit_of_not_testBit_eq_testBit
    (h ▸ testBit_flipBit_of_eq.symm ▸ Bool.not_not _), testRes_flipBit_of_eq,
  testRes_lt_testRes_iff_lt_of_testBit_eq_testBit h]

theorem testRes_lt_testRes_of_lt_of_flipBit_lt (hqr : q < r) (hqr' : q.flipBit i < r) :
    q.testRes i < r.testRes i := by
  rcases Bool.eq_or_eq_not (q.testBit i) (r.testBit i) with hqrb | hqrb
  · simp_rw [testRes_lt_testRes_iff_lt_of_testBit_eq_testBit hqrb, hqr]
  · simp_rw [testRes_lt_testRes_iff_flipBit_lt_of_testBit_eq_not_testBit hqrb, hqr']

theorem testRes_lt_testRes_of_flipBit_lt_of_lt (hqr : q < r) (hqr' : q < r.flipBit i) :
    q.testRes i < r.testRes i := by
  rcases Bool.eq_or_eq_not (q.testBit i) (r.testBit i) with hqrb | hqrb
  · simp_rw [testRes_lt_testRes_iff_lt_of_testBit_eq_testBit hqrb, hqr]
  · simp_rw [testRes_lt_testRes_iff_lt_flipBit_of_testBit_eq_not_testBit hqrb, hqr']

@[simp]
theorem flipBit_flipBit_of_eq : (q.flipBit i).flipBit i = q := by
  simp_rw [flipBit_def, Nat.xor_cancel_right]

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

variable {p q k : ℕ}

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
  · rw [cond_false, Bool.xor, Bool.false_bne]
  · rw [cond_true, Bool.xor, Bool.true_bne]

theorem testBit_condFlipBit_of_le_testRes (h : c.size ≤ q.testRes i) :
    (q.condFlipBit i c).testBit j = q.testBit j := by
  rw [condFlipBit_apply_of_le_testRes h]

theorem testBit_condFlipBit_of_testRes_lt_of_eq (h : q.testRes i < c.size) :
  (q.condFlipBit i c).testBit i = (c[q.testRes i]).xor (q.testBit i) := by
  rw [testBit_condFlipBit_of_eq, c.getElem?_lt h, Option.getD_some]

theorem testBit_condFlipBit : (q.condFlipBit j c).testBit i =
    (decide (i = j) && (c[q.testRes i]?.getD false)).xor (q.testBit i) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [decide_true, Bool.true_and, testBit_condFlipBit_of_eq]
  · simp_rw [hij, decide_false, Bool.false_and, Bool.false_xor, testBit_condFlipBit_of_ne hij]

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

theorem condFlipBit_condFlipBit {d : Array Bool} :
    (q.condFlipBit i c).condFlipBit i d = (q.condFlipBit i d).condFlipBit i c := by
  simp_rw [testBit_ext_iff, testBit_condFlipBit]
  intro k
  rcases eq_or_ne k i with rfl | hki
  · simp_rw [decide_true, Bool.true_and, testRes_condFlipBit_of_eq,
    ← Bool.xor_assoc, Bool.xor_comm]
  · simp_rw [hki, decide_false, Bool.false_and]

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

def flipBitIndices (as : Array α) (i t : ℕ) : Array α := t.recOn
  as fun k as => as.swapIfInBounds (k.mergeBit i false) (k.mergeBit i true)

@[simp]
theorem flipBitIndices_zero {as : Array α} {i : ℕ} : flipBitIndices as i 0 = as := rfl
@[simp]
theorem flipBitIndices_succ {as : Array α} {i t : ℕ} :
    flipBitIndices as i (t.succ) =
    (flipBitIndices as i t).swapIfInBounds (t.mergeBit i false) (t.mergeBit i true) := rfl

@[simp]
theorem size_flipBitIndices {as : Array α} {i t : ℕ} :
    (flipBitIndices as i t).size = as.size := by
  induction' t with t IH
  · rfl
  · simp_rw [flipBitIndices_succ, size_swapIfInBounds, IH]

theorem getElem_flipBitIndices {as : Array α} {i t k : ℕ}
    (hk : k < (flipBitIndices as i t).size) :
    (flipBitIndices as i t)[k] = if hk' : k.testRes i < t ∧ k.flipBit i < as.size then
      as[k.flipBit i] else as[k]'(hk.trans_eq size_flipBitIndices) := by
  induction' t with t IH generalizing k
  · rfl
  · simp_rw [flipBitIndices_succ, getElem_swapIfInBounds, IH, size_flipBitIndices,
    Nat.testRes_mergeBit_of_eq, lt_self_iff_false, false_and, dite_false, Nat.eq_mergeBit_iff,
    Nat.lt_succ_iff]
    rcases lt_trichotomy (k.testRes i) t with hkt | rfl | hkt
    · simp_rw [hkt, hkt.ne, hkt.le, and_false, false_and, dite_false]
    · simp_rw [and_true, lt_self_iff_false, false_and, dite_false, le_refl, true_and]
      rcases (k.testBit i).eq_false_or_eq_true with hkb | hkb <;> simp_rw [hkb]
      · simp_rw [Bool.true_eq_false, false_and, true_and, dite_false,
          Nat.flipBit_eq_of_testBit_true hkb]
      · simp_rw [Bool.false_eq_true, false_and, true_and, dite_false,
        Nat.flipBit_eq_of_testBit_false hkb]
    · simp_rw [hkt.ne', hkt.not_lt, hkt.not_le,  and_false, false_and, dite_false]

theorem flipBitIndices_eq_of_testRes_lt {as : Array α} {i t t' : ℕ}
  (h : ∀ k, k < as.size → k.flipBit i < as.size → k.testRes i < min t t') :
    flipBitIndices as i t = flipBitIndices as i t' := by
  simp_rw [Array.ext_iff, size_flipBitIndices, true_and, getElem_flipBitIndices]
  intro k hk _
  rcases lt_or_le (k.flipBit i) (as.size) with hk' | hk'
  · simp_rw [hk', and_true, (h _ hk hk').trans_le (Nat.min_le_left _ _),
    (h _ hk hk').trans_le (Nat.min_le_right _ _)]
  · simp_rw [hk'.not_lt, and_false]

theorem flipBitIndices_of_ge_testRes_size {as : Array α} {i t : ℕ} (h : as.size.testRes i ≤ t) :
    flipBitIndices as i t = flipBitIndices as i (as.size.testRes i) := by
  refine flipBitIndices_eq_of_testRes_lt (fun k hk hk' => ?_)
  simp_rw [min_eq_right h]
  exact Nat.testRes_lt_testRes_of_lt_of_flipBit_lt hk hk'

theorem getElem_flipBitIndices_testRes_size {as : Array α} {i k : ℕ}
    (hk : k < (flipBitIndices as i (as.size.testRes i)).size) :
    (flipBitIndices as i (as.size.testRes i))[k] =
    if h : k.flipBit i < as.size then as[k.flipBit i]
    else as[k]'(hk.trans_eq size_flipBitIndices) := by
  simp_rw [getElem_flipBitIndices]
  rcases Bool.eq_or_eq_not (k.testBit i) (as.size.testBit i) with hkas | hkas
  · simp_rw [size_flipBitIndices] at hk
    simp_rw [Nat.testRes_lt_testRes_iff_lt_of_testBit_eq_testBit hkas, hk, true_and]
  · simp_rw [Nat.testRes_lt_testRes_iff_flipBit_lt_of_testBit_eq_not_testBit hkas, and_self]

def flipBitVals (as : Array ℕ) (i : ℕ) : Array ℕ := as.map
  (fun k => if k.flipBit i < as.size then k.flipBit i else k)

@[simp]
theorem size_flipBitVals {as : Array ℕ} {i : ℕ} : (flipBitVals as i).size = as.size :=
  size_map _ _

@[simp]
theorem getElem_flipBitVals {as : Array ℕ} {i k : ℕ} (hk : k < (flipBitVals as i).size) :
    (flipBitVals as i)[k] = (if (as[k]'(hk.trans_eq size_flipBitVals)).flipBit i < as.size then
    (as[k]'(hk.trans_eq size_flipBitVals)).flipBit i else as[k]'(hk.trans_eq size_flipBitVals)) :=
  getElem_map _ _ _ _

end FlipBit

section CondFlipBit

def condFlipBitIndices (as : Array α) (i : ℕ) (c : Array Bool) (t : ℕ) : Array α := t.recOn
  as fun k as => as.swapIfInBounds (k.mergeBit i false) (k.mergeBit i (c[k]?.getD false))

@[simp]
theorem condFlipBitIndices_zero {as : Array α} {i : ℕ} {c : Array Bool} :
    condFlipBitIndices as i c 0 = as := rfl

@[simp]
theorem condFlipBitIndices_succ {as : Array α} {i t : ℕ} {c : Array Bool} :
    condFlipBitIndices as i c (t.succ) = (condFlipBitIndices as i c t).swapIfInBounds
    (t.mergeBit i false) (t.mergeBit i (c[t]?.getD false)) := rfl

@[simp]
theorem size_condFlipBitIndices {as : Array α} {i t : ℕ} {c : Array Bool} :
    (condFlipBitIndices as i c t).size = as.size := by
  induction' t with t IH
  · rfl
  · simp_rw [condFlipBitIndices_succ, size_swapIfInBounds, IH]

theorem getElem_condFlipBitIndices {as : Array α} {i t k : ℕ} {c : Array Bool}
    (hk : k < (condFlipBitIndices as i c t).size) :
    (condFlipBitIndices as i c t)[k] = if hk' : k.testRes i < t ∧ k.condFlipBit i c < as.size then
      as[k.condFlipBit i c] else as[k]'(hk.trans_eq size_condFlipBitIndices) := by
  induction' t with t IH generalizing k
  · rfl
  · simp_rw [condFlipBitIndices_succ, getElem_swapIfInBounds, IH, size_condFlipBitIndices,
    Nat.testRes_mergeBit_of_eq, lt_self_iff_false, false_and, dite_false, Nat.eq_mergeBit_iff,
    Nat.lt_succ_iff]
    rcases lt_trichotomy (k.testRes i) t with hkt | rfl | hkt
    · simp_rw [hkt, hkt.ne, hkt.le, and_false, false_and, dite_false]
    · simp_rw [and_true, lt_self_iff_false, false_and, dite_false, le_refl, true_and]
      simp_rw [size_condFlipBitIndices] at hk
      rcases lt_or_le (k.testRes i) c.size with hkc | hkc
      · simp_rw [getElem?_lt _ hkc, Option.getD_some, Nat.condFlipBit_apply_of_testRes_lt hkc]
        rcases Bool.eq_false_or_eq_true (c[k.testRes i]) with hc | hc <;> simp_rw [hc]
        · simp_rw [cond_true]
          rcases Bool.eq_false_or_eq_true (k.testBit i) with hki | hki <;> simp_rw [hki]
          · simp_rw [Bool.true_eq_false, false_and, dite_false, true_and,
              Nat.flipBit_eq_of_testBit_true hki]
          · simp_rw [Bool.false_eq_true, true_and, false_and, dite_false,
              Nat.flipBit_eq_of_testBit_false hki]
        · simp_rw [cond_false, hk, dite_true]
          split_ifs with h
          · simp_rw [← h.1, Nat.mergeBit_testBit_testRes_of_eq]
          · rfl
      · simp_rw [getElem?_ge _ hkc, Option.getD_none, Nat.condFlipBit_apply_of_le_testRes hkc]
        simp_rw [hk, dite_true]
        split_ifs with h
        · simp_rw [← h.1, Nat.mergeBit_testBit_testRes_of_eq]
        · rfl
    · simp_rw [hkt.ne', hkt.not_lt, hkt.not_le,  and_false, false_and, dite_false]

theorem condFlipBitIndices_eq_of_testRes_lt {as : Array α} {i t t' : ℕ} {c : Array Bool}
    (h : ∀ k, k < as.size → k.flipBit i < as.size → k.testRes i < min t t') :
    condFlipBitIndices as i c t = condFlipBitIndices as i c t' := by
  simp_rw [Array.ext_iff, size_condFlipBitIndices, true_and, getElem_condFlipBitIndices]
  intro k hk _
  rcases lt_or_le (k.condFlipBit i c) (as.size) with hk' | hk'
  · rcases lt_or_le (k.testRes i) c.size with hck | hck
    · simp_rw [Nat.condFlipBit_apply_of_testRes_lt hck] at hk'
      simp_rw [Nat.condFlipBit_apply_of_testRes_lt hck, hk', and_true]
      rcases Bool.eq_false_or_eq_true (c[k.testRes i]) with hcki | hcki <;> simp_rw [hcki] at hk' ⊢
      · simp_rw [cond_true, (h _ hk hk').trans_le (Nat.min_le_left _ _),
        (h _ hk hk').trans_le (Nat.min_le_right _ _)]
      · simp_rw [cond_false]
        split_ifs <;> rfl
    · simp_rw [Nat.condFlipBit_apply_of_le_testRes hck]
      split_ifs <;> rfl
  · simp_rw [hk'.not_lt, and_false]

theorem condFlipBitIndices_of_ge_min_size_testRes_size {as : Array α} {i t : ℕ} {c : Array Bool}
    (h : min c.size (as.size.testRes i) ≤ t) :
    condFlipBitIndices as i c t = condFlipBitIndices as i c (min c.size (as.size.testRes i)) := by
  rcases lt_or_le c.size (as.size.testRes i) with h' | h'
  · rw [min_eq_left h'.le] at h ⊢
    simp_rw [Array.ext_iff, size_condFlipBitIndices, true_and, getElem_condFlipBitIndices]
    intro k hk _
    rcases lt_or_le (k.condFlipBit i c) (as.size) with hk' | hk'
    · rcases lt_or_le (k.testRes i) c.size with hck | hck
      · simp_rw [hck, hk', and_true, hck.trans_le h]
      · simp_rw [Nat.condFlipBit_apply_of_le_testRes hck]
        split_ifs <;> rfl
    · simp_rw [hk'.not_lt, and_false]
  · rw [min_eq_right h'] at h ⊢
    refine condFlipBitIndices_eq_of_testRes_lt (fun k hk hk' => ?_)
    simp_rw [min_eq_right h]
    exact Nat.testRes_lt_testRes_of_lt_of_flipBit_lt hk hk'

theorem condFlipBitIndices_of_ge_testRes_size {as : Array α} {i t : ℕ} {c : Array Bool}
    (h : as.size.testRes i ≤ t) :
    condFlipBitIndices as i c t = condFlipBitIndices as i c (min c.size (as.size.testRes i)) := by
  rw [condFlipBitIndices_of_ge_min_size_testRes_size (min_le_of_right_le h)]

theorem condFlipBitIndices_of_ge_size {as : Array α} {i t : ℕ} {c : Array Bool}
    (h : c.size ≤ t) : condFlipBitIndices as i c t =
    condFlipBitIndices as i c (min c.size (as.size.testRes i)) := by
  rw [condFlipBitIndices_of_ge_min_size_testRes_size (min_le_of_left_le h)]

theorem getElem_condFlipBitIndices_min_size_size_testRes {as : Array α} {i k : ℕ} {c : Array Bool}
    (hk : k < (condFlipBitIndices as i c (min c.size (as.size.testRes i))).size) :
    (condFlipBitIndices as i c (min c.size (as.size.testRes i)))[k] =
    if h : k.condFlipBit i c < as.size then as[k.condFlipBit i c]
    else as[k]'(hk.trans_eq size_condFlipBitIndices) := by
  simp_rw [← condFlipBitIndices_of_ge_min_size_testRes_size (min_le_left _ _),
    getElem_condFlipBitIndices]
  rcases lt_or_le (k.testRes i) c.size with hck | hck
  · simp_rw [hck, true_and]
  · simp_rw [hck.not_lt, false_and, dite_false,
      Nat.condFlipBit_apply_of_le_testRes hck]
    split_ifs <;> rfl

theorem condFlipBitIndices_of_mkArray_true (a : Array α) (i : ℕ)  :
    a.condFlipBitIndices i (mkArray (a.size.testRes i) true) (a.size.testRes i) =
    a.flipBitIndices i (a.size.testRes i) := by
  simp_rw [Array.ext_iff, size_condFlipBitIndices, size_flipBitIndices, true_and,
    condFlipBitIndices_of_ge_size (size_mkArray _ _).le,
    getElem_flipBitIndices_testRes_size,
    getElem_condFlipBitIndices_min_size_size_testRes,
    Nat.condFlipBit_of_mkArray_true]
  intro k hk _
  split_ifs with hki hk'
  · rfl
  · rfl
  · rcases Bool.eq_or_eq_not (k.testBit i) (a.size.testBit i) with hkas | hkas
    · rw [Nat.testRes_lt_testRes_iff_lt_of_testBit_eq_testBit hkas] at hki
      exact (hki hk).elim
    · simp_rw [Nat.testRes_lt_testRes_iff_flipBit_lt_of_testBit_eq_not_testBit hkas] at hki
      simp_rw [hki, dite_false]

def condFlipBitVals (as : Array ℕ) (i : ℕ) (c : Array Bool) : Array ℕ :=
  as.map (fun k => if k.condFlipBit i c < as.size then k.condFlipBit i c else k)

@[simp]
theorem size_condFlipBitVals {as : Array ℕ} {i : ℕ} {c : Array Bool} :
    (condFlipBitVals as i c).size = as.size := size_map _ _

theorem getElem_condFlipBitVals (as : Array ℕ) (i : ℕ) (c : Array Bool) (k : ℕ)
    (hk : k < (condFlipBitVals as i c).size) :
    (condFlipBitVals as i c)[k] =
    if (as[k]'(hk.trans_eq size_condFlipBitVals)).condFlipBit i c < as.size then
    (as[k]'(hk.trans_eq size_condFlipBitVals)).condFlipBit i c else
    as[k]'(hk.trans_eq size_condFlipBitVals) := getElem_map _ _ _ _

end CondFlipBit

end Array

namespace VectorPerm

section FlipBit

def flipBitIndices (a : VectorPerm n) (i : ℕ) : VectorPerm n where
  fwdVector := ⟨a.fwdVector.flipBitIndices i (n.testRes i), by
    simp_rw [Array.size_flipBitIndices, Vector.size_toArray]⟩
  bwdVector := ⟨a.bwdVector.flipBitVals i, by
    simp_rw [Array.size_flipBitVals, Vector.size_toArray]⟩
  getElem_fwdVector_lt' := fun _ => by
    simp_rw [Vector.getElem_mk, Array.flipBitIndices_of_ge_testRes_size
      (congrArg (Nat.testRes · i) (Vector.size_toArray _)).le,
      Array.getElem_flipBitIndices_testRes_size, Vector.getElem_toArray, getElem_fwdVector]
    split_ifs <;> exact getElem_lt
  getElem_bwdVector_lt' := fun hk => by
    simp_rw [Vector.getElem_mk, Array.getElem_flipBitVals, Vector.getElem_toArray,
      getElem_bwdVector, Vector.size_toArray]
    split_ifs
    · assumption
    · exact getElem_lt
  left_inv' := fun {j} hk => by
    simp_rw [Vector.getElem_mk, Array.getElem_flipBitVals, Array.flipBitIndices_of_ge_testRes_size
      (congrArg (Nat.testRes · i) (Vector.size_toArray _)).le,
      Array.getElem_flipBitIndices_testRes_size, Vector.getElem_toArray,
      getElem_fwdVector, getElem_bwdVector,
      Vector.size_toArray]
    by_cases hj : j.flipBit i < n
    · simp_rw [hj, dite_true, getElem_inv_getElem, Nat.flipBit_flipBit_of_eq, hk, ite_true]
    · simp_rw [hj, dite_false, getElem_inv_getElem, hj, if_false]

def flipBitVals (a : VectorPerm n) (i : ℕ) : VectorPerm n where
  fwdVector := ⟨a.fwdVector.flipBitVals i, by
    simp only [Array.size_flipBitVals, Vector.size_toArray]⟩
  bwdVector := ⟨a.bwdVector.flipBitIndices i (n.testRes i), by
    simp only [Array.size_flipBitIndices, Vector.size_toArray]⟩
  getElem_fwdVector_lt' := fun hk => by
    simp_rw [Vector.getElem_mk, Array.getElem_flipBitVals, Vector.getElem_toArray,
      getElem_fwdVector, Vector.size_toArray]
    split_ifs
    · assumption
    · exact getElem_lt
  getElem_bwdVector_lt' := fun _ => by
    simp_rw [Array.flipBitIndices_of_ge_testRes_size
      (congrArg (Nat.testRes · i) (Vector.size_toArray _)).le, Vector.getElem_mk,
      Array.getElem_flipBitIndices_testRes_size, Vector.getElem_toArray, getElem_bwdVector]
    split_ifs <;> exact getElem_lt
  left_inv' := fun {j} hk => by
    simp_rw [Vector.getElem_mk, Array.getElem_flipBitVals, Array.flipBitIndices_of_ge_testRes_size
      (congrArg (Nat.testRes · i) (Vector.size_toArray _)).le,
      Array.getElem_flipBitIndices_testRes_size, Vector.getElem_toArray, getElem_fwdVector,
      getElem_bwdVector, Vector.size_toArray]
    by_cases hj : a[j].flipBit i < n
    · simp_rw [hj, ite_true, Nat.flipBit_flipBit_of_eq, getElem_lt, dite_true, getElem_inv_getElem]
    · simp_rw [hj, ite_false, hj, dite_false, getElem_inv_getElem]


variable {a b : VectorPerm n} {i k : ℕ}

theorem getElem_flipBitIndices {hk : k < n} :
    (a.flipBitIndices i)[k] =
    if hk : k.flipBit i < n then a[k.flipBit i] else a[k] := by
  unfold flipBitIndices
  simp_rw [getElem_mk, Array.flipBitIndices_of_ge_testRes_size
      (congrArg (Nat.testRes · i) (Vector.size_toArray _)).le, Vector.getElem_mk,
      Array.getElem_flipBitIndices_testRes_size, Vector.getElem_toArray,
      getElem_fwdVector, Vector.size_toArray]

theorem getElem_flipBitVals {hk : k < n} :
    (a.flipBitVals i)[k] =
    if a[k].flipBit i < n then a[k].flipBit i else a[k] := by
  unfold flipBitVals
  simp_rw [getElem_mk, Vector.getElem_mk, Array.getElem_flipBitVals,
  Vector.getElem_toArray, getElem_fwdVector, Vector.size_toArray]

theorem getElem_inv_flipBitIndices {hk : k < n} :
    (a.flipBitIndices i)⁻¹[k] = if a⁻¹[k].flipBit i < n then a⁻¹[k].flipBit i else a⁻¹[k] := by
  unfold flipBitIndices
  simp_rw [getElem_inv_mk, Vector.getElem_mk, Array.getElem_flipBitVals,
  Vector.getElem_toArray, getElem_bwdVector, Vector.size_toArray]

theorem getElem_inv_flipBitVals {hk : k < n} :
    (a.flipBitVals i)⁻¹[k] =
    if hk : k.flipBit i < n then a⁻¹[k.flipBit i] else a⁻¹[k] := by
  unfold flipBitVals
  simp_rw [getElem_inv_mk, Array.flipBitIndices_of_ge_testRes_size
      (congrArg (Nat.testRes · i) (Vector.size_toArray _)).le, Vector.getElem_mk,
      Array.getElem_flipBitIndices_testRes_size, Vector.getElem_toArray,
      getElem_bwdVector, Vector.size_toArray]

def flipBit (i : ℕ) : VectorPerm n := (1 : VectorPerm n).flipBitIndices i

theorem getElem_flipBit {hk : k < n} :
    (flipBit i)[k] = if k.flipBit i < n then k.flipBit i else k := by
  unfold flipBit
  simp_rw [getElem_flipBitIndices, getElem_one, dite_eq_ite]

theorem getElem_inv_flipBit {hk : k < n} :
    (flipBit i)⁻¹[k] = if k.flipBit i < n then k.flipBit i else k := by
  unfold flipBit
  simp_rw [getElem_inv_flipBitIndices, inv_one, getElem_one]

@[simp]
theorem flipBit_inv : (flipBit i : VectorPerm n)⁻¹ = flipBit i := by
  ext : 1
  simp_rw [getElem_flipBit, getElem_inv_flipBit]

@[simp]
theorem flipBit_mul_self : (flipBit i : VectorPerm n) * flipBit i = 1 := by
  rw [← eq_inv_iff_mul_eq_one, flipBit_inv]

@[simp]
theorem flipBit_mul_self_mul : flipBit i * (flipBit i * a) = a := by
  rw [← mul_assoc, flipBit_mul_self, one_mul]

@[simp]
theorem mul_flipBit_mul_self : a * flipBit i * flipBit i = a := by
  rw [mul_assoc, flipBit_mul_self, mul_one]

theorem flipBitIndices_eq_mul_flipBit (a : VectorPerm n) :
    a.flipBitIndices i = a * flipBit i := by
  ext k hk : 1
  simp only [getElem_flipBitIndices, getElem_flipBit, getElem_mul, getElem_one]
  split_ifs <;> rfl

theorem flipBitVals_eq_flipBit_mul (a : VectorPerm n) :
    a.flipBitVals i = flipBit i * a := by
  ext k hk : 1
  simp only [getElem_flipBitVals, getElem_flipBit, getElem_mul, getElem_one]

@[simp]
theorem inv_flipBitVals {a : VectorPerm n} {i : ℕ} :
    a⁻¹.flipBitVals i = (a.flipBitIndices i)⁻¹ := by
  simp_rw [flipBitIndices_eq_mul_flipBit, flipBitVals_eq_flipBit_mul, mul_inv_rev, flipBit_inv]

@[simp]
theorem inv_flipBitIndices  {a : VectorPerm n} {i : ℕ} :
    a⁻¹.flipBitIndices i = (a.flipBitVals i)⁻¹ := by
  simp_rw [flipBitIndices_eq_mul_flipBit, flipBitVals_eq_flipBit_mul, mul_inv_rev, flipBit_inv]

theorem flipBitIndices_inv_eq_flipBit_mul (a : VectorPerm n) :
    (a.flipBitIndices i)⁻¹ = flipBit i * a⁻¹ := by
  rw [← inv_flipBitVals, flipBitVals_eq_flipBit_mul]

theorem flipBitVals_inv_eq_mul_flipBit (a : VectorPerm n) :
    (a.flipBitVals i)⁻¹ = a⁻¹ * flipBit i := by
  rw [← inv_flipBitIndices, flipBitIndices_eq_mul_flipBit]

@[simp]
theorem one_flipBitIndices : (1 : VectorPerm n).flipBitIndices i = flipBit i := by
  rw [flipBitIndices_eq_mul_flipBit, one_mul]
@[simp]
theorem one_flipBitVals : (1 : VectorPerm n).flipBitVals i = flipBit i := by
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
theorem flipBit_flipBitIndices : (flipBit i : VectorPerm n).flipBitIndices i = 1 := by
  rw [flipBitIndices_eq_mul_flipBit, flipBit_mul_self]
@[simp]
theorem flipBit_flipBitVals : (flipBit i : VectorPerm n).flipBitVals i = 1 := by
  rw [flipBitVals_eq_flipBit_mul, flipBit_mul_self]

theorem flipBitVals_comm_flipBitIndices :
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

theorem flipBit_smul_eq_self :
    (flipBit i : VectorPerm n) • x = x ↔ n ≤ x ∨ n ≤ x.flipBit i := by
  simp_rw [smul_nat_eq_dite, getElem_flipBit,
    dite_eq_ite, ite_eq_right_iff, Nat.flipBit_ne_self, imp_false,
    imp_iff_or_not, not_lt, or_comm]

theorem flipBit_smul_ne_self :
    (flipBit i : VectorPerm n) • x ≠ x ↔ x < n ∧ x.flipBit i < n := by
  simp_rw [ne_eq, flipBit_smul_eq_self, not_or, not_le]

theorem mem_fixedBy_flipBit :
    x ∈ MulAction.fixedBy ℕ (flipBit i : VectorPerm n) ↔ n ≤ x ∨ n ≤ x.flipBit i := by
  simp_rw [MulAction.mem_fixedBy, flipBit_smul_eq_self]

theorem movedBy_flipBit :
    x ∈ (MulAction.fixedBy ℕ (flipBit i : VectorPerm n))ᶜ ↔ x < n ∧ x.flipBit i < n := by
  simp only [Set.mem_compl_iff, MulAction.mem_fixedBy, flipBit_smul_ne_self]

theorem getElem_flipBit_ne_self_of_flipBit_lt {hk : k < n} (hk' : k.flipBit i < n) :
    (flipBit i)[k] ≠ k := by
  simp_rw [← smul_of_lt hk, flipBit_smul_ne_self]
  exact ⟨hk, hk'⟩

theorem getElem_flipBitIndices_of_flipBit_lt {hk : k < n} (hk' : k.flipBit i < n) :
    (a.flipBitIndices i)[k] = a[k.flipBit i] := by
  simp_rw [flipBitIndices_eq_mul_flipBit, getElem_mul, getElem_flipBit_of_flipBit_lt hk']

theorem getElem_flipBitIndices_of_le_flipBit {hk : k < n} (hk' : n ≤ k.flipBit i) :
    (a.flipBitIndices i)[k] = a[k] := by
  simp_rw [flipBitIndices_eq_mul_flipBit, getElem_mul, getElem_flipBit_of_le_flipBit hk']

theorem flipBitIndices_smul_eq_smul :
    (a.flipBitIndices i) • x = a • x ↔ n ≤ x ∨ n ≤ x.flipBit i := by
  simp_rw [flipBitIndices_eq_mul_flipBit, mul_smul, smul_left_cancel_iff, flipBit_smul_eq_self]

theorem flipBitIndices_smul_ne_smul :
     (a.flipBitIndices i) • x ≠ a • x ↔ x < n ∧ x.flipBit i < n := by
  simp_rw [ne_eq, flipBitIndices_smul_eq_smul, not_or, not_le]

theorem getElem_flipBitIndices_ne_self_of_flipBit_lt {hk : k < n} (hk' : k.flipBit i < n) :
    (a.flipBitIndices i)[k] ≠ a[k] := by
  simp_rw [← smul_of_lt hk, flipBitIndices_smul_ne_smul]
  exact ⟨hk, hk'⟩

theorem getElem_flipBitVals_of_flipBit_lt {hk : k < n} (hk' : a[k].flipBit i < n) :
    (a.flipBitVals i)[k] = a[k].flipBit i := by
  simp_rw [flipBitVals_eq_flipBit_mul, getElem_mul, getElem_flipBit_of_flipBit_lt hk']

theorem getElem_flipBitVals_of_le_flipBit {hk : k < n} (hk' : n ≤ a[k].flipBit i) :
    (a.flipBitVals i)[k] = a[k] := by
  simp_rw [flipBitVals_eq_flipBit_mul, getElem_mul, getElem_flipBit_of_le_flipBit hk']

theorem flipBitVals_smul_eq_smul :
    (a.flipBitVals i) • x = a • x ↔ n ≤ x ∨ n ≤ (a • x).flipBit i := by
  simp_rw [flipBitVals_eq_flipBit_mul, mul_smul, flipBit_smul_eq_self, ← not_lt, smul_lt_iff_lt]

theorem flipBitVals_smul_ne_smul :
     (a.flipBitVals i) • x ≠ a • x ↔ x < n ∧ (a • x).flipBit i < n := by
  simp_rw [ne_eq, flipBitVals_smul_eq_smul, not_or, not_le]

theorem getElem_flipBitVals_ne_self_of_flipBit_lt {hk : k < n} (hk' : a[k].flipBit i < n) :
    (a.flipBitVals i)[k] ≠ a[k] := by
  simp_rw [← smul_of_lt hk, flipBitVals_smul_ne_smul, smul_of_lt hk]
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
theorem flipBit_mul_flipBit_of_le (hij : j ≤ i) :
    (flipBit i : VectorPerm n) * flipBit j = flipBit j * flipBit i := by
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
theorem natPerm_flipBit : natPerm n (flipBit i) =
    ofSubtype ((Nat.flipBitPerm i).subtypePerm (fun k => (k.flipBit_lt_iff_lt hin).symm)) := by
  ext k : 1
  simp_rw [natPerm_apply_apply]
  rcases lt_or_le k n with hk | hk
  · rw [Equiv.Perm.ofSubtype_subtypePerm_of_mem (p := fun i => i < n) _ hk]
    simp_rw [Nat.flipBitPerm_apply, smul_of_lt hk, getElem_flipBit, Nat.flipBit_lt_iff_lt hin,
      if_pos hk]
  · rw [Equiv.Perm.ofSubtype_subtypePerm_of_not_mem (p := fun i => i < n) _ hk.not_lt,
      smul_of_ge hk]

theorem ofPerm_flipBit :
    ofPerm (Nat.flipBitPerm i) (fun k => k.flipBit_lt_iff_lt hin) = flipBit i := by
  ext k hk : 1
  simp only [getElem_ofPerm, Nat.flipBitPerm_apply, getElem_flipBit, getElem_one,
  k.flipBit_lt_iff_lt hin, hk, ite_true]

end FlipBit

section CondFlipBit

def condFlipBitIndices (a : VectorPerm n) (i : ℕ) (c : Array Bool) : VectorPerm n where
  fwdVector := ⟨a.fwdVector.condFlipBitIndices i c (min c.size (n.testRes i)), by
    simp only [Array.size_condFlipBitIndices, Vector.size_toArray]⟩
  bwdVector := ⟨a.bwdVector.condFlipBitVals i c, by
    simp only [Array.size_condFlipBitVals, Vector.size_toArray]⟩
  getElem_fwdVector_lt' := fun _ => by
    have H : min c.size (a.fwdVector.size.testRes i) ≤ min c.size (n.testRes i) := by
      simp_rw [Vector.size_toArray, le_refl]
    simp_rw [Array.condFlipBitIndices_of_ge_min_size_testRes_size H, Vector.getElem_mk,
      Array.getElem_condFlipBitIndices_min_size_size_testRes,
      Vector.getElem_toArray, getElem_fwdVector]
    split_ifs <;> exact getElem_lt
  getElem_bwdVector_lt' := fun hk => by
    simp_rw [Vector.getElem_mk, Array.getElem_condFlipBitVals,
    Vector.getElem_toArray, getElem_bwdVector, Vector.size_toArray]
    split_ifs
    · assumption
    · exact getElem_lt
  left_inv' := fun {j} hk => by
    have H : min c.size (a.fwdVector.size.testRes i) ≤ min c.size (n.testRes i) := by
      simp_rw [Vector.size_toArray, le_refl]
    simp_rw [Vector.getElem_mk, Array.getElem_condFlipBitVals,
      Array.condFlipBitIndices_of_ge_min_size_testRes_size H,
      Array.getElem_condFlipBitIndices_min_size_size_testRes,
      Vector.getElem_toArray, getElem_fwdVector, getElem_bwdVector,
      Vector.size_toArray]
    by_cases hj : j.condFlipBit i c < n
    · simp_rw [hj, dite_true, getElem_inv_getElem, Nat.condFlipBit_condFlipBit_of_eq, hk, ite_true]
    · simp_rw [hj, dite_false, getElem_inv_getElem, hj, if_false]

def condFlipBitVals (a : VectorPerm n) (i : ℕ) (c : Array Bool) : VectorPerm n where
  fwdVector := ⟨a.fwdVector.condFlipBitVals i c, by
    simp only [Array.size_condFlipBitVals, Vector.size_toArray]⟩
  bwdVector := ⟨a.bwdVector.condFlipBitIndices i c (min c.size (n.testRes i)), by
    simp only [Array.size_condFlipBitIndices, Vector.size_toArray]⟩
  getElem_fwdVector_lt' := fun hk => by
    simp_rw [Vector.getElem_mk, Array.getElem_condFlipBitVals,
      Vector.getElem_toArray, getElem_fwdVector, Vector.size_toArray]
    split_ifs
    · assumption
    · exact getElem_lt
  getElem_bwdVector_lt' := fun _ => by
    have H : min c.size (a.bwdVector.size.testRes i) ≤ min c.size (n.testRes i) := by
      simp_rw [Vector.size_toArray, le_refl]
    simp_rw [Array.condFlipBitIndices_of_ge_min_size_testRes_size H, Vector.getElem_mk,
      Array.getElem_condFlipBitIndices_min_size_size_testRes, Vector.getElem_toArray, getElem_bwdVector]
    split_ifs <;> exact getElem_lt
  left_inv' := fun {j} hk => by
    have H : min c.size (a.bwdVector.size.testRes i) ≤ min c.size (n.testRes i) := by
      simp_rw [Vector.size_toArray, le_refl]
    simp_rw [Vector.getElem_mk, Array.getElem_condFlipBitVals,
      Array.condFlipBitIndices_of_ge_min_size_testRes_size H,
      Array.getElem_condFlipBitIndices_min_size_size_testRes, Vector.getElem_toArray, getElem_fwdVector, getElem_bwdVector,
      Vector.size_toArray]
    by_cases hj : a[j].condFlipBit i c < n
    · simp_rw [hj, ite_true, Nat.condFlipBit_condFlipBit_of_eq, getElem_lt,
        dite_true, getElem_inv_getElem]
    · simp_rw [hj, ite_false, hj, dite_false, getElem_inv_getElem]

variable {a : VectorPerm n} {i k : ℕ} {c : Array Bool}

theorem getElem_condFlipBitIndices {hk : k < n} :
    (a.condFlipBitIndices i c)[k] =
    if hk : k.condFlipBit i c < n then a[k.condFlipBit i c] else a[k] := by
  unfold condFlipBitIndices
  have H : min c.size (a.fwdVector.size.testRes i) ≤ min c.size (n.testRes i) := by
      simp_rw [Vector.size_toArray, le_refl]
  simp_rw [getElem_mk, Array.condFlipBitIndices_of_ge_min_size_testRes_size H, Vector.getElem_mk,
    Array.getElem_condFlipBitIndices_min_size_size_testRes,
    Vector.getElem_toArray, getElem_fwdVector, Vector.size_toArray]

theorem getElem_condFlipBitVals {hk : k < n} :
    (a.condFlipBitVals i c)[k] =
    if a[k].condFlipBit i c < n then a[k].condFlipBit i c else a[k] := by
  unfold condFlipBitVals
  simp_rw [getElem_mk, Vector.getElem_mk, Array.getElem_condFlipBitVals, Vector.getElem_toArray,
  getElem_fwdVector, Vector.size_toArray]

theorem getElem_inv_condFlipBitIndices {hk : k < n} :
    (a.condFlipBitIndices i c)⁻¹[k] =
    if a⁻¹[k].condFlipBit i c < n then a⁻¹[k].condFlipBit i c else a⁻¹[k] := by
  unfold condFlipBitIndices
  simp_rw [getElem_inv_mk, Vector.getElem_mk, Array.getElem_condFlipBitVals, Vector.getElem_toArray,
  getElem_bwdVector, Vector.size_toArray]

theorem getElem_inv_condFlipBitVals {hk : k < n} :
    (a.condFlipBitVals i c)⁻¹[k] =
    if hk : k.condFlipBit i c < n then a⁻¹[k.condFlipBit i c] else a⁻¹[k] := by
  unfold condFlipBitVals
  have H : min c.size (a.bwdVector.size.testRes i) ≤ min c.size (n.testRes i) := by
      simp_rw [Vector.size_toArray, le_refl]
  simp_rw [getElem_inv_mk, Array.condFlipBitIndices_of_ge_min_size_testRes_size H,
    Vector.getElem_mk,
    Array.getElem_condFlipBitIndices_min_size_size_testRes, Vector.getElem_toArray,
    getElem_bwdVector, Vector.size_toArray]

def condFlipBit (i : ℕ) (c : Array Bool) : VectorPerm n := (1 : VectorPerm n).condFlipBitIndices i c

theorem getElem_condFlipBit {hk : k < n} :
    (condFlipBit i c)[k] = if k.condFlipBit i c < n then k.condFlipBit i c else k := by
  unfold condFlipBit
  simp_rw [getElem_condFlipBitIndices, getElem_one, dite_eq_ite]

theorem getElem_inv_condFlipBit {hk : k < n} :
    (condFlipBit i c)⁻¹[k] = if k.condFlipBit i c < n then k.condFlipBit i c else k := by
  unfold condFlipBit
  simp_rw [getElem_inv_condFlipBitIndices, inv_one, getElem_one]

@[simp]
theorem condFlipBit_inv : (condFlipBit i c : VectorPerm n)⁻¹ = condFlipBit i c := by
  ext : 1
  simp_rw [getElem_condFlipBit, getElem_inv_condFlipBit]

@[simp]
theorem condFlipBit_mul_self : (condFlipBit i c : VectorPerm n) * condFlipBit i c = 1 := by
  rw [← eq_inv_iff_mul_eq_one, condFlipBit_inv]

@[simp]
theorem condFlipBit_mul_self_mul : condFlipBit i c * (condFlipBit i c * a) = a := by
  rw [← mul_assoc, condFlipBit_mul_self, one_mul]

@[simp]
theorem mul_condFlipBit_mul_self : a * condFlipBit i c * condFlipBit i c = a := by
  rw [mul_assoc, condFlipBit_mul_self, mul_one]

theorem condFlipBitIndices_eq_mul_condFlipBit (a : VectorPerm n) :
    a.condFlipBitIndices i c = a * condFlipBit i c := by
  ext k hk : 1
  simp only [getElem_condFlipBitIndices, getElem_condFlipBit, getElem_mul, getElem_one]
  split_ifs <;> try {rfl}

theorem condFlipBitVals_eq_condFlipBit_mul (a : VectorPerm n) :
    a.condFlipBitVals i c = condFlipBit i c * a := by
  ext k hk : 1
  simp only [getElem_condFlipBitVals, getElem_condFlipBit, getElem_mul, getElem_one]

@[simp]
theorem inv_condFlipBitVals {a : VectorPerm n} {i : ℕ} :
    a⁻¹.condFlipBitVals i c = (a.condFlipBitIndices i c)⁻¹ := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, condFlipBitVals_eq_condFlipBit_mul,
    mul_inv_rev, condFlipBit_inv]

@[simp]
theorem inv_condFlipBitIndices  {a : VectorPerm n} {i : ℕ} :
    a⁻¹.condFlipBitIndices i c = (a.condFlipBitVals i c)⁻¹ := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, condFlipBitVals_eq_condFlipBit_mul,
    mul_inv_rev, condFlipBit_inv]

theorem condFlipBitIndices_inv_eq_condFlipBit_mul (a : VectorPerm n) :
    (a.condFlipBitIndices i c)⁻¹ = condFlipBit i c * a⁻¹ := by
  rw [← inv_condFlipBitVals, condFlipBitVals_eq_condFlipBit_mul]

theorem condFlipBitVals_inv_eq_mul_condFlipBit (a : VectorPerm n) :
    (a.condFlipBitVals i c)⁻¹ = a⁻¹ * condFlipBit i c := by
  rw [← inv_condFlipBitIndices, condFlipBitIndices_eq_mul_condFlipBit]

@[simp]
theorem one_condFlipBitIndices : (1 : VectorPerm n).condFlipBitIndices i c = condFlipBit i c := by
  rw [condFlipBitIndices_eq_mul_condFlipBit, one_mul]

@[simp]
theorem one_condFlipBitVals : (1 : VectorPerm n).condFlipBitVals i c = condFlipBit i c := by
  rw [condFlipBitVals_eq_condFlipBit_mul, mul_one]

@[simp]
theorem mul_condFlipBitIndices : a * b.condFlipBitIndices i c = (a * b).condFlipBitIndices i c := by
  simp_rw [condFlipBitIndices_eq_mul_condFlipBit, mul_assoc]

@[simp]
theorem condFlipBitVals_mul : a.condFlipBitVals i c * b = (a * b).condFlipBitVals i c := by
  simp_rw [condFlipBitVals_eq_condFlipBit_mul, mul_assoc]

theorem condFlipBitVals_comm_condFlipBitIndices {d : Array Bool} :
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
theorem condFlipBit_mul_condFlipBit_of_lt {d : Array Bool}  :
    (condFlipBit i c : VectorPerm n) * condFlipBit i d = condFlipBit i d * condFlipBit i c := by
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
theorem natPerm_condFlipBit : natPerm n (condFlipBit i c) =
    ofSubtype ((Nat.condFlipBitPerm i c).subtypePerm
    (fun k => (k.condFlipBit_lt_iff_lt hin).symm)) := by
  ext k : 1
  simp_rw [natPerm_apply_apply]
  rcases lt_or_le k n with hk | hk
  · rw [Equiv.Perm.ofSubtype_subtypePerm_of_mem (p := fun i => i < n) _ hk]
    simp_rw [Nat.condFlipBitPerm_apply, smul_of_lt hk, getElem_condFlipBit,
      Nat.condFlipBit_lt_iff_lt hin, if_pos hk]
  · rw [Equiv.Perm.ofSubtype_subtypePerm_of_not_mem (p := fun i => i < n) _ hk.not_lt,
      smul_of_ge hk]

theorem ofPerm_condFlipBit :
    ofPerm (Nat.condFlipBitPerm i c)
    (fun k => k.condFlipBit_lt_iff_lt hin) = condFlipBit i c := by
  ext k hk : 1
  simp only [getElem_ofPerm, Nat.condFlipBitPerm_apply, getElem_condFlipBit, getElem_one,
  k.condFlipBit_lt_iff_lt hin, hk, ite_true]

end CondFlipBit

section FlipCommutator

def flipBitCommutator (a : VectorPerm n) (i : ℕ) : VectorPerm n :=
  (a.flipBitIndices i) * (a.flipBitVals i)⁻¹

variable {a : VectorPerm n} {i k : ℕ}

theorem flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv :
    (a.flipBitCommutator i) = (a.flipBitIndices i) * (a.flipBitVals i)⁻¹ := rfl

theorem flipBitCommutator_eq_flipBitIndices_mul_flipBitIndices :
    (a.flipBitCommutator i) = (a.flipBitIndices i) * (a⁻¹.flipBitIndices i) := by
  rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv, inv_flipBitIndices]

theorem flipBitCommutator_inv_eq_flipBitVals_mul_flipBitVals :
    (a.flipBitCommutator i)⁻¹ = (a.flipBitVals i) * (a⁻¹.flipBitVals i) := by
  rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv, mul_inv_rev, inv_inv,
  inv_flipBitVals]

theorem flipBitCommutator_eq_commutatorElement :
    (a.flipBitCommutator i) = ⁅a, flipBit i⁆ := by
  simp_rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv,
  commutatorElement_def, flipBitIndices_eq_mul_flipBit, flipBitVals_eq_flipBit_mul,
  mul_inv_rev, mul_assoc]

theorem flipBitCommutator_inv_eq_commutatorElement :
    (a.flipBitCommutator i)⁻¹ = ⁅(flipBit i : VectorPerm n), a⁆ := by
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

lemma flipBitCommutator_smul_eq_flipBit :
    (a.flipBitCommutator i) • k = (flipBit i : VectorPerm n) • k ↔
    n ≤ k ∨ n ≤ (a⁻¹ • (flipBit i : VectorPerm n) • k).flipBit i := by
  simp_rw [flipBitCommutator_eq_commutatorElement, commutatorElement_def, mul_smul,
    ← eq_inv_smul_iff (g := a), flipBit_inv, flipBit_smul_eq_self, ← not_lt, smul_lt_iff_lt]

lemma flipBitCommutator_smul_ne_flipBit :
    (a.flipBitCommutator i) • k ≠ (flipBit i : VectorPerm n) • k ↔
    k < n ∧ (a⁻¹ • (flipBit i : VectorPerm n) • k).flipBit i < n := by
  simp_rw [ne_eq, flipBitCommutator_smul_eq_flipBit, not_or, not_le]

lemma getElem_flipBitCommutator_ne_flipBit {hk : k < n}
    (hk' : (a⁻¹ • (flipBit i : VectorPerm n) • k).flipBit i < n) :
    (a.flipBitCommutator i)[k] ≠ (flipBit i : VectorPerm n)[k] := by
  simp_rw [← smul_of_lt hk, flipBitCommutator_smul_ne_flipBit]
  exact ⟨hk, hk'⟩

lemma flipBitCommutator_flipBitIndices_smul_eq_self :
    (a.flipBitCommutator i).flipBitIndices i • k = k ↔ n ≤ k ∨ n ≤ (a⁻¹ • k).flipBit i := by
  simp_rw [flipBitCommutator_eq_flipBitIndices_mul_flipBitIndices, mul_flipBitIndices,
    flipBitIndices_flipBitIndices_of_eq, flipBitIndices_eq_mul_flipBit, mul_smul,
    ← eq_inv_smul_iff (g := a), flipBit_smul_eq_self, ← not_lt, smul_lt_iff_lt]

lemma flipBitCommutator_flipBitIndices_smul_ne_self :
    (a.flipBitCommutator i).flipBitIndices i • k ≠ k ↔ k < n ∧ (a⁻¹ • k).flipBit i < n := by
  simp_rw [ne_eq, flipBitCommutator_flipBitIndices_smul_eq_self, not_or, not_le]

lemma getElem_flipBitCommutator_flipBitIndices_ne_self {hk : k < n}
    (hk' : (a⁻¹ • k).flipBit i < n) : ((a.flipBitCommutator i).flipBitIndices i)[k] ≠ k := by
  simp_rw [← smul_of_lt hk, flipBitCommutator_flipBitIndices_smul_ne_self]
  exact ⟨hk, hk'⟩

lemma flipBitCommutator_flipBitVals_smul_eq_self :
    (a.flipBitCommutator i).flipBitVals i • k = k ↔
    n ≤ k ∨ n ≤ (a⁻¹ • (flipBit i : VectorPerm n) • k).flipBit i := by
  simp_rw [flipBitCommutator_eq_commutatorElement, commutatorElement_def, mul_flipBitVals,
    flipBitVals_eq_flipBit_mul, mul_smul, ← eq_inv_smul_iff (g := (flipBit i)),
    ← eq_inv_smul_iff (g := a), flipBit_smul_eq_self, ← not_lt, smul_lt_iff_lt, flipBit_inv]

lemma flipBitCommutator_flipBitVals_smul_ne_self :
    (a.flipBitCommutator i).flipBitVals i • k ≠ k ↔ k < n ∧
      (a⁻¹ • (flipBit i : VectorPerm n) • k).flipBit i < n := by
  simp_rw [ne_eq, flipBitCommutator_flipBitVals_smul_eq_self, not_or, not_le]

lemma getElem_flipBitCommutator_flipBitVals_ne_self {hk : k < n}
    (hk' : (a⁻¹ • (flipBit i : VectorPerm n) • k).flipBit i < n) :
    ((a.flipBitCommutator i).flipBitVals i)[k] ≠ k := by
  simp_rw [← smul_of_lt hk, flipBitCommutator_flipBitVals_smul_ne_self]
  exact ⟨hk, hk'⟩

variable (hin : 2^(i + 1) ∣ n)

include hin

@[simp]
theorem getElem_flipBitCommutator_of_div {hk : k < n} :
    (a.flipBitCommutator i)[k] =
      a[(a⁻¹[k.flipBit i]'((k.flipBit_lt_iff_lt hin).mpr hk)).flipBit i]'
      ((Nat.flipBit_lt_iff_lt hin).mpr getElem_lt) := by
  simp_rw [getElem_flipBitCommutator, Nat.flipBit_lt_iff_lt hin, getElem_lt, hk, dite_true]

@[simp]
theorem getElem_inv_flipBitCommutator_of_div {hk : k < n} :
    (a.flipBitCommutator i)⁻¹[k] = (a[a⁻¹[k].flipBit i]'
    ((Nat.flipBit_lt_iff_lt hin).mpr getElem_lt) ).flipBit i := by
  simp_rw [getElem_inv_flipBitCommutator, Nat.flipBit_lt_iff_lt hin, hk,
  getElem_lt, dite_true, if_true]

lemma getElem_flipBitIndices_flipBitCommutator {hk : k < n} :
    ((a.flipBitCommutator i).flipBitIndices i)[k] =
    (a.flipBitCommutator i)⁻¹[k].flipBit i := by
  simp_rw [← inv_flipBitCommutator_flipBitVals, getElem_flipBitVals_of_div hin]

lemma getElem_flipBitIndices_flipBitCommutator_inv {hk : k < n} :
    ((a.flipBitCommutator i)⁻¹.flipBitIndices i)[k] =
    (a.flipBitCommutator i)[k].flipBit i := by
  rw [inv_flipBitCommutator_flipBitIndices, getElem_flipBitVals_of_div hin]

lemma getElem_flipBitIndices_flipBitCommutator_pow_inv {hk : k < n} :
    (((a.flipBitCommutator i)^p)⁻¹.flipBitIndices i)[k] =
    ((a.flipBitCommutator i)^p)[k].flipBit i := by
  rw [inv_flipBitCommutator_pow_flipBitIndices, getElem_flipBitVals_of_div hin]

lemma getElem_flipBit_flipBitCommutator_pow {hk : k < n} :
    (((a.flipBitCommutator i)^p).flipBitIndices i)[k] =
    ((a.flipBitCommutator i)^p)⁻¹[k].flipBit i := by
  rw [← inv_flipBitCommutator_pow_flipBitVals, getElem_flipBitVals_of_div hin]

lemma getElem_flipBit_flipBitCommutator_zpow_inv {p : ℤ} {hk : k < n} :
    (((a.flipBitCommutator i)^p)⁻¹.flipBitIndices i)[k] =
    ((a.flipBitCommutator i)^p)[k].flipBit i := by
  rw [inv_flipBitCommutator_zpow_flipBitIndices, getElem_flipBitVals_of_div hin]

lemma getElem_flipBit_flipBitCommutator_zpow {p : ℤ} {hk : k < n} :
    (((a.flipBitCommutator i)^p).flipBitIndices i)[k] =
    ((a.flipBitCommutator i)^p)⁻¹[k].flipBit i := by
  rw [← inv_flipBitCommutator_zpow_flipBitVals, getElem_flipBitVals_of_div hin]

lemma getElem_flipBitCommutator_ne_flipBit_of_div {hk : k < n} :
    (a.flipBitCommutator i)[k] ≠ k.flipBit i := by
  simp_rw [← getElem_flipBit_of_div hin (hk := hk), ← smul_of_lt hk,
  flipBitCommutator_smul_ne_flipBit, Nat.flipBit_lt_iff_lt hin, smul_lt_iff_lt, and_self, hk]

lemma getElem_flipBitCommutator_flipBit_ne {hk : k < n} :
    (a.flipBitCommutator i)[k].flipBit i ≠ k := by
  simp_rw [← getElem_flipBitVals_of_div hin, ← smul_of_lt hk,
    flipBitCommutator_flipBitVals_smul_ne_self, Nat.flipBit_lt_iff_lt hin, smul_lt_iff_lt,
    and_self, hk]

lemma getElem_pow_flipBitCommutator_ne_flipBit {hk : k < n} {p : ℕ} :
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

lemma getElem_flipBitCommutator_pow_flipBit_ne {hk : k < n} {p : ℕ} :
    ((a.flipBitCommutator i) ^ p)[k].flipBit i ≠ k := by
  intros H
  apply (a.getElem_pow_flipBitCommutator_ne_flipBit hin (hk := hk) (p := p))
  nth_rewrite 2 [← H]
  simp_rw [Nat.flipBit_flipBit_of_eq]

lemma getElem_zpow_flipBitCommutator_ne_flipBit {hk : k < n} {p : ℤ} :
    ((a.flipBitCommutator i) ^ p)[k] ≠ k.flipBit i := by
  cases p
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact getElem_pow_flipBitCommutator_ne_flipBit hin
  · have hk' : k.flipBit i < n := by rwa [Nat.flipBit_lt_iff_lt hin]
    simp_rw [zpow_negSucc, getElem_inv_ne_iff _ _ hk']
    exact (Nat.flipBit_flipBit_of_eq (i := i)).symm.trans_ne
      (getElem_pow_flipBitCommutator_ne_flipBit hin).symm

lemma getElem_flipBitCommutator_zpow_flipBit_ne {hk : k < n} {p : ℤ} :
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
  · simp_rw [smul_of_lt hk]
    exact fun _ _ => getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow hin
  · simp_rw [smul_of_ge hk]
    exact fun _ _ => Nat.flipBit_ne_self.symm

lemma two_mul_filter_sameCycle_card_le_card (s : Finset ℕ)
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

end FlipCommutator

end VectorPerm

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

namespace VectorPerm

theorem getElem_testBit (a : VectorPerm n) {k : ℕ} (h : n ≤ 2^k) {i : ℕ} (hi : i < n) :
    a[i].testBit k = false :=
  Nat.testBit_eq_false_of_lt <| (a.getElem_lt).trans_le h

open Nat Array

def BitInvariant (i : ℕ) (a : VectorPerm n) : Prop :=
  a.fwdVector.map (testBit · i) = (Vector.range n).map (testBit · i)

variable {a b : VectorPerm n}

theorem one_bitInvariant : BitInvariant i (1 : VectorPerm n) := rfl

theorem bitInvariant_iff_testBit_getElem_eq_testBit : a.BitInvariant i ↔
    ∀ {x} (h : x < n), a[x].testBit i = x.testBit i := by
  unfold BitInvariant
  simp_rw [Vector.ext_iff]
  simp_rw [Vector.getElem_map, getElem_fwdVector, Vector.getElem_range]

theorem bitInvariant_of_ge (h : n ≤ 2^i) : a.BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, a.getElem_testBit h]
  exact fun (hx : _ < n) => (Nat.testBit_eq_false_of_lt (hx.trans_le h)).symm

theorem bitInvariant_of_ge_of_ge (h : n ≤ 2^i) (hk : i ≤ k) : a.BitInvariant k :=
  bitInvariant_of_ge (h.trans (Nat.pow_le_pow_right zero_lt_two hk))

theorem forall_lt_bitInvariant_iff_eq_one_of_ge (hin : n ≤ 2^i) :
    (∀ k < i, a.BitInvariant k) ↔ a = 1 := by
  refine ⟨fun h => VectorPerm.ext ?_, fun h _ _ => h ▸ one_bitInvariant⟩
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
  rw [← ha.testBit_getElem_eq_testBit getElem_lt, getElem_getElem_inv]

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

theorem bitInvariant_iff_smul_bitInvariant :
    a.BitInvariant i ↔ (a • ·).BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, Function.bitInvariant_iff,
    smul_nat_eq_dite, apply_dite (testBit · i), dite_eq_right_iff]

theorem BitInvariant.flipBitCommutator (ha : a.BitInvariant i) {j : ℕ} (hjn : 2 ^ (j + 1) ∣ n) :
    (a.flipBitCommutator j).BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, getElem_flipBitCommutator_of_div hjn,
  ha.testBit_getElem_eq_testBit, testBit_flipBit,
  ha.inv.testBit_getElem_eq_testBit, testBit_flipBit, Bool.xor, Bool.xor_assoc,
  Bool.xor_self, Bool.xor_false, implies_true]

def BitInvariantEQ (i : ℕ) : Subgroup (VectorPerm n) where
  carrier := BitInvariant i
  mul_mem' := BitInvariant.mul
  one_mem' := one_bitInvariant
  inv_mem' := BitInvariant.inv

@[simp]
theorem mem_bitInvariantEQ_iff : a ∈ BitInvariantEQ i ↔ a.BitInvariant i := Iff.rfl

theorem mem_bitInvariantEQ_iff_smul_bitInvariant :
  a ∈ BitInvariantEQ i ↔ (a • ·).BitInvariant i := bitInvariant_iff_smul_bitInvariant

def BitInvariantLT (i : ℕ) : Subgroup (VectorPerm n) :=
  ⨅ (k : ℕ) (_ : k < i), BitInvariantEQ k

theorem mem_bitInvariantLT_iff : a ∈ BitInvariantLT i ↔ ∀ k < i, a ∈ BitInvariantEQ k := by
  unfold BitInvariantLT
  simp_rw [Subgroup.mem_iInf]

theorem mem_bitInvariantLT_iff_smul_bitInvariant :
    a ∈ BitInvariantLT i ↔ (a • ·).BitInvariantLT i := by
  simp_rw [mem_bitInvariantLT_iff, Function.bitInvariantLT_iff,
  mem_bitInvariantEQ_iff_smul_bitInvariant]

def BitInvariantGE (i : ℕ) : Subgroup (VectorPerm n) :=
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
    (BitInvariantGE i : Subgroup (VectorPerm n)) = ⊤ := by
  ext
  simp_rw [Subgroup.mem_top, iff_true, mem_bitInvariantGE_of_ge h]

theorem bitInvariantLT_iff_eq_one_of_ge (h : n ≤ 2^i) : a ∈ BitInvariantLT i ↔ a = 1 := by
  simp_rw [mem_bitInvariantLT_iff, mem_bitInvariantEQ_iff,
  forall_lt_bitInvariant_iff_eq_one_of_ge h]

theorem bitInvariantLT_eq_bot_of_ge (h : n ≤ 2^i) :
    (BitInvariantLT i : Subgroup (VectorPerm n)) = ⊥ := by
  ext
  simp_rw [Subgroup.mem_bot, bitInvariantLT_iff_eq_one_of_ge h]

theorem cycleOf_subset_bitMatchTo {x : ℕ} (a : VectorPerm n) (ha : ∀ k < i, a.BitInvariant k)
    (hk : x < n) (hn : n ≤ 2^j) : a.cycleOf x ⊆ bitMatchTo x j i := by
  simp_rw [Finset.subset_iff, mem_cycleOf_iff_exists_getElem_zpow _ hk, mem_bitMatchTo_iff,
    forall_exists_index, forall_apply_eq_imp_iff, getElem_lt.trans_le hn,
    true_and]
  intros _ _ hk
  exact ((ha _ hk).zpow _).testBit_getElem_eq_testBit _

theorem period_le_two_pow (a : VectorPerm n) (k : ℕ) (hin : 2 ^ (i + 1) ∣ n) (hn : n ≤ 2^(j + 1))
    (ha : ∀ k < i, a.BitInvariant k) (hij : i ≤ j) :
    MulAction.period (a.flipBitCommutator i) k ≤ 2 ^ (j - i) := by
  rcases lt_or_le k n with hk | hk
  · trans ((bitMatchTo k (j + 1) i).card / 2)
    · apply two_mul_filter_sameCycle_card_le_card hin
      · exact flipBit_mem_bitMatchTo ⟨le_rfl, Nat.lt_succ_of_le hij⟩
      · exact (a.flipBitCommutator i).cycleOf_subset_bitMatchTo
          (fun _ hl => (ha _ hl).flipBitCommutator hin) hk hn
    · rw [card_bitMatchInRange_eq_of_le _ (hij.trans <| Nat.le_succ _), Nat.succ_sub hij,
      pow_succ, Nat.mul_div_cancel _ (zero_lt_two)]
  · rw [period_eq_one_of_ge hk]
    exact Nat.one_le_pow _ _ zero_lt_two

lemma flipBitCommutator_cycleMin_flipBit_eq_flipBit_cycleMin_flipBitCommutator
    (hin : 2 ^ (i + 1) ∣ n) (hn : n ≤ 2^(j + 1))
    (ha : ∀ k < i, BitInvariant k a) (hij : i ≤ j) {k : ℕ} :
    ((a.flipBitCommutator i).CycleMin (j - i)) (k.flipBit i) =
    ((a.flipBitCommutator i).CycleMin (j - i) k).flipBit i := by
  rcases lt_or_le k n with hk | hk
  · have hk' := (Nat.flipBit_lt_iff_lt hin).mpr hk
    rw [cycleMin_eq_min'_cycleOf _ _ (period_le_two_pow _ k hin hn ha hij),
    cycleMin_eq_min'_cycleOf _ _ (period_le_two_pow _ (k.flipBit i) hin hn ha hij)]
    · have H := Finset.min'_mem ((a.flipBitCommutator i).cycleOf k) nonempty_cycleOf
      simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hk] at H
      rcases H with ⟨p, hp⟩
      refine eq_of_le_of_not_lt ?_ ?_
      · refine Finset.min'_le _ _ ?_
        simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hk']
        exact ⟨-p, by simp_rw [← hp, ← a.getElem_flipBit_flipBitCommutator_zpow_inv hin (hk := hk),
          zpow_neg, getElem_flipBitIndices_of_div hin]⟩
      · have H := Finset.min'_mem
          ((a.flipBitCommutator i).cycleOf (k.flipBit i)) nonempty_cycleOf
        simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hk',
        ← getElem_flipBit_of_div hin (hk := hk), ← getElem_mul,
        ← flipBitIndices_eq_mul_flipBit, getElem_flipBit_of_div hin (hk := hk)] at H
        rcases H with ⟨q, hq⟩
        simp_rw [a.getElem_flipBit_flipBitCommutator_zpow hin, ← zpow_neg] at hq
        rcases (Finset.min'_le _ _ ((a.flipBitCommutator i).getElem_zpow_mem_cycleOf
          hk (-q))).eq_or_lt with H | H
        · rw [H, hq]
          exact lt_irrefl _
        · rw [← hq, ← hp]
          rw [← hp] at H
          intro h
          refine getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow
            hin <| Nat.eq_flipBit_of_lt_of_flipBit_ge_of_lt_testBit_eq H h.le (fun hji => ?_)
          simp_rw [(((ha _ hji).flipBitCommutator hin).zpow p).testBit_getElem_eq_testBit,
            (((ha _ hji).flipBitCommutator hin).zpow (-(q : ℤ))).testBit_getElem_eq_testBit]
  · simp_rw [cycleMin_of_ge hk, cycleMin_of_ge <| le_of_not_lt <|
    (Nat.flipBit_lt_iff_lt hin).not.mpr hk.not_lt]

lemma flipBit_getElem_cycleMinArray_flipBitCommutator_eq_getElem_flipBit_cycleMinArray_flipBitCommutator
    (hin : 2 ^ (i + 1) ∣ n) (hn : n ≤ 2^(j + 1))
    (ha : ∀ k < i, BitInvariant k a) (hij : i ≤ j) {k : ℕ}
    (hk : k < n):
    (((a.flipBitCommutator i).CycleMinVector (j - i))[k]).flipBit i
    = ((a.flipBitCommutator i).CycleMinVector (j - i))[(k.flipBit i)]'
      (by rwa [flipBit_lt_iff_lt <| hin.trans (dvd_of_eq rfl)]) := by
  simp_rw [getElem_cycleMinVector]
  exact (flipBitCommutator_cycleMin_flipBit_eq_flipBit_cycleMin_flipBitCommutator hin hn ha
  hij).symm

end VectorPerm

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
