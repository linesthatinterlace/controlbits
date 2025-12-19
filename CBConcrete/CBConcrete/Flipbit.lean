import CBConcrete.PermOf.BitInvariant
import CBConcrete.RemoveInsert

namespace Nat

section FlipBit

variable {p q b i j k n m : ℕ} {b : Bool}

def flipBit (q i : ℕ) := q ^^^ 1 <<< i

@[grind =]
theorem flipBit_def : ∀ (i q : ℕ), q.flipBit i = q ^^^ 1 <<< i := fun _ _ => rfl

-- inductive theorems

theorem flipBit_zero : q.flipBit 0 = bit (!q.bodd) q.div2 := by
  cases q using bitCasesOn with | bit b q => _
  simp_rw [flipBit_def, shiftLeft_zero, div2_bit, bodd_bit]
  refine (xor_bit b q true 0).trans ?_
  simp_rw [Bool.bne_true, xor_zero]

theorem flipBit_succ : q.flipBit i.succ = bit q.bodd (q.div2.flipBit i) := by
  cases q using bitCasesOn with | bit b q => _
  simp_rw [flipBit_def, shiftLeft_succ, div2_bit, bodd_bit]
  refine (xor_bit b q false (1 <<< i)).trans ?_
  simp_rw [Bool.bne_false]

-- testBit_flipBit

theorem testBit_flipBit : (q.flipBit j).testBit i = (q.testBit i).xor (i = j) := by
  simp_rw [flipBit_def, testBit_xor, testBit_shiftLeft, testBit_one, Nat.sub_eq_zero_iff_le,
    le_antisymm_iff (a := i), Bool.decide_and, Bool.and_comm]

@[simp, grind =]
theorem testBit_flipBit_of_eq : (q.flipBit i).testBit i = !(q.testBit i) := by
  simp_rw [testBit_flipBit, decide_true, Bool.xor_true]

@[grind =]
theorem testBit_flipBit_of_ne {i j : ℕ} (hij : i ≠ j) :
    (q.flipBit j).testBit i = q.testBit i := by
  simp_rw [testBit_flipBit, hij, decide_false, Bool.xor_false]

-- representations of flipBit

@[grind =]
theorem flipBit_apply {i : ℕ} :
    q.flipBit i = (q.removeBit i).insertBit (!(testBit q i)) i := by
  simp_rw [Nat.testBit_eq_iff]
  intro j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [testBit_flipBit_of_ne hij.ne', testBit_insertBit_of_gt hij, testBit_pred_removeBit_of_gt hij]
  · rw [testBit_flipBit_of_eq, testBit_insertBit_of_eq]
  · rw [testBit_flipBit_of_ne hij.ne, testBit_insertBit_of_lt hij, testBit_removeBit_of_lt hij]

theorem flipBit_eq_of_testBit_false {i : ℕ} (hqi : q.testBit i = false) :
    q.flipBit i = (q.removeBit i).insertBit true i := by
  rw [flipBit_apply, hqi, Bool.not_false]

theorem flipBit_eq_of_testBit_true {i : ℕ} (hqi : q.testBit i = true) :
    q.flipBit i = (q.removeBit i).insertBit false i := by
  rw [flipBit_apply, hqi, Bool.not_true]

theorem flipBit_eq_cond {i : ℕ} : q.flipBit i = if testBit q i then q - 2^i else q + 2^i := by
  rw [flipBit_apply, insertBit_not_testBit_removeBit_of_eq]

-- flipBit equalities and inequalities

theorem flipBit_div_two_pow_eq {i : ℕ} (h : i < k) : q.flipBit i / 2^k = q / 2^k := by
  simp_rw [testBit_eq_iff, testBit_div_two_pow,
  testBit_flipBit_of_ne (h.trans_le (Nat.le_add_left _ _)).ne', implies_true]

theorem flipBit_mod_two_pow_eq {i : ℕ} (h : k ≤ i) : q.flipBit i % 2^k = q % 2^k := by
  simp_rw [testBit_eq_iff, testBit_mod_two_pow]
  intro j
  rcases eq_or_ne j i with rfl | hji
  · simp_rw [h.not_gt, decide_false, Bool.false_and]
  · simp_rw [testBit_flipBit_of_ne hji]

theorem flipBit_modEq_two_pow (h : k ≤ i) : q.flipBit i ≡ q [MOD 2^k] := flipBit_mod_two_pow_eq h

@[simp, grind =]
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
    q ∈ Finset.bitMatchUnder i x → q.flipBit k ∈ Finset.bitMatchUnder i x := by
  simp_rw [Finset.mem_bitMatchUnder_iff,
    Nat.flipBit_lt_iff_lt (Nat.pow_dvd_pow _ ( Nat.succ_le_of_lt hk.2)),
    testBit_flipBit]
  exact And.imp_right (fun hq _ hjk => by
    simp_rw [hq _ hjk, (hjk.trans_le hk.1).ne, decide_false, Bool.xor_false])

theorem flipBit_removeBit_of_lt (hij : i < j):
    (q.removeBit j).flipBit i = (q.flipBit i).removeBit j := by
  simp_rw [flipBit_apply, removeBit_removeBit_of_lt hij, testBit_removeBit_of_lt hij,
  removeBit_insertBit_of_gt hij]

theorem flipBit_removeBit_of_ge (hij : j ≤ i):
    (q.removeBit j).flipBit i = (q.flipBit (i + 1)).removeBit j := by
  simp_rw [flipBit_apply, removeBit_removeBit_of_ge hij, testBit_removeBit_of_ge hij,
  insertBit_removeBit_of_ge hij]

theorem flipBit_removeBit :
    (q.removeBit j).flipBit i = (q.flipBit (i + (decide (j ≤ i)).toNat)).removeBit j := by
  rcases lt_or_ge i j with hij | hij
  · simp_rw [flipBit_removeBit_of_lt hij, hij.not_ge, decide_false, Bool.toNat_false, add_zero]
  · simp_rw [flipBit_removeBit_of_ge hij, hij, decide_true, Bool.toNat_true]

-- removeBit_flipBit

theorem removeBit_flipBit_of_gt (hij : j < i):
    (q.flipBit j).removeBit i = (q.removeBit i).flipBit j := (flipBit_removeBit_of_lt hij).symm

theorem removeBit_flipBit_of_lt (hij : i < j):
    (q.flipBit j).removeBit i = (q.removeBit i).flipBit (j - 1) := by
  rw [flipBit_removeBit_of_ge (Nat.le_sub_one_of_lt hij), Nat.sub_add_cancel (one_le_of_lt hij)]

theorem removeBit_flipBit_of_ne (hij : i ≠ j) :
    (q.flipBit j).removeBit i = (q.removeBit i).flipBit (j - (decide (i < j)).toNat) := by
  rcases hij.lt_or_gt with hij | hij
  · simp only [removeBit_flipBit_of_lt hij, hij, decide_true, Bool.toNat_true]
  · simp only [removeBit_flipBit_of_gt hij, hij, not_lt_of_gt,
    decide_false, Bool.toNat_false, Nat.sub_zero]

@[simp, grind =]
theorem removeBit_flipBit_of_eq : (q.flipBit i).removeBit i = q.removeBit i := by
  rw [flipBit_apply, removeBit_insertBit_of_eq]

theorem removeBit_flipBit : (q.flipBit j).removeBit i = bif i = j then q.removeBit i else
    (q.removeBit i).flipBit (j - (decide (i < j)).toNat) := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [removeBit_flipBit_of_eq, decide_true, cond_true]
  · simp_rw [removeBit_flipBit_of_ne hij, hij, decide_false, cond_false]

-- flipBit_insertBit

theorem flipBit_insertBit_of_eq : (p.insertBit b i).flipBit i = p.insertBit (!b) i := by
  rw [flipBit_apply, testBit_insertBit_of_eq, removeBit_insertBit_of_eq]

theorem flipBit_insertBit_of_lt (hij : i < j) :
    (p.insertBit b j).flipBit i = (p.flipBit i).insertBit b j := by
  rw [flipBit_apply, flipBit_apply, testBit_insertBit_of_lt hij,
  removeBit_insertBit_of_lt hij, insertBit_insertBit_pred_of_lt hij]

theorem flipBit_insertBit_of_gt (hij : j < i) :
    (p.insertBit b j).flipBit i = (p.flipBit (i - 1)).insertBit b j := by
  rw [flipBit_apply, flipBit_apply, testBit_insertBit_of_gt hij,
  removeBit_insertBit_of_gt hij, insertBit_insertBit_pred_of_lt hij]

theorem flipBit_insertBit_of_ne (hij : i ≠ j) :
    (p.insertBit b j).flipBit i = (p.flipBit (i - (decide (j < i)).toNat)).insertBit b j := by
  rcases hij.lt_or_gt with hij | hij
  · simp_rw [flipBit_insertBit_of_lt hij, hij.not_gt, decide_false, Bool.toNat_false,
    Nat.sub_zero]
  · simp_rw [flipBit_insertBit_of_gt hij, hij, decide_true, Bool.toNat_true]

theorem flipBit_insertBit :
    (p.insertBit b j).flipBit i = if i = j then p.insertBit (!b) i else
    (p.flipBit (i - (decide (j < i)).toNat)).insertBit b j := by
  rcases eq_or_ne i j with rfl | hij
  · simp_rw [flipBit_insertBit_of_eq, if_true]
  · simp_rw [flipBit_insertBit_of_ne hij, hij, if_false]

-- properties of flipBit

theorem ne_of_testBit_eq_not_testBit {r : ℕ} (i : ℕ)(h : q.testBit i = !r.testBit i) :
    q ≠ r := by
  rw [testBit_ne_iff]
  exact ⟨i, h ▸ Bool.not_ne_self _⟩

theorem ne_of_not_testBit_eq_iff {r : ℕ} (i : ℕ) (h : (!q.testBit i) = r.testBit i) :
    q ≠ r := by
  rw [testBit_ne_iff]
  exact ⟨i, h ▸ Bool.self_ne_not _⟩

theorem ne_flipBit_of_testBit_eq {r : ℕ} (h : q.testBit i = r.testBit i) : q ≠ r.flipBit i :=
  ne_of_not_testBit_eq_iff i (h ▸ testBit_flipBit_of_eq.symm)

theorem flipBit_ne_of_testBit_eq {r : ℕ} (h : q.testBit i = r.testBit i) : q.flipBit i ≠ r :=
  ne_of_testBit_eq_not_testBit i (h ▸ testBit_flipBit_of_eq)

theorem removeBit_lt_removeBit_iff {r : ℕ} :
    q.removeBit i < r.removeBit i ↔
    (q < r ∧ q.testBit i = r.testBit i) ∨ (q < r.flipBit i ∧ q.testBit i = !r.testBit i) := by
  rw [removeBit_lt_iff]
  rcases Bool.eq_or_eq_not (q.testBit i) (r.testBit i) with hqr | hqr
  · simp_rw [hqr, insertBit_testBit_removeBit_of_eq,
      Bool.eq_not_self, and_true, and_false, or_false]
  · simp_rw [hqr, ← flipBit_apply, Bool.not_eq_self, and_true, and_false, false_or]

theorem removeBit_eq_removeBit_iff {r : ℕ} :
    q.removeBit i = r.removeBit i ↔ q = r ∨ q = r.flipBit i := by
  rw [removeBit_eq_iff]
  rcases Bool.eq_or_eq_not (q.testBit i) (r.testBit i) with hqr | hqr
  · simp_rw [hqr, insertBit_testBit_removeBit_of_eq, ne_flipBit_of_testBit_eq hqr, or_false]
  · simp_rw [hqr, flipBit_apply, ne_of_testBit_eq_not_testBit i hqr, false_or]

theorem removeBit_le_removeBit_iff {r : ℕ} :
    q.removeBit i ≤ r.removeBit i ↔
    (q ≤ r ∧ q.testBit i = r.testBit i) ∨ (q ≤ r.flipBit i ∧ q.testBit i = !r.testBit i) := by
  simp_rw [le_iff_lt_or_eq, or_and_right, removeBit_eq_removeBit_iff, removeBit_lt_removeBit_iff]
  rw [or_or_or_comm]
  exact or_congr
    (or_congr Iff.rfl (iff_self_and.mpr (fun h => h ▸ rfl)))
    (or_congr Iff.rfl (iff_self_and.mpr (fun h => h ▸ testBit_flipBit_of_eq)))

@[grind =]
theorem flipBit_lt_iff_lt_flipBit_of_testBit_eq_not_testBit {r : ℕ}
    (h : q.testBit i ≠ r.testBit i) : q.flipBit i < r ↔ q < r.flipBit i := by
  simp_rw [flipBit_apply, Bool.not_eq.mpr h, ← Bool.eq_not.mpr h,
    ← removeBit_lt_iff, ← lt_removeBit_iff]

@[simp, grind =]
theorem flipBit_flipBit_of_eq : (q.flipBit i).flipBit i = q := by
  simp_rw [flipBit_def, Nat.xor_xor_cancel_right]

theorem flipBit_lt_flipBit_iff_lt_of_testBit_eq_iff {q r : ℕ}
    (h : q.testBit i = r.testBit i) : q.flipBit i < r.flipBit i ↔ q < r := by
  rw [flipBit_lt_iff_lt_flipBit_of_testBit_eq_not_testBit
    (testBit_flipBit_of_eq ▸ (Bool.not_eq_not.mpr h)), flipBit_flipBit_of_eq]

theorem insertBit_true_removeBit_lt_iff {r : ℕ} :
    (p.removeBit i).insertBit true i < r ↔ (p < r ∧ p.flipBit i < r) := by grind

theorem flipBit_flipBit (i j) : (q.flipBit i).flipBit j = (q.flipBit j).flipBit i := by
  simp_rw [testBit_eq_iff, testBit_flipBit, Bool.xor_assoc, Bool.xor_comm, implies_true]

@[simp, grind .]
theorem flipBit_ne_self : q.flipBit i ≠ q := by
  simp_rw [ne_eq, testBit_eq_iff, not_forall]
  exact ⟨i, by simp_rw [testBit_flipBit_of_eq, Bool.not_eq_self, not_false_eq_true]⟩

@[simp]
theorem self_ne_flipBit : q ≠ q.flipBit i := flipBit_ne_self.symm

theorem testBit_eq_false_true_of_lt_of_flipBit_ge {r : ℕ} (hrq : r < q)
    (hf : q.flipBit i ≤ r.flipBit i) : r.testBit i = false ∧ q.testBit i = true := by
  simp_rw [flipBit_eq_cond] at hf
  rcases hr : r.testBit i <;> rcases hq : q.testBit i <;> try grind
  simp_rw [hq, hr, ite_true, tsub_le_iff_right, Nat.sub_add_cancel (ge_two_pow_of_testBit hr)] at hf
  grind

theorem testBit_eq_of_le_of_flipBit_lt_ge {r : ℕ} (hrq : r ≤ q)
    (hf : q.flipBit i ≤ r.flipBit i) (hik : i < k) : r.testBit k = q.testBit k := by
  simp_rw [testBit_eq_decide_div_mod_eq, decide_eq_decide]
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
  rw [testBit_eq_iff]
  intros k
  rcases lt_or_ge k i with hik | hik
  · rw [testBit_flipBit_of_ne hik.ne, h hik]
  · exact testBit_eq_flipBit_testBit_of_le_of_flipBit_le_ge hrq hf hik

theorem flipBit_lt_flipBit_of_lt_of_ne_flipBit_of_lt_testBit_eq {r : ℕ} (hrq : r < q)
    (hrq' : r ≠ q.flipBit i) (h : ∀ {k}, k < i → r.testBit k = q.testBit k) :
    r.flipBit i < q.flipBit i := by
  rw [← not_le]
  exact fun H => hrq' (eq_flipBit_of_lt_of_flipBit_ge_of_lt_testBit_eq hrq H h)

@[pp_nodot, simps!]
def flipBitPerm (i : ℕ) : Equiv.Perm ℕ :=
  ⟨(flipBit · i), (flipBit · i),
    fun _ => xor_xor_cancel_right _ _, fun _ => xor_xor_cancel_right _ _⟩

@[simp]
theorem flipBitPerm_inv_apply : ∀ (x i : ℕ), (flipBitPerm i)⁻¹ x = x.flipBit i := fun _ _ => rfl

theorem flipBitPerm_eq_permCongr (i : ℕ) :
    flipBitPerm i = (insertBitEquiv i).permCongr (boolInversion.prodCongr (Equiv.refl _)) := by
  simp_rw [Equiv.ext_iff, flipBitPerm_apply,
    flipBit_apply, Equiv.permCongr_apply, insertBitEquiv_apply,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, boolInversion_apply,
    insertBitEquiv_symm_apply, implies_true]

end FlipBit

section CondFlipBit

def condFlipBit (q : ℕ) (i : ℕ) {l : ℕ} (c : Vector Bool l) : ℕ :=
  q ^^^ ((c[q.removeBit i]?.getD false).toNat <<< i)

variable {p q l k i j n m : ℕ} {c d :  Vector Bool l} {b : Bool}

@[grind =]
theorem condFlipBit_apply_of_removeBit_lt (h : q.removeBit i < l) :
    q.condFlipBit i c = if c[q.removeBit i] then q.flipBit i else q := by grind [condFlipBit]

@[grind =]
theorem condFlipBit_apply_of_le_removeBit {c : Vector Bool l} (h : l ≤ q.removeBit i) :
    q.condFlipBit i c = q := by grind [condFlipBit]

theorem condFlipBit_apply : q.condFlipBit i c = if h : q.removeBit i < l then
    if c[q.removeBit i] then q.flipBit i else q else q := by grind

@[simp, grind =]
theorem condFlipBit_empty {i : ℕ}  :
    q.condFlipBit i #v[] = q := by grind

@[simp, grind =]
theorem condFlipBit_push {i : ℕ} {c : Vector Bool l} {b : Bool} :
    q.condFlipBit i (c.push b) =
    if q.removeBit i = l ∧ b then q.flipBit i else q.condFlipBit i c := by grind

@[grind =]
theorem removeBit_condFlipBit_of_eq : (q.condFlipBit i c).removeBit i = q.removeBit i := by grind

@[grind =]
theorem testBit_condFlipBit_of_ne (hij : i ≠ j) :
    (q.condFlipBit j c).testBit i = q.testBit i := by grind

@[grind =]
theorem testBit_condFlipBit_of_eq :
    (q.condFlipBit i c).testBit i = (c[q.removeBit i]?.getD false).xor (q.testBit i) := by grind

theorem testBit_condFlipBit : (q.condFlipBit j c).testBit i =
    (decide (i = j) && (c[q.removeBit i]?.getD false)).xor (q.testBit i) := by grind

theorem testBit_condFlipBit_of_le_removeBit (h : l ≤ q.removeBit i) :
    (q.condFlipBit i c).testBit j = q.testBit j := by grind

theorem testBit_condFlipBit_of_removeBit_lt_of_eq (h : q.removeBit i < l) :
  (q.condFlipBit i c).testBit i = c[q.removeBit i].xor (q.testBit i) := by grind

theorem condflipBit_apply : q.condFlipBit i c =
    (q.removeBit i).insertBit ((c[q.removeBit i]?.getD false).xor (q.testBit i)) i  := by grind

theorem condflipBit_apply_of_removeBit_lt (h : q.removeBit i < l) :
    q.condFlipBit i c = (q.removeBit i).insertBit (c[q.removeBit i].xor (q.testBit i)) i := by grind

theorem condFlipBit_apply_comm :
    (q.condFlipBit i d).condFlipBit i c = (q.condFlipBit i c).condFlipBit i d := by grind

theorem condFlipBit_insertBit :
    (p.insertBit b i).condFlipBit i c = p.insertBit ((c[p]?.getD false).xor b) i := by grind

@[simp]
theorem condFlipBit_condFlipBit_of_eq : (q.condFlipBit i c).condFlipBit i c = q := by grind

theorem condFlipBit_condFlipBit {d : Vector Bool l} :
    (q.condFlipBit i c).condFlipBit i d = (q.condFlipBit i d).condFlipBit i c := by grind

@[simp, grind =]
theorem condFlipBit_flipBit {c : Vector Bool l} :
    (q.flipBit i).condFlipBit i c = (q.condFlipBit i c).flipBit i := by grind

theorem condFlipBit_of_all (hq : q.removeBit i < l)
    (hc : c.all id) : q.condFlipBit i c = q.flipBit i := by grind

@[simp, grind =]
theorem condFlipBit_of_replicate_true :
    q.condFlipBit i (Vector.replicate n true) = if q.removeBit i < n then q.flipBit i else q := by
  grind

theorem condFlipBit_of_all_not (hc : c.all (!·)) :
    q.condFlipBit i c = q := by grind

@[simp, grind =]
theorem condFlipBit_of_replicate_false :
    q.condFlipBit i (Vector.replicate n false) = q := by grind

@[simp, grind =]
theorem condFlipBit_lt_iff_lt (hin : 2^(i + 1) ∣ n) :
    q.condFlipBit i c < n ↔ q < n := by grind

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

@[grind =]
theorem getElem_swap_insertBit {α : Type*} {n i : ℕ}
    {v : Vector α n} {k l : ℕ} (hk : k < n) {hl hl'}:
    (v.swap (l.insertBit false i) (l.insertBit true i) hl hl')[k] =
    if h : k.removeBit i = l then v[k.flipBit i]'(Nat.flipBit_apply ▸ by grind) else v[k] := by
  simp_rw [getElem_swap, Nat.eq_insertBit_iff]
  grind

section CondFlipBit

variable {α : Type*} {n i l : ℕ} {c : Vector Bool l}

def condFlipBitIndices (v : Vector α n) (i : ℕ) (c : Vector Bool l) :
    Vector α n :=
  c.foldl (fun vn b => (vn.1.bswapIfInBounds b (vn.2.insertBit false i)
    (vn.2.insertBit true i), vn.2 + 1)) (v, 0) |>.1

@[simp, grind =]
theorem condFlipBitIndices_empty {v : Vector α n} {i : ℕ}  :
    condFlipBitIndices v i #v[] = v := by grind [condFlipBitIndices]

@[simp, grind =]
theorem condFlipBitIndices_zero {v : Vector α n} {i : ℕ} {c : Vector Bool 0} :
    condFlipBitIndices v i c = v := c.eq_empty ▸ condFlipBitIndices_empty

@[simp, grind =]
theorem condFlipBitIndices_push {v : Vector α n} {i : ℕ} {c : Vector Bool l} {b : Bool} :
    condFlipBitIndices v i (c.push b) =
    if h : l.insertBit true i < n ∧ b then
    (condFlipBitIndices v i c).swap
    (l.insertBit false i) (l.insertBit true i)
    (Nat.insertBit_false_le_insertBit_true.trans_lt h.1) h.1 else
    condFlipBitIndices v i c := by
  trans (condFlipBitIndices v i c).bswapIfInBounds b
    (l.insertBit false i) (l.insertBit true i)
  · suffices (c.foldl (fun vn b => (vn.1.bswapIfInBounds b (vn.2.insertBit false i)
    (vn.2.insertBit true i), vn.2 + 1)) (v, 0)) = (condFlipBitIndices v i c, l) by
      grind [condFlipBitIndices]
    induction c <;> grind [condFlipBitIndices]
  · grind

theorem condFlipBitIndices_succ {v : Vector α n} {i : ℕ} {c : Vector Bool (l + 1)} :
    condFlipBitIndices v i c = if h : l.insertBit true i < n ∧ c.back then
    (condFlipBitIndices v i c.pop).swap
    (l.insertBit false i) (l.insertBit true i)
    (Nat.insertBit_false_le_insertBit_true.trans_lt h.1) else condFlipBitIndices v i c.pop := by
  convert condFlipBitIndices_push
  exact c.push_pop_back.symm

@[grind =]
theorem getElem_condFlipBitIndices {v : Vector α n} {c : Vector Bool l}
    {i k : ℕ} (hk : k < n) :
  (v.condFlipBitIndices i c)[k] =
  if h : k.condFlipBit i c < n then v[k.condFlipBit i c] else v[k] := by
  induction c generalizing k
  · grind
  · simp only [condFlipBitIndices_push, Nat.condFlipBit_push]
    grind

@[simp] theorem condFlipBitIndices_condFlipBitIndices {v : Vector α n} :
    (v.condFlipBitIndices i c).condFlipBitIndices i c = v := by grind

def condFlipBitVals (v : Vector ℕ n) (i : ℕ) (c : Vector Bool l) : Vector ℕ n :=
  v.map (fun k => if k.condFlipBit i c < n then k.condFlipBit i c else k)

@[grind =]
theorem getElem_condFlipBitVals {v : Vector ℕ n} {i : ℕ} {c : Vector Bool l} {k : ℕ}
    (hk : k < n) : (condFlipBitVals v i c)[k] =
    if v[k].condFlipBit i c < n then v[k].condFlipBit i c else v[k] := getElem_map _ _

@[simp] theorem condFlipBitVals_condFlipBitVals_of_lt {v : Vector ℕ n}
    (hv : ∀ i (hi : i < n), v[i] < n) :
    (v.condFlipBitVals i c).condFlipBitVals i c = v := by grind

end CondFlipBit

section FlipBit

variable {α : Type*} {n i : ℕ}

def flipBitIndices (v : Vector α n) (i : ℕ) : Vector α n :=
    v.condFlipBitIndices i (replicate (n.removeBit i) true)

@[grind =]
theorem getElem_flipBitIndices {v : Vector α n} {i k : ℕ} (hk : k < n) :
    (v.flipBitIndices i)[k] = if hk : k.flipBit i < n then v[k.flipBit i] else v[k] := by
  grind [flipBitIndices]

@[simp] theorem flipBitIndices_flipBitIndices {v : Vector α n} :
    (v.flipBitIndices i).flipBitIndices i = v := by
  ext i hi
  simp_rw [getElem_flipBitIndices, Nat.flipBit_flipBit_of_eq, hi, dite_true, dite_eq_ite,
    ite_eq_left_iff, dite_eq_right_iff]
  exact fun C h => (C h).elim

def flipBitVals (v : Vector ℕ n) (i : ℕ) : Vector ℕ n := v.map
  (fun k => if k.flipBit i < n then k.flipBit i else k)

@[grind =]
theorem getElem_flipBitVals {v : Vector ℕ n} {i k : ℕ} (hk : k < n) :
    (flipBitVals v i)[k] = if v[k].flipBit i < n then v[k].flipBit i else v[k] :=
  getElem_map _ _

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

end Vector

namespace PermOf

section FlipBit

variable {n : ℕ}

def flipBitIndices (a : PermOf n) (i : ℕ) : PermOf n where
  toVector := a.toVector.flipBitIndices i
  invVector := a.invVector.flipBitVals i
  getElem_invVector_getElem_toVector := by grind

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

@[simp] theorem shuffle_flipBit {α : Type*} (v : Vector α n) :
    (v.shuffle (flipBit i)) = v.flipBitIndices i := by
  ext j hj
  simp_rw [Vector.getElem_flipBitIndices, Vector.getElem_shuffle, getElem_flipBit]
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
  simp only [getElem_flipBitIndices, getElem_flipBit, getElem_mul]
  split_ifs <;> rfl

theorem flipBitVals_eq_flipBit_mul (a : PermOf n) :
    a.flipBitVals i = flipBit i * a := by
  ext k hk : 1
  simp only [getElem_flipBitVals, getElem_flipBit, getElem_mul]

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
  simp_rw [getElem_flipBit, hk'.not_gt, ite_false]

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
  simp_rw [← smul_of_lt hk, flipBit_smul_ne_self]
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
  simp_rw [← smul_of_lt hk, flipBitIndices_smul_ne_smul]
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

end FlipBit

section CondFlipBit

variable {n l i j : ℕ}

def condFlipBitIndices (a : PermOf n) (i : ℕ) (c : Vector Bool l) : PermOf n where
  toVector := a.toVector.condFlipBitIndices i c
  invVector := a.invVector.condFlipBitVals i c
  getElem_invVector_getElem_toVector := by grind

def condFlipBitVals (a : PermOf n) (i : ℕ) (c : Vector Bool l) : PermOf n :=
  (a⁻¹.condFlipBitIndices i c)⁻¹

variable {a b : PermOf n} {i k : ℕ} {c : Vector Bool l}

@[grind =]
theorem getElem_condFlipBitIndices {hk : k < n} :
    (a.condFlipBitIndices i c)[k] =
    if hk : k.condFlipBit i c < n then a[k.condFlipBit i c] else a[k] :=
  Vector.getElem_condFlipBitIndices _

@[grind =]
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

@[simp] theorem condFlipBitIndices_of_replicate_false :
    (a.condFlipBitIndices i (Vector.replicate l false)) = a := by grind

@[simp] theorem condFlipBitVals_of_replicate_false :
    (a.condFlipBitVals i (Vector.replicate l false)) = a := by grind

def condFlipBit (i : ℕ) (c : Vector Bool l) : PermOf n :=
  (1 : PermOf n).condFlipBitIndices i c

theorem getElem_condFlipBit {hk : k < n} :
    (condFlipBit i c)[k] = if k.condFlipBit i c < n then k.condFlipBit i c else k := by
  unfold condFlipBit
  simp_rw [getElem_condFlipBitIndices, getElem_one, dite_eq_ite]

@[simp] theorem condFlipBit_of_replicate_false :
    (condFlipBit i (Vector.replicate l false)) = (1 : PermOf n) := by
  ext
  simp_rw [getElem_condFlipBit, Nat.condFlipBit_of_replicate_false, ite_self, getElem_one]

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
  simp only [getElem_condFlipBitIndices, getElem_condFlipBit, getElem_mul]
  split_ifs <;> try {rfl}

theorem condFlipBitVals_eq_condFlipBit_mul (a : PermOf n) :
    a.condFlipBitVals i c = condFlipBit i c * a := by
  ext k hk : 1
  simp only [getElem_condFlipBitVals, getElem_condFlipBit, getElem_mul]

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
  simp_rw [getElem_condFlipBit, hk'.not_gt, ite_false]

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
  induction p with | zero | succ p IH
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
  induction p with | zero | succ p IH
  · simp_rw [pow_zero, one_flipBitIndices, flipBit_inv]
  · nth_rewrite 1 [pow_succ']
    simp_rw [pow_succ, mul_flipBitIndices, mul_inv_rev, IH, flipBitIndices_mul,
      inv_flipBitCommutator_flipBitVals]

@[simp]
theorem flipBitCommutator_pow_flipBitVals_inv :
    (((a.flipBitCommutator i)^p).flipBitVals i)⁻¹ =
    ((a.flipBitCommutator i)^p).flipBitVals i := by
  induction p with | zero | succ p IH
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
  · simp_rw [Int.ofNat_eq_natCast, zpow_natCast, flipBitCommutator_pow_flipBitIndices_inv]
  · simp_rw [zpow_negSucc, inv_flipBitCommutator_pow_flipBitIndices,
      flipBitCommutator_pow_flipBitVals_inv]

@[simp]
theorem flipBitCommutator_zpow_flipBitVals_inv {p : ℤ} :
    (((a.flipBitCommutator i)^p).flipBitVals i)⁻¹ =
    ((a.flipBitCommutator i)^p).flipBitVals i := by
  cases p
  · simp_rw [Int.ofNat_eq_natCast, zpow_natCast, flipBitCommutator_pow_flipBitVals_inv]
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
  simp_rw [← smul_of_lt hk, flipBitCommutator_smul_ne_flipBit]
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
  simp_rw [← smul_of_lt hk, flipBitCommutator_flipBitIndices_smul_ne_self]
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
  simp_rw [← smul_of_lt hk, flipBitCommutator_flipBitVals_smul_ne_self]
  exact ⟨hk, hk'⟩

variable (hin : 2^(i + 1) ∣ n)

include hin

@[simp]
theorem getElem_flipBitCommutator_of_div {hk : k < n} :
    (a.flipBitCommutator i)[k] =
      a[(a⁻¹[k.flipBit i]'((k.flipBit_lt_iff_lt hin).mpr hk)).flipBit i]'
      ((Nat.flipBit_lt_iff_lt hin).mpr (getElem_lt _)) := by
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
  simp_rw [← getElem_flipBit_of_div hin (hk := hk), ← smul_of_lt hk,
  flipBitCommutator_smul_ne_flipBit, Nat.flipBit_lt_iff_lt hin, smul_lt_iff_lt, and_self, hk]

theorem getElem_flipBitCommutator_flipBit_ne {hk : k < n} :
    (a.flipBitCommutator i)[k].flipBit i ≠ k := by
  simp_rw [← getElem_flipBitVals_of_div hin, ← smul_of_lt hk,
    flipBitCommutator_flipBitVals_smul_ne_self, Nat.flipBit_lt_iff_lt hin, smul_lt_iff_lt,
    and_self, hk]

theorem getElem_pow_flipBitCommutator_ne_flipBit {hk : k < n} {p : ℕ} :
    ((a.flipBitCommutator i) ^ p)[k] ≠ k.flipBit i := by
  induction p using Nat.twoStepInduction generalizing k with | zero | one | more p IH
  · rw [pow_zero, getElem_one]
    exact Nat.flipBit_ne_self.symm
  · rw [pow_one]
    exact a.getElem_flipBitCommutator_ne_flipBit_of_div hin
  · have hk' : k.flipBit i < n := by rwa [Nat.flipBit_lt_iff_lt hin]
    simp_rw [pow_succ (n := p.succ), pow_succ' (n := p), getElem_mul,
    ← (ne_getElem_inv_iff _ hk'),
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
  · simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact getElem_pow_flipBitCommutator_ne_flipBit hin
  · have hk' : k.flipBit i < n := by rwa [Nat.flipBit_lt_iff_lt hin]
    simp_rw [zpow_negSucc, getElem_inv_ne_iff _ hk']
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
  rcases lt_or_ge k n with hk | hk
  · simp_rw [smul_of_lt hk]
    exact fun _ _ => getElem_flipBitCommutator_zpow_ne_flipBit_getElem_flipBitCommutator_zpow hin
  · simp_rw [smul_of_ge hk]
    exact fun _ _ => Nat.flipBit_ne_self.symm

theorem period_le_card_div_two_of_flipBit_invar_of_cycle_subset (s : Finset ℕ)
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

section BitInvariant

open Nat

variable {n i k x l : ℕ} {a b : PermOf n}

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
  (ha : ∀ k < i, a.BitInvariant k) (hk : x < 2^(n + 1)) :
  a.cycleOf x ⊆ Finset.bitMatchUnder i ⟨x, hk⟩ := by
  simp_rw [Finset.subset_iff, mem_cycleOf_iff_exists_getElem_zpow _ hk, Finset.mem_bitMatchUnder_iff,
      forall_exists_index, forall_apply_eq_imp_iff, getElem_lt _,
      true_and]
  intros _ _ hk
  exact ((ha _ hk).zpow _).testBit_getElem_eq_testBit _

theorem period_le_two_pow_sub_of_bitInvariant_lt {a : PermOf (2^(n + 1))} {i : ℕ}
    (ha : ∀ k < i, a.BitInvariant k) :
    ∀ {k : ℕ}, MulAction.period (a.flipBitCommutator i) k ≤ 2 ^ (n - i) := fun {k} => by
  rcases le_or_gt i n with hi | hi
  · have hin := (Nat.pow_dvd_pow 2 (Nat.succ_le_succ hi))
    rcases lt_or_ge k (2^(n + 1)) with hk | hk
    · rw [← Nat.mul_div_cancel (2^(n - i)) (zero_lt_two), ← pow_succ,
        ← Nat.sub_add_comm hi, ← Finset.card_bitMatchUnder i ⟨k, hk⟩]
      refine period_le_card_div_two_of_flipBit_invar_of_cycle_subset
        (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi)) _ ?_ _ ?_
      · exact flipBit_mem_bitMatchUnder ⟨le_rfl, Nat.lt_succ_of_le hi⟩
      · exact (a.flipBitCommutator i).cycleOf_subset_bitMatchUnder _
          (fun _ hl => (ha _ hl).flipBitCommutator_of_ne hl.ne) _
    · rw [period_eq_one_of_ge _ hk]
      exact Nat.one_le_pow _ _ zero_lt_two
  · rw [forall_lt_bitInvariant_iff_eq_one_of_ge (Nat.pow_le_pow_of_le one_lt_two hi)] at ha
    simp_rw [ha, one_flipBitCommutator, MulAction.period_one, Nat.one_le_iff_ne_zero]
    exact (Nat.two_pow_pos (n - i)).ne'

theorem flipBitCommutator_cycleMinVector_getElem_getElem_flipBit (a : PermOf (2^(n + 1)))
    {hk : k < 2^(n + 1)}
    (ha : ∀ {x : ℕ}, MulAction.period (a.flipBitCommutator i) x ≤ 2 ^ (n - i)) :
    ((a.flipBitCommutator i).CycleMinVector (n - i))[(a.flipBitIndices i)[k]] =
    ((a.flipBitCommutator i).CycleMinVector (n - i))[(a.flipBitVals i)[k]] := by
  simp_rw [cycleMinVector_eq_apply_cycleMinVector _ _ ha (a.flipBitVals i).getElem_lt,
    ← getElem_mul, flipBitCommutator_eq_flipBitIndices_mul_flipBitVals_inv, inv_mul_cancel_right]

theorem flipBit_getElem_cycleMinVector_flipBitCommutator_comm (a : PermOf (2^(n + 1)))
    (ha : ∀ k < i, a.BitInvariant k) {k : ℕ}
    (hk : k < 2^(n + 1)) (hi : i < n + 1):
    ((a.flipBitCommutator i).CycleMinVector (n - i))[(k.flipBit i)]'
    (by rwa [flipBit_lt_iff_lt <| (Nat.pow_dvd_pow _ hi).trans (dvd_of_eq rfl)]) =
    (((a.flipBitCommutator i).CycleMinVector (n - i))[k]).flipBit i := by
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
  rcases lt_or_ge i (n + 1) with hi | hi
  · have hin :  2 ^ ((i : ℕ) + 1) ∣ 2^(n + 1) := Nat.pow_dvd_pow _ hi
    rcases lt_or_ge k (2^(n + 1)) with hk | hk
    · have H := flipBit_getElem_cycleMinVector_flipBitCommutator_comm a ha hk hi
      simp_rw [getElem_cycleMinVector] at H
      exact H
    · simp_rw [cycleMin_of_ge _ hk, cycleMin_of_ge _ <| le_of_not_gt <|
      (Nat.flipBit_lt_iff_lt hin).not.mpr hk.not_gt]
  · rw [forall_lt_bitInvariant_iff_eq_one_of_ge (Nat.pow_le_pow_of_le one_lt_two hi)] at ha
    simp_rw [ha, one_flipBitCommutator, one_cycleMin]

end BitInvariant

end PermOf
