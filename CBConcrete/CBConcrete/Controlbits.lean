import CBConcrete.BitResiduum

namespace PermOf

variable {n i p k : ℕ} {a : PermOf (2^(n + 1))}

section Decomposition
open Equiv Equiv.Perm Nat Function

def leftLayer (a : PermOf (2^(n + 1))) (i : ℕ) : Vector Bool (2^n) :=
  if hi : i ≤ n then
    let A := (a.flipBitCommutator i).CycleMinVector (n - i);
    (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      (A[(p : ℕ).mergeBitRes false i]'
      ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
  else Vector.replicate _ false

section LeftLayer

theorem getElem_leftLayer (hp : p < 2^n) :
    (leftLayer a i)[p] =
  if hi : i ≤ n then
    (((a.flipBitCommutator i).CycleMinVector (n - i))[p.mergeBitRes false i]'
    ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (hp.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
  else false := by
  unfold leftLayer
  split_ifs
  · simp_rw [Vector.getElem_map, Vector.getElem_finRange]
  · simp_rw [Vector.getElem_replicate]

theorem getElem_leftLayer_of_le (hi : i ≤ n) (hp : p < 2^n) :
    (leftLayer a i)[p] =
    (((a.flipBitCommutator i).CycleMinVector (n - i))[p.mergeBitRes false i]'
    ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (hp.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i := by
  rw [getElem_leftLayer, dif_pos hi]

theorem getElem_leftLayer_of_gt (hi : n < i) (hp : p < 2^n) :
    (leftLayer a i)[p] = false := by
  rw [getElem_leftLayer, dif_neg (hi.not_le)]

theorem leftLayer_eq_of_gt (hi : n < i) :
    leftLayer a i = Vector.replicate _ false := by
  ext
  simp_rw [getElem_leftLayer_of_gt hi, Vector.getElem_replicate]

theorem getElem_leftLayer_of_lt_of_bitInvariant_lt
    (ha : ∀ j < i, a.BitInvariant j) (hp : p < 2^i) {hp' : p < 2^n} :
    (leftLayer a i)[p] = false := by
  rcases le_or_lt i n with hi | hi
  · simp_rw [getElem_leftLayer_of_le hi, mergeBitRes_apply_false_of_lt_two_pow hp,
    getElem_cycleMinVector_of_self_le_getElem (getElem_eq_self_of_forall_bitInvariant_lt_of_lt
    (fun _ hk => (ha _ hk).flipBitCommutator_of_ne hk.ne) hp
    (Nat.pow_le_pow_of_le one_lt_two (hi.trans (Nat.le_succ _)))), testBit_lt_two_pow hp]
  · simp_rw [getElem_leftLayer_of_gt hi]

theorem leftLayer_eq_of_bitInvariant_lt {a : PermOf (2^(n + 1))}
    (ha : ∀ j < n, a.BitInvariant j) :
    leftLayer a n = Vector.replicate _ false := by
  ext i hi
  simp_rw [Vector.getElem_replicate]
  exact getElem_leftLayer_of_lt_of_bitInvariant_lt ha hi

theorem getElem_zero_leftLayer_zero :
    (leftLayer a 0)[0] = false := getElem_leftLayer_of_lt_of_bitInvariant_lt
      (by simp only [not_lt_zero', IsEmpty.forall_iff, implies_true]) (Nat.two_pow_pos _)

end LeftLayer

def leftPerm (a : PermOf (2^(n + 1))) (i : ℕ) : PermOf (2^(n + 1)) :=
  condFlipBit i (leftLayer a i)

section LeftPerm

theorem getElem_leftPerm (hk : k < 2^(n + 1)) :
  (leftPerm a i)[k] = (condFlipBit i (leftLayer a i))[k] := rfl

theorem getElem_leftPerm_of_gt (hi : n < i) (hk : k < 2^(n + 1))  :
    (leftPerm a i)[k] = k := by
  unfold leftPerm
  rw [leftLayer_eq_of_gt hi, condFlipBit_of_mkVector_false, getElem_one]

@[simp]
theorem getElem_leftPerm_leftPerm (hk : k < 2^(n + 1)) :
    (leftPerm a i)[(leftPerm a i)[k]] = k := getElem_condFlipBit_condFlipBit

theorem leftPerm_inv : (leftPerm a i)⁻¹ = (leftPerm a i) := by
  simp_rw [inv_eq_iff_mul_eq_one]
  ext
  simp_rw [getElem_mul, getElem_leftPerm_leftPerm, getElem_one]

theorem leftPerm_bitInvariant_of_ne {i : ℕ} {j : ℕ} (hj : j ≠ i) :
    (leftPerm a i).BitInvariant j := condFlipBit_of_ne hj

theorem testBit_leftPerm_of_ne {i : ℕ} {j : ℕ} (hj : j ≠ i) (hk : k < 2^(n + 1)):
    (leftPerm a i)[k].testBit j = k.testBit j := by
  simp_rw [(leftPerm_bitInvariant_of_ne hj).testBit_getElem_eq_testBit]

theorem testBit_leftPerm {i : ℕ}
    (ha : ∀ j < i, a.BitInvariant j) {hk : k < 2^(n + 1)} :
    (leftPerm a i)[k].testBit i =
    ((a.flipBitCommutator i).CycleMinVector (n - i))[k].testBit i := by
  rcases le_or_lt i n with hi | hi
  · have hin :  2 ^ (i + 1) ∣ 2^(n + 1) := Nat.pow_dvd_pow _ (Nat.succ_le_succ hi)
    rw [getElem_leftPerm, getElem_condFlipBit_of_div hin,
      condFlipBit_apply_of_testRes_lt ((testRes_lt_two_pow_iff_lt_two_pow hi).mpr hk),
      getElem_leftLayer_of_le hi]
    rcases Bool.eq_false_or_eq_true (k.testBit i) with hkb | hkb
    · simp_rw [← Bool.not_true, ← hkb, ← flipBit_apply,
      a.flipBit_getElem_cycleMinVector_flipBitCommutator_comm ha hk (Nat.lt_succ_of_le hi),
      Bool.apply_cond (fun (k : ℕ) => k.testBit i), testBit_flipBit_of_eq, hkb,
      Bool.not_true, Bool.cond_not, Bool.cond_false_right, Bool.and_true]
    · simp_rw [← hkb, mergeBitRes_testBit_testRes_of_eq, Bool.apply_cond (fun (k : ℕ) => k.testBit i),
      testBit_flipBit_of_eq, hkb, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · simp_rw [getElem_leftPerm_of_gt hi, Nat.sub_eq_zero_of_le hi.le, getElem_cycleMinVector_zero]

end LeftPerm

def rightLayer (a : PermOf (2^(n + 1))) (i : ℕ) : Vector Bool (2^n) :=
  if hi : i ≤ n then
    let A := (a.flipBitCommutator i).CycleMinVector (n - i);
    let F := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      (A[(p : ℕ).mergeBitRes false i]'
      ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
    (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      ((a.condFlipBitVals i F)[((p : ℕ).mergeBitRes false i)]'
      ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
  else Vector.replicate _ false

section RightLayer

theorem getElem_rightLayer {i : ℕ} (hp : p < 2^n) :
    (rightLayer a i)[p] =
    if hi : i ≤ n then
    ((leftPerm a i)[a[(p.mergeBitRes false i)]'
      ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (hp.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))]).testBit i
    else false := by
  unfold rightLayer leftPerm leftLayer
  split_ifs
  · simp_rw [Vector.getElem_map, Vector.getElem_finRange,
      condFlipBitVals_eq_condFlipBit_mul, getElem_mul]
  · simp_rw [Vector.getElem_replicate]

theorem getElem_rightLayer_of_le {i : ℕ} (hi : i ≤ n) (hp : p < 2^n) :
    (rightLayer a i)[p] =
    ((leftPerm a i)[a[(p.mergeBitRes false i)]'
      ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (hp.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))]).testBit i := by
  rw [getElem_rightLayer, dif_pos hi]

theorem getElem_rightLayer_of_gt {i : ℕ} (hi : n < i) (hp : p < 2^n) :
    (rightLayer a i)[p] = false := by
  rw [getElem_rightLayer, dif_neg (hi.not_le)]

theorem rightLayer_eq_of_gt {i : ℕ} (hi : n < i) :
    rightLayer a i = Vector.replicate _ false := by
  ext
  simp_rw [getElem_rightLayer_of_gt hi, Vector.getElem_replicate]

end RightLayer

def rightPerm (a : PermOf (2^(n + 1))) (i : ℕ) : PermOf (2^(n + 1)) :=
  condFlipBit i (rightLayer a i)

section RightPerm

theorem getElem_rightPerm (hk : k < 2^(n + 1)) :
  (rightPerm a i)[k] = (condFlipBit i (rightLayer a i))[k] := rfl

theorem getElem_rightPerm_of_gt (hi : n < i) (hk : k < 2^(n + 1))  :
    (rightPerm a i)[k] = k := by
  unfold rightPerm
  rw [rightLayer_eq_of_gt hi, condFlipBit_of_mkVector_false, getElem_one]

@[simp]
theorem getElem_rightPerm_rightPerm (hk : k < 2^(n + 1)) :
    (rightPerm a i)[(rightPerm a i)[k]] = k := getElem_condFlipBit_condFlipBit

theorem rightPerm_inv : (rightPerm a i)⁻¹ = (rightPerm a i) := by
  simp_rw [inv_eq_iff_mul_eq_one]
  ext
  simp_rw [getElem_mul, getElem_rightPerm_rightPerm, getElem_one]

theorem rightPerm_bitInvariant_of_ne {i : ℕ} {j : ℕ} (hj : j ≠ i) :
    (rightPerm a i).BitInvariant j := condFlipBit_of_ne hj

theorem testBit_rightPerm_of_ne {i : ℕ} {j : ℕ} (hj : j ≠ i) (hk : k < 2^(n + 1)):
    (rightPerm a i)[k].testBit j = k.testBit j := by
  simp_rw [(rightPerm_bitInvariant_of_ne hj).testBit_getElem_eq_testBit]

theorem testBit_rightPerm {i : ℕ}
    (ha : ∀ j < i, a.BitInvariant j) {hk : k < 2^(n + 1)}:
    (rightPerm a i)[k].testBit i =
    (leftPerm a i)[a[k]].testBit i := by
  rcases le_or_lt i n with hi | hi
  · have hin :  2 ^ (i + 1) ∣ 2^(n + 1) := Nat.pow_dvd_pow _ (Nat.lt_succ_of_le hi)
    have hk' := (flipBit_lt_two_pow_iff_lt_two_pow (Nat.lt_succ_of_le hi)).mpr hk
    simp_rw [getElem_rightPerm, getElem_condFlipBit_of_div hin,
      condFlipBit_apply_of_testRes_lt ((testRes_lt_two_pow_iff_lt_two_pow hi).mpr hk),
      getElem_rightLayer_of_le hi, Bool.apply_cond (fun (k : ℕ) => k.testBit i),
      testBit_flipBit_of_eq]
    rcases (Bool.eq_false_or_eq_true (k.testBit i)) with hkb | hkb
    · simp_rw [hkb, testBit_leftPerm ha, Bool.not_true, Bool.cond_true_right, Bool.or_false,
        Bool.not_eq_eq_eq_not, ← testBit_flipBit_of_eq, ← Bool.not_true, ← hkb, ← flipBit_apply,
        ← getElem_flipBitIndices_of_div hin (hk := hk),
        a.flipBitCommutator_cycleMinVector_getElem_getElem_flipBit
        (period_le_two_pow_sub_of_bitInvariant_lt ha), getElem_flipBitVals_of_div hin,
        a.flipBit_getElem_cycleMinVector_flipBitCommutator_comm ha (a.getElem_lt _)
        (Nat.lt_succ_of_le hi)]
    · simp_rw [hkb, Bool.not_false, Bool.cond_false_right, Bool.and_true,
        ← hkb, mergeBitRes_testBit_testRes_of_eq]
  · simp_rw [getElem_leftPerm_of_gt hi, getElem_rightPerm_of_gt hi,
      (bitInvariant_of_ge (Nat.pow_le_pow_of_le one_lt_two hi)).testBit_getElem_eq_testBit]

end RightPerm

def middlePerm (a : PermOf (2^(n + 1))) (i : ℕ) : PermOf (2^(n + 1)) :=
  if hi : i ≤ n then
    let A := (a.flipBitCommutator i).CycleMinVector (n - i);
    let L := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      (A[(p : ℕ).mergeBitRes false i]'
      ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
    let a' := a.condFlipBitVals i L;
    let R := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      (a'[((p : ℕ).mergeBitRes false i)]'
      ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
    a'.condFlipBitIndices i R
  else a

section MiddlePerm

@[simp] theorem getElem_middlePerm (hk : k < 2^(n + 1)) :
    (middlePerm a i)[k] = (leftPerm a i)[a[(rightPerm a i)[k]]] := by
  unfold middlePerm leftPerm rightPerm leftLayer rightLayer
  simp_rw [condFlipBitVals_eq_condFlipBit_mul, condFlipBitIndices_eq_mul_condFlipBit]
  rcases le_or_lt i n with hi | hi
  · simp_rw [dif_pos hi, getElem_mul]
  · simp_rw [dif_neg hi.not_le,  condFlipBit_of_mkVector_false, getElem_one]

theorem middlePerm_eq_condFlipBitVals_condFlipBitIndices :
    a.middlePerm i =
    (a.condFlipBitVals i (leftLayer a i)).condFlipBitIndices i (rightLayer a i) := by
  ext
  simp [condFlipBitVals_eq_condFlipBit_mul, leftPerm, rightPerm,
   condFlipBitIndices_eq_mul_condFlipBit]


theorem middlePerm_eq_leftPerm_mul_mul_rightPerm  :
    middlePerm a i = leftPerm a i * a * rightPerm a i := by
  ext
  simp_rw [getElem_middlePerm, getElem_mul]

theorem leftPerm_mul_middlePerm_mul_rightPerm  :
    leftPerm a i * middlePerm a i * rightPerm a i = a := by
  ext
  simp_rw [middlePerm_eq_leftPerm_mul_mul_rightPerm, getElem_mul,
    getElem_rightPerm_rightPerm, getElem_leftPerm_leftPerm]

@[simp] theorem bitInvariant_middlePerm {i : ℕ} {a : PermOf (2^(n + 1))}
  (ha : ∀ j < i, a.BitInvariant j) : ∀ j < i + 1, (middlePerm a i).BitInvariant j := by
  simp_rw [Nat.lt_succ_iff]
  intro j hj
  rcases hj.eq_or_lt with rfl | hj
  · simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, getElem_middlePerm,
      ← testBit_rightPerm ha, getElem_rightPerm_rightPerm, implies_true]
  · rw [middlePerm_eq_leftPerm_mul_mul_rightPerm]
    exact ((leftPerm_bitInvariant_of_ne hj.ne).mul (ha _ hj)).mul
      (rightPerm_bitInvariant_of_ne hj.ne)

@[simp] theorem bitInvariant_middlePerm_zero :
    (middlePerm a 0).BitInvariant 0 :=
  bitInvariant_middlePerm
    (by simp_rw [not_lt_zero', IsEmpty.forall_iff, implies_true]) _ zero_lt_one

theorem bitInvariant_middlePerm_of_gt {i : ℕ} {j : ℕ} (hj : n < j):
  (middlePerm a i).BitInvariant j := bitInvariant_of_ge (Nat.pow_le_pow_of_le one_lt_two hj)

end MiddlePerm

def mlrDecomp (a : PermOf (2^(n + 1))) (i : ℕ) :
    PermOf (2^(n + 1)) × Vector Bool (2^n) × Vector Bool (2^n) :=
  if hi : i ≤ n then
    let A := (a.flipBitCommutator i).CycleMinVector (n - i);
    let L := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
    (A[(p : ℕ).mergeBitRes false i]'
    ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i;
    let R := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
    ((a.condFlipBitVals i L)[((p : ℕ).mergeBitRes false i)]'
      ((mergeBitRes_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
    let M := (a.condFlipBitVals i L).condFlipBitIndices i R;
    (M, L, R)
  else (a, Vector.replicate _ false, Vector.replicate _ false)

section mlrDecomp

theorem mlrDecomp_eq_left_middle_right :
    mlrDecomp a i = (middlePerm a i, leftLayer a i, rightLayer a i) := by
  unfold mlrDecomp middlePerm rightLayer leftLayer
  rcases le_or_lt i n with hi | hi
  · simp_rw [dif_pos hi]
  · simp_rw [dif_neg hi.not_le]

@[simp] theorem condFlipBit_mlrDecomp_snd_fst {i : ℕ} :
    (condFlipBit i (mlrDecomp a i).snd.fst :
    PermOf (2^(n + 1))) = leftPerm a i := by
  rw [mlrDecomp_eq_left_middle_right]
  rfl

@[simp] theorem condFlipBit_mlrDecomp_snd_snd {i : ℕ} :
    (condFlipBit i (mlrDecomp a i).snd.snd :
    PermOf (2^(n + 1))) = rightPerm a i := by
  rw [mlrDecomp_eq_left_middle_right]
  rfl

theorem condFlipBit_mlrDecomp_snd_fst_mul_mlrDecomp_fst_mul_mlrDecomp_snd_snd {i : ℕ} :
    (condFlipBit i (mlrDecomp a i).snd.fst) * (mlrDecomp a i).fst *
    (condFlipBit i (mlrDecomp a i).snd.snd) = a := by
  rw [mlrDecomp_eq_left_middle_right]
  exact leftPerm_mul_middlePerm_mul_rightPerm

end mlrDecomp

def toCBLayer (a : PermOf (2^(n + 1))) (i : ℕ) :
    PermOf (2^(n + 1)) × Vector (Vector Bool (2^n)) i ×
    Vector (Vector Bool (2^n)) i := i.recOn ((a, #v[], #v[]))
    (fun i ⟨M, LS, RS⟩ =>
      let (M, L, R) := mlrDecomp M i
      (M, LS.push L, RS.push R))

@[simp] theorem toCBLayer_zero :
  a.toCBLayer 0 = (a, #v[], #v[]) := rfl

theorem toCBLayer_succ :
  a.toCBLayer (i + 1) =
    ((a.toCBLayer i).1.middlePerm i,
    (a.toCBLayer i).2.1.push ((a.toCBLayer i).1.leftLayer i),
    (a.toCBLayer i).2.2.push ((a.toCBLayer i).1.rightLayer i)) := by
  trans (((mlrDecomp (a.toCBLayer i).1 i).1,
    (a.toCBLayer i).2.1.push (mlrDecomp (a.toCBLayer i).1 i).2.1,
    (a.toCBLayer i).2.2.push (mlrDecomp (a.toCBLayer i).1 i).2.2))
  · rfl
  · simp_rw [mlrDecomp_eq_left_middle_right]

@[simp] theorem toCBLayer_one :
  a.toCBLayer 1 =
    ((middlePerm a 0), #v[leftLayer a 0], #v[rightLayer a 0]) := by
  simp_rw [toCBLayer_succ, toCBLayer_zero, Vector.push_mk,
    List.push_toArray, List.nil_append]

def middlePermIth (a : PermOf (2^(n + 1))) (i : ℕ) : PermOf (2^(n + 1)) :=
  (toCBLayer a i).1

@[simp] theorem middlePermIth_zero :
    a.middlePermIth 0 = a := congrArg _ toCBLayer_zero

@[simp] theorem middlePermIth_succ :
    a.middlePermIth (i + 1) = (a.middlePermIth i).middlePerm i := congrArg _ toCBLayer_succ

@[simp] theorem middlePermIth_one :
    a.middlePermIth 1 = a.middlePerm 0 := congrArg _ toCBLayer_succ

@[simp] theorem middlePermIth_bitInvariant :
    ∀ j < i, (a.middlePermIth i).BitInvariant j := by
  induction i generalizing a with | zero => _ | succ i IH => _
  · simp_rw [not_lt_zero', IsEmpty.forall_iff, implies_true]
  · simp_rw [middlePermIth_succ]
    exact bitInvariant_middlePerm IH

theorem middlePermIth_eq_of_gt (hi : n < i):
    a.middlePermIth i = 1 := by
  rw [← forall_lt_bitInvariant_iff_eq_one_of_ge le_rfl]
  exact fun _ hk => a.middlePermIth_bitInvariant _ (hk.trans_le (Nat.succ_le_of_lt hi))

def leftLayerIth (a : PermOf (2^(n + 1))) (i : ℕ) : Vector Bool (2^n) :=
  (toCBLayer a (i + 1)).2.1.back

theorem leftLayerIth_eq :
    a.leftLayerIth i = (a.middlePermIth i).leftLayer i := by
  unfold leftLayerIth middlePermIth
  simp_rw [toCBLayer_succ, Vector.back_succ, Vector.getElem_push_eq]

@[simp] theorem leftLayerIth_zero :
    a.leftLayerIth 0 = a.leftLayer 0 := by
  rw [leftLayerIth_eq, middlePermIth_zero]

theorem getElem_leftLayerIth_of_lt (hp : p < 2^i) (hp' : p < 2^n) :
    (a.leftLayerIth i)[p] = false := by
  rw [leftLayerIth_eq]
  exact getElem_leftLayer_of_lt_of_bitInvariant_lt middlePermIth_bitInvariant hp

theorem getElem_leftLayerIth :
    (a.leftLayerIth 0)[0] = false := by
  rw [leftLayerIth_eq]
  exact getElem_zero_leftLayer_zero

theorem leftLayerNth_eq :
    a.leftLayerIth n = Vector.replicate _ false := by
  rw [leftLayerIth_eq]
  exact leftLayer_eq_of_bitInvariant_lt middlePermIth_bitInvariant

theorem leftLayerIth_eq_of_ge (hi : n ≤ i) :
    a.leftLayerIth i = Vector.replicate _ false :=
  hi.eq_or_lt.elim (fun h => h ▸ leftLayerNth_eq) (leftLayerIth_eq ▸ leftLayer_eq_of_gt)

def rightLayerIth (a : PermOf (2^(n + 1))) (i : ℕ) : Vector Bool (2^n) :=
  (toCBLayer a (i + 1)).2.2.back

theorem rightLayerIth_eq :
    a.rightLayerIth i = (a.middlePermIth i).rightLayer i := by
  unfold rightLayerIth middlePermIth
  simp_rw [toCBLayer_succ, Vector.back_succ, Vector.getElem_push_eq]

@[simp] theorem rightLayerIth_zero :
    a.rightLayerIth 0 = a.rightLayer 0 := by
  rw [rightLayerIth_eq, middlePermIth_zero]

theorem rightLayerIth_eq_of_gt (hi : n < i) :
    a.rightLayerIth i = Vector.replicate _ false :=
  rightLayerIth_eq ▸ (rightLayer_eq_of_gt hi)

theorem toCBLayer_eq :
    a.toCBLayer i =
    (a.middlePermIth i, Vector.ofFn (fun i => a.leftLayerIth i),
    Vector.ofFn (fun i => a.rightLayerIth i)) := by
  induction i with | zero => _ | succ i IH => _
  · simp_rw [toCBLayer_zero, middlePermIth_zero, Prod.mk.injEq, true_and]
    exact ⟨Vector.ext (fun _ h => (Nat.not_lt_zero _ h).elim),
    Vector.ext (fun _ h => (Nat.not_lt_zero _ h).elim)⟩
  · simp_rw [toCBLayer_succ, IH, middlePermIth_succ, Prod.mk.injEq, true_and,
      leftLayerIth_eq, rightLayerIth_eq]
    refine ⟨Vector.ext fun _ => ?_, Vector.ext fun _ => ?_⟩ <;>
    simp_rw [Vector.push, Vector.toArray_ofFn, Vector.getElem_mk, Vector.getElem_ofFn,
        Array.getElem_push, Array.size_ofFn, Array.getElem_ofFn, dite_eq_ite, ite_eq_left_iff,
        not_lt, Nat.lt_succ_iff] <;>
    exact fun hle hge => le_antisymm hle hge ▸ rfl

def leftPermIth (a : PermOf (2^(n + 1))) (i : ℕ) : PermOf (2^(n + 1)) :=
  condFlipBit i (a.leftLayerIth i)

theorem leftPermIth_eq :
    a.leftPermIth i = (a.middlePermIth i).leftPerm i := by
  unfold leftPermIth leftPerm
  simp_rw [leftLayerIth_eq]

theorem leftPermIth_inv : (leftPermIth a i)⁻¹ = (leftPermIth a i) := by
  simp_rw [leftPermIth_eq, leftPerm_inv]

theorem leftPermIth_eq_of_ge (hi : n ≤ i) :
    a.leftPermIth i = 1 := by
  simp_rw [leftPermIth, leftLayerIth_eq_of_ge hi, condFlipBit_of_mkVector_false]

theorem leftPermIth_zero :
    a.leftPermIth 0 = a.leftPerm 0 := by
  rw [leftPermIth_eq, middlePermIth_zero]

def rightPermIth (a : PermOf (2^(n + 1))) (i : ℕ) : PermOf (2^(n + 1)) :=
  condFlipBit i (a.rightLayerIth i)

theorem rightPermIth_eq :
    a.rightPermIth i = (a.middlePermIth i).rightPerm i := by
  unfold rightPermIth rightPerm
  simp_rw [rightLayerIth_eq]

theorem rightPermIth_inv : (rightPermIth a i)⁻¹ = (rightPermIth a i) := by
  simp_rw [rightPermIth_eq, rightPerm_inv]

theorem rightPermIth_eq_of_gt (hi : n < i) :
    a.rightPermIth i = 1 := by
  simp_rw [rightPermIth, rightLayerIth_eq_of_gt hi, condFlipBit_of_mkVector_false]

theorem rightPermIth_zero :
    a.rightPermIth 0 = a.rightPerm 0 := by
  rw [rightPermIth_eq, middlePermIth_zero]

theorem leftPermIth_mul_middlePermISuccTh_mul_rightPermIth :
    a.leftPermIth i * a.middlePermIth (i + 1) * a.rightPermIth i = a.middlePermIth i := by
  simp_rw [leftPermIth_eq, middlePermIth_succ, rightPermIth_eq,
    leftPerm_mul_middlePerm_mul_rightPerm]

theorem middlePermISuccTh_eq_leftPermIth_mul_middlePermIth_mul_rightPermIth :
    a.middlePermIth (i + 1) = a.leftPermIth i * a.middlePermIth i * a.rightPermIth i := by
  rw [← mul_inv_eq_iff_eq_mul, ← inv_mul_eq_iff_eq_mul, leftPermIth_inv, rightPermIth_inv,
    ← mul_assoc, leftPermIth_mul_middlePermISuccTh_mul_rightPermIth]

theorem eq_fold_mul_middlePermIth_mul_fold (i : ℕ) :
    a = (Nat.fold i (fun k _ l => l * a.leftPermIth k) 1) * a.middlePermIth i *
    (Nat.fold i (fun k _ r => a.rightPermIth k * r) 1) := by
  induction i generalizing a with | zero => _ | succ i IH => _
  · simp_rw [Nat.fold_zero, middlePermIth_zero, one_mul, mul_one]
  · simp_rw [Nat.fold_succ, mul_assoc _ (a.leftPermIth i), mul_assoc _ (a.leftPermIth i * _),
      ← mul_assoc _ (a.rightPermIth i), leftPermIth_mul_middlePermISuccTh_mul_rightPermIth,
      ← mul_assoc]
    exact IH

theorem eq_foldl_mul_foldl_succ :
    a = (Nat.fold n (fun k _ l => l * a.leftPermIth k) 1) *
    (Nat.fold (n + 1) (fun k _ r => a.rightPermIth k * r) 1) := by
  have H := a.eq_fold_mul_middlePermIth_mul_fold (n + 1)
  rwa [middlePermIth_eq_of_gt (Nat.lt_succ_self _),
    Nat.fold_succ _ (fun k _ l => l * a.leftPermIth k),
    leftPermIth_eq_of_ge le_rfl, mul_one, mul_one] at H

def toControlBits (a : PermOf (2^(n + 1))) :
    Vector (Vector Bool (2^n)) (2*n + 1) :=
  let (_, L, R) := toCBLayer a (n + 1)
  (L.pop ++ R.reverse).cast (by simp_rw [add_tsub_cancel_right, two_mul, add_assoc])

theorem getElem_toControlBits_of_lt (hi : i < n) :
    a.toControlBits[i] = a.leftLayerIth i := by
  unfold toControlBits
  simp_rw [toCBLayer_eq, Vector.getElem_cast,
    Vector.getElem_append, Vector.getElem_pop, Vector.getElem_ofFn,
    Nat.add_one_sub_one, dif_pos hi]

theorem getElem_toControlBits_of_ge (hi : n ≤ i) {hi' : i < (2*n + 1)} :
    a.toControlBits[i] = a.rightLayerIth (n - (i - n)) := by
  unfold toControlBits
  simp_rw [toCBLayer_eq, Vector.getElem_cast,
    Vector.getElem_append, Vector.getElem_reverse, Vector.getElem_ofFn,
    Nat.add_one_sub_one, dif_neg hi.not_lt]

theorem getElem_toControlBits (hi' : i < (2*n + 1)) :
    a.toControlBits[i] = if i < n then a.leftLayerIth i else a.rightLayerIth (n - (i - n)) := by
  split_ifs with hi
  · exact getElem_toControlBits_of_lt hi
  · exact getElem_toControlBits_of_ge (le_of_not_lt hi)

end Decomposition

def ofControlBits {α : Type*} {m : ℕ} (v : Vector (Vector Bool (2^n)) (2*n + 1)) (a : Vector α m) :
    Vector α m :=
  v.zipIdx.foldl (fun a c => a.condFlipBitIndices (min c.2 ((n + 1) - c.2)) c.1) a

end PermOf
