import Controlbits.BitResiduumAlt

section Decomposition
open Equiv Equiv.Perm Nat Function

open VectorPerm

def leftLayer (a : VectorPerm (2^(n + 1))) (i : ℕ) : Vector Bool (2^n) :=
  if hi : i ≤ n then
    let A := (a.flipBitCommutator i).CycleMinVector (n - i);
    (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      (A[(p : ℕ).mergeBit i false]'
      ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
  else Vector.mkVector _ false

section LeftLayer

theorem getElem_leftLayer {a : VectorPerm (2^(n + 1))} {i : ℕ} (hp : p < 2^n) :
    (leftLayer a i)[p] =
  if hi : i ≤ n then
    (((a.flipBitCommutator i).CycleMinVector (n - i))[p.mergeBit i false]'
    ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (hp.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
  else false := by
  unfold leftLayer
  split_ifs
  · simp_rw [Vector.getElem_map, Vector.getElem_finRange]
  · simp_rw [Vector.getElem_mkVector]

theorem getElem_leftLayer_of_le {a : VectorPerm (2^(n + 1))} {i : ℕ} (hi : i ≤ n) (hp : p < 2^n) :
    (leftLayer a i)[p] =
    (((a.flipBitCommutator i).CycleMinVector (n - i))[p.mergeBit i false]'
    ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (hp.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i := by
  rw [getElem_leftLayer, dif_pos hi]

theorem getElem_leftLayer_of_gt {a : VectorPerm (2^(n + 1))} {i : ℕ} (hi : n < i) (hp : p < 2^n) :
    (leftLayer a i)[p] = false := by
  rw [getElem_leftLayer, dif_neg (hi.not_le)]

theorem getElem_leftLayer_of_lt {a : VectorPerm (2^(n + 1))} (ha : ∀ j < i, a.BitInvariant j)
    (hp : p < 2^i) (hp' : p < 2^n) :
    (leftLayer a i)[p] = false := by
  rcases le_or_lt i n with hi | hi
  · simp_rw [getElem_leftLayer_of_le hi, mergeBit_apply_false_of_lt_two_pow hp,
    getElem_cycleMinVector_of_self_le_getElem (getElem_eq_self_of_forall_bitInvariant_lt_of_lt
    (fun _ hk => (ha _ hk).flipBitCommutator_of_ne hk.ne) hp
    (Nat.pow_le_pow_of_le one_lt_two (hi.trans (Nat.le_succ _)))), testBit_lt_two_pow hp]
  · simp_rw [getElem_leftLayer_of_gt hi]

theorem getElem_zero_leftLayer_zero {a : VectorPerm (2^(n + 1))} :
    (leftLayer a 0)[0] = false := getElem_leftLayer_of_lt
      (by simp only [not_lt_zero', IsEmpty.forall_iff, implies_true]) (Nat.two_pow_pos _) _

end LeftLayer

def leftPerm (a : VectorPerm (2^(n + 1))) (i : ℕ) : VectorPerm (2^(n + 1)) :=
  condFlipBit i (leftLayer a i)

section LeftPerm

theorem getElem_leftPerm (hk : k < 2^(n + 1)) :
  (leftPerm a i)[k] = (condFlipBit i (leftLayer a i))[k] := rfl

theorem getElem_leftPerm_of_gt (hi : n < i) (hk : k < 2^(n + 1))  :
    (leftPerm a i)[k] = k := by
  unfold leftPerm leftLayer
  rw [dif_neg (hi.not_le), getElem_condFlipBit, condFlipBit_of_mkVector_false, ite_self]

@[simp]
theorem getElem_leftPerm_leftPerm (hk : k < 2^(n + 1)) :
    (leftPerm a i)[(leftPerm a i)[k]] = k := getElem_condFlipBit_condFlipBit

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
    · simp_rw [← Bool.not_true, ← hkb, ← flipBit_apply_eq_mergeBit,
      a.flipBit_getElem_cycleMinVector_flipBitCommutator_comm ha hk (Nat.lt_succ_of_le hi),
      Bool.apply_cond (fun (k : ℕ) => k.testBit i), testBit_flipBit_of_eq, hkb,
      Bool.not_true, Bool.cond_not, Bool.cond_false_right, Bool.and_true]
    · simp_rw [← hkb, mergeBit_testBit_testRes_of_eq, Bool.apply_cond (fun (k : ℕ) => k.testBit i),
      testBit_flipBit_of_eq, hkb, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · simp_rw [getElem_leftPerm_of_gt hi, Nat.sub_eq_zero_of_le hi.le, getElem_cycleMinVector_zero]

end LeftPerm

def rightLayer (a : VectorPerm (2^(n + 1))) (i : ℕ) : Vector Bool (2^n) :=
  if hi : i ≤ n then
    let A := (a.flipBitCommutator i).CycleMinVector (n - i);
    let F := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      (A[(p : ℕ).mergeBit i false]'
      ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
    (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      ((a.condFlipBitVals i F)[((p : ℕ).mergeBit i false)]'
      ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
  else Vector.mkVector _ false

section RightLayer

theorem getElem_rightLayer {a : VectorPerm (2^(n + 1))} {i : ℕ} (hp : p < 2^n) :
    (rightLayer a i)[p] =
    if hi : i ≤ n then
    ((leftPerm a i)[a[(p.mergeBit i false)]'
      ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (hp.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))]).testBit i
    else false := by
  unfold rightLayer leftPerm leftLayer
  split_ifs
  · simp_rw [Vector.getElem_map, Vector.getElem_finRange,
      condFlipBitVals_eq_condFlipBit_mul, getElem_mul]
  · simp_rw [Vector.getElem_mkVector]

theorem getElem_rightLayer_of_le {a : VectorPerm (2^(n + 1))} {i : ℕ} (hi : i ≤ n) (hp : p < 2^n) :
    (rightLayer a i)[p] =
    ((leftPerm a i)[a[(p.mergeBit i false)]'
      ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (hp.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))]).testBit i := by
  rw [getElem_rightLayer, dif_pos hi]

theorem getElem_rightLayer_of_gt {a : VectorPerm (2^(n + 1))} {i : ℕ} (hi : n < i) (hp : p < 2^n) :
    (rightLayer a i)[p] = false := by
  rw [getElem_rightLayer, dif_neg (hi.not_le)]

end RightLayer

def rightPerm (a : VectorPerm (2^(n + 1))) (i : ℕ) : VectorPerm (2^(n + 1)) :=
  condFlipBit i (rightLayer a i)

section RightPerm

theorem getElem_rightPerm (hk : k < 2^(n + 1)) :
  (rightPerm a i)[k] = (condFlipBit i (rightLayer a i))[k] := rfl

theorem getElem_rightPerm_of_gt (hi : n < i) (hk : k < 2^(n + 1))  :
    (rightPerm a i)[k] = k := by
  unfold rightPerm rightLayer
  rw [dif_neg (hi.not_le), getElem_condFlipBit, condFlipBit_of_mkVector_false, ite_self]

@[simp]
theorem getElem_rightPerm_rightPerm (hk : k < 2^(n + 1)) :
    (rightPerm a i)[(rightPerm a i)[k]] = k := getElem_condFlipBit_condFlipBit

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
    rw [getElem_rightPerm, getElem_condFlipBit_of_div hin,
      condFlipBit_apply_of_testRes_lt ((testRes_lt_two_pow_iff_lt_two_pow hi).mpr hk),
      getElem_rightLayer_of_le hi]
    rcases Bool.eq_false_or_eq_true (k.testBit i) with hkb | hkb
    · simp_rw [← Bool.not_true, ← hkb, ← flipBit_apply_eq_mergeBit,
        testBit_leftPerm ha, Bool.apply_cond (fun (k : ℕ) => k.testBit i), testBit_flipBit_of_eq,
        ← getElem_flipBit_of_div hin (hk := hk), hkb, Bool.cond_true_right, Bool.not_true,
        Bool.or_false, Bool.not_eq_eq_eq_not, a.flipBitCommutator_cycleMinVector_of_period_bounded
        (period_le_two_pow_sub_of_bitInvariant_lt ha), getElem_flipBit_of_div hin,
        a.flipBit_getElem_cycleMinVector_flipBitCommutator_comm ha (a.getElem_lt _)
          (Nat.lt_succ_of_le hi),
        testBit_flipBit_of_eq]
    · simp_rw [← hkb, mergeBit_testBit_testRes_of_eq, Bool.apply_cond (fun (k : ℕ) => k.testBit i),
      testBit_flipBit_of_eq, hkb, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · simp_rw [getElem_leftPerm_of_gt hi, getElem_rightPerm_of_gt hi,
      (bitInvariant_of_ge (Nat.pow_le_pow_of_le one_lt_two hi)).testBit_getElem_eq_testBit]

end RightPerm

def middlePerm (a : VectorPerm (2^(n + 1))) (i : ℕ) : VectorPerm (2^(n + 1)) :=
  if hi : i ≤ n then
    let A := (a.flipBitCommutator i).CycleMinVector (n - i);
    let L := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      (A[(p : ℕ).mergeBit i false]'
      ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
    let a' := a.condFlipBitVals i L;
    let R := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
      (a'[((p : ℕ).mergeBit i false)]'
      ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
    a'.condFlipBitIndices i R
  else a

section MiddlePerm

theorem middlePerm_eq_condFlipBitVals_condFlipBitIndices {a : VectorPerm (2^(n + 1))} :
    middlePerm a i =
    (a.condFlipBitVals i (leftLayer a i)).condFlipBitIndices i (rightLayer a i) := by
  unfold middlePerm leftLayer rightLayer
  rcases le_or_lt i n with hi | hi
  · simp_rw [dif_pos hi]
  · simp_rw [dif_neg hi.not_le, condFlipBitVals_eq_condFlipBit_mul,
      condFlipBitIndices_eq_mul_condFlipBit, VectorPerm.ext_iff,
      getElem_mul, getElem_condFlipBit, condFlipBit_of_mkVector_false, getElem_lt,
      if_true, ite_self, implies_true]

@[simp] theorem getElem_middlePerm (hk : k < 2^(n + 1)) :
    (middlePerm a i)[k] = (leftPerm a i)[a[(rightPerm a i)[k]]] := by
  unfold middlePerm leftPerm leftLayer rightPerm rightLayer
  simp_rw [condFlipBitVals_eq_condFlipBit_mul,
      condFlipBitIndices_eq_mul_condFlipBit]
  rcases le_or_lt i n with hi | hi
  · simp_rw [dif_pos hi, getElem_mul]
  · simp_rw [dif_neg hi.not_le, getElem_condFlipBit, condFlipBit_of_mkVector_false,
      getElem_lt, if_true, ite_self]

theorem middlePerm_eq_leftPerm_mul_mul_rightPerm  :
    middlePerm a i = leftPerm a i * a * rightPerm a i := by
  ext
  simp_rw [getElem_middlePerm, getElem_mul]

theorem leftPerm_mul_middlePerm_mul_rightPerm  :
    leftPerm a i * middlePerm a i * rightPerm a i = a := by
  ext
  simp_rw [middlePerm_eq_leftPerm_mul_mul_rightPerm, getElem_mul,
    getElem_rightPerm_rightPerm, getElem_leftPerm_leftPerm]

@[simp] theorem bitInvariant_middlePerm {i : ℕ} {a : VectorPerm (2^(n + 1))}
  (ha : ∀ j < i, a.BitInvariant j) : ∀ j ≤ i, (middlePerm a i).BitInvariant j := by
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
    (by simp_rw [not_lt_zero', IsEmpty.forall_iff, implies_true]) _ le_rfl

theorem bitInvariant_middlePerm_of_gt {i : ℕ} {a : VectorPerm (2^(n + 1))} {j : ℕ} (hj : n < j):
  (middlePerm a i).BitInvariant j := bitInvariant_of_ge (Nat.pow_le_pow_of_le one_lt_two hj)

end MiddlePerm

def flmDecomp (a : VectorPerm (2^(n + 1))) (i : ℕ) :
    VectorPerm (2^(n + 1)) × Vector Bool (2^n) × Vector Bool (2^n) :=
  if hi : i ≤ n then
    let A := (a.flipBitCommutator i).CycleMinVector (n - i);
    let L := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
    (A[(p : ℕ).mergeBit i false]'
    ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i;
    let R := (Vector.finRange (2^n)).map fun (p : Fin (2^n)) =>
    ((a.condFlipBitVals i L)[((p : ℕ).mergeBit i false)]'
      ((mergeBit_lt_iff_lt_div_two (n := 2^(n + 1)) (i := i)
      (Nat.pow_dvd_pow _ (Nat.succ_le_succ hi))).mpr
      (p.isLt.trans_eq (by simp_rw [pow_succ, Nat.mul_div_cancel _ zero_lt_two])))).testBit i
    let M := (a.condFlipBitVals i L).condFlipBitIndices i R;
    (M, L, R)
  else (a, Vector.mkVector _ false, Vector.mkVector _ false)

section FlmDecomp

theorem flmDecomp_eq_left_middle_right {a : VectorPerm (2^(n + 1))} :
    flmDecomp a i = (middlePerm a i, leftLayer a i, rightLayer a i) := by
  unfold flmDecomp middlePerm rightLayer leftLayer
  rcases le_or_lt i n with hi | hi
  · simp_rw [dif_pos hi]
  · simp_rw [dif_neg hi.not_le]

@[simp] theorem condFlipBit_flmDecomp_snd_fst {i : ℕ} :
    (condFlipBit i (flmDecomp a i).snd.fst :
    VectorPerm (2^(n + 1))) = leftPerm a i := by
  rw [flmDecomp_eq_left_middle_right]
  rfl

@[simp] theorem condFlipBit_flmDecomp_snd_snd {i : ℕ} :
    (condFlipBit i (flmDecomp a i).snd.snd :
    VectorPerm (2^(n + 1))) = rightPerm a i := by
  rw [flmDecomp_eq_left_middle_right]
  rfl

theorem condFlipBit_flmDecomp_snd_fst_mul_flmDecomp_fst_mul_flmDecomp_snd_snd {i : ℕ} :
    (condFlipBit i (flmDecomp a i).snd.fst) * (flmDecomp a i).fst *
    (condFlipBit i (flmDecomp a i).snd.snd) = a := by
  rw [flmDecomp_eq_left_middle_right]
  exact leftPerm_mul_middlePerm_mul_rightPerm

end FlmDecomp

def ControlBits (k : ℕ) (a : VectorPerm (2^(n + 1))) : Array Bool := Id.run do
    let mut (M, LS, RS) := (a, (#[] : Array (Vector Bool (2^n))),
      (#[] : Array (Vector Bool (2^n)) ))
    for i in [0:k + 1] do
      let (M', L, R) := flmDecomp M i
      M := M'
      if i < n then LS := LS.push L else pure ()
      RS := RS.push R

    pure ((LS ++ RS.reverse).map (Vector.toArray)).flatten

#eval ControlBits (n := 2) 2 (ofVector #v[3,4,1,2,7,6,5,0])

end Decomposition
