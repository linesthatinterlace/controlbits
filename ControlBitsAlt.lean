import Controlbits.PermFintwo
import Controlbits.BitResiduumAlt
import Controlbits.CommutatorCycles
import Controlbits.ArrayPerm

section Decomposition
open Equiv Equiv.Perm Nat Function

abbrev XBackXForth (i : ℕ) (π : Perm ℕ) := ⁅π, flipBitPerm i⁆

lemma xBXF_def {i : ℕ} {π : Perm ℕ} : XBackXForth i π = ⁅π, flipBitPerm i⁆ := rfl

theorem lt_iff_xBXF_lt (h : i < m) (hπ : ∀ q, π q < 2^m ↔ q < 2^m) :
    ∀ q, XBackXForth i π q < 2^m ↔ q < 2^m := fun q => by
  unfold XBackXForth
  simp_rw [commutatorElement_def, Perm.mul_apply, flipBitPerm_inv_apply, flipBitPerm_apply,
  hπ, flipBit_lt_two_pow_iff_lt_two_pow h, ← hπ (π⁻¹ (q.flipBit i)), Perm.apply_inv_self]
  exact flipBit_lt_two_pow_iff_lt_two_pow h

--Theorem 4.3 (c)
lemma univ_filter_sameCycle_le_pow_two {q : ℕ} [DecidableRel (XBackXForth i π).SameCycle]
(hπ : π ∈ Subgroup.bitInvarLT i) :
((Finset.range (2^m)).filter (fun y => (XBackXForth i π).SameCycle q y)).card ≤ 2 ^ m := sorry
  --apply Nat.le_of_mul_le_mul_left _ (zero_lt_two)
  --rw [← pow_succ']
  --have H := two_mul_filter_sameCycle_card_le_card (x := π) (y := flipBit 0)
  --  rfl flipBit_ne_self Finset.univ (fun _ _ => Finset.mem_univ _) q
  --exact H.trans_eq (by simp_rw [Finset.card_univ, Fintype.card_fin])

-- Theorem 4.4
lemma cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF {π : Perm ℕ}
  (hπ : π ∈ Subgroup.bitInvarLT i) :
(XBackXForth i π).CycleMin (q.flipBit i) = ((XBackXForth i π).CycleMin q).flipBit i := by
  refine' cycleMin_cmtr_right_apply_eq_apply_cycleMin_cmtr' (q :=q) rfl (fun _ => flipBit_ne_self)
    (fun h h' => eq_flipBit_of_lt_of_flipBit_ge_of_lt_testBit_eq h h'.le (fun hk => _))
  rw [Subgroup.mem_bitInvarLT_iff] at hπ
  specialize hπ _ hk
  simp_rw [(hπ.commutatorElement
    (flipBitPerm_bitInvariant_of_ne hk.ne)).zpow_perm_bitInvariant.testBit_apply_eq_testBit]

lemma blahj {π : Perm ℕ} (hπ : π ∈ Subgroup.bitInvarLT i) (hπ' : π ∈ Subgroup.bitInvarGE (m + 1))
  (hp : p < 2 ^ m) :
    FastCycleMin (m - i) (XBackXForth i π) (p.mergeBit i false) =
    (XBackXForth i π).CycleMin (p.mergeBit i false) := by
  classical
  refine' fastCycleMin_eq_cycleMin_of_zpow_apply_mem_finset
    ((Finset.range (2^(m + 1))).filter (fun y => (XBackXForth i π).SameCycle (p.mergeBit i false) y)) _ _
  · rw [Finset.card_filter_le_iff]
  · simp only [Finset.mem_filter, Finset.mem_range, sameCycle_zpow_right, Perm.SameCycle.rfl, and_true]
    intro k
    sorry
    --refine' (lt_iff_xBXF_lt _ _ _).mp _

/-

-/
def FirstLayer'' (a : ArrayPerm n) (m i : ℕ) :
    Array Bool := (Array.range (2^m)).map
  fun p => ((a.flipBitCommutator i).CycleMin (m - i) (p.mergeBit i false)).testBit i

def FirstLayer' (a : ArrayPerm n) (m i : ℕ) :
    Array Bool := (Array.range (2^m)).map
  fun p => (((a.flipBitCommutator i).CycleMinArray (m - i)).getD (p.mergeBit i false) 0).testBit i

def Array.popOff' (a : Array α) (n : ℕ) [NeZero n] : Array α :=
  (·.2.2) <| a.foldl (init := (true, (0 : Fin n), Array.empty)) fun (b, n, r) a =>
    ((n == -1).xor b, n + 1, if b then r.push a else r)

def FirstLayer (a : ArrayPerm n) (m i : ℕ) :
    Array Bool :=
      let A := (a.flipBitCommutator i).CycleMinArray (m - i);
      (Fin.enum (2^m)).map fun p => (A[p.1.mergeBit i false]?.getD 0).testBit i

theorem size_firstLayer (a : ArrayPerm n) (m i : ℕ) : (FirstLayer a m i).size = 2^m := by
  unfold FirstLayer
  simp_rw [Array.size_map, Fin.size_enum]

theorem getElem_firstLayer (m : ℕ) (a : ArrayPerm (2^(m + 1))) (i : Fin (m + 1)) {x : ℕ}
    (hx : x < (FirstLayer a m i).size) :
    (FirstLayer a m i)[x] = ((a.flipBitCommutator i).CycleMin i.rev (x.mergeBit i false)).testBit i := by
  unfold FirstLayer
  simp_rw [Array.getElem_map, Fin.getElem_enum]
  have H : x.mergeBit i false < ((a.flipBitCommutator i).CycleMinArray (m - i)).size := by
    simp
    rw [mergeBit_lt_two_pow_iff_lt_two_pow i.is_le]
    exact hx.trans_eq (size_firstLayer _ _ _)
  rw [Array.getD_eq_get_lt _ _ _ H, ArrayPerm.getElem_cycleMinArray _ _ H, Fin.val_rev,
  Nat.add_sub_add_right]


def FirstLayer4 (a : ArrayPerm n) (m i : ℕ)  :
    Array Bool := (((a.flipBitCommutator i).CycleMinArray (m - i)).map (testBit · i)).popOff' (2^i)

def LastLayer (a : ArrayPerm n) (m i : ℕ) :
    Array Bool :=
    let A := (a⁻¹.condFlipBit i (FirstLayer a m i)).bwdArray;
    (Fin.enum (2^m)).map fun p => (A[p.1.mergeBit i false]?.getD 0).testBit i

def MiddlePerm (a : ArrayPerm n) (m i : ℕ) : ArrayPerm n :=
  (a⁻¹.condFlipBit i (FirstLayer a m i))⁻¹.condFlipBit i (LastLayer a m i)

def FLMDecomp (a : ArrayPerm n) (m i : ℕ) : Array Bool × ArrayPerm n × Array Bool :=
(FirstLayer a m i, MiddlePerm a m i, LastLayer a m i)

def CBAux (a : ArrayPerm n) (m i : ℕ) : List (Array Bool) :=
let (F, M, L) := FLMDecomp a m i;
if m ≤ i then [L] else F :: CBAux M m (i + 1) ++ [L]
termination_by m - i

#eval CBAux (ArrayPerm.ofArray #[2, 3, 5, 1, 0, 7, 4, 6]) 2 0

def Bits (a : ArrayPerm n) (m : ℕ) (i : Fin (m + 1)) : ArrayPerm n :=
i.induction (MiddlePerm a m 0) fun i a => MiddlePerm a m i.succ


set_option profiler true
--#eval Bits (1 : ArrayPerm (2^13)) 12 12


--#eval (Array.range (2^12)).map (fun p => (Array.range (2^12)).getD (mergeBit 3 p true) 0)
--#eval FirstLayer' (1 : ArrayPerm (2^9)) 10 8
#eval FirstLayer (1 : ArrayPerm (2^15)) 14 8
--#eval FirstLayer'' (1 : ArrayPerm (2^9)) 11 8
--#eval FirstLayer4 (1 : ArrayPerm (2^15)) 14 8
--#eval FirstLayer5 14 (1 : ArrayPerm (2^15)) 8
/-





example : ∀ (i : ℕ) (hi : i < #[0, 1, 2, 3, 4, 5, 6].size), #[0, 1, 2, 3, 4, 5, 6][i] < 7 := by decide

#eval ArrayPerm.ofArray #[7, 4, 3, 1, 0, 2, 6, 5]

#eval
  let a := ArrayPerm.ofArray #[0, 3, 2, 1, 5, 4]
  let f0 := FirstLayer a 2 0;
  let l0 := LastLayer a 2 0;
  let m0 := MiddlePerm a 2 0;
  (a, f0, l0, m0)

#eval
  let a := ArrayPerm.ofArray #[1, 3, 2, 5, 4, 0, 6, 7]
  let f0 := FirstLayer a 2 0;
  let l0 := LastLayer a 2 0;
  let m0 := MiddlePerm a 2 0;
  let f1 := FirstLayer m0 2 1;
  let l1 := LastLayer m0 2 1;
  let m1 := MiddlePerm m0 2 1
  let f2 := FirstLayer m1 2 2;
  let l2 := LastLayer m1 2 2;
  let m2 := MiddlePerm m1 2 2
  (a, f0, l0, m0, f1, l1, m1, f2, l2, m2)
/-if i = Fin.last _ then
MiddlePerm a m m ((pow_dvd_pow _ le_rfl).trans hin)
 else
MiddlePerm (Bits a m hin (i + 1)) m i ((pow_dvd_pow _ (by simp only [add_le_add_iff_right, Fin.is_le])).trans hin)
-/
--#eval ((1 : ArrayPerm (2^15)).CycleMinAux 6)
--

--#eval LastLayer (1 : ArrayPerm (2^12)) 11 0
-- 8 - 278
-- 7 - 33.5
-- 6 5.26
-- 4 0.25

#check MiddlePerm (ArrayPerm.mk #[1, 2, 3, 0] #[3, 0, 1, 2]) 1 0

#eval MiddlePerm (ArrayPerm.mk #[1, 2, 7, 5, 3, 4, 0, 6] #[6, 0, 1, 4, 5, 3, 7, 2])
  2 0

#eval MiddlePerm (MiddlePerm (MiddlePerm (ArrayPerm.mk #[1, 2, 7, 5, 3, 4, 0, 6] #[6, 0, 1, 4, 5, 3, 7, 2])
  2 0) 2 1) 2 2 (_)

-/
    /--/

def LastLayer (a : ArrayPerm n) (m i : ℕ) (hin : 2 ^ (i + 1) ∣ n) :
    Array Bool := (Array.range (2^m)).map
  fun p => ((a.flipBitCommutator hin).CycleMin (m - i) (p.mergeBit i false)).testBit i


def FirstLayer (π : Perm ℕ) (m i : ℕ) : Array Bool := (Array.range (2^m)).map
  fun p => (FastCycleMin (m - i) (XBackXForth i π) (p.mergeBit i false)).testBit i

#eval [0, 1, 2, 3].map <| ((Equiv.swap (2 : ℕ) 3) * (Equiv.swap (0 : ℕ) 2) * (Equiv.swap (0 : ℕ) 1))
#eval FirstLayer (((Equiv.swap (2 : ℕ) 3) * (Equiv.swap (0 : ℕ) 2) * (Equiv.swap (0 : ℕ) 1))) 1 0
/-def FirstLayer (π : Perm ℕ) (m i : ℕ) : Array Bool :=
  (Array.range (2^m)).map fun p => testBit (FastCycleMin (m - i) (XBackXForth i π) p) i-/

@[simp]
lemma size_firstLayer : (FirstLayer π m i).size = 2^m := by
  unfold FirstLayer
  rw [Array.size_map, Array.size_range]

@[simp]
lemma firstLayer_getElem (h : p < (FirstLayer π m i).size) : (FirstLayer π m i)[p] =
    testBit (FastCycleMin (m - i) (XBackXForth i π) (p.mergeBit i false)) i := by
  unfold FirstLayer
  simp_rw [Array.getElem_map, Array.getElem_range]

lemma firstLayer_getElem' (h : p < (FirstLayer π m i).size) (hπ : π ∈ Subgroup.bitInvarLT i)
    (hπ' : π ∈ Subgroup.bitInvarGE (m + 1)) :
  (FirstLayer π m i)[p] = testBit (CycleMin (XBackXForth i π) (p.mergeBit i false)) i := by
  unfold FirstLayer
  simp_rw [Array.getElem_map, Array.getElem_range]
  congr
  rw [size_firstLayer] at h
  exact blahj hπ hπ' h

def FirstLayerPerm (π : Perm ℕ) (m i : ℕ) := Nat.condFlipBitPerm (FirstLayer π m i) i

lemma firstLayerPerm_apply (hπ : π ∈ Subgroup.bitInvarLT i)
    (hπ' : π ∈ Subgroup.bitInvarGE (m + 1)) (hq : q < 2^(m + 1)) (hi : i ≤ m) :
    FirstLayerPerm π m i q =
  bif (CycleMin (XBackXForth i π) ((q.testRes i).mergeBit i false )).testBit i
  then q.flipBit i else q := by
  unfold FirstLayerPerm
  rw [condFlipBitPerm_apply,
    condFlipBit_eq_of_testRes_lt (((lt_iff_testRes_lt hi).mp hq).trans_eq size_firstLayer.symm),
    firstLayer_getElem' _ hπ hπ']

-- Theorem 5.3
lemma testBit_zero_firstLayerPerm_apply_eq_testBit_zero_cycleMin {q} :
    testBit i (FirstLayerPerm i π q) = testBit i (CycleMin (XBackXForth i π) q) := by
  simp_rw [firstLayerPerm_apply, Bool.apply_cond (testBit i), testBit_flipBit]
  rcases mergeBitRes_getRes_cases_flipBit i q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · simp_rw [h₁, h₂, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · simp_rw [h₁, h₂]
    simp


def LastLayer (π : Perm ℕ) (m i : ℕ) : Array Bool := (Array.range (2^m)).map
  fun p => ((π (p.mergeBit i false)).condFlipBit (FirstLayer π m i) i).testBit i

@[simp]
lemma size_lastLayer : (LastLayer π m i).size = 2^m := by
  unfold LastLayer
  rw [Array.size_map, Array.size_range]

def LastLayerPerm (π : Perm ℕ) (m i : ℕ) := Nat.condFlipBitPerm (LastLayer π m i) i


def MiddlePerm (π : Perm ℕ) (m i : ℕ) := (FirstLayerPerm π m i) * π * (LastLayerPerm π m i)

-- Theorem 5.2
lemma firstLayer_apply_zero {π : Perm ℕ} : (FirstLayer π m i)[0] = false := by
  simp_rw [firstLayer_getElem, zero_mergeBit_false, fastCycleMin_apply_zero, zero_testBit]

end Decomposition

/-




abbrev ControlBitsLayer (m : ℕ) := BV m → Bool




lemma firstLayer_def {i : Fin (m + 1)} : FirstLayer (π : Perm (BV (m + 1))) i p =
(FastCycleMin i.rev (XBackXForth i π) (p.mergeBit i false)).testBit i  := by rfl

lemma firstLayer_apply {i : Fin (m + 1)} : FirstLayer π i p =
  testBit (CycleMin (XBackXForth i π) (p.mergeBit i false)) i := by
  rw [FirstLayer]
  congr
  exact cycleMin_eq_fastCycleMin sorry

-- Theorem 5.2
lemma firstLayer_apply_zero {π : Perm (BV (m + 1))} :
  FirstLayer π i 0 = false := by
  simp_rw [firstLayer_apply,
    Fin.cycleMin_zero, testBit_apply_zero]

def LastLayer (i : Fin (m + 1)) (π : Perm (BV (m + 1))) : ControlBitsLayer m :=
  fun p => testBit i ((FirstLayerPerm i π) (π (mergeBitRes i false p)))

def LastLayerPerm (i : Fin (m + 1)) (π : Perm (BV (m + 1))) := condFlipBit i (LastLayer i π)

def MiddlePerm (i : Fin (m + 1)) (π : Perm (BV (m + 1))) :=
(FirstLayerPerm i π) * π * (LastLayerPerm i π)

@[simp]
lemma condFlipBit_firstLayer : condFlipBit 0 (FirstLayer π i) = FirstLayerPerm i π := rfl

lemma firstLayerPerm_apply : FirstLayerPerm i π q =
  bif testBit i (CycleMin (XBackXForth i π) (mergeBitRes i false (getRes i q)))
  then flipBit i q else q := firstLayer_apply ▸ condFlipBit_apply

@[simp]
lemma firstLayerPerm_symm : (FirstLayerPerm i π).symm = FirstLayerPerm i π := rfl

@[simp]
lemma inv_firstLayerPerm : (FirstLayerPerm i π)⁻¹ = FirstLayerPerm i π := rfl

@[simp]
lemma firstLayerPerm_firstLayerPerm : FirstLayerPerm i π (FirstLayerPerm i π q) = q :=
  condFlipBit_condFlipBit

@[simp]
lemma firstLayerPerm_mul_self : (FirstLayerPerm i π) * (FirstLayerPerm i π) = 1 :=
  condFlipBit_mul_self

@[simp]
lemma firstLayerPerm_mul_cancel_right : ρ * (FirstLayerPerm i π) * (FirstLayerPerm i π) = ρ :=
condFlipBit_mul_cancel_right

@[simp]
lemma firstLayerPerm_mul_cancel_left : (FirstLayerPerm i π) * ((FirstLayerPerm i π) * ρ) = ρ :=
condFlipBit_mul_cancel_left

-- Theorem 5.3
lemma testBit_zero_firstLayerPerm_apply_eq_testBit_zero_cycleMin {q} :
    testBit i (FirstLayerPerm i π q) = testBit i (CycleMin (XBackXForth i π) q) := by
  simp_rw [firstLayerPerm_apply, Bool.apply_cond (testBit i), testBit_flipBit]
  rcases mergeBitRes_getRes_cases_flipBit i q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · simp_rw [h₁, h₂, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · simp_rw [h₁, h₂]
    simp

lemma lastLayer_apply : LastLayer π p =
  testBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false p))) :=
  testBit_zero_firstLayerPerm_apply_eq_testBit_zero_cycleMin

lemma lastLayer_base : LastLayer (m := 0) π = fun _ => decide (π 0 = 1) := by
  ext
  simp_rw [LastLayer, firstLayerPerm_base, mergeBitRes_base_false,
    testBit_base, Perm.one_apply]

def LastLayerPerm (π : Perm (BV (m + 1))) := condFlipBit 0 (LastLayer π)

@[simp]
lemma condFlipBit_lastLayer : condFlipBit 0 (LastLayer π) = LastLayerPerm π := rfl

lemma lastLayerPerm_apply : LastLayerPerm π q =
  bif testBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false (getRes 0 q))))
  then flipBit 0 q
  else q := by
  simp_rw [← condFlipBit_lastLayer, condFlipBit_apply, lastLayer_apply]

lemma lastLayerPerm_base : LastLayerPerm (m := 0) π = π := by
  simp_rw [LastLayerPerm, lastLayer_base, condFlipBit_base, Bool.cond_decide]
  exact (perm_fin_two π).symm

@[simp]
lemma lastLayerPerm_symm : (LastLayerPerm π).symm = LastLayerPerm π := rfl

@[simp]
lemma lastLayerPerm_inv : (LastLayerPerm π)⁻¹ = LastLayerPerm π := rfl

@[simp]
lemma lastLayerPerm_lastLayerPerm : LastLayerPerm π (LastLayerPerm π q) = q := condFlipBit_condFlipBit

@[simp]
lemma lastLayerPerm_mul_self : (LastLayerPerm π) * (LastLayerPerm π) = 1 := condFlipBit_mul_self

@[simp]
lemma lastLayerPerm_mul_cancel_right : ρ * (LastLayerPerm π) * (LastLayerPerm π) = ρ :=
condFlipBit_mul_cancel_right

@[simp]
lemma lastLayerPerm_mul_cancel_left : (LastLayerPerm π) * ((LastLayerPerm π) * ρ) = ρ :=
condFlipBit_mul_cancel_left

-- Theorem 5.4
lemma testBit_zero_lastLayerPerm_apply_eq_testBit_zero_firstLayerPerm_perm_apply :
    testBit 0 (LastLayerPerm π q) = testBit 0 (FirstLayerPerm π (π q)) := by
  rw [testBit_zero_firstLayerPerm_apply_eq_testBit_zero_cycleMin]
  rw [lastLayerPerm_apply, Bool.apply_cond (testBit 0), testBit_flipBit]
  rcases mergeBitRes_getRes_cases_flipBit 0 q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · rw [h₁, h₂, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · rw [h₁, h₂, Bool.not_false, Bool.not_true, Bool.cond_true_right, Bool.or_false,
    cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero_apply,
    cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF, testBit_flipBit, Bool.not_not]

abbrev PartialControlBits (m n : ℕ) := Fin (2*n + 1) → ControlBitsLayer m
-/

namespace PartialControlBits

variable {m : ℕ}

def toPerm (n : Fin (m + 1)) :
  PartialControlBits m n → Perm (BV (m + 1)) :=
  n.induction (fun cb => condFlipBit (last _) (cb 0))
  (fun i re cb =>
    condFlipBit (i.rev.castSucc) (cb 0) *
    re (fun i => cb i.castSucc.succ) *
    condFlipBit (i.rev.castSucc) (cb (last _)))

lemma toPerm_zero {cb : PartialControlBits m 0} :
  toPerm 0 cb = condFlipBit (last _) (cb 0) := rfl

lemma toPerm_succ {n : Fin m} {cb} : toPerm (n.succ) cb =
    condFlipBit (n.rev.castSucc) (cb 0) * toPerm (n.castSucc) (fun i ↦ cb i.castSucc.succ) *
    condFlipBit (n.rev.castSucc) (cb (last _)) := rfl

def fromPerm {m : ℕ} (n : Fin (m + 1)) : Perm (BV (m + 1)) → PartialControlBits m n :=
n.induction (fun π _ => LastLayer (Fin.last _) π)
(fun n re π => Fin.cons (FirstLayer n.rev.castSucc π)
  (Fin.snoc (re (MiddlePerm n.rev.castSucc π)) (LastLayer n.rev.castSucc π)))

lemma fromPerm_zero : fromPerm (0 : Fin (m + 1)) = fun π _ => LastLayer (last _) π := rfl

lemma fromPerm_succ {n : Fin m} {π : Perm (BV (m + 1))} :
  fromPerm n.succ π = Fin.cons (FirstLayer n.rev.castSucc π)
  (Fin.snoc (fromPerm n.castSucc (MiddlePerm n.rev.castSucc π)) (LastLayer n.rev.castSucc π)) := rfl

lemma toPerm_leftInverse (n : Fin (m + 1)) : (toPerm n).LeftInverse (fromPerm n) := by
  unfold Function.LeftInverse
  induction' n using Fin.induction with n IH
  · simp_rw [fromPerm_zero, toPerm_zero]
    sorry
  · simp_rw [fromPerm_succ, toPerm_succ]

/-

    piFinSuccCastSucc.symm ((FirstLayer n.rev.castSucc π, LastLayer n.rev.castSucc π),
    re (MiddlePerm n.rev.castSucc π)))

-/
end PartialControlBits


abbrev ControlBits (m : ℕ) := PartialControlBits m m

namespace ControlBits

variable {m : ℕ}

abbrev toPerm : ControlBits m → Perm (BV (m + 1)) :=
  PartialControlBits.toPerm (last _)

def fromPerm {m : ℕ} : Perm (BV (m + 1)) → ControlBits m  := PartialControlBits.fromPerm (last _)

end ControlBits

abbrev SerialControlBits (m : ℕ) := Fin ((2*m + 1)*(2^m)) → Bool

namespace SerialControlBits

variable {m : ℕ}

def equivControlBits {m : ℕ} : SerialControlBits m ≃ ControlBits m :=
(finProdFinEquiv.arrowCongr (Equiv.refl _)).symm.trans (curry _ _ _)

def toPerm (cb : SerialControlBits m) : Perm (BV (m + 1)) :=
  (ControlBits.toPerm (m := m)) (equivControlBits cb)

def fromPerm (π : Perm (BV (m + 1))) : SerialControlBits m :=
  equivControlBits.symm (ControlBits.fromPerm (m := m) π)

end SerialControlBits

def serialControlBits1 : SerialControlBits 1 := ![true, false, true, false, false, false]
def controlBits1 : ControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def controlBits1_normal  : ControlBits 1 := ![![false, true], ![false, true], ![true, true]]
def controlBits1_perm : Perm (BV 2) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv s := by fin_cases s <;> rfl
  right_inv s := by fin_cases s <;> rfl

def serialControlBits2 : SerialControlBits 2 :=
  (![true, false, true, false, true, false, false, false, false, false,
  false, false, false, false, false, true, false, false, false, false] )
def controlBits2 : ControlBits 2 :=
  (![![true, false, true, false], ![true, false, false, false], ![false, false,
  false, false], ![false, false, false, true], ![false, false, false, false]] )
def controlBits2_normal : ControlBits 2 :=
  ![![false, true, false, true],
  ![false, false, false, false],
  ![false, false, false, false],
  ![false, true, true, false],
  ![true, true, true, true]]

def controlBits3_normal : ControlBits 3 :=
![![false, false, false, false, false, false, false, false],
  ![false, false, false, false, false, false, false, false],
  ![false, false, false, false, false, false, false, false],
  ![false, false, false, false, true, true, true, true],
  ![false, false, true, true, true, true, false, false],
  ![false, true, true, false, false, true, true, false],
  ![false, true, false, true, false, true, false, true]]



def controlBits2_perm : Perm (Fin 8) := ArrayPerm.mulEquivPerm (ArrayPerm.mk (n := 8)
  (#[2, 0, 1, 3, 5, 7, 6, 4]) (#[1, 2, 0, 3, 7, 4, 6, 5]))

def controlBits3_perm : Perm (Fin 16) := ArrayPerm.mulEquivPerm <| ArrayPerm.mk (n := 16)
  (#[0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8])
  (#[0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1])

def controlBits4_perm : Perm (Fin 32) := ArrayPerm.mulEquivPerm <| ArrayPerm.mk (n := 32)
  (#[0, 31, 1, 30, 2, 29, 3, 28, 4, 27, 5, 26, 6, 25, 7, 24,
      8, 23, 9, 22, 10, 21, 11, 20, 12, 19, 13, 18, 14, 17, 15, 16])
  (#[0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26,
    28, 30, 31, 29, 27, 25, 23, 21, 19, 17, 15, 13, 11, 9, 7, 5, 3, 1])

def foo (n : ℕ) (i : Fin 32) : Fin 32 :=
match n with
| 0 => controlBits4_perm i
| (n + 1) => (foo n) (foo n i)

instance repr_pifin_perm {n : ℕ} : Repr (Perm (Fin n)) :=
  ⟨fun f _ => Std.Format.paren (Std.Format.joinSep
      ((List.finRange n).map fun n => repr (f n)) (" " ++ Std.Format.line))⟩

instance repr_unique {α β : Type u} [Repr α] [Unique β] : Repr (β → α) :=
  ⟨fun f _ => repr (f default)⟩

instance repr_bool {α : Type u} [Repr α] : Repr (Bool → α) :=
  ⟨fun f _ => repr (f false) ++ " | " ++ repr (f true)⟩

#eval serialControlBits1.toPerm
#eval controlBits1.toPerm
#eval controlBits1_normal.toPerm
#eval controlBits1_perm
#eval (ControlBits.fromPerm (m := 1) controlBits1_perm)
--#eval (ControlBits.fromPerm <| serialControlBits2.toPerm)

#eval serialControlBits2.toPerm
#eval controlBits2.toPerm
#eval controlBits2_normal.toPerm
#eval controlBits2_perm
#eval FirstLayer (m := 2) 0 controlBits2_perm
#eval MiddlePerm (m := 2) 0 controlBits2_perm
#eval MiddlePerm 1 <| MiddlePerm (m := 2) 0 controlBits2_perm
#eval LastLayerPerm 1 <| MiddlePerm (m := 2) 0 controlBits2_perm
#eval (FirstLayerPerm 1 <| MiddlePerm (m := 2) 0 controlBits2_perm) *
  (MiddlePerm 1 <| MiddlePerm (m := 2) 0 controlBits2_perm) * (LastLayerPerm 1 <| MiddlePerm (m := 2) 0 controlBits2_perm)
#eval (ControlBits.fromPerm (m := 2) controlBits2_perm)
--#eval (ControlBits.fromPerm <| serialControlBits2.toPerm)

-- #eval MiddlePerm controlBits3_perm
#eval FastCycleMin 1 controlBits4_perm 12
set_option profiler true
#eval ControlBits.fromPerm (m := 2) controlBits2_perm
#eval ControlBits.fromPerm (m := 3) controlBits3_perm
#eval controlBits3_normal.toPerm

/-

-- Theorem 4.3 (c)
lemma orderOf_xBXF_cycleOf {i : Fin (m + 1)} {π : Perm (BV (m + 1))} {q : BV (m + 1)}
    (h : ∀ k < i, bitInvar k ⇑π) : orderOf ((XBackXForth i π).cycleOf q) ≤ 2^m := by
refine' le_of_le_of_eq (cycleAt_cmtr_card_le_card_univ_div_two rfl flipBit_ne_self) _
· rw [Finset.card_fin, pow_succ, Nat.mul_div_left _ Nat.ofNat_pos]

-- Theorem 4.4
lemma cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF :
CycleMin (XBackXForth i π) (flipBit i q) = (flipBit i) (CycleMin (XBackXForth i π) q) :=
cycleMin_cmtr_right_apply_eq_apply_cycleMin_cmtr rfl flipBit_ne_self _

lemma cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero_apply :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = CycleMin (XBackXForth π) (flipBit 0 (π q)) :=
cycleMin_cmtr_apply_comm



lemma firstLayer_def : FirstLayer (π : Perm (BV (m + 1))) p =
testBit 0 (FastCycleMin m (XBackXForth π) (mergeBitRes 0 false p)) := by rfl

lemma firstLayer_apply : FirstLayer π p =
  testBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p)) := by
  rw [FirstLayer, cycleMin_eq_fastCycleMin orderOf_xBXF_cycleOf]

-- Theorem 5.2
lemma firstLayer_apply_zero {π : Perm (BV (m + 1))} :
  FirstLayer π 0 = false := by
  simp_rw [firstLayer_apply, mergeBitRes_apply_false_zero,
    Fin.cycleMin_zero, testBit_apply_zero]

lemma firstLayer_base : FirstLayer (m := 0) π = ![false] := by
  ext
  simp_rw [eq_zero, firstLayer_apply_zero, Matrix.cons_val_fin_one]

def FirstLayerPerm (π : Perm (BV (m + 1))) := condFlipBit 0 (FirstLayer π)

@[simp]
lemma condFlipBit_firstLayer : condFlipBit 0 (FirstLayer π) = FirstLayerPerm π := rfl

lemma firstLayerPerm_apply : FirstLayerPerm π q =
  bif testBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false (getRes 0 q)))
  then flipBit 0 q else q := firstLayer_apply ▸ condFlipBit_apply

lemma firstLayerPerm_base : FirstLayerPerm (m := 0) π = 1 := by
  ext
  simp_rw [FirstLayerPerm, firstLayer_base, condFlipBit_apply, Matrix.cons_val_fin_one,
    cond_false, Perm.coe_one, id_eq]

@[simp]
lemma firstLayerPerm_symm : (FirstLayerPerm π).symm = FirstLayerPerm π := rfl

@[simp]
lemma inv_firstLayerPerm : (FirstLayerPerm π)⁻¹ = FirstLayerPerm π := rfl

@[simp]
lemma firstLayerPerm_firstLayerPerm : FirstLayerPerm π (FirstLayerPerm π q) = q :=
  condFlipBit_condFlipBit

@[simp]
lemma firstLayerPerm_mul_self : (FirstLayerPerm π) * (FirstLayerPerm π) = 1 :=
  condFlipBit_mul_self

@[simp]
lemma firstLayerPerm_mul_cancel_right : ρ * (FirstLayerPerm π) * (FirstLayerPerm π) = ρ :=
condFlipBit_mul_cancel_right

@[simp]
lemma firstLayerPerm_mul_cancel_left : (FirstLayerPerm π) * ((FirstLayerPerm π) * ρ) = ρ :=
condFlipBit_mul_cancel_left

-- Theorem 5.3
lemma testBit_zero_firstLayerPerm_apply_eq_testBit_zero_cycleMin {q} :
    testBit 0 (FirstLayerPerm π q) = testBit 0 (CycleMin (XBackXForth π) q) := by
  simp_rw [firstLayerPerm_apply, Bool.apply_cond (testBit 0), testBit_flipBit]
  rcases mergeBitRes_getRes_cases_flipBit 0 q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · simp_rw [h₁, h₂, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · simp_rw [h₁, h₂, cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF,
    testBit_flipBit, Bool.not_false, Bool.not_true,  Bool.cond_false_left, Bool.and_true,
    Bool.not_not]

def LastLayer (π : Perm (BV (m + 1))) : ControlBitsLayer m :=
  fun p => testBit 0 ((FirstLayerPerm π) (π (mergeBitRes 0 false p)))

lemma lastLayer_apply : LastLayer π p =
  testBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false p))) :=
  testBit_zero_firstLayerPerm_apply_eq_testBit_zero_cycleMin

lemma lastLayer_base : LastLayer (m := 0) π = fun _ => decide (π 0 = 1) := by
  ext
  simp_rw [LastLayer, firstLayerPerm_base, mergeBitRes_base_false,
    testBit_base, Perm.one_apply]

def LastLayerPerm (π : Perm (BV (m + 1))) := condFlipBit 0 (LastLayer π)

@[simp]
lemma condFlipBit_lastLayer : condFlipBit 0 (LastLayer π) = LastLayerPerm π := rfl

lemma lastLayerPerm_apply : LastLayerPerm π q =
  bif testBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false (getRes 0 q))))
  then flipBit 0 q
  else q := by
  simp_rw [← condFlipBit_lastLayer, condFlipBit_apply, lastLayer_apply]

lemma lastLayerPerm_base : LastLayerPerm (m := 0) π = π := by
  simp_rw [LastLayerPerm, lastLayer_base, condFlipBit_base, Bool.cond_decide]
  exact (perm_fin_two π).symm

@[simp]
lemma lastLayerPerm_symm : (LastLayerPerm π).symm = LastLayerPerm π := rfl

@[simp]
lemma lastLayerPerm_inv : (LastLayerPerm π)⁻¹ = LastLayerPerm π := rfl

@[simp]
lemma lastLayerPerm_lastLayerPerm : LastLayerPerm π (LastLayerPerm π q) = q := condFlipBit_condFlipBit

@[simp]
lemma lastLayerPerm_mul_self : (LastLayerPerm π) * (LastLayerPerm π) = 1 := condFlipBit_mul_self

@[simp]
lemma lastLayerPerm_mul_cancel_right : ρ * (LastLayerPerm π) * (LastLayerPerm π) = ρ :=
condFlipBit_mul_cancel_right

@[simp]
lemma lastLayerPerm_mul_cancel_left : (LastLayerPerm π) * ((LastLayerPerm π) * ρ) = ρ :=
condFlipBit_mul_cancel_left

-- Theorem 5.4
lemma testBit_zero_lastLayerPerm_apply_eq_testBit_zero_firstLayerPerm_perm_apply :
    testBit 0 (LastLayerPerm π q) = testBit 0 (FirstLayerPerm π (π q)) := by
  rw [testBit_zero_firstLayerPerm_apply_eq_testBit_zero_cycleMin]
  rw [lastLayerPerm_apply, Bool.apply_cond (testBit 0), testBit_flipBit]
  rcases mergeBitRes_getRes_cases_flipBit 0 q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · rw [h₁, h₂, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · rw [h₁, h₂, Bool.not_false, Bool.not_true, Bool.cond_true_right, Bool.or_false,
    cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero_apply,
    cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF, testBit_flipBit, Bool.not_not]

def MiddlePerm (π : Perm (BV (m + 1))) : bitInvarSubgroup (0 : Fin (m + 1)) :=
  ⟨(FirstLayerPerm π) * π * (LastLayerPerm π), by
    simp_rw [mem_bitInvarSubgroup, bitInvar_iff_testBit_apply_eq_testBit,
    Perm.coe_mul, Function.comp_apply,
    ← testBit_zero_lastLayerPerm_apply_eq_testBit_zero_firstLayerPerm_perm_apply,
    ← Perm.mul_apply, lastLayerPerm_mul_self, Perm.one_apply, implies_true]⟩

lemma MiddlePerm_mem_bitInvarSubgroup_zero : (MiddlePerm π).val ∈ bitInvarSubgroup 0 :=
  SetLike.coe_mem _

lemma MiddlePerm_mem_bitInvarSubmonoid_zero : ⇑(MiddlePerm π).val ∈ bitInvarSubmonoid 0 :=
  MiddlePerm_mem_bitInvarSubgroup_zero

lemma MiddlePerm_bitInvar_zero : bitInvar 0 ⇑(MiddlePerm π).val :=
  MiddlePerm_mem_bitInvarSubgroup_zero

lemma MiddlePerm_val : (MiddlePerm π : Perm (BV (m + 1))) =
  FirstLayerPerm π * π * LastLayerPerm π := rfl

lemma firstMiddleLast_decomposition {π : Perm (BV (m + 1))} :
  π = FirstLayerPerm π * MiddlePerm π * LastLayerPerm π := by
  simp_rw [MiddlePerm_val, mul_assoc (a := FirstLayerPerm π),
    firstLayerPerm_mul_cancel_left, lastLayerPerm_mul_cancel_right]

end Decomposition

abbrev PartialControlBits (m n : ℕ) := Fin (2*n + 1) → ControlBitsLayer m

namespace PartialControlBits

variable {m : ℕ}

def PartialControlBitsZero : PartialControlBits m 0 ≃ ControlBitsLayer m :=
  funUnique (Fin 1) (ControlBitsLayer m)

def toPerm (n : Fin (m + 1)) :
  PartialControlBits m n → Perm (BV (m + 1)) :=
  n.induction (fun cb => condFlipBit (last _) (cb 0))
  (fun i re cb =>
    condFlipBit (i.rev.castSucc) (cb 0) *
    re (fun i => cb i.castSucc.succ) *
    condFlipBit (i.rev.castSucc) (cb (last _)))

lemma toPerm_zero {cb : PartialControlBits m 0} :
  toPerm 0 cb = condFlipBit (last _) (cb 0) := rfl

lemma toPerm_succ {n : Fin m} {cb} : toPerm (n.succ) cb =
    condFlipBit (n.rev.castSucc) (cb 0) * toPerm (n.castSucc) (fun i ↦ cb i.castSucc.succ) *
    condFlipBit (n.rev.castSucc) (cb (last _)) := rfl

lemma toPerm_succ_castSucc {n : Fin (m + 1)} {cb} :
    toPerm (n.castSucc) cb = (bitInvarMulEquiv 0) (fun b =>
    toPerm n (fun i p => cb i (mergeBitRes 0 b p))) := by
  induction' n using induction with i IH
  · simp_rw [castSucc_zero, toPerm_zero,
    bitInvarMulEquiv_zero_apply_condFlipBits, succ_last]
  · simp_rw [← succ_castSucc, toPerm_succ,  IH, ← Pi.mul_def,
    MulEquiv.map_mul, Submonoid.coe_mul, bitInvarMulEquiv_zero_apply_condFlipBits,
    rev_castSucc,  succ_castSucc, coe_castSucc]

lemma toPerm_succ_last {cb : PartialControlBits (m + 1) (m + 1)} :
    toPerm (last _) cb =
  condFlipBit 0 (cb 0) * ((bitInvarMulEquiv 0) fun b =>
    toPerm (last _) fun i k => cb i.castSucc.succ (mergeBitRes 0 b k)) *
    condFlipBit 0 (cb (last _)) := by
  simp_rw [← succ_last, toPerm_succ, rev_last, toPerm_succ_castSucc, castSucc_zero,
  succ_last, val_last]

lemma bitInvar_zero_toPerm_castSucc {n : Fin m} {cb} :
    bitInvar 0 ⇑(toPerm n.castSucc cb) := by
  cases m
  · exact n.elim0
  · rw [toPerm_succ_castSucc]
    exact Subtype.prop _

lemma bitInvar_zero_toPerm_of_ne_last {n : Fin (m + 1)} (h : n ≠ last _) {cb} :
    bitInvar 0 ⇑(toPerm n cb) := by
  rcases (exists_castSucc_eq_of_ne_last h) with ⟨_, rfl⟩
  exact bitInvar_zero_toPerm_castSucc

lemma bitInvar_toPerm {n t : Fin (m + 1)} (htn : t < n.rev) {cb} :
    bitInvar t ⇑(toPerm n cb) := by
  induction' n using inductionOn with n IH
  · exact condFlipBit_bitInvar_of_ne htn.ne
  · rw [rev_succ] at htn
    rw [rev_castSucc] at IH
    simp_rw [toPerm_succ]
    have H := fun {c} => (condFlipBit_bitInvar_of_ne (c := c) htn.ne)
    refine' bitInvar_mulPerm_of_bitInvar (bitInvar_mulPerm_of_bitInvar H (IH _)) H
    exact htn.trans (castSucc_lt_succ _)

end PartialControlBits

-- SECTION

abbrev ControlBits (m : ℕ) := PartialControlBits m m

namespace ControlBits

variable {m : ℕ}

abbrev toPerm : ControlBits m → Perm (BV (m + 1)) :=
  PartialControlBits.toPerm (last _)

lemma toPerm_zero {cb : ControlBits 0} : toPerm cb = condFlipBit 0 (cb 0) := rfl

lemma toPerm_succ {cb : ControlBits (m + 1)} : toPerm cb = condFlipBit 0 (cb 0) *
    (bitInvarMulEquiv 0) (fun b => toPerm
    (fun i k => cb i.castSucc.succ (mergeBitRes 0 b k))) * condFlipBit 0 (cb (last _)) :=
  PartialControlBits.toPerm_succ_last

def fromPerm {m : ℕ} : Perm (BV (m + 1)) → ControlBits m :=
match m with
| 0 => fun π _ => LastLayer π
| (_ + 1) => fun π => piFinSuccCastSucc.symm ((FirstLayer π, LastLayer π), (fun p =>
    fromPerm ((bitInvarMulEquiv 0).symm (MiddlePerm π) (testBit 0 p)) · (getRes 0 p)))

lemma fromPerm_zero : fromPerm (m := 0) = fun π _ => LastLayer π := rfl

lemma fromPerm_succ {π : Perm (BV (m + 2))} : fromPerm π =
  piFinSuccCastSucc.symm ((FirstLayer π, LastLayer π), (fun p =>
  fromPerm ((bitInvarMulEquiv 0).symm (MiddlePerm π) (testBit 0 p)) · (getRes 0 p))) := rfl

lemma fromPerm_succ_apply_zero {π : Perm (BV (m + 2))} :
  fromPerm π 0 = FirstLayer π := piFinSuccCastSucc_symm_apply_zero _ _ _

lemma fromPerm_succ_apply_last {π : Perm (BV (m + 2))} :
    fromPerm π (last _) = LastLayer π := piFinSuccCastSucc_symm_apply_last _ _ _

lemma fromPerm_succ_apply_castSucc_succ : fromPerm π i.castSucc.succ =
    fun p => fromPerm ((bitInvarMulEquiv 0).symm
    (MiddlePerm π) (testBit 0 p)) i (getRes 0 p) :=
  piFinSuccCastSucc_symm_apply_castSucc_succ _ _ _ _

lemma fromPerm_succ_apply_succ_castSucc : fromPerm π i.succ.castSucc =
    fun p => fromPerm ((bitInvarMulEquiv 0).symm
    (MiddlePerm π) (testBit 0 p)) i (getRes 0 p) :=
  fromPerm_succ_apply_castSucc_succ

lemma fromPerm_succ_apply_mergeBitRes {π : Perm (BV (m + 2))} :
    (fun i k => fromPerm π i.castSucc.succ (mergeBitRes 0 b k)) =
    fromPerm ((bitInvarMulEquiv 0).symm (MiddlePerm π) b) := by
  simp_rw [fromPerm_succ_apply_castSucc_succ, testBit_mergeBitRes, getRes_mergeBitRes]

lemma toPerm_leftInverse : (toPerm (m := m)).LeftInverse fromPerm := by
  unfold Function.LeftInverse ; induction' m with m IH <;> intro π
  · exact lastLayerPerm_base
  · trans FirstLayerPerm π * MiddlePerm π * LastLayerPerm π
    · refine' toPerm_succ.trans _
      refine' congrArg₂ _ (congrArg₂ _ _ (congrArg _ _)) _
      · rw [fromPerm_succ_apply_zero, condFlipBit_firstLayer]
      · simp_rw [fromPerm_succ_apply_mergeBitRes, IH, (bitInvarMulEquiv 0).apply_symm_apply]
      · rw [fromPerm_succ_apply_last, condFlipBit_lastLayer]
    · exact firstMiddleLast_decomposition.symm

lemma fromPerm_rightInverse : (fromPerm (m := m)).RightInverse toPerm := toPerm_leftInverse

def unweave : ControlBits (m + 1) ≃
(ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → ControlBits m) :=
  calc
  _ ≃ _ :=    piFinSuccCastSucc.trans ((Equiv.refl _).prodCongr
    (calc
    _ ≃ _ :=  (Equiv.refl _).arrowCongr (((testBitRes 0).arrowCongr (Equiv.refl _)).trans
              (curry _ _ _))
    _ ≃ _ :=  (piComm _)))

lemma unweave_apply_fst_fst {cb : ControlBits (m + 1)} : (unweave cb).1.1 = cb 0 := rfl

lemma unweave_apply_fst_snd {cb : ControlBits (m + 1)} :
    (unweave cb).1.2 = cb (last _) := rfl

lemma unweave_apply_snd {cb : ControlBits (m + 1)} : (unweave cb).2 =
  fun b i k => cb i.castSucc.succ (mergeBitRes 0 b k) := by
  ext ; exact congr_fun (congr_fun (piFinSuccCastSucc_apply_snd cb) _) _

lemma unweave_symm_apply_zero {fl ll : ControlBitsLayer (m + 1)} {mbs} :
    unweave.symm ((fl, ll), mbs) 0 = fl := rfl

lemma unweave_symm_apply_last {fl ll : ControlBitsLayer (m + 1)} {mbs} :
    unweave.symm ((fl, ll), mbs) (last _) = ll := by
  simp_rw [unweave, instTrans_trans, symm_trans_apply]
  exact (piFinSuccCastSucc_symm_apply_last _ _ _)

lemma unweave_symm_apply_castSucc_succ {i : Fin (2*m + 1)} {fl ll mbs} :
    unweave.symm ((fl, ll), mbs) (i.castSucc.succ) = fun p => (mbs (testBit 0 p) i (getRes 0 p)) := by
  simp_rw [unweave, instTrans_trans, symm_trans_apply]
  exact (piFinSuccCastSucc_symm_apply_castSucc_succ fl ll _ _)

lemma unweave_symm_apply_succ_castSucc {i : Fin (2*m + 1)} {fl ll mbs} :
    unweave.symm ((fl, ll), mbs) (i.succ.castSucc) = fun p => (mbs (testBit 0 p) i (getRes 0 p)) := by
  simp_rw [unweave, instTrans_trans, symm_trans_apply]
  exact (piFinSuccCastSucc_symm_apply_succ_castSucc fl ll _ _)

end ControlBits

abbrev SerialControlBits (m : ℕ) := Fin ((2*m + 1)*(2^m)) → Bool

namespace SerialControlBits

variable {m : ℕ}

def equivControlBits {m : ℕ} : SerialControlBits m ≃ ControlBits m :=
(finProdFinEquiv.arrowCongr (Equiv.refl _)).symm.trans (curry _ _ _)

def toPerm (cb : SerialControlBits m) : Perm (BV (m + 1)) :=
  (ControlBits.toPerm (m := m)) (equivControlBits cb)

def fromPerm (π : Perm (BV (m + 1))) : SerialControlBits m :=
  equivControlBits.symm (ControlBits.fromPerm (m := m) π)

lemma toPerm_leftInverse : (toPerm (m := m)).LeftInverse (fromPerm)  :=
  Function.LeftInverse.comp equivControlBits.right_inv ControlBits.toPerm_leftInverse

lemma fromPerm_rightInverse : (fromPerm (m := m)).RightInverse (toPerm) := toPerm_leftInverse

end SerialControlBits

def serialControlBits1 : SerialControlBits 1 := ![true, false, true, false, false, false]
def controlBits1 : ControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def controlBits1_normal  : ControlBits 1 := ![![false, true], ![false, true], ![true, true]]
def controlBits1_perm : Perm (BV 2) where
  toFun := ![2, 0, 1, 3]
  invFun := ![1, 2, 0, 3]
  left_inv s := by fin_cases s <;> rfl
  right_inv s := by fin_cases s <;> rfl

def serialControlBits2 : SerialControlBits 2 :=
  (![true, false, true, false, true, false, false, false, false, false,
  false, false, false, false, false, true, false, false, false, false] )
def controlBits2 : ControlBits 2 :=
  (![![true, false, true, false], ![true, false, false, false], ![false, false,
  false, false], ![false, false, false, true], ![false, false, false, false]] )
def controlBits2_normal : ControlBits 2 :=
  ![![false, true, false, true],
  ![false, false, false, false],
  ![false, false, false, false],
  ![false, true, true, false],
  ![true, true, true, true]]

def controlBits3_normal : ControlBits 3 :=
![![false, false, false, false, false, false, false, false],
  ![false, false, false, false, false, false, false, false],
  ![false, false, false, false, false, false, false, false],
  ![false, false, false, false, true, true, true, true],
  ![false, false, true, true, true, true, false, false],
  ![false, true, true, false, false, true, true, false],
  ![false, true, false, true, false, true, false, true]]



def controlBits2_perm : Perm (Fin 8) := ArrayPerm.mulEquivPerm (ArrayPerm.mk (n := 8)
  (#[2, 0, 1, 3, 5, 7, 6, 4]) (#[1, 2, 0, 3, 7, 4, 6, 5]))

def controlBits3_perm : Perm (Fin 16) := ArrayPerm.mulEquivPerm <| ArrayPerm.mk (n := 16)
  (#[0, 15, 1, 14, 2, 13, 3, 12, 4, 11, 5, 10, 6, 9, 7, 8])
  (#[0, 2, 4, 6, 8, 10, 12, 14, 15, 13, 11, 9, 7, 5, 3, 1])

def controlBits4_perm : Perm (Fin 32) := ArrayPerm.mulEquivPerm <| ArrayPerm.mk (n := 32)
  (#[0, 31, 1, 30, 2, 29, 3, 28, 4, 27, 5, 26, 6, 25, 7, 24,
      8, 23, 9, 22, 10, 21, 11, 20, 12, 19, 13, 18, 14, 17, 15, 16])
  (#[0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26,
    28, 30, 31, 29, 27, 25, 23, 21, 19, 17, 15, 13, 11, 9, 7, 5, 3, 1])

def foo (n : ℕ) (i : Fin 32) : Fin 32 :=
match n with
| 0 => controlBits4_perm i
| (n + 1) => (foo n) (foo n i)

instance repr_pifin_perm {n : ℕ} : Repr (Perm (Fin n)) :=
  ⟨fun f _ => Std.Format.paren (Std.Format.joinSep
      ((List.finRange n).map fun n => repr (f n)) (" " ++ Std.Format.line))⟩

instance repr_unique {α β : Type u} [Repr α] [Unique β] : Repr (β → α) :=
  ⟨fun f _ => repr (f default)⟩

instance repr_bool {α : Type u} [Repr α] : Repr (Bool → α) :=
  ⟨fun f _ => repr (f false) ++ " | " ++ repr (f true)⟩

#eval serialControlBits1.toPerm
#eval controlBits1.toPerm
#eval controlBits1_normal.toPerm
#eval controlBits1_perm
#eval (ControlBits.fromPerm (m := 1) controlBits1_perm)
--#eval (ControlBits.fromPerm <| serialControlBits2.toPerm)

#eval serialControlBits2.toPerm
#eval controlBits2.toPerm
#eval controlBits2_normal.toPerm
#eval controlBits2_perm
#eval (ControlBits.fromPerm (m := 2) controlBits2_perm)
--#eval (ControlBits.fromPerm <| serialControlBits2.toPerm)

-- #eval MiddlePerm controlBits3_perm
#eval FastCycleMin 1 controlBits4_perm 12
#eval MiddlePerm (m := 4) controlBits4_perm
set_option profiler true
#eval ControlBits.fromPerm (m := 2) controlBits2_perm
#eval ControlBits.fromPerm (m := 3) controlBits3_perm
#eval controlBits3_normal.toPerm
-/
