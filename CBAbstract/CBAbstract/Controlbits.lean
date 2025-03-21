import CBAbstract.BitResiduum
import CBAbstract.CommutatorCycles
import CBAbstract.PermFintwo
import Mathlib.Tactic.FinCases
import Mathlib.GroupTheory.Perm.Cycle.Factors
open Fin Equiv

abbrev ControlBitsLayer (m : ℕ) := BV m → Bool

variable {m : ℕ} {π : Perm (BV (m + 1))} {q : BV (m + 1)} {p : BV m}

section Decomposition

abbrev XBackXForth (π : Perm (BV (m + 1))) := ⁅π, flipBit (0 : Fin (m + 1))⁆

lemma xBXF_def {π : Perm (BV (m + 1))} :
    XBackXForth π = ⁅π, flipBit (0 : Fin (m + 1))⁆ := rfl

lemma xBXF_base {π : Perm (BV 1)} : XBackXForth (m := 0) π = 1 := cmtr_fin_two

--Theorem 4.3 (c)
lemma univ_filter_sameCycle_le_pow_two {q : BV (m + 1)} :
(Finset.univ.filter (fun y => (XBackXForth π).SameCycle q y)).card ≤ 2 ^ m := by
  apply Nat.le_of_mul_le_mul_left _ (zero_lt_two)
  rw [← pow_succ']
  have H := two_mul_filter_sameCycle_card_le_card (x := π) (y := flipBit 0)
    rfl flipBit_ne_self Finset.univ (fun _ _ => Finset.mem_univ _) q
  exact H.trans_eq (by simp_rw [Finset.card_univ, Fintype.card_fin])

-- Theorem 4.4
lemma cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF {π : Perm (BV (m + 1))} :
(XBackXForth π).CycleMin (flipBit 0 q) = (flipBit 0) ((XBackXForth π).CycleMin q) :=
  cycleMin_cmtr_right_apply_eq_apply_cycleMin_cmtr
    rfl flipBit_ne_self eq_flipBit_of_lt_of_flipBit_gt

lemma cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero {q : BV (m + 1)} :
(XBackXForth π).CycleMin (π (flipBit 0 q)) = (XBackXForth π).CycleMin (flipBit 0 (π q)) :=
cycleMin_cmtr_apply_comm

def FirstLayer (π : Perm (BV (m + 1))) : ControlBitsLayer m :=
  fun p => getBit 0 ((XBackXForth π).FastCycleMin m (mergeBitRes 0 false p))

lemma firstLayer_def : FirstLayer (π : Perm (BV (m + 1))) p =
getBit 0 ((XBackXForth π).FastCycleMin m (mergeBitRes 0 false p)) := by rfl

lemma firstLayer_apply {π : Perm (BV (m + 1))} : FirstLayer π p =
  getBit 0 ((XBackXForth π).CycleMin (mergeBitRes 0 false p)) := by
  refine congrArg (getBit 0 ·) <| (XBackXForth π).fastCycleMin_eq_cycleMin_of_zpow_apply_mem_finset
    (Finset.univ.filter (fun y => (XBackXForth π).SameCycle (mergeBitRes 0 false p) y))
    univ_filter_sameCycle_le_pow_two ?_
  simp_rw [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.sameCycle_zpow_right,
    Perm.SameCycle.rfl, implies_true]

-- Theorem 5.2
lemma firstLayer_apply_zero {π : Perm (BV (m + 1))} :
  FirstLayer π 0 = false := by
  simp_rw [firstLayer_apply, mergeBitRes_apply_false_zero,
    Fin.cycleMin_zero, getBit_apply_zero]

lemma firstLayer_base  {π : Perm (BV 1)} : FirstLayer (m := 0) π = ![false] := by
  ext
  simp_rw [eq_zero, firstLayer_apply_zero, Matrix.cons_val_fin_one]

def FirstLayerPerm (π : Perm (BV (m + 1))) := condFlipBit 0 (FirstLayer π)

@[simp]
lemma condFlipBit_firstLayer : condFlipBit 0 (FirstLayer π) = FirstLayerPerm π := rfl

lemma firstLayerPerm_apply {q : BV (m + 1)} : FirstLayerPerm π q =
  bif getBit 0 ((XBackXForth π).CycleMin (mergeBitRes 0 false (getRes 0 q)))
  then flipBit 0 q else q := firstLayer_apply ▸ condFlipBit_apply

lemma firstLayerPerm_base  {π : Perm (BV 1)} : FirstLayerPerm (m := 0) π = 1 := by
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

variable {ρ : Equiv.Perm (BV (m + 1))}

@[simp]
lemma firstLayerPerm_mul_cancel_right : ρ * (FirstLayerPerm π) * (FirstLayerPerm π) = ρ :=
condFlipBit_mul_cancel_right

@[simp]
lemma firstLayerPerm_mul_cancel_left : (FirstLayerPerm π) * ((FirstLayerPerm π) * ρ) = ρ :=
condFlipBit_mul_cancel_left

-- Theorem 5.3
lemma getBit_zero_firstLayerPerm_apply_eq_getBit_zero_cycleMin {q : BV (m + 1)} :
    getBit 0 (FirstLayerPerm π q) = getBit 0 ((XBackXForth π).CycleMin q) := by
  simp_rw [firstLayerPerm_apply, Bool.apply_cond (getBit 0), getBit_flipBit_of_eq]
  rcases mergeBitRes_getRes_cases_flipBit 0 q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · simp_rw [h₁, h₂, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · simp_rw [h₁, h₂, cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF,
    getBit_flipBit_of_eq, Bool.not_false, Bool.not_true,  Bool.cond_false_left, Bool.and_true,
    Bool.not_not]

def LastLayer (π : Perm (BV (m + 1))) : ControlBitsLayer m :=
  fun p => getBit 0 ((FirstLayerPerm π) (π (mergeBitRes 0 false p)))

lemma lastLayer_apply {p : BV m} : LastLayer π p =
  getBit 0 ((XBackXForth π).CycleMin (π (mergeBitRes 0 false p))) :=
  getBit_zero_firstLayerPerm_apply_eq_getBit_zero_cycleMin

lemma lastLayer_base {π : Perm (BV 1)} : LastLayer (m := 0) π = fun _ => decide (π 0 = 1) := by
  ext
  simp_rw [LastLayer, firstLayerPerm_base, mergeBitRes_base_false,
    getBit_base, Perm.one_apply]

def LastLayerPerm (π : Perm (BV (m + 1))) := condFlipBit 0 (LastLayer π)

@[simp]
lemma condFlipBit_lastLayer : condFlipBit 0 (LastLayer π) = LastLayerPerm π := rfl

lemma lastLayerPerm_apply {q : BV (m + 1)} : LastLayerPerm π q =
  bif getBit 0 ( (XBackXForth π).CycleMin (π (mergeBitRes 0 false (getRes 0 q))))
  then flipBit 0 q
  else q := by
  simp_rw [← condFlipBit_lastLayer, condFlipBit_apply, lastLayer_apply]

lemma lastLayerPerm_base {π : Perm (BV 1)} : LastLayerPerm (m := 0) π = π := by
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
lemma getBit_zero_lastLayerPerm_apply_eq_getBit_zero_firstLayerPerm_perm_apply :
    getBit 0 (LastLayerPerm π q) = getBit 0 (FirstLayerPerm π (π q)) := by
  rw [getBit_zero_firstLayerPerm_apply_eq_getBit_zero_cycleMin]
  rw [lastLayerPerm_apply, Bool.apply_cond (getBit 0), getBit_flipBit_of_eq]
  rcases mergeBitRes_getRes_cases_flipBit 0 q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · rw [h₁, h₂, Bool.not_false, Bool.cond_false_right, Bool.and_true]
  · rw [h₁, h₂, Bool.not_false, Bool.not_true, Bool.cond_true_right, Bool.or_false,
    cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero,
    cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF, getBit_flipBit_of_eq, Bool.not_not]

def MiddlePerm (π : Perm (BV (m + 1))) : bitInvarSubgroup (0 : Fin (m + 1)) :=
  ⟨(FirstLayerPerm π) * π * (LastLayerPerm π), by
    simp_rw [mem_bitInvarSubgroup, bitInvar_iff_getBit_apply_eq_getBit,
    Perm.coe_mul, Function.comp_apply,
    ← getBit_zero_lastLayerPerm_apply_eq_getBit_zero_firstLayerPerm_perm_apply,
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

def toPermPartial (n : Fin (m + 1)) :
  PartialControlBits m n → Perm (BV (m + 1)) :=
  n.induction (fun cb => condFlipBit (last _) (cb 0))
  (fun i re cb =>
    condFlipBit (i.rev.castSucc) (cb 0) *
    re (fun i => cb i.castSucc.succ) *
    condFlipBit (i.rev.castSucc) (cb (last _)))

lemma toPermPartial_zero {cb : PartialControlBits m 0} :
  toPermPartial 0 cb = condFlipBit (last _) (cb 0) := rfl

lemma toPermPartial_succ {n : Fin m} {cb} : toPermPartial (n.succ) cb =
    condFlipBit (n.rev.castSucc) (cb 0) * toPermPartial (n.castSucc) (fun i ↦ cb i.castSucc.succ) *
    condFlipBit (n.rev.castSucc) (cb (last _)) := rfl

lemma toPermPartial_succ_castSucc {n : Fin (m + 1)} {cb} :
    toPermPartial (n.castSucc) cb = (bitInvarMulEquiv 0) (fun b =>
    toPermPartial n (fun i p => cb i (mergeBitRes 0 b p))) := by
  induction' n using induction with i IH
  · simp_rw [castSucc_zero, toPermPartial_zero,
    bitInvarMulEquiv_zero_apply_condFlipBits, succ_last]
  · simp_rw [← succ_castSucc, toPermPartial_succ,  IH, ← Pi.mul_def,
    map_mul, Subgroup.coe_mul, bitInvarMulEquiv_zero_apply_condFlipBits,
    rev_castSucc,  succ_castSucc, coe_castSucc]

lemma toPermPartial_succ_last {cb : PartialControlBits (m + 1) (m + 1)} :
    toPermPartial (last _) cb =
  condFlipBit 0 (cb 0) * ((bitInvarMulEquiv 0) fun b =>
    toPermPartial (last _) fun i k => cb i.castSucc.succ (mergeBitRes 0 b k)) *
    condFlipBit 0 (cb (last _)) := by
  simp_rw [← succ_last, toPermPartial_succ, rev_last, toPermPartial_succ_castSucc, castSucc_zero,
  succ_last, val_last]

lemma bitInvar_zero_toPermPartial_castSucc {n : Fin m} {cb} :
    bitInvar 0 ⇑(toPermPartial n.castSucc cb) := by
  cases m
  · exact n.elim0
  · rw [toPermPartial_succ_castSucc]
    exact Subtype.prop _

lemma bitInvar_zero_toPermPartial_of_ne_last {n : Fin (m + 1)} (h : n ≠ last _) {cb} :
    bitInvar 0 ⇑(toPermPartial n cb) := by
  rcases (eq_castSucc_of_ne_last h) with ⟨_, rfl⟩
  exact bitInvar_zero_toPermPartial_castSucc

lemma bitInvar_toPermPartial {n t : Fin (m + 1)} (htn : t < n.rev) {cb} :
    bitInvar t ⇑(toPermPartial n cb) := by
  induction' n using inductionOn with n IH
  · exact condFlipBit_bitInvar_of_ne htn.ne
  · rw [rev_succ] at htn
    rw [rev_castSucc] at IH
    simp_rw [toPermPartial_succ]
    have H := fun {c} => (condFlipBit_bitInvar_of_ne (c := c) htn.ne)
    refine bitInvar_mulPerm_of_bitInvar (bitInvar_mulPerm_of_bitInvar H (IH ?_)) H
    exact htn.trans (castSucc_lt_succ _)

end PartialControlBits

-- SECTION

abbrev ControlBits (m : ℕ) := PartialControlBits m m

namespace ControlBits

variable {m : ℕ}

abbrev toPerm : ControlBits m → Perm (BV (m + 1)) :=
  PartialControlBits.toPermPartial (last _)

lemma toPerm_zero {cb : ControlBits 0} : toPerm cb = condFlipBit 0 (cb 0) := rfl

lemma toPerm_succ {cb : ControlBits (m + 1)} : toPerm cb = condFlipBit 0 (cb 0) *
    (bitInvarMulEquiv 0) (fun b => toPerm
    (fun i k => cb i.castSucc.succ (mergeBitRes 0 b k))) * condFlipBit 0 (cb (last _)) :=
  PartialControlBits.toPermPartial_succ_last

def fromPerm {m : ℕ} : Perm (BV (m + 1)) → ControlBits m :=
match m with
| 0 => fun π _ => LastLayer π
| (_ + 1) => fun π => piFinSuccCastSucc.symm ((FirstLayer π, LastLayer π), (fun p =>
    fromPerm ((bitInvarMulEquiv 0).symm (MiddlePerm π) (getBit 0 p)) · (getRes 0 p)))

lemma fromPerm_zero : fromPerm (m := 0) = fun π _ => LastLayer π := rfl

lemma fromPerm_succ {π : Perm (BV (m + 2))} : fromPerm π =
  piFinSuccCastSucc.symm ((FirstLayer π, LastLayer π), (fun p =>
  fromPerm ((bitInvarMulEquiv 0).symm (MiddlePerm π) (getBit 0 p)) · (getRes 0 p))) := rfl

lemma fromPerm_succ_apply_zero {π : Perm (BV (m + 2))} :
  fromPerm π 0 = FirstLayer π := piFinSuccCastSucc_symm_apply_zero _ _ _

lemma fromPerm_succ_apply_last {π : Perm (BV (m + 2))} :
    fromPerm π (last _) = LastLayer π := piFinSuccCastSucc_symm_apply_last _ _ _

lemma fromPerm_succ_apply_castSucc_succ {π : Perm (BV (m + 2))} {i} :
    fromPerm π i.castSucc.succ =
    fun p => fromPerm ((bitInvarMulEquiv 0).symm
    (MiddlePerm π) (getBit 0 p)) i (getRes 0 p) :=
  piFinSuccCastSucc_symm_apply_castSucc_succ _ _ _ _

lemma fromPerm_succ_apply_mergeBitRes {π : Perm (BV (m + 2))} {b : Bool} :
    (fun i k => fromPerm π i.castSucc.succ (mergeBitRes 0 b k)) =
    fromPerm ((bitInvarMulEquiv 0).symm (MiddlePerm π) b) := by
  simp_rw [fromPerm_succ_apply_castSucc_succ, getBit_mergeBitRes, getRes_mergeBitRes]

lemma toPerm_leftInverse : (toPerm (m := m)).LeftInverse fromPerm := by
  unfold Function.LeftInverse ; induction' m with m IH <;> intro π
  · exact lastLayerPerm_base
  · trans FirstLayerPerm π * MiddlePerm π * LastLayerPerm π
    · rw [toPerm_succ]
      refine congrArg₂ _ (congrArg₂ _ ?_ (congrArg _ ?_)) ?_
      · rw [fromPerm_succ_apply_zero, condFlipBit_firstLayer]
      · simp_rw [fromPerm_succ_apply_mergeBitRes, IH, (bitInvarMulEquiv 0).apply_symm_apply]
      · rw [fromPerm_succ_apply_last, condFlipBit_lastLayer]
    · exact firstMiddleLast_decomposition.symm

lemma fromPerm_rightInverse : (fromPerm (m := m)).RightInverse toPerm := toPerm_leftInverse

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
  left_inv s := by
    fin_cases s <;> rfl
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

/-


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
#eval (CBAbstract.fromPerm (m := 1) controlBits1_perm)
--#eval (CBAbstract.fromPerm <| serialControlBits2.toPerm)

#eval serialControlBits2.toPerm
#eval controlBits2.toPerm
#eval controlBits2_normal.toPerm
#eval controlBits2_perm
#eval (CBAbstract.fromPerm (m := 2) controlBits2_perm)
--#eval (CBAbstract.fromPerm <| serialControlBits2.toPerm)

-- #eval MiddlePerm controlBits3_perm
#eval Perm.FastCycleMin 1 controlBits4_perm 12
#eval MiddlePerm (m := 4) controlBits4_perm
set_option profiler true
#eval CBAbstract.fromPerm (m := 2) controlBits2_perm
#eval CBAbstract.fromPerm (m := 3) controlBits3_perm
#eval controlBits3_normal.toPerm
-/
