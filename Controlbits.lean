import Controlbits.PermFintwo
import Controlbits.BitResiduumEquivs
import Controlbits.FoldFin
import Controlbits.CommutatorCycles
import Controlbits.Equivs
import Controlbits.Bool
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

section ControlBits

def XBackXForth (π : Equiv.Perm (Fin (2^(m + 1)))) := ⁅π, (flipBit (0 : Fin (m + 1)))⁆

lemma XBackXForth_def {π : Equiv.Perm (Fin (2^(m + 1)))} :
  XBackXForth π = ⁅π, (flipBit (0 : Fin (m + 1)))⁆ := rfl

lemma xBXF_base : XBackXForth (m := 0) π = 1 := Fin.cmtr_fin_two

-- Theorem 4.3 (c)
lemma orderOf_xBXF_cycleOf {q : Fin (2 ^ (m + 1))} :
  orderOf ((XBackXForth π).cycleOf q) ≤ 2^m := by
refine' le_of_le_of_eq (cycleAt_cmtr_card_le_card_univ_div_two rfl flipBit_ne_self) _
· rw [Finset.card_fin, pow_succ, Nat.mul_div_right _ (zero_lt_two)]

-- Theorem 4.4
lemma cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF :
CycleMin (XBackXForth π) (flipBit 0 q) = (flipBit 0) (CycleMin (XBackXForth π) q) := by
exact cycleMin_cmtr_right_apply_eq_apply_cycleMin_cmtr rfl flipBit_ne_self eq_flipBit_of_lt_of_flipBit_gt

lemma cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero_apply :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = CycleMin (XBackXForth π) (flipBit 0 (π q)) :=
cycleMin_cmtr_apply_comm

def FirstControlBits (π : Equiv.Perm (Fin (2^(m + 1)))) (p : Fin (2^m)) :=
getBit 0 (FastCycleMin m (XBackXForth π) (mergeBitRes 0 false p))

lemma firstControlBits_def : FirstControlBits (π : Equiv.Perm (Fin (2^(m + 1)))) p =
getBit 0 (FastCycleMin m (XBackXForth π) (mergeBitRes 0 false p)) := by rfl

lemma firstControlBits_apply : FirstControlBits π p = getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p)) := by
rw [FirstControlBits, cycleMin_eq_fastCycleMin orderOf_xBXF_cycleOf]

-- Theorem 5.2
lemma firstControlBits_apply_zero {π : Equiv.Perm (Fin (2^(m + 1)))} : FirstControlBits π 0 = false := by
simp_rw [firstControlBits_apply, mergeBitRes_apply_false_zero, Fin.cycleMin_zero, getBit_apply_zero]

lemma firstControlBits_base : FirstControlBits (m := 0) π = ![false] := by
  ext
  simp_rw [Fin.eq_zero, firstControlBits_apply_zero]

def FirstControl (π : Equiv.Perm (Fin (2^(m + 1)))) := resCondFlip 0 (FirstControlBits π)

@[simp]
lemma resCondFlip_firstControlBits : resCondFlip 0 (FirstControlBits π) = FirstControl π := rfl

lemma firstControl_apply : FirstControl π q =
bif getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false (getRes 0 q))) then flipBit 0 q else q :=
firstControlBits_apply ▸ resCondFlip_apply

lemma firstControl_base : FirstControl (m := 0) π = 1 := by
  ext
  simp_rw [FirstControl, firstControlBits_base, resCondFlip_apply, Matrix.cons_val_fin_one,
    cond_false, Equiv.Perm.coe_one, id_eq]

@[simp]
lemma firstControl_symm : (FirstControl π).symm = FirstControl π := rfl

@[simp]
lemma firstControl_inv : (FirstControl π)⁻¹ = FirstControl π := rfl

@[simp]
lemma firstControl_firstControl : FirstControl π (FirstControl π q) = q := resCondFlip_resCondFlip

@[simp]
lemma firstControl_mul_self : (FirstControl π) * (FirstControl π) = 1 := resCondFlip_mul_self

@[simp]
lemma firstControl_mul_cancel_right : ρ * (FirstControl π) * (FirstControl π) = ρ := resCondFlip_mul_cancel_right

@[simp]
lemma firstControl_mul_cancel_left : (FirstControl π) * ((FirstControl π) * ρ) = ρ := resCondFlip_mul_cancel_left

-- Theorem 5.3
lemma getBit_zero_firstControl_apply_eq_getBit_zero_cycleMin :
∀ {q}, getBit 0 (FirstControl π q) = getBit 0 (CycleMin (XBackXForth π) q) := by
simp_rw [forall_iff_forall_mergeBitRes 0, ← resCondFlip_firstControlBits, getBit_resCondFlip', getRes_mergeBitRes,
  getBit_mergeBitRes, Bool.xor_false, Bool.xor_true, ← Bool.not_false, ← flipBit_mergeBitRes,
  cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF, getBit_flipBit, firstControlBits_apply, forall_const]

def LastControlBits (π) (p : Fin (2^m)) :=
getBit 0 ((FirstControl π) (π (mergeBitRes 0 false p)))

lemma lastControlBits_apply : LastControlBits π p =
getBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false p))) := getBit_zero_firstControl_apply_eq_getBit_zero_cycleMin

lemma lastControlBits_base : LastControlBits (m := 0) π = ![decide (π 0 = 1)] := by
  ext
  simp_rw [LastControlBits, firstControl_base, mergeBitRes_false_base_eq_zero,
    getBit_base, Equiv.Perm.one_apply, Matrix.cons_val_fin_one]

def LastControl (π : Equiv.Perm (Fin (2^(m + 1)))) := resCondFlip 0 (LastControlBits π)

@[simp]
lemma resCondFlip_lastControlBits : resCondFlip 0 (LastControlBits π) = LastControl π := rfl

lemma lastControl_apply : LastControl π q =
bif getBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false (getRes 0 q)))) then flipBit 0 q else q := by
simp_rw [← resCondFlip_lastControlBits, resCondFlip_apply, lastControlBits_apply]

lemma lastControl_base : LastControl (m := 0) π = if π 0 = 1 then Equiv.swap 0 1 else 1 := by
  simp_rw [LastControl, lastControlBits_base, resCondFlip_base, Matrix.cons_val_fin_one,
    Bool.cond_decide]

@[simp]
lemma lastControl_symm : (LastControl π).symm = LastControl π := rfl

@[simp]
lemma lastControl_inv : (LastControl π)⁻¹ = LastControl π := rfl

@[simp]
lemma lastControl_lastControl : LastControl π (LastControl π q) = q := resCondFlip_resCondFlip

@[simp]
lemma lastControl_mul_self : (LastControl π) * (LastControl π) = 1 := resCondFlip_mul_self

@[simp]
lemma lastControl_mul_cancel_right : ρ * (LastControl π) * (LastControl π) = ρ := resCondFlip_mul_cancel_right

@[simp]
lemma lastControl_mul_cancel_left : (LastControl π) * ((LastControl π) * ρ) = ρ := resCondFlip_mul_cancel_left

-- Theorem 5.4
lemma getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply :
getBit 0 (FirstControl π (π q)) = getBit 0 (LastControl π q)  := by
rcases mergeBitRes_getRes_cases_flipBit 0 (π q) false with (⟨h₃, h₄⟩ | ⟨h₃, h₄⟩) <;>
rcases mergeBitRes_getRes_cases_flipBit 0 q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
simp only [firstControl_apply, lastControl_apply, h₁, h₂, h₃, h₄, Bool.not_not, getBit_flipBit,
  Bool.cond_not, cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero_apply,
  apply_cond (getBit 0), cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF]

def MiddlePerm (π : Equiv.Perm (Fin (2^(m + 1)))) : {π : Equiv.Perm (Fin (2^(m + 1))) // bitInvar 0 π} :=
⟨(FirstControl π) * π * (LastControl π), by simp_rw [bitInvar_iff_getBit_apply_eq_getBit, Equiv.Perm.mul_apply,
  getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply, ← Equiv.Perm.mul_apply,
  lastControl_mul_self, Equiv.Perm.one_apply, forall_const]⟩

lemma MiddlePerm_coe : MiddlePerm π = (FirstControl π) * π * (LastControl π) := rfl

lemma FirstControl_mul_MiddlePerm_mul_LastControl_eq_self :
  FirstControl π * (MiddlePerm π) * LastControl π = π := by
  simp_rw [MiddlePerm_coe, mul_assoc (a := FirstControl π),
    firstControl_mul_cancel_left, lastControl_mul_cancel_right]

-- SECTION

abbrev ControlBitsLayer (m : ℕ) := Fin (2^m) → Bool

abbrev ControlBits (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

@[simps!]
def ControlBitsZero : ControlBits 0 ≃ ControlBitsLayer 0 := (Equiv.funUnique (Fin 1) _)

@[simps!?]
def ControlBitsWeave : ControlBits (m + 1) ≃
(ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → ControlBits m) :=
(splitOffFirstLast.trans ((Equiv.refl _).prodCongr (unweaveOddTuplePowTwoTuple 0)))

def permToControlBits (m : ℕ) : Equiv.Perm (Fin (2^(m + 1))) → ControlBits m :=
m.recOn (fun π => (ControlBitsZero.symm (LastControlBits π)))
(fun _ re π => (ControlBitsWeave.symm) (((FirstControlBits π), (LastControlBits π)),
  (re ∘ ((equivBitInvar 0).symm (MiddlePerm π)))))

def controlBitsToPerm (m : ℕ) : ControlBits m → Equiv.Perm (Fin (2^(m + 1))) :=
m.recOn (fun cb => resCondFlip 0 (ControlBitsZero cb))
  (fun _ re cb => (resCondFlip 0 (ControlBitsWeave cb).fst.fst) *
                  ((equivBitInvar 0) (re ∘ (ControlBitsWeave cb).snd)) *
                  (resCondFlip 0 ((ControlBitsWeave cb).fst.snd)))

lemma permToControlBitsZero :
  permToControlBits 0 = fun π => ControlBitsZero.symm (LastControlBits π) := rfl

lemma controlBitsToPerm_zero :
  controlBitsToPerm 0 = fun cb => resCondFlip 0 (ControlBitsZero cb) := rfl

lemma permToControlBits_succ :
  permToControlBits (m + 1) = fun π => ControlBitsWeave.symm (((FirstControlBits π), (LastControlBits π)),
  (permToControlBits m) ∘ ((equivBitInvar 0).symm (MiddlePerm π))) := rfl

lemma controlBitsToPerm_succ :
  controlBitsToPerm (m + 1) = fun cb => ((resCondFlip 0 (ControlBitsWeave cb).fst.fst) *
    ((equivBitInvar 0) ((controlBitsToPerm m) ∘ (ControlBitsWeave cb).snd)) *
      (resCondFlip 0 ((ControlBitsWeave cb).fst.snd))) := rfl

lemma controlBitsToPerm_leftInverse :
  (controlBitsToPerm m).LeftInverse (permToControlBits m) := by
  induction' m with m IH
  · intro π
    nth_rewrite 2 [Fin.perm_fin_two π]
    simp_rw [permToControlBits, controlBitsToPerm, Equiv.apply_symm_apply,
      resCondFlip_lastControlBits]
    exact lastControl_base
  · intro π
    simp_rw [permToControlBits_succ, controlBitsToPerm_succ, Equiv.apply_symm_apply,
      resCondFlip_firstControlBits, resCondFlip_lastControlBits, ← Function.comp.assoc,
      IH.comp_eq_id, Function.comp.left_id, Equiv.apply_symm_apply,
      FirstControl_mul_MiddlePerm_mul_LastControl_eq_self]

-- SECTION

def PartialLayerTuple (n m : ℕ) := Fin (2*n + 1) → ControlBitsLayer m

def PartialLayerTupleZero : PartialLayerTuple 0 m  ≃ ControlBitsLayer m := Equiv.funUnique (Fin 1) (ControlBitsLayer m)

def PartialLayerTupleWeave :
  PartialLayerTuple (n + 1) m ≃ ((ControlBitsLayer m × ControlBitsLayer m) × PartialLayerTuple n m) := splitOffFirstLast

def partialControlBitsToPerm (n m : ℕ) : PartialLayerTuple n m → Equiv.Perm (Fin (2^(m + 1))) :=
n.recOn (fun cb => resCondFlip (Fin.last m) (cb 0))
  (fun i re cb => resCondFlip (Fin.rev (i.succ)) (splitOffFirstLast cb).fst.fst * re (splitOffFirstLast cb).snd *
                  resCondFlip (Fin.rev (i.succ)) (splitOffFirstLast cb).fst.snd)

lemma partialControlBitsToPerm_zero : partialControlBitsToPerm 0 m =
  fun cb => resCondFlip (Fin.last m) (cb 0) := rfl

lemma partialControlBitsToPerm_succ (n m : ℕ)
  : partialControlBitsToPerm (n + 1) m =
  fun cb => resCondFlip (Fin.rev (n.succ)) (splitOffFirstLast cb).fst.fst *
    partialControlBitsToPerm n m (splitOffFirstLast cb).snd *
      resCondFlip (Fin.rev (n.succ)) (splitOffFirstLast cb).fst.snd := rfl

lemma bitInvar_partialControlBitsToPerm
(cb : PartialLayerTuple n m) (t : Fin (m + 1)) (htn : (t : ℕ) + n < m) :
  bitInvar t (partialControlBitsToPerm n m cb) := by
induction' n with n IH generalizing m t
· simp_rw [Nat.zero_eq, add_zero] at htn
  simp_rw [partialControlBitsToPerm_zero]
  refine' resCondFlip_bitInvar (Fin.ne_of_lt htn)
· simp_rw [partialControlBitsToPerm_succ]
  have hmn : n + 1 < m + 1 := (lt_of_le_of_lt ((n + 1).le_add_left _) htn).trans (Nat.lt_succ_self _)
  refine' mul_bitInvar_of_bitInvar (mul_bitInvar_of_bitInvar (resCondFlip_bitInvar _) _) (resCondFlip_bitInvar _)
  · rw [Fin.ne_iff_vne, Fin.val_rev, Fin.coe_ofNat_eq_mod,
      Nat.succ_sub_succ_eq_sub, Nat.mod_eq_of_lt hmn]
    exact ne_of_lt (Nat.lt_sub_of_add_lt htn)
  · exact IH _ _ ((Nat.add_lt_add_left (Nat.lt_succ_self _) _).trans htn)
  · rw [Fin.ne_iff_vne, Fin.val_rev, Fin.coe_ofNat_eq_mod,
      Nat.succ_sub_succ_eq_sub, Nat.mod_eq_of_lt hmn]
    exact ne_of_lt (Nat.lt_sub_of_add_lt htn)

lemma bitInvar_zero_partialControlBitsToPerm
(cb : PartialLayerTuple n m) (hmn : n < m) :
  bitInvar 0 (partialControlBitsToPerm n m cb) := by
  refine' bitInvar_partialControlBitsToPerm cb _ _
  rw [Fin.val_zero, zero_add]
  exact hmn

def controlBitsToPerm' (m : ℕ) := partialControlBitsToPerm m m

lemma controlBitsToPerm'_zero : controlBitsToPerm' 0 = fun cb => resCondFlip 0 (cb 0) := rfl

lemma controlBitsToPerm'_succ : controlBitsToPerm' (m + 1) =
fun cb => resCondFlip 0 (splitOffFirstLast cb).fst.fst *
    partialControlBitsToPerm m (m + 1) (splitOffFirstLast cb).snd *
      resCondFlip 0 (splitOffFirstLast cb).fst.snd
      := by
  have H : ∀ m : ℕ, Fin.rev m = (0 : Fin (m + 1))
  · simp_rw [Fin.cast_nat_eq_last, ← Fin.top_eq_last, ← OrderDual.ofDual_bot,
    ← Fin.revOrderIso_apply, map_bot, Fin.bot_eq_zero, implies_true]
  rw [controlBitsToPerm', partialControlBitsToPerm_succ, H]

lemma controlBitsToPerm_eq : controlBitsToPerm m = controlBitsToPerm' m := by
  induction' m with m IH <;> ext cb : 1
  · rw [controlBitsToPerm_zero, controlBitsToPerm'_zero]
    simp_rw [resCondFlip_base, ControlBitsZero_apply]
  · rw [controlBitsToPerm_succ, controlBitsToPerm'_succ]
    simp_rw [ControlBitsWeave_apply, mul_right_cancel_iff, mul_left_cancel_iff, IH,
    controlBitsToPerm']--blahj2
    ext q : 1
    simp [boolArrowPermsToBitInvarPerm_coe_apply, unweaveOddTuplePowTwoTuple_apply']
    ext : 1
    simp [coe_mergeBitRes_zero, mergeBitRes_apply]
    simp_rw [← getRes_succ_eq_mergeBitRes_zero_getBit_zero_getRes_getRes_zero]
    dsimp

    simp


def  controlBitsToPerm'' (m : ℕ) (cb : ControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => resCondFlip (foldFin k) (cb k))).prod

--SECTION

def BitTupleControlBits (m : ℕ) := Fin ((2*m + 1)*(2^m)) → Bool

def layerTupleEquivBitTuple {m : ℕ} : ControlBits m ≃ BitTupleControlBits m := finArrowFinEquiv

def bitTupleControlBitsToPerm (m : ℕ) := (controlBitsToPerm m) ∘ layerTupleEquivBitTuple.symm

def permToBitTupleControlBits (m : ℕ) := layerTupleEquivBitTuple ∘ permToControlBits m

lemma bitControlBitsToPerm_leftInverse :
  (bitTupleControlBitsToPerm m).LeftInverse (permToBitTupleControlBits m) :=
  Function.LeftInverse.comp layerTupleEquivBitTuple.left_inv controlBitsToPerm_leftInverse

end ControlBits

-- Testing

def myControlBits69 := (![true, false, true, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false] : BitTupleControlBits 2)
def myControlBits69' := (![![true, false, true, false], ![true, false, false, false], ![false, false, false, false],
 ![false, false, false, false], ![false, false, false, false]] : ControlBits 2)

def myControlBits1 : ControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def myControlBits2 : ControlBits 1 := ![![false, false], ![true, true], ![false, true]]
def myControlBits2a : BitTupleControlBits 1 := ![false, true, true, true, true, true]
def myControlBits3 : ControlBits 0 := ![![true]]
def myControlBits4 : ControlBits 0 := ![![false]]
/-
#eval [0, 1, 2, 3].map (controlBitsToPerm 1 myControlBits2)
#eval [0, 1, 2, 3].map (controlBitsToPerm' 1 myControlBits2)
#eval [0, 1, 2, 3].map (controlBitsToPerm'' 1 myControlBits2)
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPerm 2 (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPerm' 2 (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPerm'' 2 (myControlBits69'))
#eval permToControlBits 1 <| (controlBitsToPerm 1 (myControlBits1))
#eval permToControlBits 1 <| (controlBitsToPerm' 1 (myControlBits1))
#eval (DomMulAct.mk (bitTupleControlBitsToPerm 1 myControlBits2a)) • (!["a", "b", "c", "d"])
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (bitTupleControlBitsToPerm 2 myControlBits69)
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPerm'' 2 ((layerTupleEquivBitTuple (m := 2)).symm myControlBits69))
-/
