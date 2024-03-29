import Controlbits.PermFintwo
import Controlbits.BitResiduum
import Controlbits.CommutatorCycles

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
CycleMin (XBackXForth π) (flipBit 0 q) = (flipBit 0) (CycleMin (XBackXForth π) q) :=
cycleMin_cmtr_right_apply_eq_apply_cycleMin_cmtr rfl flipBit_ne_self eq_flipBit_of_lt_of_flipBit_gt

lemma cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero_apply :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = CycleMin (XBackXForth π) (flipBit 0 (π q)) :=
cycleMin_cmtr_apply_comm

def FirstControlBits (π : Equiv.Perm (Fin (2^(m + 1)))) (p : Fin (2^m)) :=
getBit 0 (FastCycleMin m (XBackXForth π) (mergeBitRes 0 false p))

lemma firstControlBits_def : FirstControlBits (π : Equiv.Perm (Fin (2^(m + 1)))) p =
getBit 0 (FastCycleMin m (XBackXForth π) (mergeBitRes 0 false p)) := by rfl

lemma firstControlBits_apply : FirstControlBits π p =
  getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p)) := by
  rw [FirstControlBits, cycleMin_eq_fastCycleMin orderOf_xBXF_cycleOf]

-- Theorem 5.2
lemma firstControlBits_apply_zero {π : Equiv.Perm (Fin (2^(m + 1)))} :
  FirstControlBits π 0 = false := by
  simp_rw [firstControlBits_apply, mergeBitRes_apply_false_zero,
    Fin.cycleMin_zero, getBit_apply_zero]

lemma firstControlBits_base : FirstControlBits (m := 0) π = ![false] := by
  ext
  simp_rw [Fin.eq_zero, firstControlBits_apply_zero, Matrix.cons_val_fin_one]

def FirstControl (π : Equiv.Perm (Fin (2^(m + 1)))) := condFlipBit 0 (FirstControlBits π)

@[simp]
lemma condFlipBit_firstControlBits : condFlipBit 0 (FirstControlBits π) = FirstControl π := rfl

lemma firstControl_apply : FirstControl π q =
  bif getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false (getRes 0 q)))
  then flipBit 0 q
  else q :=
  firstControlBits_apply ▸ condFlipBit_apply

lemma firstControl_base : FirstControl (m := 0) π = 1 := by
  ext
  simp_rw [FirstControl, firstControlBits_base, condFlipBit_apply, Matrix.cons_val_fin_one,
    cond_false, Equiv.Perm.coe_one, id_eq]

@[simp]
lemma firstControl_symm : (FirstControl π).symm = FirstControl π := rfl

@[simp]
lemma firstControl_inv : (FirstControl π)⁻¹ = FirstControl π := rfl

@[simp]
lemma firstControl_firstControl : FirstControl π (FirstControl π q) = q := condFlipBit_condFlipBit

@[simp]
lemma firstControl_mul_self : (FirstControl π) * (FirstControl π) = 1 := condFlipBit_mul_self

@[simp]
lemma firstControl_mul_cancel_right : ρ * (FirstControl π) * (FirstControl π) = ρ :=
condFlipBit_mul_cancel_right

@[simp]
lemma firstControl_mul_cancel_left : (FirstControl π) * ((FirstControl π) * ρ) = ρ :=
condFlipBit_mul_cancel_left

-- Theorem 5.3
lemma getBit_zero_firstControl_apply_eq_getBit_zero_cycleMin :
∀ {q}, getBit 0 (FirstControl π q) = getBit 0 (CycleMin (XBackXForth π) q) := by
simp_rw [forall_iff_forall_mergeBitRes_bool 0, ← condFlipBit_firstControlBits, getBit_condFlipBit',
  getRes_mergeBitRes, getBit_mergeBitRes, Bool.xor_false, Bool.xor_true, ← Bool.not_false,
  ← flipBit_mergeBitRes, cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF, getBit_flipBit,
  firstControlBits_apply, forall_const, and_self]

def LastControlBits (π) (p : Fin (2^m)) :=
getBit 0 ((FirstControl π) (π (mergeBitRes 0 false p)))

lemma lastControlBits_apply : LastControlBits π p =
  getBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false p))) :=
  getBit_zero_firstControl_apply_eq_getBit_zero_cycleMin

lemma lastControlBits_base : LastControlBits (m := 0) π = fun _ => decide (π 0 = 1) := by
  ext
  simp_rw [LastControlBits, firstControl_base, mergeBitRes_false_base_eq_zero,
    getBit_base, Equiv.Perm.one_apply]

def LastControl (π : Equiv.Perm (Fin (2^(m + 1)))) := condFlipBit 0 (LastControlBits π)

@[simp]
lemma condFlipBit_lastControlBits : condFlipBit 0 (LastControlBits π) = LastControl π := rfl

lemma lastControl_apply : LastControl π q =
  bif getBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false (getRes 0 q))))
  then flipBit 0 q
  else q := by
  simp_rw [← condFlipBit_lastControlBits, condFlipBit_apply, lastControlBits_apply]

lemma lastControl_base : LastControl (m := 0) π = π := by
  simp_rw [LastControl, lastControlBits_base, condFlipBit_base, Bool.cond_decide]
  exact (Fin.perm_fin_two π).symm

@[simp]
lemma lastControl_symm : (LastControl π).symm = LastControl π := rfl

@[simp]
lemma lastControl_inv : (LastControl π)⁻¹ = LastControl π := rfl

@[simp]
lemma lastControl_lastControl : LastControl π (LastControl π q) = q := condFlipBit_condFlipBit

@[simp]
lemma lastControl_mul_self : (LastControl π) * (LastControl π) = 1 := condFlipBit_mul_self

@[simp]
lemma lastControl_mul_cancel_right : ρ * (LastControl π) * (LastControl π) = ρ :=
condFlipBit_mul_cancel_right

@[simp]
lemma lastControl_mul_cancel_left : (LastControl π) * ((LastControl π) * ρ) = ρ :=
condFlipBit_mul_cancel_left

-- Theorem 5.4
lemma getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply :
getBit 0 (FirstControl π (π q)) = getBit 0 (LastControl π q)  := by
rcases mergeBitRes_getRes_cases_flipBit 0 (π q) false with (⟨h₃, h₄⟩ | ⟨h₃, h₄⟩) <;>
rcases mergeBitRes_getRes_cases_flipBit 0 q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
simp only [firstControl_apply, lastControl_apply, h₁, h₂, h₃, h₄, Bool.not_not, getBit_flipBit,
  Bool.cond_not, cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero_apply,
  Bool.apply_cond (getBit 0), cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF]

def MiddlePerm (π : Equiv.Perm (Fin (2^(m + 1)))) : Equiv.Perm (Fin (2^(m + 1))) :=
(FirstControl π) * π * (LastControl π)

lemma MiddlePerm_bitInvar_zero : bitInvar 0 ⇑(MiddlePerm π) := by
simp_rw [MiddlePerm, bitInvar_iff_getBit_apply_eq_getBit, Equiv.Perm.mul_apply,
  getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply, ← Equiv.Perm.mul_apply,
  lastControl_mul_self, Equiv.Perm.one_apply, forall_const]

lemma MiddlePerm_mem_bitInvarSubmonoid_zero : ⇑(MiddlePerm π) ∈ bitInvarSubmonoid 0 :=
  MiddlePerm_bitInvar_zero


lemma MiddlePerm_mem_bitInvarSubgroup_zero : MiddlePerm π ∈ bitInvarSubgroup 0 :=
  MiddlePerm_mem_bitInvarSubmonoid_zero

lemma MiddlePerm_def : (MiddlePerm π : Equiv.Perm (Fin (2^(m + 1)))) =
  (FirstControl π) * π * (LastControl π) := rfl

lemma FirstControl_mul_MiddlePerm_mul_LastControl_eq_self :
  FirstControl π * (MiddlePerm π) * LastControl π = π := by
  simp_rw [MiddlePerm_def, mul_assoc (a := FirstControl π),
    firstControl_mul_cancel_left, lastControl_mul_cancel_right]

-- SECTION

abbrev ControlBitsLayer (m : ℕ) := Fin (2^m) → Bool

-- SECTION

abbrev PartialLayerTuple (m n : ℕ) := Fin (2*n + 1) → ControlBitsLayer m

def PartialLayerTupleZero : PartialLayerTuple m 0 ≃ ControlBitsLayer m :=
Equiv.funUnique (Fin 1) (ControlBitsLayer m)

def partialControlBitsToPerm (m : ℕ) (n : Fin (m + 1)) :
  PartialLayerTuple m n → Equiv.Perm (Fin (2^(m + 1))) :=
  n.inductionOn (fun cb => condFlipBit (Fin.last m) (PartialLayerTupleZero cb)) (fun i re cb =>
                  condFlipBit (i.succ.rev) ((piFinSuccCastSucc cb).1.1) *
                  re (piFinSuccCastSucc cb).2 *
                  condFlipBit (i.succ.rev) (piFinSuccCastSucc cb).1.2)

lemma bitInvar_partialControlBitsToPerm {n t : Fin (m + 1)} :
(htn : t < Fin.rev n) → ∀ {cb}, bitInvar t ⇑(partialControlBitsToPerm m n cb) :=
  n.inductionOn
  (fun htn _ => condFlipBit_bitInvar_of_ne htn.ne)
  (fun n IH htn _ => (bitInvar_mulPerm_of_bitInvar
    (bitInvar_mulPerm_of_bitInvar (condFlipBit_bitInvar_of_ne htn.ne)
    (IH (htn.trans (Fin.rev_lt_rev.mpr (n.castSucc_lt_succ))))) (condFlipBit_bitInvar_of_ne htn.ne)))

lemma partialControlBitsToPerm_zero {cb : PartialLayerTuple m 0}:
  partialControlBitsToPerm m 0 cb = condFlipBit (Fin.last m) (PartialLayerTupleZero cb) := rfl

lemma partialControlBitsToPerm_succ {n : Fin m} {cb : PartialLayerTuple m n.succ}
  : partialControlBitsToPerm m (n.succ) cb =
  condFlipBit (n.succ.rev) (piFinSuccCastSucc cb).1.1 *
  partialControlBitsToPerm m (n.castSucc) (piFinSuccCastSucc cb).2 *
  condFlipBit (n.succ.rev) (piFinSuccCastSucc cb).1.2 := rfl

lemma partialControlBitsToPerm_last_zero :
  partialControlBitsToPerm 0 (Fin.last 0) cb = condFlipBit 0 (PartialLayerTupleZero cb) := rfl

lemma partialControlBitsToPerm_last_succ :
    partialControlBitsToPerm (m + 1) (Fin.last (m + 1)) cb = (
    condFlipBit 0 (piFinSuccCastSucc cb).1.1 *
    partialControlBitsToPerm (m + 1) (Fin.last m).castSucc (piFinSuccCastSucc cb).2 *
    condFlipBit 0 (piFinSuccCastSucc cb).1.2) := by
  simp_rw [← Fin.succ_last, partialControlBitsToPerm_succ, Fin.rev_succ, Fin.rev_last]
  rfl

def PartialLayerTupleUnweave :
  PartialLayerTuple (m + 1) n ≃ (Bool → PartialLayerTuple m n) :=
  calc
  _ ≃ _ := (Equiv.refl _).arrowCongr (((getBitRes 0).arrowCongr (Equiv.refl _)).trans
             (Equiv.curry _ _ _))
  _ ≃ _ := (Equiv.piComm _)

lemma partialControlBitsToPerm_castSucc
(m : ℕ) (n : Fin (m + 1)) : (cb : PartialLayerTuple (m + 1) (n.castSucc)) →
partialControlBitsToPerm (m + 1) (n.castSucc) cb = (bitInvarMulEquiv 0)
(fun b => partialControlBitsToPerm m n (PartialLayerTupleUnweave cb b)) := by
  refine' n.inductionOn (fun _ => _) (fun i IH cb => _)
  · simp_rw [Fin.castSucc_zero, partialControlBitsToPerm_zero, ← Fin.succ_last,
      condFlipBit_succ_eq_bitInvarMulEquiv_apply]
    rfl
  · simp_rw [← Fin.succ_castSucc, partialControlBitsToPerm_succ,
    Fin.rev_castSucc_succ, Fin.rev_succ, ← Pi.mul_def, MulEquiv.map_mul, Submonoid.coe_mul,
      IH, condFlipBit_succ_eq_bitInvarMulEquiv_apply]
    rfl


-- SECTION

abbrev ControlBits (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

def ControlBitsZero : ControlBits 0 ≃ ControlBitsLayer 0 := (Equiv.funUnique (Fin 1) _)

def ControlBitsWeave : ControlBits (m + 1) ≃
(ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → ControlBits m) :=
(piFinSuccCastSucc.trans ((Equiv.refl _).prodCongr PartialLayerTupleUnweave))

def permToControlBits (m : ℕ) : Equiv.Perm (Fin (2^(m + 1))) → ControlBits m :=
m.recOn (fun π => (ControlBitsZero.symm (LastControlBits π)))
(fun _ re π => (ControlBitsWeave.symm) ((FirstControlBits π, LastControlBits π),
  (re ∘ ((bitInvarMulEquiv 0).symm ⟨MiddlePerm π, MiddlePerm_mem_bitInvarSubgroup_zero⟩))))

def controlBitsToPermInductive (m : ℕ) : ControlBits m → Equiv.Perm (Fin (2^(m + 1))) :=
m.recOn (fun cb => condFlipBit 0 (ControlBitsZero cb))
  (fun _ re cb => (condFlipBit 0 (ControlBitsWeave cb).fst.fst) *
                  ((bitInvarMulEquiv 0) (re ∘ (ControlBitsWeave cb).snd)) *
                  (condFlipBit 0 ((ControlBitsWeave cb).fst.snd)))

lemma permToControlBits_zero :
  permToControlBits 0 = fun π => ControlBitsZero.symm (LastControlBits π) := rfl

lemma controlBitsToPermInductive_zero :
  controlBitsToPermInductive 0 cb = condFlipBit 0 (ControlBitsZero cb) := rfl

lemma permToControlBits_succ : permToControlBits (m + 1) = fun π =>
  ControlBitsWeave.symm (((FirstControlBits π), (LastControlBits π)),
    (permToControlBits m) ∘ ((bitInvarMulEquiv 0).symm ⟨MiddlePerm π,
      MiddlePerm_mem_bitInvarSubgroup_zero⟩)) := rfl

lemma controlBitsToPermInductive_succ :
  controlBitsToPermInductive (m + 1) cb = ((condFlipBit 0 (ControlBitsWeave cb).fst.fst) *
    ((bitInvarMulEquiv 0) ((controlBitsToPermInductive m) ∘ (ControlBitsWeave cb).snd)) *
      (condFlipBit 0 ((ControlBitsWeave cb).fst.snd))) := rfl

lemma controlBitsToPermInductive_leftInverse :
  (controlBitsToPermInductive m).LeftInverse (permToControlBits m) := by
  induction' m with m IH
  · intro _
    simp_rw [permToControlBits_zero, controlBitsToPermInductive_zero, Equiv.apply_symm_apply]
    exact lastControl_base
  · intro _
    simp_rw [permToControlBits_succ, controlBitsToPermInductive_succ, Equiv.apply_symm_apply,
      ← Function.comp.assoc, IH.comp_eq_id, Function.comp.left_id, MulEquiv.apply_symm_apply]
    exact FirstControl_mul_MiddlePerm_mul_LastControl_eq_self

abbrev controlBitsToPermLeftRightMul (m : ℕ) := partialControlBitsToPerm m (Fin.last m)

lemma controlBitsToPermLeftRightMul_zero :
  controlBitsToPermLeftRightMul 0 cb = condFlipBit 0 (PartialLayerTupleZero cb) := rfl

lemma controlBitsToPermLeftRightMul_succ : controlBitsToPermLeftRightMul (m + 1) cb =
    condFlipBit 0 (piFinSuccCastSucc cb).1.1 *
    partialControlBitsToPerm (m + 1) (Fin.last m).castSucc (piFinSuccCastSucc cb).2 *
    condFlipBit 0 (piFinSuccCastSucc cb).1.2 := partialControlBitsToPerm_last_succ

lemma controlBitsToPerm_eq : controlBitsToPermInductive = controlBitsToPermLeftRightMul := by
  ext m : 1
  induction' m with m IH <;> ext cb : 1
  · rfl
  · rw [controlBitsToPermInductive_succ, IH, controlBitsToPermLeftRightMul_succ,
        partialControlBitsToPerm_castSucc]
    rfl

lemma controlBitsToPermLeftRightMul_leftInverse :
  (controlBitsToPermLeftRightMul m).LeftInverse (permToControlBits m) :=
  controlBitsToPerm_eq ▸ controlBitsToPermInductive_leftInverse


-- SECTION

/-abbrev controlBitsToPermRightMul (m : ℕ) (cb : ControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => condFlipBit (foldFin m k) (cb k))).prod-/

abbrev BitTupleControlBits (m : ℕ) := Fin ((2*m + 1)*(2^m)) → Bool

def layerTupleEquivBitTuple {m : ℕ} : ControlBits m ≃ BitTupleControlBits m :=
(Equiv.curry _ _ _).symm.trans (finProdFinEquiv.arrowCongr <| Equiv.refl _)

def bitTupleControlBitsToPerm (m : ℕ) :=
(controlBitsToPermLeftRightMul m) ∘ layerTupleEquivBitTuple.symm

def permToBitTupleControlBits (m : ℕ) := layerTupleEquivBitTuple ∘ permToControlBits m

lemma bitControlBitsToPerm_leftInverse :
  (bitTupleControlBitsToPerm m).LeftInverse (permToBitTupleControlBits m) :=
  Function.LeftInverse.comp layerTupleEquivBitTuple.left_inv
    controlBitsToPermLeftRightMul_leftInverse

end ControlBits

-- Testing

def myControlBits69 := (![true, false, true, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false] : BitTupleControlBits 2)
def myControlBits69' := (![![true, false, true, false], ![true, false, false, false],
  ![false, false, false, false], ![false, false, false, false], ![false, false, false, false]]
  : ControlBits 2)

def myControlBits1  : ControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def myControlBits2  : ControlBits 1 := ![![false, false], ![true, true], ![false, true]]
def myControlBits2a : BitTupleControlBits 1 := ![false, true, true, true, true, true]
def myControlBits3  : ControlBits 0 := ![![true]]
def myControlBits4  : ControlBits 0 := ![![false]]

#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPermInductive 2 (myControlBits69')).symm
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPermLeftRightMul 2 (myControlBits69')).symm

/-
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPermRightMul 2 (myControlBits69')).symm
#eval [0, 1, 2, 3].map (controlBitsToPermInductive 1 myControlBits2)
#eval [0, 1, 2, 3].map (controlBitsToPermLeftRightMul 1 myControlBits2)
#eval [0, 1, 2, 3].map (controlBitsToPermRightMul 1 myControlBits2)
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPermInductive 2 (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPermLeftRightMul 2 (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPermRightMul 2 (myControlBits69'))
#eval permToControlBits 1 <| (controlBitsToPermInductive 1 (myControlBits1))
#eval permToControlBits 1 <| (controlBitsToPermLeftRightMul 1 (myControlBits1))
#eval (DomMulAct.mk (bitTupleControlBitsToPerm 1 myControlBits2a)) • (!["a", "b", "c", "d"])
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (bitTupleControlBitsToPerm 2 myControlBits69)
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (controlBitsToPermRightMul 2
  ((layerTupleEquivBitTuple (m := 2)).symm myControlBits69))
-/
