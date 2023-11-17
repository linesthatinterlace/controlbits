import Controlbits.PermFintwo
import Controlbits.BitResiduumEquivs
import Controlbits.FoldFin
import Controlbits.CommutatorCycles
import Controlbits.Equivs
import Controlbits.Bool

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

structure CBType where
  fam : ℕ → Type*
  zero : fam 0 ≃ ControlBitsLayer 0
  weave m : fam (m + 1) ≃ (ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → fam m)

def cbTypeEquiv (x y : CBType) (m : ℕ) : x.fam m ≃ y.fam m :=
m.recOn (x.zero.trans y.zero.symm) (fun n IE => (x.weave n).trans <| (prodArrowEquivCongr IE).trans (y.weave n).symm)

def cbTypeOfEquiv (x : CBType) (F : ℕ → Type*) (Fe : ∀ m, x.fam m ≃ F m) : CBType where
  fam := F
  zero := (Fe 0).symm.trans x.zero
  weave m := (Fe (m + 1)).symm.trans <| (x.weave m).trans (prodArrowEquivCongr (Fe m))

def permToControlBits (x : CBType) (m : ℕ) : Equiv.Perm (Fin (2^(m + 1))) → x.fam m :=
m.recOn (fun π => x.zero.symm (LastControlBits π))
(fun _ re π => (x.weave _).symm (((FirstControlBits π), (LastControlBits π)),
  (re ∘ ((equivBitInvar 0).symm (MiddlePerm π)))))

def controlBitsToPerm (x : CBType) (m : ℕ) : x.fam m → Equiv.Perm (Fin (2^(m + 1))) :=
m.recOn (fun cb => resCondFlip 0 (x.zero cb))
  (fun _ re cb => (resCondFlip 0 (x.weave _ cb).fst.fst) * ((equivBitInvar 0) (re ∘ (x.weave _ cb).snd)) *
                  (resCondFlip 0 ((x.weave _ cb).fst.snd)))

lemma permToControlBits_succ (x : CBType) :
  permToControlBits x (m + 1) = fun π => (x.weave _).symm (((FirstControlBits π), (LastControlBits π)),
  (permToControlBits x m) ∘ ((equivBitInvar 0).symm (MiddlePerm π))) := rfl

lemma controlBitsToPerm_succ (x : CBType) :
  controlBitsToPerm x (m + 1) = fun cb => ((resCondFlip 0 (x.weave _ cb).fst.fst) *
    ((equivBitInvar 0) ((controlBitsToPerm x m) ∘ (x.weave _ cb).snd)) *
      (resCondFlip 0 ((x.weave _ cb).fst.snd))) := rfl

lemma controlBitsToPerm_leftInverse (x : CBType) :
  (controlBitsToPerm x m).LeftInverse (permToControlBits x m) := by
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

--SECTION

def InductiveControlBits : CBType where
  fam m := m.recOn (ControlBitsLayer 0) (fun m T => (ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → T))
  zero := Equiv.refl _
  weave := fun _ => Equiv.refl _

def inductiveControlBitsToPerm {m : ℕ} := controlBitsToPerm InductiveControlBits m

def permToinductiveControlBits {m : ℕ} := permToControlBits InductiveControlBits m

lemma indToPermLeftInverse : Function.LeftInverse (inductiveControlBitsToPerm (m := m)) (permToinductiveControlBits) :=
controlBitsToPerm_leftInverse _

--SECTION

abbrev LayerTupleControlBits' (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

def LayerTupleControlBits : CBType where
  fam m := Fin (2*m + 1) → ControlBitsLayer m
  zero := Equiv.funUnique (Fin 1) _
  weave := fun _ => splitOffFirstLast.trans ((Equiv.refl _).prodCongr (unweaveOddTuplePowTwoTuple 0))

def layerTupleControlBitsToPerm {m : ℕ} := controlBitsToPerm LayerTupleControlBits m

def permToLayerTupleControlBits {m : ℕ} := permToControlBits LayerTupleControlBits m

def PartialLayerTuple (n m : ℕ) := Fin (2*n + 1) → ControlBitsLayer m

def zeroPartialLayerTuple : PartialLayerTuple 0 m  ≃ ControlBitsLayer m := Equiv.funUnique (Fin 1) (ControlBitsLayer m)

def succPartialLayerTuple :
  PartialLayerTuple (n + 1) m ≃ ((ControlBitsLayer m × ControlBitsLayer m) × PartialLayerTuple n m) := splitOffFirstLast

def partialControlBitsToPerm (n : ℕ) : (Fin (2*n + 1) → ControlBitsLayer m) → Equiv.Perm (Fin (2^(m + 1))) :=
n.recOn (fun cb => resCondFlip (Fin.last _) (cb 0))
  (fun i re cb => resCondFlip (Fin.rev (i.succ)) (splitOffFirstLast cb).fst.fst * re (splitOffFirstLast cb).snd *
                  resCondFlip (Fin.rev (i.succ)) (splitOffFirstLast cb).fst.snd)

lemma partialControlBitsToPerm_zero (m : ℕ) : partialControlBitsToPerm 0 =
  fun cb => resCondFlip (Fin.last m) (cb 0) := rfl

lemma partialControlBitsToPerm_succ (n m : ℕ)
  : partialControlBitsToPerm (n + 1) =
  fun cb => resCondFlip ((n.succ : Fin (m + 1)).rev) (splitOffFirstLast cb).fst.fst *
    partialControlBitsToPerm n (splitOffFirstLast cb).snd *
      resCondFlip ((n.succ : Fin _).rev) (splitOffFirstLast cb).fst.snd := rfl

lemma bitInvar_partialControlBitsToPerm
(cb : Fin (2*n + 1) → ControlBitsLayer m) (t : Fin (m + 1)) (htn : (t : ℕ) + n < m) :
  bitInvar t (partialControlBitsToPerm n cb) := by
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
(cb : Fin (2*n + 1) → ControlBitsLayer m) (hmn : n < m) :
  bitInvar 0 (partialControlBitsToPerm n cb) := by
  refine' bitInvar_partialControlBitsToPerm cb _ _
  rw [Fin.val_zero, zero_add]
  exact hmn

def layerTupleControlBitsToPerm' {m : ℕ} := partialControlBitsToPerm (m := m) m

def  layerTupleControlBitsToPerm'' (cb : LayerTupleControlBits.fam m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => resCondFlip (foldFin k) (cb k))).prod

--SECTION

--abbrev BitTupleControlBits (m : ℕ) := Fin ((2*m + 1)*(2^m)) → Bool

def BitTupleControlBits : CBType := cbTypeOfEquiv LayerTupleControlBits (fun m => Fin ((2*m + 1)*(2^m)) → Bool)
(fun _ => finArrowFinEquiv)

def bitTupleControlBitsToPerm {m : ℕ} := controlBitsToPerm BitTupleControlBits m

def permToBitTupleControlBits {m : ℕ} := permToControlBits BitTupleControlBits m

def bitTupleEquivLayerTuple {m : ℕ} : BitTupleControlBits.fam m ≃ LayerTupleControlBits.fam m := cbTypeEquiv _ _ _

end ControlBits


-- Testing

def myControlBits69 := (![true, false, true, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false] : BitTupleControlBits.fam 2)
def myControlBits69' := (![![true, false, true, false], ![true, false, false, false], ![false, false, false, false],
 ![false, false, false, false], ![false, false, false, false]] : LayerTupleControlBits.fam 2)

def myControlBits1 : LayerTupleControlBits.fam 1 := ![![true, false], ![true, false], ![false, false]]
def myControlBits2 : LayerTupleControlBits.fam 1 := ![![false, false], ![true, true], ![false, true]]
def myControlBits2a : BitTupleControlBits.fam 1 := ![false, true, false, true, true, true]
def myControlBits3 : LayerTupleControlBits.fam 0 := ![![true]]
def myControlBits4 : LayerTupleControlBits.fam 0 := ![![false]]
#eval [0, 1, 2, 3].map (layerTupleControlBitsToPerm (myControlBits2))
#eval [0, 1, 2, 3].map (layerTupleControlBitsToPerm' (myControlBits2))
#eval [0, 1, 2, 3].map (layerTupleControlBitsToPerm'' myControlBits2)
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleControlBitsToPerm (m := 2) (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleControlBitsToPerm' (m := 2) (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleControlBitsToPerm'' (m := 2) (myControlBits69'))
#eval permToLayerTupleControlBits <| (layerTupleControlBitsToPerm (myControlBits1))
#eval permToLayerTupleControlBits <| (layerTupleControlBitsToPerm' (myControlBits1))
#eval permToBitTupleControlBits <| bitTupleControlBitsToPerm (m := 1) myControlBits2a
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (bitTupleControlBitsToPerm (m := 2) myControlBits69)
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleControlBitsToPerm'' (m := 2) ((bitTupleEquivLayerTuple (m := 2)) myControlBits69))
