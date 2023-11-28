import Controlbits.PermFintwo
import Controlbits.BitResiduum
import Controlbits.FoldFin
import Controlbits.CommutatorCycles
import Mathlib.GroupTheory.GroupAction.DomAct.Basic

section ControlBits

-- FACTOR THESE

lemma Fin.rev_last {m : ℕ} : (last m).rev = 0 := by
  simp_rw [← top_eq_last, ← OrderDual.ofDual_bot, ← revOrderIso_apply, map_bot,
  bot_eq_zero]

lemma Fin.rev_zero {m : ℕ} : (0 : Fin (m + 1)).rev = (last m) := rfl

lemma Fin.lt_last_iff_ne_last {i : Fin (m + 1)} : i < last m ↔ i ≠ last m := lt_top_iff_ne_top

lemma Fin.rev_eq_zero_iff_last {i : Fin (m + 1)} : i.rev = 0 ↔ i = last m := by
  convert rev_inj
  exact rev_last.symm

lemma Fin.rev_ne_zero_iff_ne_last {i : Fin (m + 1)} : i.rev ≠ 0 ↔ i ≠ last m := by
  simp_rw [ne_eq, rev_eq_zero_iff_last]

lemma Fin.rev_pos_iff_lt_last {i : Fin (m + 1)} : 0 < i.rev ↔ i < last m := by
  simp_rw [lt_last_iff_ne_last, Fin.pos_iff_ne_zero]
  exact rev_ne_zero_iff_ne_last

lemma Fin.eq_zero_iff_rev_eq_last {i : Fin (m + 1)} : i = 0 ↔ i.rev = last m := by
  convert rev_rev i ▸ rev_eq_zero_iff_last

lemma Fin.ne_zero_iff_rev_ne_last {i : Fin (m + 1)} : i ≠ 0 ↔ i.rev ≠ last m := by
  convert rev_rev i ▸ rev_ne_zero_iff_ne_last

lemma Fin.pos_iff_rev_lt_last {i : Fin (m + 1)} : 0 < i ↔ i.rev < last m := by
  convert rev_rev i ▸ rev_pos_iff_lt_last

lemma Fin.rev_castSucc_eq_succ_rev {i : Fin m}: Fin.rev (Fin.castSucc i) = Fin.succ (Fin.rev i) := by
  rcases m with (_ | m)
  · exact i.elim0
  · simp only [Fin.ext_iff, val_rev, coe_castSucc, val_succ, Nat.succ_sub_succ_eq_sub,
      add_le_add_iff_right, tsub_add_eq_add_tsub (Nat.le_of_lt_succ i.isLt)]

lemma Fin.last_zero : Fin.last 0 = 0 := rfl

lemma Fin.last_one : Fin.last 1 = 1 := rfl

lemma Fin.last_zero_add_one : Fin.last (0 + 1) = 1 := rfl

-- FACTOR TO HERE

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
  Bool.apply_cond (getBit 0), cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF]

def MiddlePerm (π : Equiv.Perm (Fin (2^(m + 1)))) : Equiv.Perm (Fin (2^(m + 1))) :=
(FirstControl π) * π * (LastControl π)

lemma MiddlePerm_bitInvar_zero : bitInvar 0 (MiddlePerm π) := by
simp_rw [MiddlePerm, bitInvar_iff_getBit_apply_eq_getBit, Equiv.Perm.mul_apply,
  getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply, ← Equiv.Perm.mul_apply,
  lastControl_mul_self, Equiv.Perm.one_apply, forall_const]


def MiddlePermInvar (π : Equiv.Perm (Fin (2^(m + 1)))) : {π : Equiv.Perm (Fin (2^(m + 1))) // bitInvar 0 π} :=
⟨MiddlePerm π, MiddlePerm_bitInvar_zero⟩

lemma MiddlePerm_coe : (MiddlePerm π : Equiv.Perm (Fin (2^(m + 1)))) = (FirstControl π) * π * (LastControl π) := rfl

lemma FirstControl_mul_MiddlePerm_mul_LastControl_eq_self :
  FirstControl π * (MiddlePerm π) * LastControl π = π := by
  simp_rw [MiddlePerm_coe, mul_assoc (a := FirstControl π),
    firstControl_mul_cancel_left, lastControl_mul_cancel_right]

lemma FirstControl_mul_MiddlePermInvar_mul_LastControl_eq_self :
  (FirstControl π) * (MiddlePermInvar π).1 * (LastControl π) = π :=
  FirstControl_mul_MiddlePerm_mul_LastControl_eq_self

-- SECTION

abbrev ControlBitsLayer (m : ℕ) := Fin (2^m) → Bool

abbrev ControlBits (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

def ControlBitsLayerEquiv (m : ℕ) : ControlBitsLayer (m + 1) ≃ (Bool → ControlBitsLayer m) :=
unweavePowTwoTuple 0

def ControlBitsZero : ControlBits 0 ≃ ControlBitsLayer 0 := (Equiv.funUnique (Fin 1) _)

lemma ControlBitsZero_apply (cb : ControlBits 0) : ControlBitsZero cb = cb 0 := rfl

lemma ControlBitsZero_symm_apply : ControlBitsZero.symm cb = fun _ => cb := rfl

def ControlBitsWeave : ControlBits (m + 1) ≃
(ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → ControlBits m) :=
(splitOffFirstLast.trans ((Equiv.refl _).prodCongr (unweaveOddTuplePowTwoTuple 0)))

lemma ControlBitsWeave_apply (cb : ControlBits (m + 1)) :
  ControlBitsWeave cb =
  ((cb 0, cb (Fin.last _)),
    fun b t p => cb t.castSucc.succ (mergeBitRes 0 b p)) := by
  refine Prod.ext rfl ?_
  simp_rw [ControlBitsWeave, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod_map,
    splitOffFirstLast_apply_snd, unweaveOddTuplePowTwoTuple_apply]

def permToControlBits (m : ℕ) : Equiv.Perm (Fin (2^(m + 1))) → ControlBits m :=
m.recOn (fun π => (ControlBitsZero.symm (LastControlBits π)))
(fun _ re π => (ControlBitsWeave.symm) (((FirstControlBits π), (LastControlBits π)),
  (re ∘ ((equivBitInvar 0).symm (MiddlePermInvar π)))))

def controlBitsToPerm (m : ℕ) : ControlBits m → Equiv.Perm (Fin (2^(m + 1))) :=
m.recOn (fun cb => resCondFlip 0 (ControlBitsZero cb))
  (fun _ re cb => (resCondFlip 0 (ControlBitsWeave cb).fst.fst) *
                  ((equivBitInvar 0) (re ∘ (ControlBitsWeave cb).snd)) *
                  (resCondFlip 0 ((ControlBitsWeave cb).fst.snd)))

lemma permToControlBitsZero :
  permToControlBits 0 = fun π => ControlBitsZero.symm (LastControlBits π) := rfl

lemma controlBitsToPerm_zero :
  controlBitsToPerm 0 cb = resCondFlip 0 (ControlBitsZero cb) := rfl

lemma permToControlBits_succ :
  permToControlBits (m + 1) = fun π => ControlBitsWeave.symm (((FirstControlBits π), (LastControlBits π)),
  (permToControlBits m) ∘ ((equivBitInvar 0).symm (MiddlePermInvar π))) := rfl

lemma controlBitsToPerm_succ :
  controlBitsToPerm (m + 1) cb = ((resCondFlip 0 (ControlBitsWeave cb).fst.fst) *
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
      FirstControl_mul_MiddlePermInvar_mul_LastControl_eq_self]

-- SECTION

def PartialLayerTuple (m n : ℕ) := Fin (2*n + 1) → ControlBitsLayer m

def PartialLayerTupleZero : PartialLayerTuple m 0 ≃ ControlBitsLayer m :=
Equiv.funUnique (Fin 1) (ControlBitsLayer m)

lemma PartialLayerTupleZero_apply (cb : PartialLayerTuple m 0) : PartialLayerTupleZero cb = cb 0 := rfl

lemma PartialLayerTupleZero_symm_apply (cb : ControlBitsLayer 0) : PartialLayerTupleZero.symm cb = fun _ => cb := rfl

@[simps!]
def PartialLayerTupleWeave :
  PartialLayerTuple m (n + 1) ≃ ((ControlBitsLayer m × ControlBitsLayer m) × PartialLayerTuple m n) :=
  splitOffFirstLast

def PartialLayerTupleUnweave :
  PartialLayerTuple (m + 1) n ≃ (Bool → PartialLayerTuple m n) :=
  unweaveOddTuplePowTwoTuple 0

@[simp]
lemma PartialLayerTupleUnweave_apply (cb : Fin (2 * n + 1) → Fin (2 ^ (m + 1)) → Bool) :
  PartialLayerTupleUnweave cb = fun b t p => cb t (mergeBitRes 0 b p) :=
  unweaveOddTuplePowTwoTuple_apply

@[simp]
lemma PartialLayerTupleUnweave_symm_apply (cb : Bool → PartialLayerTuple m n) :
  PartialLayerTupleUnweave.symm cb = fun t q => cb (getBit 0 q) t (getRes 0 q) :=
  unweaveOddTuplePowTwoTuple_symm_apply

lemma ControlBitsWeave_eq_PartialLayerTupleWeave_PartialLayerTupleUnweave :
  ControlBitsWeave cb = ((PartialLayerTupleWeave cb).1,
  PartialLayerTupleUnweave (fun j => cb (j.castSucc.succ))) := by
  simp_rw [ControlBitsWeave_apply, PartialLayerTupleWeave_apply, PartialLayerTupleUnweave_apply]
  rfl

def partialControlBitsToPerm (m : ℕ) (n : Fin (m + 1)) : PartialLayerTuple m n → Equiv.Perm (Fin (2^(m + 1))) :=
n.inductionOn (fun cb => resCondFlip (Fin.last m) (PartialLayerTupleZero cb)) (fun i re cb =>
                resCondFlip (i.succ.rev) (PartialLayerTupleWeave cb).1.1 *
                re (PartialLayerTupleWeave cb).2 *
                resCondFlip (i.succ.rev) (PartialLayerTupleWeave cb).1.2)

lemma partialControlBitsToPerm_zero {cb : PartialLayerTuple m 0}:
  partialControlBitsToPerm m 0 cb = resCondFlip (Fin.last m) (PartialLayerTupleZero cb) := rfl

lemma partialControlBitsToPerm_succ {n : Fin m} {cb : PartialLayerTuple m n.succ}
  : partialControlBitsToPerm m (n.succ) cb =
  resCondFlip (n.succ.rev) (PartialLayerTupleWeave cb).1.1 *
  partialControlBitsToPerm m (n.castSucc) (PartialLayerTupleWeave cb).2 *
  resCondFlip (n.succ.rev) (PartialLayerTupleWeave cb).1.2 := rfl

lemma partialControlBitsToPerm_last_zero :
  partialControlBitsToPerm 0 (Fin.last 0) cb = resCondFlip 0 (PartialLayerTupleZero cb) := rfl

lemma partialControlBitsToPerm_castSucc_zero :
  partialControlBitsToPerm (m + 1) (Fin.castSucc 0) cb =
  resCondFlip (Fin.last (m + 1)) (PartialLayerTupleZero cb) := rfl

lemma partialControlBitsToPerm_succ_castSucc {n : Fin m} {cb : PartialLayerTuple (m + 1) n.succ.castSucc}
  : partialControlBitsToPerm (m + 1) (n.succ.castSucc) cb =
  resCondFlip n.succ.castSucc.rev (PartialLayerTupleWeave cb).1.1 *
  partialControlBitsToPerm (m + 1) n.castSucc.castSucc (PartialLayerTupleWeave cb).2 *
  resCondFlip n.succ.castSucc.rev (PartialLayerTupleWeave cb).1.2 := rfl

lemma partialControlBitsToPerm_last_succ :
  partialControlBitsToPerm (m + 1) (Fin.last (m + 1)) cb = (
  resCondFlip 0 (PartialLayerTupleWeave cb).1.1 *
  partialControlBitsToPerm (m + 1) (Fin.last m).castSucc (PartialLayerTupleWeave cb).2 *
  resCondFlip 0 (PartialLayerTupleWeave cb).1.2) := by
  simp_rw [← Fin.succ_last, partialControlBitsToPerm_succ, Fin.succ_last, Fin.rev_last, Fin.val_last]

lemma bitInvar_partialControlBitsToPerm (n t : Fin (m + 1)) :
(htn : t < Fin.rev n) → ∀ cb, bitInvar t (partialControlBitsToPerm m n cb) :=
  n.inductionOn
  (fun htn _ => resCondFlip_bitInvar htn.ne)
  (fun n IH htn _ => (mul_bitInvar_of_bitInvar (mul_bitInvar_of_bitInvar
    (resCondFlip_bitInvar htn.ne)
    (IH (htn.trans (Fin.rev_lt_rev.mpr (n.castSucc_lt_succ))) _)) <| resCondFlip_bitInvar htn.ne))

lemma bitInvar_zero_partialControlBitsToPerm (m : ℕ) (n : Fin (m + 1)) (hmn : n < Fin.last m)
  : ∀ cb, bitInvar 0 (partialControlBitsToPerm m n cb) :=
  bitInvar_partialControlBitsToPerm n 0 (Fin.rev_pos_iff_lt_last.mpr hmn)

lemma PartialLayerTupleWeave_PartialLayerTupleUnweave_snd (cb : PartialLayerTuple (m + 1) (n + 1)) (b) :
(PartialLayerTupleWeave (PartialLayerTupleUnweave cb b)).2 =
PartialLayerTupleUnweave ((PartialLayerTupleWeave cb).2) b :=
splitOffFirstLast_unweaveOddTuplePowTwoTuple_snd _ _

lemma PartialLayerTupleWeave_PartialLayerTupleUnweave_fst_fst :
  (PartialLayerTupleWeave (PartialLayerTupleUnweave cb b)).1.1 =
  (fun p => (PartialLayerTupleWeave cb).1.1 (mergeBitRes 0 b p)) :=
  splitOffFirstLast_unweaveOddTuplePowTwoTuple_fst_fst _ _

lemma PartialLayerTupleWeave_PartialLayerTupleUnweave_fst_snd :
  (PartialLayerTupleWeave (PartialLayerTupleUnweave cb b)).1.2 =
    (fun p => (PartialLayerTupleWeave cb).1.2 (mergeBitRes 0 b p)) :=
    splitOffFirstLast_unweaveOddTuplePowTwoTuple_fst_snd _ _

lemma equivBitInvar_map_pi_mul (π ρ : Bool → Equiv.Perm (Fin (2 ^ m))) :
((equivBitInvar 0) (fun b => π b * ρ b)).val =
  ((equivBitInvar 0) (fun b => π b)).val * ((equivBitInvar 0) (fun b => ρ b)).val := by
  ext q : 1
  simp only [equivBitInvar_apply, boolArrowPermsToBitInvarPerm_coe_apply, Equiv.Perm.coe_mul,
    Function.comp_apply, getBit_mergeBitRes, getRes_mergeBitRes]

lemma equivBitInvar_map_mul (π ρ : Bool → Equiv.Perm (Fin (2 ^ m))) :
(equivBitInvar 0) (π * ρ) = ((equivBitInvar 0) π).val * ((equivBitInvar 0) ρ).val := by
  simp_rw [Pi.mul_def, equivBitInvar_map_pi_mul]

lemma partialControlBitsToPerm_equivBitInvar
(m : ℕ) (n : Fin (m + 1)) : (cb : PartialLayerTuple (m + 1) (n.castSucc)) →
partialControlBitsToPerm (m + 1) (n.castSucc) cb = (equivBitInvar 0)
(fun b => partialControlBitsToPerm m n (PartialLayerTupleUnweave cb b)) := by
  refine' n.inductionOn (fun _ => _) (fun i IH cb => _)
  · simp_rw [partialControlBitsToPerm_castSucc_zero, partialControlBitsToPerm_zero,
      ← Nat.succ_eq_add_one, ← Fin.succ_last, resCondFlip_succ_eq_equivBitInvar_apply,
      PartialLayerTupleZero_apply, PartialLayerTupleUnweave_apply]
  · simp_rw [Fin.coe_castSucc] at IH
    simp_rw [partialControlBitsToPerm_succ_castSucc,
    partialControlBitsToPerm_succ, Fin.coe_castSucc, Fin.val_succ,
      PartialLayerTupleWeave_PartialLayerTupleUnweave_snd,
      Fin.rev_castSucc_eq_succ_rev, resCondFlip_succ_eq_equivBitInvar_apply,
      PartialLayerTupleWeave_PartialLayerTupleUnweave_fst_fst,
      PartialLayerTupleWeave_PartialLayerTupleUnweave_fst_snd,
      equivBitInvar_map_pi_mul, IH]

def controlBitsToPerm' (m : ℕ) := partialControlBitsToPerm m (Fin.last m)

lemma controlBitsToPerm'_zero :
  controlBitsToPerm' 0 cb = resCondFlip 0 (PartialLayerTupleZero cb) :=
  partialControlBitsToPerm_last_zero

lemma controlBitsToPerm'_succ : controlBitsToPerm' (m + 1) cb =
  resCondFlip 0 (PartialLayerTupleWeave cb).1.1 *
  partialControlBitsToPerm (m + 1) (Fin.last m).castSucc (PartialLayerTupleWeave cb).2 *
  resCondFlip 0 (PartialLayerTupleWeave cb).1.2 :=
  partialControlBitsToPerm_last_succ

lemma controlBitsToPerm_eq : controlBitsToPerm m = controlBitsToPerm' m := by
  induction' m with m IH <;> ext cb : 1
  · rw [controlBitsToPerm_zero, controlBitsToPerm'_zero]
    simp_rw [ControlBitsZero_apply, PartialLayerTupleZero_apply]
  · rw [controlBitsToPerm_succ, controlBitsToPerm'_succ]
    simp_rw [ControlBitsWeave_eq_PartialLayerTupleWeave_PartialLayerTupleUnweave,
      PartialLayerTupleWeave_apply, PartialLayerTupleUnweave_apply, mul_left_inj, mul_right_inj]
    simp_rw [IH, controlBitsToPerm']
    rcases m with (_ | m)
    · simp only [Function.comp_def, Fin.last_zero, Fin.castSucc_zero, partialControlBitsToPerm_zero,
      PartialLayerTupleZero_apply, Fin.last_zero_add_one, resCondFlip_one_succ_eq_equivBitInvar_apply]
    · rw [partialControlBitsToPerm_equivBitInvar, PartialLayerTupleUnweave_apply]
      congr

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
