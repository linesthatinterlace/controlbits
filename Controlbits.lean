import Controlbits.PermFintwo
import Controlbits.BitResiduum
import Controlbits.FoldFin
import Controlbits.Cycles
import Controlbits.CommutatorCycles
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Perm.Cycle.Concrete

theorem apply_cond (f : α → β) (b : Bool) (x y : α) :
    f (cond b x y) = cond b (f x) (f y) := by cases b <;> rfl

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
  getBit_mergeBitRes, Bool.xor_false_right, Bool.xor_true, ← Bool.not_false, ← flipBit_mergeBitRes,
  cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF, getBit_flipBit, firstControlBits_apply, forall_const]

def LastControlBits (π) (p : Fin (2^m)) :=
getBit 0 ((FirstControl π) (π (mergeBitRes 0 false p)))

--lemma lastControlBits_def : LastControlBits π p = getBit 0 ((FirstControl π) (π (mergeBitRes 0 false p))) := rfl

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

-- Theorem 5.5



-- SECTION

def funToBoolArrowFuns (i : Fin (m + 1)) (f : Fin (2^(m + 1)) → Fin (2^(m + 1))) : Bool → Fin (2^m) → Fin (2^m) :=
fun b p => getRes i (f (mergeBitRes i b p))

lemma funToBoolArrowFuns_apply : funToBoolArrowFuns i f b p = getRes i (f (mergeBitRes i b p)) :=
rfl

lemma funToBoolArrowFuns_leftInverse_of_leftInverse_bitInvar (h : bitInvar i f)
  (hfg : Function.LeftInverse g f) :
(funToBoolArrowFuns i g b).LeftInverse (funToBoolArrowFuns i f b) := by
  intros q
  simp_rw [funToBoolArrowFuns_apply, mergeBitRes_getRes_apply_mergeBitRes_eq_apply_mergeBitRes h,
    hfg (mergeBitRes i b q), getRes_mergeBitRes]

lemma funToBoolArrowFuns_rightInverse_of_rightInverse_bitInvar (h : bitInvar i f)
  (hfg : Function.RightInverse g f) :
(funToBoolArrowFuns i g b).RightInverse (funToBoolArrowFuns i f b) :=
funToBoolArrowFuns_leftInverse_of_leftInverse_bitInvar (bitInvar_of_rightInverse_bitInvar h hfg) hfg

def boolArrowFunsToFun (i : Fin (m + 1)) (feo : Bool → Fin (2^m) → Fin (2^m)) :
  Fin (2^(m + 1)) → Fin (2^(m + 1)) := fun q => mergeBitRes i (getBit i q) ((feo (getBit i q)) (getRes i q))

lemma boolArrowFunsToFun_apply :
  boolArrowFunsToFun i feo q = mergeBitRes i (getBit i q) ((feo (getBit i q)) (getRes i q)) := rfl

lemma boolArrowFunsToFun_leftInverse_of_forall_Bool_leftInverse {feo : Bool → (Fin (2^m) → Fin (2^m))}
{geo : Bool → (Fin (2^m) → Fin (2^m))} (hπρ : ∀ b, (geo b).LeftInverse (feo b)) :
(boolArrowFunsToFun i geo).LeftInverse (boolArrowFunsToFun i feo) := by
  intros q
  simp_rw [boolArrowFunsToFun_apply, getBit_mergeBitRes, getRes_mergeBitRes,
    hπρ (getBit i q) (getRes i q), mergeBitRes_getBit_getRes]

lemma boolArrowFunsToFun_rightInverse_of_forall_Bool_rightInverse {feo : Bool → (Fin (2^m) → Fin (2^m))}
{geo : Bool → (Fin (2^m) → Fin (2^m))} (hπρ : ∀ b, (geo b).RightInverse (feo b)) :
(boolArrowFunsToFun i geo).RightInverse (boolArrowFunsToFun i feo) := by
  intros q
  simp_rw [boolArrowFunsToFun_apply, getBit_mergeBitRes, getRes_mergeBitRes,
    hπρ (getBit i q) (getRes i q), mergeBitRes_getBit_getRes]

lemma boolArrowFunsToFun_bitInvar (i : Fin (m + 1)) (feo : Bool → Fin (2^m) → Fin (2^m)) :
  bitInvar i (boolArrowFunsToFun i feo) := by
  simp_rw [bitInvar_iff_getBit_apply_eq_getBit, boolArrowFunsToFun_apply, getBit_mergeBitRes,
    implies_true]

lemma leftInverse_funToBoolArrowFuns_boolArrowFunsToFun_apply :
  (funToBoolArrowFuns i) (boolArrowFunsToFun i f) b q = f b q := by
    simp_rw [funToBoolArrowFuns_apply, boolArrowFunsToFun_apply,
    getBit_mergeBitRes, getRes_mergeBitRes]

lemma rightInverse_funToBoolArrowFuns_boolArrowFunsToFun_apply_of_bitInvar (hf : bitInvar i f) :
  (boolArrowFunsToFun i) (funToBoolArrowFuns i f) q = f q := by
  simp_rw [boolArrowFunsToFun_apply,
    funToBoolArrowFuns_apply, mergeBitRes_getBit_getRes,
    mergeBitRes_getRes_of_getBit_eq (getBit_apply_eq_getBit_of_bitInvar hf)]

def bitInvarToBoolArrowPerms (i : Fin (m + 1)) (π : {π : Equiv.Perm (Fin (2^(m + 1))) // bitInvar i π}) (b : Bool) :
Equiv.Perm (Fin (2^m)) where
  toFun := funToBoolArrowFuns i π.val b
  invFun := funToBoolArrowFuns i π.val.symm b
  left_inv := funToBoolArrowFuns_leftInverse_of_leftInverse_bitInvar π.property π.val.left_inv
  right_inv := funToBoolArrowFuns_rightInverse_of_rightInverse_bitInvar π.property π.val.right_inv

lemma bitInvarToBoolArrowPerms_apply :
  bitInvarToBoolArrowPerms i π b p = getRes i (π.val (mergeBitRes i b p)) := funToBoolArrowFuns_apply

lemma bitInvarToBoolArrowPerms_eq_funToBoolArrowFuns
  : bitInvarToBoolArrowPerms i π b = funToBoolArrowFuns i π b := rfl

def boolArrowPermsToBitInvarPerm (i : Fin (m + 1)) (πeo : Bool → Equiv.Perm (Fin (2^m))) :
{π : Equiv.Perm (Fin (2^(m + 1))) // bitInvar i π} where
  val := {  toFun := boolArrowFunsToFun i (fun b => πeo b)
            invFun := boolArrowFunsToFun i (fun b => (πeo b).symm)
            left_inv := boolArrowFunsToFun_leftInverse_of_forall_Bool_leftInverse (fun b => (πeo b).left_inv)
            right_inv := boolArrowFunsToFun_rightInverse_of_forall_Bool_rightInverse (fun b => (πeo b).right_inv)}
  property := boolArrowFunsToFun_bitInvar i (fun b => πeo b)

lemma boolArrowPermsToBitInvarPerm_coe_apply :
  (boolArrowPermsToBitInvarPerm i πeo : Fin (2^(m + 1)) → Fin (2^(m + 1))) q =
    mergeBitRes i (getBit i q) ((πeo (getBit i q)) (getRes i q)) := rfl

lemma boolArrowPermsToBitInvarPerm_eq_boolArrowFunsToFun :
  boolArrowPermsToBitInvarPerm i πeo = boolArrowFunsToFun i (fun b => πeo b) := rfl

lemma rightInverse_bitInvarToBoolArrowPerms_boolArrowPermsToBitInvarPerm :
   ((boolArrowPermsToBitInvarPerm i) (bitInvarToBoolArrowPerms i π)).val q = π.val q :=
rightInverse_funToBoolArrowFuns_boolArrowFunsToFun_apply_of_bitInvar π.property

lemma leftInverse_bitInvarToBoolArrowPerms_boolArrowPermsToBitInvarPerm {i : Fin (m + 1)} :
  (bitInvarToBoolArrowPerms i) (boolArrowPermsToBitInvarPerm i πeo) b q = πeo b q := by
exact leftInverse_funToBoolArrowFuns_boolArrowFunsToFun_apply (f := (fun b => πeo b))

def equivBitInvar (i : Fin (m + 1)) :
(Bool → Equiv.Perm (Fin (2^m))) ≃ {π : Equiv.Perm (Fin (2^(m + 1))) // bitInvar i π} where
  toFun := boolArrowPermsToBitInvarPerm i
  invFun := bitInvarToBoolArrowPerms i
  left_inv f := by ext : 2; exact leftInverse_bitInvarToBoolArrowPerms_boolArrowPermsToBitInvarPerm
  right_inv f := by ext : 2; exact rightInverse_bitInvarToBoolArrowPerms_boolArrowPermsToBitInvarPerm

lemma equivBitInvar_apply_eq_iff_symm_apply_of_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (hπ : bitInvar i π) :
  equivBitInvar i (πeo) = π ↔ πeo = (equivBitInvar i).symm ⟨π, hπ⟩ := by
  simp_rw [Equiv.eq_symm_apply, Subtype.ext_iff]

-- SECTION

def splitOffFirstLast : (Fin (2*(n + 1) + 1) → α) ≃ (α × α) × (Fin (2*n + 1) → α) :=
calc
  _ ≃ _ := Equiv.piFinSucc _ _
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (Equiv.piFinSuccAboveEquiv _ (Fin.last _))
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm

def unweavePowTwoTuple (i : Fin (m + 1)) : (Fin (2^(m + 1)) → α) ≃ (Bool → (Fin (2^m) → α)) :=
calc
  _ ≃ _ := Equiv.arrowCongr ((getBitRes i).trans (Equiv.boolProdEquivSum _)) (Equiv.refl _)
  _ ≃ _ := Equiv.sumArrowEquivProdArrow _ _ _
  _ ≃ _ := (Equiv.boolArrowEquivProd _).symm

lemma unweavePowTwoTuple_apply :
  (unweavePowTwoTuple i cb) b p = cb (mergeBitRes i b p) := by
  cases b <;> rfl

lemma unweavePowTwoTuple_apply_getBit_getRes :
  (unweavePowTwoTuple i cb) (getBit i q) (getRes i q) = cb q := by
  simp_rw [unweavePowTwoTuple_apply, mergeBitRes_getBit_getRes]

lemma unweavePowTwoTuple_symm_apply' :
  (unweavePowTwoTuple i).symm cb q  = (Equiv.sumArrowEquivProdArrow _ _ _).symm
    (cb false, cb true) ((getBit i q).rec (Sum.inl (getRes i q)) (Sum.inr (getRes i q))) := rfl

lemma unweavePowTwoTuple_symm_apply:
  (unweavePowTwoTuple i).symm cb q = cb (getBit i q) (getRes i q) := by
  rw [unweavePowTwoTuple_symm_apply']
  cases (getBit i q) <;> rfl

lemma unweavePowTwoTuple_symm_apply_mergeBitRes:
  (unweavePowTwoTuple i).symm cb (mergeBitRes i b p) = cb b p := by
  simp_rw [unweavePowTwoTuple_symm_apply, getBit_mergeBitRes, getRes_mergeBitRes]

def unweaveOddTuplePowTwoTuple (i : Fin (m + 1)) :
  (Fin (2*n + 1) → Fin (2 ^ (m + 1)) → α) ≃ (Bool → Fin (2*n + 1) → Fin (2^m) → α) :=
calc
  _ ≃ _ := Equiv.arrowCongr (Equiv.refl _) (unweavePowTwoTuple i)
  _ ≃ _ := Equiv.piComm _

lemma unweaveOddTuplePowTwoTuple_zero :
  unweaveOddTuplePowTwoTuple (n := 0) i cb b t p = cb t (mergeBitRes i b p) := by
  cases b <;> rfl

lemma unweaveOddTuplePowTwoTuple_apply :
  (unweaveOddTuplePowTwoTuple i cb) b t p = cb t (mergeBitRes i b p) := by
  cases b <;> rfl

lemma unweaveOddTuplePowTwoTuple_apply' :
  (unweaveOddTuplePowTwoTuple i cb) b = fun t p => cb t (mergeBitRes i b p) := by
  cases b <;> rfl

lemma unweaveOddTuplePowTwoTuple_apply_getBit_getRes :
  (unweaveOddTuplePowTwoTuple i cb) (getBit i q) t (getRes i q) = cb t q := by
  simp_rw [unweaveOddTuplePowTwoTuple_apply, mergeBitRes_getBit_getRes]

abbrev ControlBitsLayer (m : ℕ) := Fin (2^m) → Bool

def permToControlBits {cbType : (m : ℕ) → Type u} (m : ℕ) (zero : cbType 0 ≃ ControlBitsLayer 0)
  (weave : (m : ℕ) → cbType (m + 1) ≃ ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → cbType m)))
: Equiv.Perm (Fin (2^(m + 1))) → cbType m :=
m.recOn (fun π => zero.symm (LastControlBits π))
(fun _ re π => (weave _).symm (((FirstControlBits π), (LastControlBits π)), (re ∘ ((equivBitInvar 0).symm (MiddlePerm π)))))

def controlBitsToPerm {cbType : (m : ℕ) → Type u} (m : ℕ) (zero : cbType 0 ≃ ControlBitsLayer 0)
  (weave : (m : ℕ) → cbType (m + 1) ≃ ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → cbType m)))
: cbType m → Equiv.Perm (Fin (2^(m + 1))) :=
m.recOn (fun cb => resCondFlip 0 (zero cb))
  (fun _ re cb => (resCondFlip 0 (weave _ cb).fst.fst) * ((equivBitInvar 0) (re ∘ (weave _ cb).snd)) *
                  (resCondFlip 0 ((weave _ cb).fst.snd)))

lemma permToControlBits_succ {cbType : (m : ℕ) → Type u} (m : ℕ) (zero : cbType 0 ≃ ControlBitsLayer 0)
  (weave : (m : ℕ) → cbType (m + 1) ≃ ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → cbType m))):
  permToControlBits (m + 1) zero weave = fun π => (weave _).symm (((FirstControlBits π), (LastControlBits π)),
  (permToControlBits m zero weave) ∘ ((equivBitInvar 0).symm (MiddlePerm π))) := rfl

lemma controlBitsToPerm_succ {cbType : (m : ℕ) → Type u} (m : ℕ) (zero : cbType 0 ≃ ControlBitsLayer 0)
  (weave : (m : ℕ) → cbType (m + 1) ≃ ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → cbType m))) :
  controlBitsToPerm (m + 1) zero weave = fun cb => ((resCondFlip 0 (weave _ cb).fst.fst) *
    ((equivBitInvar 0) ((controlBitsToPerm m zero weave) ∘ (weave _ cb).snd)) *
      (resCondFlip 0 ((weave _ cb).fst.snd))) := rfl

lemma controlBitsToPerm_leftInverse {cbType : (m : ℕ) → Type u} {zero : cbType 0 ≃ ControlBitsLayer 0}
  {weave : (m : ℕ) → cbType (m + 1) ≃ ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → cbType m))} :
  (controlBitsToPerm m zero weave).LeftInverse (permToControlBits m zero weave) := by
  induction' m with m IH
  · intro π
    nth_rewrite 2 [Fin.perm_fin_two π]
    simp_rw [permToControlBits, controlBitsToPerm, Equiv.apply_symm_apply,
      resCondFlip_lastControlBits, lastControl_base]
  · intro π
    simp_rw [permToControlBits_succ, controlBitsToPerm_succ, Equiv.apply_symm_apply,
      resCondFlip_firstControlBits, resCondFlip_lastControlBits, ← Function.comp.assoc,
      IH.comp_eq_id, Function.comp.left_id, Equiv.apply_symm_apply,
      FirstControl_mul_MiddlePerm_mul_LastControl_eq_self]

def PartialLayerTuple (n m : ℕ):= Fin (2*n + 1) → ControlBitsLayer m

def zeroPartialLayerTuple : PartialLayerTuple 0 m ≃ ControlBitsLayer m := Equiv.funUnique (Fin 1) _

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
(cb : Fin (2*n + 1) → ControlBitsLayer m) (hmn : n < m) (t : Fin (m + 1)) (htn : (t : ℕ) + n < m) :
  bitInvar t (partialControlBitsToPerm n cb) := by
induction' n with n IH generalizing m t
· simp_rw [Nat.zero_eq, add_zero] at htn
  simp_rw [partialControlBitsToPerm_zero]
  refine' resCondFlip_bitInvar (Fin.ne_of_lt htn)
· simp_rw [partialControlBitsToPerm_succ]
  refine' mul_bitInvar_of_bitInvar (mul_bitInvar_of_bitInvar (resCondFlip_bitInvar _) _) (resCondFlip_bitInvar _)
  · rw [Fin.ne_iff_vne, Fin.val_rev, Fin.coe_ofNat_eq_mod,
      Nat.succ_sub_succ_eq_sub, Nat.mod_eq_of_lt (hmn.trans (Nat.lt_succ_self _))]
    exact ne_of_lt (Nat.lt_sub_of_add_lt htn)
  · exact IH _ ((Nat.lt_succ_self _).trans hmn) _ ((Nat.add_lt_add_left (Nat.lt_succ_self _) _).trans htn)
  · rw [Fin.ne_iff_vne, Fin.val_rev, Fin.coe_ofNat_eq_mod,
      Nat.succ_sub_succ_eq_sub, Nat.mod_eq_of_lt (hmn.trans (Nat.lt_succ_self _))]
    exact ne_of_lt (Nat.lt_sub_of_add_lt htn)

lemma bitInvar_zero_partialControlBitsToPerm
(cb : Fin (2*n + 1) → ControlBitsLayer m) (hmn : n < m) :
  bitInvar 0 (partialControlBitsToPerm n cb) := by
  refine' bitInvar_partialControlBitsToPerm cb hmn _ _
  rw [Fin.val_zero, zero_add]
  exact hmn

def fullControlBitsToPerm (m : ℕ) : (Fin (2*m + 1) → ControlBitsLayer m) →
  Equiv.Perm (Fin (2^(m + 1))) := partialControlBitsToPerm m

def fullControlBitsToPerm' (m : ℕ) : (Fin (2*m + 1) → ControlBitsLayer m) →
  Equiv.Perm (Fin (2^(m + 1))) :=
controlBitsToPerm m (cbType := fun m => Fin (2*m + 1) → _) (Equiv.funUnique (Fin 1) _)
  (fun _ => (splitOffFirstLast).trans ((Equiv.refl _).prodCongr (unweaveOddTuplePowTwoTuple 0)))
/-
(extra m n) ((sides (m + 1) n) cb).snd  = Bool → pcbType m n
pcbType (m + 1) (n + 1) ≃ ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × pcbType (m + 1) n))

pcbType (m + 1) (m + 1) ≃ ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → pcbType m m))

pcbType (m + 1) (n + 1) -> (Bool → pcbType m (n + 1)) -> (Bool -> ((ControlBitsLayer m × ControlBitsLayer m) × pcbType m n))
                        -> Bool -> ControlBitsLayer m × Bool -> ControlBitsLayer m × Bool -> pcbType m n
                        -> ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × pcbType (m + 1) n)
                        -> ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → pcbType m n)
pcbType (m + 1) (n + 1)  -> Bool → pcbType m n

pcbType (m + 1) (n + 1) -> (Bool → (pcbType m (n + 1)))

ControlBitsLayer (m + 1)   ≃    Bool -> ControlBitsLayer m
-/


/-
lemma foobarbar {pcbType : (m n : ℕ) → Type u} (m n : ℕ) (centre : (m : ℕ) → (pcbType m 0 ≃ ControlBitsLayer m))
  (sides : (m n : ℕ) → pcbType m (n + 1) ≃ ((ControlBitsLayer m × ControlBitsLayer m) × pcbType m n))
  (extra : (m n : ℕ) → pcbType (m + 1) n ≃ (Bool → pcbType m n))
  (cb : pcbType (m + 1) (n + 1)) (q : Fin (2 ^ (m + 1 + 1))) :
    (partialControlBitsToPerm m n centre sides ((extra m n) ((sides (m + 1) n) cb).snd (getBit 0 q)))
      (getRes 0 q) = getRes 0 (partialControlBitsToPerm (m + 1) n centre sides ((sides (m + 1) n) cb).snd q) := by
induction' n with n IH generalizing m
· simp_rw [partialControlBitsToPerm_zero, resCondFlip_apply, apply_cond (getRes 0)] ; sorry
· simp_rw [partialControlBitsToPerm_succ, Equiv.Perm.mul_apply, IH]

simp_rw [equivBitInvar, Equiv.coe_fn_mk, boolArrowPermsToBitInvarPerm_coe_apply, Function.comp_apply, foobarbar]
rw [← getBit_apply_eq_getBit_of_bitInvar (bitInvar_partialControlBitsToPerm centre sides cb (Nat.lt_succ_self _)),
  mergeBitRes_getBit_getRes]

lemma foobar_bar (m : ℕ) : Fin.rev (Fin.last m) = 0 := by
  simp_rw [Fin.eq_iff_veq, Fin.val_rev, Nat.succ_sub_succ_eq_sub, Fin.val_zero, Fin.val_last, Nat.sub_self]

lemma foobar (m : ℕ) : Fin.rev (m : Fin (m + 1)) = 0 := by
  simp_rw [Fin.eq_iff_veq, Fin.val_rev, Nat.succ_sub_succ_eq_sub, Fin.val_zero,
    Fin.val_cast_of_lt (Nat.lt_succ_self _), Nat.sub_self]
-/

lemma barbar : mergeBitRes 0 b (getRes (Fin.last m) p) = getRes (Fin.last (m + 1)) (mergeBitRes 0 b p) := sorry
lemma barbarbarbar : (flipBit (Fin.last m)) p = getRes 0 ((flipBit (Fin.last (m + 1))) (mergeBitRes 0 b p)) := sorry

lemma succbarr (n : ℕ) : mergeBitRes 0 b (getRes (Fin.rev ((n : Fin (m + 1)) + 1)) p)=
  getRes (Fin.rev ((n : Fin (m + 2)) + 1)) (mergeBitRes 0 b p) := sorry

lemma succbarrbarr (n : ℕ) : mergeBitRes 0 b ((flipBit (Fin.rev ((n : Fin (m + 1)) + 1))) p) =
  (flipBit (Fin.rev ((n : Fin (m + 2)) + 1))) (mergeBitRes 0 b p) := sorry

lemma foobarbar
  (cb : Fin (2 * n + 1) → ControlBitsLayer (m + 1)) :
    partialControlBitsToPerm n ((unweaveOddTuplePowTwoTuple 0) cb b) =
    fun p => getRes 0 (partialControlBitsToPerm n cb (mergeBitRes 0 b p)) := by
rw [unweaveOddTuplePowTwoTuple_apply']
induction' n with n IH generalizing m
· ext p : 1
  simp_rw [partialControlBitsToPerm_zero, resCondFlip_apply, apply_cond (getRes 0)]
  rw [barbar, getRes_mergeBitRes, barbarbarbar]
· ext p : 1
  simp [partialControlBitsToPerm_succ, splitOffFirstLast, resCondFlip_apply, IH,
    apply_cond (getRes 0), apply_cond (mergeBitRes 0 b)]
  simp_rw [succbarr, succbarrbarr]
  rw [mergeBitRes_getRes_of_getBit_eq]
  · sorry
  · simp_rw [apply_cond (getBit 0)]
  rcases (getBit 0 q).dichotomy with (h | h) <;>
  simp [h, resCondFlip_apply, apply_cond (getRes 0)]
/-
cb 0
        (getRes (Fin.rev (↑n + 1))
          (mergeBitRes 0 b
            (getRes 0
              (↑(partialControlBitsToPerm n fun t => cb (Fin.succ (Fin.castSucc t)))
                (bif cb (Fin.last (Nat.succ (2 * n + 1))) (getRes (Fin.rev (↑n + 1)) (mergeBitRes 0 b p)) then
                  ↑(flipBit (Fin.rev (↑n + 1))) (mergeBitRes 0 b p)
                else mergeBitRes 0 b p)))))

cb 0
        (getRes (Fin.rev (↑n + 1))
          (↑(partialControlBitsToPerm n fun j => cb (Fin.succ (Fin.castSucc j)))
            (bif cb (Fin.last (Nat.succ (2 * n + 1))) (getRes (Fin.rev (↑n + 1)) (mergeBitRes 0 b p)) then
              ↑(flipBit (Fin.rev (↑n + 1))) (mergeBitRes 0 b p)
            else mergeBitRes 0 b p)))
-/
lemma h_extra_sides (hnm : n < m + 1) (cb : Fin (2 * n + 1) → ControlBitsLayer (m + 1))
  : ↑((equivBitInvar 0) (partialControlBitsToPerm n ∘ (unweaveOddTuplePowTwoTuple 0) cb)) =
    partialControlBitsToPerm n cb := by

ext q : 1
simp_rw [equivBitInvar]
simp [boolArrowPermsToBitInvarPerm_coe_apply, foobarbar]
rw [← getBit_apply_eq_getBit_of_bitInvar (bitInvar_zero_partialControlBitsToPerm cb hnm)]
simp_rw [mergeBitRes_getBit_getRes]

lemma foobar (m : ℕ) : Fin.rev (m : Fin (m + 1)) = 0 := by
  simp_rw [Fin.eq_iff_veq, Fin.val_rev, Nat.succ_sub_succ_eq_sub, Fin.val_zero,
    Fin.val_cast_of_lt (Nat.lt_succ_self _), Nat.sub_self]

lemma foobar' (m : ℕ) : Fin.rev ((m : Fin (m + 1 + 1)) + 1) = 0 := by
  sorry

lemma foobarbar'
  (cb : Fin (2 * m + 1) → ControlBitsLayer (m + 1)) :
    partialControlBitsToPerm m ((unweaveOddTuplePowTwoTuple 0) cb b) q =
    getRes 0 (partialControlBitsToPerm m cb (mergeBitRes 0 b q)) := by
rw [unweaveOddTuplePowTwoTuple_apply']
cases b
· rw [← Fin.mk_val (mergeBitRes 0 false q)]
  simp_rw [coe_mergeBitRes_zero]
rw [Fin.eq_mk_iff_val_eq.mpr coe_getRes_zero]

ext
rw [coe_getRes_zero]
induction' m with m IH
· ext p : 1
  simp_rw [partialControlBitsToPerm_zero, resCondFlip_apply, apply_cond (getRes 0)]
  rw [barbar, getRes_mergeBitRes, barbarbarbar]
· ext p : 1
  simp_rw [partialControlBitsToPerm_succ, splitOffFirstLast,
    Nat.cast_succ, Nat.add_eq, Nat.add_zero, Nat.mul_eq, Equiv.instTransSortSortSortEquivEquivEquiv_trans,
    Equiv.trans_apply, Equiv.piFinSucc_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.piFinSuccAboveEquiv_apply,
    Fin.succAbove_last, Prod_map, id_eq, Fin.succ_last, Equiv.prodAssoc_symm_apply, Equiv.Perm.coe_mul,
    Function.comp_apply, foobar',resCondFlip_apply, IH]
  simp [partialControlBitsToPerm_succ, splitOffFirstLast, resCondFlip_apply, IH,
    apply_cond (getRes 0), apply_cond (mergeBitRes 0 b), foobar']
  simp_rw [succbarr, succbarrbarr]
  rw [mergeBitRes_getRes_of_getBit_eq]
  · sorry
  · simp_rw [apply_cond (getBit 0)]
  rcases (getBit 0 q).dichotomy with (h | h) <;>
  simp [h, resCondFlip_apply, apply_cond (getRes 0)]

lemma h_extra_sides' (cb : Fin (2 * m + 1) → ControlBitsLayer (m + 1))
  : ↑((equivBitInvar 0) (partialControlBitsToPerm m ∘ (unweaveOddTuplePowTwoTuple 0) cb)) =
    partialControlBitsToPerm m cb := by

ext q : 1
simp_rw [equivBitInvar]
simp_rw [Equiv.coe_fn_mk, boolArrowPermsToBitInvarPerm_coe_apply, Function.comp_apply, foobarbar,
  mergeBitRes_getRes_of_getBit_eq]
rw [← getBit_apply_eq_getBit_of_bitInvar (bitInvar_zero_partialControlBitsToPerm cb hnm)]
simp_rw [mergeBitRes_getBit_getRes]

lemma fullControlBitsToPerm'_eq :
  fullControlBitsToPerm' m = fullControlBitsToPerm m := by
  simp only [fullControlBitsToPerm', fullControlBitsToPerm]
  induction' m with m IH
  · rfl
  · simp_rw [partialControlBitsToPerm_succ, controlBitsToPerm_succ, Equiv.trans_apply,
      Equiv.prodCongr_apply, Equiv.coe_refl, Prod_map, id_eq,
      Function.funext_iff, IH, foobar, h_extra_sides', implies_true]

--SECTION


def InductiveControlBits : ℕ → Type
  | 0 => ControlBitsLayer 0
  | (m + 1) => (ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → (InductiveControlBits m))

@[ext]
lemma inductiveControlBits_zero_ext {a b : InductiveControlBits 0} (h : ∀ x : Fin 1, a x = b x) : a = b := funext h

lemma inductiveControlBits_zero_ext_iff {a b : InductiveControlBits 0} : a = b ↔ ∀ x : Fin 1, a x = b x :=
⟨fun H _ => H ▸ rfl, inductiveControlBits_zero_ext⟩

def indCBitsToPerm (m : ℕ) (cb : InductiveControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
  match m with
  | 0 => resCondFlip 0 cb
  | m + 1 => (resCondFlip 0 (cb.fst.fst)) *
      ((equivBitInvar 0) ((indCBitsToPerm m) ∘ cb.snd)) * (resCondFlip 0 (cb.fst.snd))

lemma indCBitsToPerm_zero_apply : indCBitsToPerm 0 (cb : InductiveControlBits 0) q = resCondFlip 0 cb q := rfl

lemma indCBitsToPerm_base : indCBitsToPerm 0 (cb : InductiveControlBits 0) = bif cb 0 then Equiv.swap 0 1 else 1 := by
  rw [indCBitsToPerm, resCondFlip_base]

@[simp]
lemma indCBitsToPerm_succ_def : indCBitsToPerm (m + 1) (cb : InductiveControlBits (m + 1)) =
(resCondFlip 0 (cb.fst.fst)) *
  ((equivBitInvar 0) ((indCBitsToPerm m) ∘ cb.snd)) * (resCondFlip 0 (cb.fst.snd)) :=
rfl

def permToIndCBits (m : ℕ) (π : Equiv.Perm (Fin (2^(m + 1)))) : InductiveControlBits m :=
  match m with
  | 0 => LastControlBits π
  | m + 1 => ((FirstControlBits π, LastControlBits π),
              (permToIndCBits m) ∘ ((equivBitInvar 0).symm (MiddlePerm π)))

lemma permToIndCBits_base : permToIndCBits 0 π = ![decide (π 0 = 1)] := by
rw [permToIndCBits, lastControlBits_base]

@[simp]
lemma permToIndCBits_succ_def :
  permToIndCBits (m + 1) π = ((FirstControlBits π, LastControlBits π),
    (permToIndCBits m) ∘ ((equivBitInvar 0).symm (MiddlePerm π))) := rfl

lemma indToPermLeftInverse : Function.LeftInverse (indCBitsToPerm m) (permToIndCBits m) := by
induction' m with m IH
· intro π
  nth_rewrite 2 [Fin.perm_fin_two π]
  simp_rw [indCBitsToPerm, permToIndCBits, resCondFlip_lastControlBits, lastControl_base]
· intro π
  simp_rw [permToIndCBits_succ_def, indCBitsToPerm_succ_def, ← Function.comp.assoc, IH.comp_eq_id,
    Function.comp.left_id, Equiv.apply_symm_apply, resCondFlip_firstControlBits,
    resCondFlip_lastControlBits, MiddlePerm_coe, mul_assoc (a := FirstControl π),
    firstControl_mul_cancel_left, lastControl_mul_cancel_right]

abbrev LayerTupleControlBits (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

abbrev BitTupleControlBits (m : ℕ) := Fin ((2*m + 1)*(2^m)) → Bool

def bitTupleEquivLayerTuple : BitTupleControlBits m ≃ LayerTupleControlBits m :=
calc
  _ ≃ ((Fin (2*m + 1) × Fin (2^m)) → Bool) := Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl _)
  _ ≃ _ := Equiv.curry _ _ _

def layerTupleEquivInductive : LayerTupleControlBits m ≃ InductiveControlBits m :=
  match m with
  | 0 => (Equiv.funUnique (Fin 1) _)
  | (m + 1) => calc
                _ ≃ _ := splitOffFirstLast
                _ ≃ _ := Equiv.prodCongr (Equiv.refl _)
                          (calc
                            _ ≃ _ := Equiv.arrowCongr (Equiv.refl _) (unweavePowTwoTuple 0)
                            _ ≃ _ := Equiv.piComm (fun _ _ => ControlBitsLayer m)
                            _ ≃ _ := Equiv.arrowCongr (Equiv.refl _) layerTupleEquivInductive)

def bar : Fin (2*n + 1) ≃ Fin n ⊕ Fin 1 ⊕ Fin n :=
calc
  _ ≃ _ := finCongr (n.two_mul.symm ▸ n.add_right_comm _ _)
  _ ≃ _ := finSumFinEquiv.symm
  _ ≃ _ := Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)
  _ ≃ _ := Equiv.sumAssoc _ _ _

def foo : (Fin (2*n + 1) → α) ≃ ((Fin n → α) × (Fin n → α)) × α :=
calc
  _ ≃ _ := Equiv.arrowCongr
            (calc
              _ ≃ _ := finCongr (n.two_mul.symm ▸ n.add_right_comm _ 1)
              _ ≃ _ := finSumFinEquiv.symm
              _ ≃ _ := Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _)
              _ ≃ _ := Equiv.sumAssoc _ _ _)
            (Equiv.refl _)
  _ ≃ _ := Equiv.sumArrowEquivProdArrow _ _ _
  _ ≃ _ := Equiv.prodCongr
            (Equiv.refl _)
            (calc
              _ ≃ _ := Equiv.sumArrowEquivProdArrow _ _ _
              _ ≃ _ := Equiv.prodCongr
                        (Equiv.funUnique _ _)
                        (Equiv.arrowCongr Fin.revPerm (Equiv.refl _))
              _ ≃ _ := Equiv.prodComm _ _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm

abbrev ListLayerListControlBits (m : ℕ) := ((Fin m → ControlBitsLayer m) × (Fin m → ControlBitsLayer m)) × ControlBitsLayer m

def layerTupleEquivListLayerList : LayerTupleControlBits m ≃ ListLayerListControlBits m := foo

def partialListLayerListToPerm (n : Fin (m + 1)) (cb : ListLayerListControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
n.reverseInduction (resCondFlip (Fin.last _) (cb.snd))
  (fun n π => (resCondFlip (n.castSucc) (cb.fst.fst n)) * π * (resCondFlip (n.castSucc) (cb.fst.snd n)))

def listLayerListToPerm (cb : ListLayerListControlBits m) : Equiv.Perm (Fin (2^(m + 1))) := partialListLayerListToPerm 0 cb



def PartialLayerTuple (n m : ℕ):= Fin (2*n + 1) → ControlBitsLayer m

def i_partialLayerTuple (m : ℕ) : PartialLayerTuple 0 m ≃ ControlBitsLayer m := Equiv.funUnique (Fin 1) _

def j_partialLayerTuple (m n : ℕ) :
  PartialLayerTuple m (n + 1) ≃ ((ControlBitsLayer m × ControlBitsLayer m) × PartialLayerTuple n m) := splitOffFirstLast

def unweaveOddTuplePowTwoTuple (m n : ℕ) : PartialLayerTuple n (m + 1) ≃ (Bool → PartialLayerTuple n m) :=
calc
  _ ≃ _ := Equiv.arrowCongr (Equiv.refl _) (unweavePowTwoTuple 0)
  _ ≃ _ := Equiv.piComm (fun _ _ => ControlBitsLayer m)

def layerTupleToPerm
  (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
  fullControlBitsToPerm m i_partialLayerTuple j_partialLayerTuple cb

def layerTupleToPerm'''
  (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
  fullControlBitsToPerm' m i_partialLayerTuple j_partialLayerTuple unweaveOddTuplePowTwoTuple cb

def layerTupleToPerm''''
  (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
  controlBitsToPerm (cbType := fun m => PartialLayerTuple m m) m (i_partialLayerTuple 0)
    (fun m => (j_partialLayerTuple (m + 1) m).trans ((Equiv.refl _).prodCongr (unweaveOddTuplePowTwoTuple _ _))) cb

/-
def controlBitsToPerm {cbType : (m : ℕ) → Type u} (m : ℕ) (zero : cbType 0 ≃ ControlBitsLayer 0)
  (weave : (m : ℕ) → cbType (m + 1) ≃ ((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (Bool → cbType m)))
: cbType m → Equiv.Perm (Fin (2^(m + 1))) :=
m.recOn (fun cb => resCondFlip 0 (i.symm cb))
  (fun _ re cb => (resCondFlip 0 ((j _).symm cb).fst.fst) *
    ((equivBitInvar 0).symm (re ∘ ((j _).symm cb).snd)) *
      (resCondFlip 0 (((j _).symm cb).fst.snd)))
-/

def bitTupleEquivInductive : BitTupleControlBits m ≃ InductiveControlBits m :=
bitTupleEquivLayerTuple.trans layerTupleEquivInductive

def permToLayerTuple (π : Equiv.Perm (Fin (2^(m + 1)))) : LayerTupleControlBits m :=
layerTupleEquivInductive.symm (permToIndCBits m π)

def permToBitTuple (π : Equiv.Perm (Fin (2^(m + 1)))) : BitTupleControlBits m :=
bitTupleEquivInductive.symm (permToIndCBits m π)

def layerTupleToPerm' (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
indCBitsToPerm m (layerTupleEquivInductive cb)

def bitTupleToPerm (cb : BitTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
indCBitsToPerm m (bitTupleEquivInductive cb)

def layerTupleToPerm'' (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => resCondFlip (foldFin k) (cb k))).prod

def bitTupleToPerm' (cb : BitTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => resCondFlip (foldFin k) (bitTupleEquivLayerTuple cb k))).prod

end ControlBits


-- Testing


def myControlBits69 := (![true, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false] : BitTupleControlBits 2)
def myControlBits69' := (![![true, false, true, false], ![true, false, true, false], ![false, false, false, false],
 ![false, false, false, false], ![false, false, false, false]] : LayerTupleControlBits 2)

def myControlBits1 : LayerTupleControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def myControlBits2 : LayerTupleControlBits 1 := ![![false, false], ![true, true], ![false, true]]
def myControlBits2a : BitTupleControlBits 1 := ![false, true, false, true, true, true]
def myControlBits3 : LayerTupleControlBits 0 := ![![true]]
def myControlBits4 : LayerTupleControlBits 0 := ![![false]]
#eval (layerTupleEquivListLayerList myControlBits2)
#eval [0, 1, 2, 3].map (layerTupleToPerm (myControlBits2))
#eval [0, 1, 2, 3].map (layerTupleToPerm' (myControlBits2))
#eval [0, 1, 2, 3].map (layerTupleToPerm'' myControlBits2)
#eval [0, 1, 2, 3].map (layerTupleToPerm''' myControlBits2)
#eval [0, 1, 2, 3].map (layerTupleToPerm'''' myControlBits2)
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleToPerm (m := 2) (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleToPerm' (m := 2) (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleToPerm'' (m := 2) (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleToPerm''' (m := 2) (myControlBits69'))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (layerTupleToPerm'''' (m := 2) (myControlBits69'))
/-
#eval bitTupleToPerm <| permToBitTuple (m := 4) (Equiv.refl _)
#eval permToLayerTuple <| (layerTupleToPerm (myControlBits1))
#eval permToLayerTuple <| (layerTupleToPerm' (myControlBits1))
#eval permToBitTuple <| (layerTupleToPerm (myControlBits1))
--layerTupleEquivListLayerList  listLayerListToPerm

#eval [0, 1, 2, 3, 4, 5, 6, 7].map (bitTupleToPerm (m := 2) (myControlBits69))
-/


-- HELL
/-

lemma cycleMin_xBXF_apply_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF_apply :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = (flipBit 0) (CycleMin (XBackXForth π) (π q)) :=
cycleMin_xBXF_apply_flipBit_zero_eq_cycleMin_xBXF_flipBit_zero_apply.trans
  cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF
def XBackXForth (π : Equiv.Perm (Fin (2^(m + 1)))) := π * (flipBit 0) * π⁻¹ * (flipBit 0)

lemma xBXF_def : XBackXForth π = π * (flipBit 0) * π⁻¹ * (flipBit 0) := rfl

lemma xBXF_apply : (XBackXForth π) q = π ((flipBit 0) (π⁻¹ (flipBit 0 q))) := rfl

lemma xBXF_refl : XBackXForth (Equiv.refl (Fin (2^(m + 1)))) = Equiv.refl _ := by
simp_rw [Equiv.ext_iff, xBXF_apply, Equiv.Perm.refl_inv, Equiv.Perm.one_apply,
  flipBit_flipBit, forall_const]

lemma xBXF_one : XBackXForth (1 : Equiv.Perm (Fin (2^(m + 1)))) = 1 := xBXF_refl

lemma xBXF_base : XBackXForth (m := 0) π = 1 := by
  have h := Fin.perm_fin_two π
  split_ifs at h <;> simp_rw [Equiv.ext_iff, xBXF_apply, h]

lemma xBXF_inv : (XBackXForth π)⁻¹ = (flipBit 0) * π * (flipBit 0) * π⁻¹ := by
rw [xBXF_def] ; simp only [mul_assoc, mul_inv_rev, flipBit_inv, inv_inv]

lemma xBXF_inv_apply : (XBackXForth π)⁻¹ q = (flipBit 0) (π ((flipBit 0) (π⁻¹ q))) := by
rw [xBXF_inv] ; rfl

lemma flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit : flipBit 0 * XBackXForth π =
(XBackXForth π)⁻¹ * flipBit 0 := by simp_rw [xBXF_inv, xBXF_def, mul_assoc]

lemma flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit : XBackXForth π * flipBit 0 =
flipBit 0 * (XBackXForth π)⁻¹ := by rw [eq_mul_inv_iff_mul_eq, mul_assoc,
  flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, mul_inv_cancel_left]

@[simp]
lemma xBXF_apply_flipBit_eq_flipBit_xBXF_inv : XBackXForth π (flipBit 0 q) =
flipBit 0 ((XBackXForth π)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_inv_apply_flipBit_eq_flipBit_xBXF : (XBackXForth π)⁻¹ (flipBit 0 q) =
flipBit 0 (XBackXForth π q)
:= by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, Equiv.Perm.mul_apply]

lemma flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit {k : ℕ} : flipBit 0 * ((XBackXForth π)^k) =
((XBackXForth π)^k)⁻¹ * flipBit 0 := by
induction' k with n hn
· rw [Nat.zero_eq, pow_zero, inv_one, mul_one, one_mul]
· simp_rw [pow_succ', ← mul_assoc, hn, ← pow_succ', pow_succ'', mul_inv_rev, mul_assoc,
    flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit]

lemma xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow {k : ℕ} : ((XBackXForth π)^k) * flipBit 0 =
flipBit 0 * ((XBackXForth π)^k)⁻¹ := by
rw [eq_mul_inv_iff_mul_eq, mul_assoc, flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit,
  mul_inv_cancel_left]

@[simp]
lemma xBXF_pow_apply_flipBit_eq_flipBit_xBXF_pow {k : ℕ} : ((XBackXForth π)^k) (flipBit 0 q) =
flipBit 0 (((XBackXForth π)^k)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_pow_inv_apply_flipBit_eq_flipBit_xBXF {k : ℕ} : ((XBackXForth π)^k)⁻¹ (flipBit 0 q)
= flipBit 0 (((XBackXForth π)^k) q)
:= by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit, Equiv.Perm.mul_apply]

lemma xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv {k : ℤ} :
(XBackXForth π)^k * (flipBit 0) = (flipBit 0) * ((XBackXForth π)^k)⁻¹ := by
cases k
· simp only [Int.ofℕ_eq_coe, zpow_coe_nat, zpow_neg]
  exact xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow
· simp only [zpow_negSucc, zpow_neg, inv_inv]
  exact flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit.symm

lemma flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit {k : ℤ} :
(flipBit 0) * (XBackXForth π)^k = ((XBackXForth π)^k)⁻¹ * (flipBit 0) := by
rw [← zpow_neg, xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, zpow_neg, inv_inv]

-- Theorem 4.3 (a) (ish)

@[simp]
lemma xBXF_zpow_apply_flipBit_eq_flipBit_xBXF_zpow_inv {k : ℤ} :
((XBackXForth π)^k) (flipBit 0 q) = (flipBit 0) (((XBackXForth π)^k)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, Equiv.Perm.mul_apply]

@[simp]
lemma xBXR_zpow_inv_apply_flipBit_eq_flipBit_xBXF_zpow {k : ℤ} :
(((XBackXForth π)^k)⁻¹) (flipBit 0 q) = flipBit 0 (((XBackXForth π)^k) q) := by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_apply_ne_flipBit : (XBackXForth π) q ≠ (flipBit 0) q := by
simp_rw [xBXF_apply, ne_eq, ← Equiv.Perm.eq_inv_iff_eq (y := (flipBit 0) q)]
exact flipBit_ne_self

@[simp]
lemma xBXF_pow_apply_ne_flipBit {k : ℕ} : ((XBackXForth π)^k) q ≠ (flipBit 0) q := by
induction' k using Nat.twoStepInduction with k IH generalizing q
· rw [pow_zero]
  exact (flipBit_ne_self).symm
· rw [pow_one]
  exact xBXF_apply_ne_flipBit
· intros h
  rw [pow_succ'' (n := k.succ), pow_succ' (n := k), Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    ← Equiv.eq_symm_apply (x := flipBit 0 q), ← Equiv.Perm.inv_def,
    xBXF_inv_apply_flipBit_eq_flipBit_xBXF] at h
  exact IH h

@[simp]
lemma xBXF_pow_inv_ne_flipBit {k : ℕ} : (((XBackXForth π)^k)⁻¹) q ≠ flipBit 0 q := by
simp_rw [ne_eq, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
convert (xBXF_pow_apply_ne_flipBit (q := flipBit 0 q)).symm
exact flipBit_flipBit.symm

@[simp]
lemma xBXF_zpow_ne_flipBit {k : ℤ} : ((XBackXForth π)^k) q ≠ flipBit 0 q := by
cases k <;> simp

-- Theorem 4.3 (b)
lemma xBXF_zpow_ne_flipBit_mul_xBXF_zpow {j k : ℤ}  :
((XBackXForth π)^j) q ≠ flipBit 0 (((XBackXForth π)^k) q) := by
rw [← sub_add_cancel j k, zpow_add, Equiv.Perm.mul_apply]
exact xBXF_zpow_ne_flipBit

lemma cycleAt_xBXF_disjoint_image_flipBit {q : Fin (2 ^ (m + 1))} : Disjoint (CycleAt (XBackXForth π) q)
((CycleAt (XBackXForth π) q).image (flipBit 0)) := by
simp_rw [Finset.disjoint_iff_ne, Finset.mem_image, mem_cycleAt_iff]
rintro _ ⟨j, rfl⟩ _ ⟨_, ⟨⟨_, rfl⟩, rfl⟩⟩
exact xBXF_zpow_ne_flipBit_mul_xBXF_zpow


lemma xBXF_eq_xBXF_inv_conj_flipBit : (XBackXForth π) = flipBit 0 * (XBackXForth π)⁻¹ * flipBit 0 := by
rw [← flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit, flipBit_mul_cancel_right]

lemma xBXF_inv_eq_xBXF_conj_flipBit : (XBackXForth π)⁻¹ = flipBit 0 * XBackXForth π * flipBit 0 := by
rw [flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, flipBit_mul_cancel_right]

lemma flipBit_eq_xBXF_mul_flipBit_mul_xBXF : flipBit 0 = (XBackXForth π) * (flipBit 0) *
  (XBackXForth π) := by rw [flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit, inv_mul_cancel_right]

lemma flipBit_eq_xBXF_inv_mul_flipBit_mul_xBXF_inv : flipBit 0 = (XBackXForth π)⁻¹ * (flipBit 0) *
  (XBackXForth π)⁻¹ := by rw [← flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, mul_inv_cancel_right]
-/
/-
lemma xBXF_pow_eq_conj_flipBit_xBXF_pow_inv {k : ℕ} :
(XBackXForth π)^k = (flipBit 0) * ((XBackXForth π)^k)⁻¹ * (flipBit 0) := by
rw [← xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow, flipBit_mul_cancel_right]

lemma xBXF_pow_inv_eq_conj_flipBit_xBXF_pow {k : ℕ} :
((XBackXForth π)^k)⁻¹ = (flipBit 0) * (XBackXForth π)^k * (flipBit 0) := by
rw [flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit, flipBit_mul_cancel_right]


lemma flipBit_eq_xBXF_pow_mul_flipBit_mul_xBXF_pow {k : ℕ} :
flipBit 0 = (XBackXForth π)^k * (flipBit 0) * (XBackXForth π)^k := by
rw [xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow, inv_mul_cancel_right]

lemma flipBit_eq_xBXF_pow_inv_mul_flipBit_mul_xBXF_pow_inv {k : ℕ} :
flipBit 0 = ((XBackXForth π)^k)⁻¹ * (flipBit 0) * ((XBackXForth π)^k)⁻¹ := by
rw [← flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit, mul_inv_cancel_right]
-/
/-
lemma xBXF_zpow_eq_conj_flipBit_xBXF_zpow_inv {k : ℤ} :
(XBackXForth π)^k = (flipBit 0) * ((XBackXForth π)^k)⁻¹ * (flipBit 0) := by
rw [← xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, flipBit_mul_cancel_right]

lemma xBXF_zpow_neg_eq_conj_flipBit_xBXF_zpow {k : ℤ} :
((XBackXForth π)^k)⁻¹ = (flipBit 0) * (XBackXForth π)^k * (flipBit 0) := by
rw [flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit, flipBit_mul_cancel_right]

lemma flipBit_eq_xBXF_zpow_mul_flipBit_mul_xBXF_zpow {k : ℤ} :
flipBit 0 = (XBackXForth π)^k * (flipBit 0) * (XBackXForth π)^k := by
rw [xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, inv_mul_cancel_right]

lemma flipBit_eq_xBXF_zpow_inv_mul_flipBit_mul_xBXF_zpow_inv {k : ℤ} :
flipBit 0 = ((XBackXForth π)^k)⁻¹ * (flipBit 0) * ((XBackXForth π)^k)⁻¹ := by
rw [← flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit, mul_inv_cancel_right]
-/

/-
lemma getBit_cycleMin_not_comm_and_getRes_cycleMin_not_eq_getRes_cycleMin :
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (!b) p)) =
  !(getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 b p))) ∧
  (getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (!b) p)) =
  (getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 b p)))) := by
rw [← eq_flipBit_zero_iff, ← flipBit_mergeBitRes]
exact cycleMin_xBXF_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF

lemma getBit_cycleMin_not_comm :
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (!b) p)) =
  !(getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 b p))) :=
getBit_cycleMin_not_comm_and_getRes_cycleMin_not_eq_getRes_cycleMin.1

lemma getBit_cycleMin_true_eq_not_getBit_cycleMin_false :
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 true p)) =
  !(getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p))) :=
Bool.not_false ▸ getBit_cycleMin_not_comm

lemma getBit_cycleMin_false_eq_not_getBit_cycleMin_true :
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p)) =
  !(getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 true p))) := by
rw [getBit_cycleMin_true_eq_not_getBit_cycleMin_false, Bool.not_not]

lemma getRes_cycleMin_not_eq_getRes_cycleMin :
(getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (!b) p)) =
  (getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 b p))))  :=
getBit_cycleMin_not_comm_and_getRes_cycleMin_not_eq_getRes_cycleMin.2

lemma getRes_cycleMin_true_eq_getRes_cycleMin_false :
(getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (true) p)) =
  (getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p))))  :=
Bool.not_false ▸ getRes_cycleMin_not_eq_getRes_cycleMin

lemma cycleMin_apply_mergeBitRes_zero_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_not :
CycleMin (XBackXForth π) (π (mergeBitRes 0 b p)) =
  (flipBit 0) (CycleMin (XBackXForth π) (π (mergeBitRes 0 (!b) p))) := by
rw [← cycleMin_xBXF_apply_flipBit_zero_eq_flipBit_zero_cycleMin_xBXF_apply, flipBit_mergeBitRes, Bool.not_not]

lemma cycleMin_apply_mergeBitRes_zero_true_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_false :
CycleMin (XBackXForth π) (π (mergeBitRes 0 true p)) =
  (flipBit 0) (CycleMin (XBackXForth π) (π (mergeBitRes 0 false p))) :=
Bool.not_true ▸ cycleMin_apply_mergeBitRes_zero_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_not

lemma cycleMin_apply_mergeBitRes_zero_false_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_true :
CycleMin (XBackXForth π) (π (mergeBitRes 0 false p)) =
  (flipBit 0) (CycleMin (XBackXForth π) (π (mergeBitRes 0 true p))) :=
Bool.not_false ▸ cycleMin_apply_mergeBitRes_zero_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_not
-/

/-
def ControlBitsEquivInductiveControlBits : LayerTupleControlBits m ≃ InductiveControlBits m :=
  match m with
  | 0 => (Equiv.funUnique (Fin 1) _)
  | _ + 1 => (Equiv.piFinSucc _ _).trans (Equiv.prodCongr (Equiv.refl _) (((Equiv.piFinSuccAboveEquiv (fun _ => _)
                (Fin.last _)).trans ((Equiv.prodComm _ _).trans (Equiv.trans (Equiv.prodCongr
                  ((Equiv.arrowCongr (Equiv.refl _) alternControlBits).trans (Equiv.trans
                    (Equiv.arrowProdEquivProdArrow _ _ _)
                      (Equiv.prodCongr ControlBitsEquivInductiveControlBits ControlBitsEquivInductiveControlBits)))
                        (Equiv.refl _)) (Equiv.prodAssoc _ _ _))))))
-/
/-
lemma tiger_tiger (π : Equiv.Perm (Fin (2^1))) : (π 0 = 0 ∧ π 1 = 1) ∨ (π 0 = 1 ∧ π 1 = 0) := by
  simp_rw [pow_one] at π
  rcases Fin.exists_fin_two.mp ⟨π 0, rfl⟩ with (h₀ | h₀) <;>
  rcases Fin.exists_fin_two.mp ⟨π 1, rfl⟩ with (h₁ | h₁)
  · rw [Function.Injective.eq_iff' π.injective h₀] at h₁ ; simp at h₁
  · exact Or.inl ⟨h₀, h₁⟩
  · exact Or.inr ⟨h₀, h₁⟩
  · exact (π.injective.ne (zero_ne_one).symm (h₀ ▸ h₁)).elim

lemma hippo (π : Equiv.Perm (Fin 2)) :
InductiveControlBitsToPerm (PermToInductiveControlBits (m := 0) ((finCongr rfl).permCongr π)) = π := by
  ext q ;
  rcases (mergeBitRes_surj 0 q) with ⟨b, p, rfl⟩
  simp_rw [Fin.eq_zero p]
  simp only [InductiveControlBitsToPerm, resCondFlip, resCondFlipCore, PermToInductiveControlBits, finCongr,
    Fin.castIso_refl, OrderIso.refl_toEquiv, Equiv.Perm.permCongr_eq_mul, Equiv.Perm.refl_mul, Equiv.Perm.refl_inv,
    mul_one, Equiv.coe_fn_mk, getRes_mergeBitRes, flipBit_mergeBitRes]
  cases b
  · simp [LastControlBits, mergeBitRes_apply_false_zero, FirstControl, getBit_resCondFlip,FirstControlBits, Fin.eq_zero]
    simp [getBit_zero]
    rcases tiger_tiger π with (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    simp_rw [h₀, h₁]
    sorry
  · simp [LastControlBits, mergeBitRes_apply_false_zero, FirstControl, getBit_resCondFlip,FirstControlBits, Fin.eq_zero]
    simp [getBit_zero, finFunctionFinEquiv, finTwoEquiv, coe_mergeBitRes_zero]

lemma in_tiger (π : Equiv.Perm (Fin (2 ^ (m + 1)))): InductiveControlBitsToPerm (PermToInductiveControlBits π) = π := by
induction' m with m IH
· exact hippo π
/-
  ext q ;
  rcases (mergeBitRes_surj 0 q) with ⟨b, p, rfl⟩
  simp_rw [Fin.eq_zero p]
  simp_rw [Nat.zero_eq, InductiveControlBitsToPerm, PermToInductiveControlBits, resCondFlip, Nat.pow_zero,
     getBit_resCondFlip, FirstControlBits, resCondFlipCore]
  simp
  cases b
  · simp [LastControlBits, mergeBitRes_apply_false_zero, FirstControl,  getBit_resCondFlip,FirstControlBits, Fin.eq_zero]
    simp [getBit_zero]
    rcases tiger_tiger π with (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    simp_rw [h₀, h₁]
    sorry
  · simp [LastControlBits, mergeBitRes_apply_false_zero, FirstControl, getBit_resCondFlip,FirstControlBits, Fin.eq_zero]
    simp [getBit_zero, finFunctionFinEquiv, finTwoEquiv, coe_mergeBitRes_zero]
    sorry-/
· simp_rw [ InductiveControlBitsToPerm, PermToInductiveControlBits]
  ext ;
  simp [IH]
  simp_rw [FirstControl, ← Equiv.Perm.mul_apply, mul_assoc]
  simp


#check permToBitTuple (m := 2) (Equiv.Refl _)
-/

def myControlBits5 : LayerTupleControlBits 0 := ![![false]]