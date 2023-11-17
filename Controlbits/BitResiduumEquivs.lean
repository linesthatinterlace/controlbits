import Controlbits.BitResiduum


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

def unweavePowTwoTuple (i : Fin (m + 1)) : (Fin (2^(m + 1)) → α) ≃ (Bool → (Fin (2^m) → α)) :=
calc
  _ ≃ _ := Equiv.arrowCongr ((getBitRes i).trans (Equiv.boolProdEquivSum _)) (Equiv.refl _)
  _ ≃ _ := Equiv.sumArrowEquivProdArrow _ _ _
  _ ≃ _ := (Equiv.boolArrowEquivProd _).symm

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
