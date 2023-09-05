import Controlbits.PermFintwo
import Controlbits.BitResiduum
import Controlbits.FoldFin
import Controlbits.Cycles
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Perm.Cycle.Concrete

section ControlBits

def XBackXForth (π : Equiv.Perm (Fin (2^(m + 1)))) := π * (flipBit 0) * π⁻¹ * (flipBit 0)

lemma xBXF_def : XBackXForth π = π * (flipBit 0) * π⁻¹ * (flipBit 0) := rfl

lemma xBXF_apply : (XBackXForth π) q = π ((flipBit 0) (π⁻¹ (flipBit 0 q))) := rfl

lemma xBXF_refl : XBackXForth (Equiv.refl (Fin (2^(m + 1)))) = Equiv.refl _ := by
simp_rw [Equiv.ext_iff, xBXF_apply, Equiv.Perm.refl_inv, Equiv.Perm.one_apply,
  flipBit_flipBit, forall_const]

lemma xBXF_one : XBackXForth (1 : Equiv.Perm (Fin (2^(m + 1)))) = 1 := xBXF_refl

lemma xBXF_base : XBackXForth (m := 0) π = 1 := by
  have h := Fin.perm_fintwo π
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
· simp only [Int.ofNat_eq_coe, zpow_coe_nat, zpow_neg]
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

-- Theorem 4.3 (c)
lemma cycleAt_xBXF_card_le_two_pow {q : Fin (2 ^ (m + 1))} :
  orderOf ((XBackXForth π).cycleOf q) ≤ 2^m := by
rw [cycleAt_card_eq_orderOf_cycleOf]
refine' le_of_mul_le_mul_left _ (zero_lt_two)
rw [two_mul]; nth_rewrite 2 [← Finset.card_image_of_injective _ ((flipBit 0).injective)]
rw [← Nat.pow_succ', ← Finset.card_disjoint_union cycleAt_xBXF_disjoint_image_flipBit]
exact le_of_le_of_eq (Finset.card_le_of_subset (Finset.subset_univ _)) (Finset.card_fin _)

-- Theorem 4.4
lemma cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin :
CycleMin (XBackXForth π) (flipBit 0 q) = (flipBit 0) (CycleMin (XBackXForth π) q) := by
rcases cycleMin_exists_pow_apply (XBackXForth π) q with ⟨j, hjq₂⟩
refine' eq_of_le_of_not_lt _ (fun h => _)
· refine' cycleMin_le (XBackXForth π) (flipBit 0 q)  ⟨-j, _⟩
  simp_rw [zpow_neg, xBXR_zpow_inv_apply_flipBit_eq_flipBit_xBXF_zpow, hjq₂]
· rcases cycleMin_exists_pow_apply (XBackXForth π) (flipBit 0 q) with ⟨k, hkq₂⟩
  rw [←hkq₂, ← hjq₂, xBXF_zpow_apply_flipBit_eq_flipBit_xBXF_zpow_inv, ← zpow_neg] at h
  rcases lt_trichotomy ((XBackXForth π ^ (-k)) q) ((XBackXForth π ^ j) q) with H | H | H
  · exact (cycleMin_le (XBackXForth π) q ⟨-k, rfl⟩).not_lt (hjq₂.symm ▸ H)
  · exact False.elim (lt_irrefl _ (H ▸ h))
  · exact xBXF_zpow_ne_flipBit_mul_xBXF_zpow (eq_flipBit_of_lt_of_flipBit_gt H h)

lemma cycleMin_apply_flipBit_zero_eq_cycleMin_flipBit_zero_apply :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = CycleMin (XBackXForth π) (flipBit 0 (π q)):= by
rw [cycleMin_eq_cycleMin_apply (x := flipBit 0 (π q)),
  xBXF_apply_flipBit_eq_flipBit_xBXF_inv,
  xBXF_inv_apply, Equiv.Perm.inv_apply_self, flipBit_flipBit]

lemma flipBit_zero_cycleMin_apply_eq_cycleMin_apply_flipBit_zero :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = (flipBit 0) (CycleMin (XBackXForth π) (π q)) := by
rw [cycleMin_apply_flipBit_zero_eq_cycleMin_flipBit_zero_apply,
  cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin]

def FirstControlBits (π : Equiv.Perm (Fin (2^(m + 1)))) (p : Fin (2^m)) :=
getBit 0 (FastCycleMin m (XBackXForth π) (mergeBitRes 0 false p))

lemma FirstControlBits_def : FirstControlBits (π : Equiv.Perm (Fin (2^(m + 1)))) p =
getBit 0 (FastCycleMin m (XBackXForth π) (mergeBitRes 0 false p)) := by
rfl

lemma FirstControlBits_apply : FirstControlBits π p = getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p)) := by
rw [FirstControlBits_def, cycleMin_eq_fastCycleMin cycleAt_xBXF_card_le_two_pow]

def FirstControl (π : Equiv.Perm (Fin (2^(m + 1)))) := resCondFlip 0 (FirstControlBits π)

lemma FirstControl_def : FirstControl π = resCondFlip 0 (FirstControlBits π) := rfl

lemma FirstControl_apply : FirstControl π q =
bif getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false (getRes 0 q))) then flipBit 0 q else q := by
rw [FirstControl_def, resCondFlip_apply, FirstControlBits_apply]

-- Theorem 5.2
lemma firstControlBit_false {π : Equiv.Perm (Fin (2^(m + 1)))} : FirstControlBits π 0 = false := by
simp_rw [FirstControlBits_apply,  getBit_zero, mergeBitRes_apply_false_zero, Fin.cycleMin_zero, Fin.val_zero']

-- Theorem 5.3
lemma getBit_zero_firstControl_apply_eq_getBit_zero_cycleMin :
∀ {q}, getBit 0 (FirstControl π q) = getBit 0 (CycleMin (XBackXForth π) q) := by
simp_rw [forall_iff_forall_mergeBitRes 0, FirstControl_def, getBit_resCondFlip', getRes_mergeBitRes,
  getBit_mergeBitRes, Bool.xor_false_right, Bool.xor_true, ← Bool.not_false, ← flipBit_mergeBitRes,
  cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin, getBit_flipBit, FirstControlBits_apply, forall_const]

def LastControlBits (π) (p : Fin (2^m)) :=
getBit 0 ((FirstControl π) (π (mergeBitRes 0 false p)))

lemma LastControlBits_def : LastControlBits π p = getBit 0 ((FirstControl π) (π (mergeBitRes 0 false p))) := rfl

lemma LastControlBits_apply : LastControlBits π p =
getBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false p))) := by
rw [LastControlBits_def, getBit_zero_firstControl_apply_eq_getBit_zero_cycleMin]

def LastControl (π : Equiv.Perm (Fin (2^(m + 1)))) := resCondFlip 0 (LastControlBits π)

lemma LastControl_def : LastControl π = resCondFlip 0 (LastControlBits π) := rfl

lemma LastControl_apply : LastControl π q =
bif getBit 0 (CycleMin (XBackXForth π) (π (mergeBitRes 0 false (getRes 0 q)))) then flipBit 0 q else q := by
simp_rw [LastControl_def, resCondFlip_apply, LastControlBits_apply]

def MiddlePerm (π : Equiv.Perm (Fin (2^(m + 1)))) := (FirstControl π) * π * (LastControl π)

lemma MiddlePerm_apply : MiddlePerm π q = (FirstControl π) (π (LastControl π q)) := rfl

-- Theorem 5.4
lemma getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply :
getBit 0 (LastControl π q) = getBit 0 (FirstControl π (π q)) := by
simp_rw [LastControl_apply, FirstControl_apply]
rcases mergeBitRes_getRes_cases_flipBit 0 q false with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;>
rcases mergeBitRes_getRes_cases_flipBit 0 (π q) false with (⟨h₃, h₄⟩ | ⟨h₃, h₄⟩)
· simp_rw [h₂, h₄, Bool.cond_eq_ite, apply_ite (f := getBit 0), getBit_flipBit, h₁, h₃]
· simp_rw [h₂, h₄, cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin, Bool.cond_eq_ite,
    apply_ite (f := getBit 0), ← Bool.cond_eq_ite, getBit_flipBit, Bool.cond_not, h₁, h₃, Bool.not_not]
· simp_rw [h₂, h₄, flipBit_zero_cycleMin_apply_eq_cycleMin_apply_flipBit_zero, Bool.cond_eq_ite,
    apply_ite (f := getBit 0), ← Bool.cond_eq_ite, getBit_flipBit, Bool.cond_not, h₁, h₃, Bool.not_not]
· simp_rw [h₂, h₄, cycleMin_apply_flipBit_zero_eq_cycleMin_flipBit_zero_apply, Bool.cond_eq_ite,
    apply_ite (f := getBit 0), getBit_flipBit, h₁, h₃]

-- Theorem 5.5
lemma MiddlePerm_invar (π : Equiv.Perm (Fin (2^((m + 1) + 1)))) : bitInvar 0 (MiddlePerm π) := by
simp_rw [bitInvar_iff_getBit_apply_eq_getBit, MiddlePerm_apply,
  ← getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply, ← Equiv.Perm.mul_apply,
  LastControl_def, resCondFlip_mul_self, Equiv.Perm.one_apply, forall_const]

@[simps]
def permsResOfBitInvar (i : Fin (m + 1)) (π : Equiv.Perm (Fin (2^(m + 1)))) (h : bitInvar i π) (b : Bool) :
Equiv.Perm (Fin (2^m)) where
  toFun p := getRes i (π (mergeBitRes i b p))
  invFun p := getRes i (π.symm (mergeBitRes i b p))
  left_inv p := by simp_rw [mergeBitRes_getRes_apply_mergeBitRes_eq_apply_mergeBitRes h,
    Equiv.symm_apply_apply, getRes_mergeBitRes]
  right_inv p := by simp_rw [mergeBitRes_getRes_apply_mergeBitRes_eq_apply_mergeBitRes (symm_bitInvar_of_bitInvar h),
                  Equiv.apply_symm_apply, getRes_mergeBitRes]

@[simps]
def permsResToBitInvar (i : Fin (m + 1)) (πe : Equiv.Perm (Fin (2^m))) (πo : Equiv.Perm (Fin (2^m))) :
Equiv.Perm (Fin (2^(m + 1))) where
  toFun q := bif getBit i q then mergeBitRes i true (πo (getRes i q)) else mergeBitRes i false (πe (getRes i q))
  invFun q := bif getBit i q then mergeBitRes i true (πo.symm (getRes i q)) else mergeBitRes i false (πe.symm (getRes i q))
  left_inv q := by rcases(getBit i q).dichotomy with (h | h) <;> simp [h]
  right_inv q := by rcases(getBit i q).dichotomy with (h | h) <;> simp [h]

lemma bitInvarPermsResToBitInvar (i : Fin (m + 1)) (πe : Equiv.Perm (Fin (2^m))) (πo : Equiv.Perm (Fin (2^m)))
: bitInvar i (permsResToBitInvar i πe πo) := by
rw [bitInvar_iff_getBit_apply_eq_getBit]
intros q ; rcases (getBit i q).dichotomy with (h | h) <;>
simp only [permsResToBitInvar_apply, h, cond_false, cond_true, getBit_mergeBitRes]

lemma leftInverse_permsResToBitInvar_permsResOfBitInvar {i : Fin (m + 1)} {π : Equiv.Perm (Fin (2^(m + 1)))}
(hπ : bitInvar i π) : permsResToBitInvar i (permsResOfBitInvar i π hπ false) (permsResOfBitInvar i π hπ true) = π := by
  ext q : 1; rcases (getBit i q).dichotomy with (h | h) <;>
  simp_rw [permsResToBitInvar_apply, permsResOfBitInvar_apply, mergeBitRes_getRes_of_getBit_eq h, h] <;>
  exact mergeBitRes_getRes_of_getBit_eq ((getBit_apply_eq_getBit_of_bitInvar hπ (q := q)).symm ▸ h)

lemma rightInverse_permsResToBitInvar_permsResOfBitInvar_false (i : Fin (m + 1)) (πe : Equiv.Perm (Fin (2^m)))
(πo : Equiv.Perm (Fin (2^m))) : permsResOfBitInvar i _ (bitInvarPermsResToBitInvar i πe πo) false = πe := by
simp_rw [Equiv.ext_iff, permsResOfBitInvar, permsResToBitInvar, Equiv.coe_fn_mk, getBit_mergeBitRes,
  cond_false, getRes_mergeBitRes, forall_const]

lemma rightInverse_permsResToBitInvar_permsResOfBitInvar_true (i : Fin (m + 1)) (πe : Equiv.Perm (Fin (2^m)))
(πo : Equiv.Perm (Fin (2^m))) : permsResOfBitInvar i _ (bitInvarPermsResToBitInvar i πe πo) true = πo := by
simp_rw [Equiv.ext_iff, permsResOfBitInvar, permsResToBitInvar, Equiv.coe_fn_mk, getBit_mergeBitRes,
  cond_true, getRes_mergeBitRes, forall_const]

def equivBitInvar (i : Fin (m + 1)) :
{π : Equiv.Perm (Fin (2^(m + 1))) // bitInvar i π} ≃ Equiv.Perm (Fin (2^m)) × Equiv.Perm (Fin (2^m)) where
  toFun π := (permsResOfBitInvar i π.val π.prop false, permsResOfBitInvar i π.val π.prop true)
  invFun := fun (πe, πo) => ⟨permsResToBitInvar i πe πo, bitInvarPermsResToBitInvar i πe πo⟩
  left_inv π := Subtype.eq (leftInverse_permsResToBitInvar_permsResOfBitInvar π.prop)
  right_inv := fun (πe, πo) => by
    simp_rw [rightInverse_permsResToBitInvar_permsResOfBitInvar_false,
    rightInverse_permsResToBitInvar_permsResOfBitInvar_true]

abbrev ControlBitsLayer (m : ℕ) := Fin (2^m) → Bool

def InductiveControlBits : ℕ → Type
  | 0 => ControlBitsLayer 0
  | (m + 1) => (ControlBitsLayer (m + 1) × (ControlBitsLayer (m + 1))) × ((InductiveControlBits m) × (InductiveControlBits m))

@[ext]
lemma inductiveControlBits_zero_ext {a b : InductiveControlBits 0} (h : ∀ x : Fin 1, a x = b x) : a = b := funext h

lemma inductiveControlBits_zero_ext_iff {a b : InductiveControlBits 0} : a = b ↔ ∀ x : Fin 1, a x = b x :=
⟨fun H _ => H ▸ rfl, inductiveControlBits_zero_ext⟩

def indCBitsToPerm (m : ℕ) (cb : InductiveControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
  match m with
  | 0 => resCondFlip 0 cb
  | m + 1 => (resCondFlip 0 cb.fst.fst) *
      ((equivBitInvar 0).symm (cb.snd.map (indCBitsToPerm m) (indCBitsToPerm m))) * (resCondFlip 0 cb.fst.snd)

lemma indCBitsToPerm_zero_def : indCBitsToPerm 0 (cb : InductiveControlBits 0) = resCondFlip 0 cb := rfl

lemma indCBitsToPerm_zero_apply : indCBitsToPerm 0 (cb : InductiveControlBits 0) q = resCondFlip 0 cb q := rfl

@[simp]
lemma indCBitsToPerm_zero_eq_cond_swap : indCBitsToPerm 0 (cb : InductiveControlBits 0) =
bif cb 0 then Equiv.swap 0 1 else 1 := by
  rw [Bool.cond_eq_ite]
  convert Fin.perm_fintwo (indCBitsToPerm 0 cb)
  rw [indCBitsToPerm_zero_apply]
  simp_rw [resCondFlip_apply, getRes_apply_zero, flipBit_fin_one, Equiv.swap_apply_left,
    Bool.cond_eq_ite, ite_eq_left_iff, imp_false, Bool.not_eq_true, Bool.not_eq_false]

lemma indCBitsToPerm_succ_def : indCBitsToPerm (m + 1) (cb : InductiveControlBits (m + 1)) =
(resCondFlip 0 cb.fst.fst) *
  ((equivBitInvar 0).symm (cb.snd.map (indCBitsToPerm m) (indCBitsToPerm m))) * (resCondFlip 0 cb.fst.snd) :=
rfl

def permToIndCBits (m : ℕ) (π : Equiv.Perm (Fin (2^(m + 1)))) : InductiveControlBits m :=
  match m with
  | 0 => LastControlBits π
  | m + 1 => ((FirstControlBits π, LastControlBits π),
      (equivBitInvar 0 ⟨_, MiddlePerm_invar π⟩).map (permToIndCBits m) (permToIndCBits m))

lemma permToIndCBits_zero_def : permToIndCBits 0 π = LastControlBits π := rfl

lemma permToIndCBits_zero_eq : permToIndCBits 0 π = fun _ => decide (π 0 = 1) := by
ext
rw [permToIndCBits_zero_def, LastControlBits_apply, xBXF_base,
  mergeBitRes_false_fin_one_eq_zero, cycleMin_one, getBit_fin_one]

lemma permToIndCBits_succ_def : permToIndCBits (m + 1) π  = ((FirstControlBits π, LastControlBits π),
      (equivBitInvar 0 ⟨_, MiddlePerm_invar π⟩).map (permToIndCBits m) (permToIndCBits m)) := rfl

lemma indToPermLeftInverse (π : Equiv.Perm (Fin (2 ^ (m + 1)))): indCBitsToPerm m (permToIndCBits m π) = π := by
induction' m with m IH
· nth_rewrite 2 [Fin.perm_fintwo π]
  simp_rw [permToIndCBits_zero_eq, indCBitsToPerm_zero_eq_cond_swap, Bool.cond_eq_ite, decide_eq_true_eq]
· simp_rw [indCBitsToPerm_succ_def, permToIndCBits_succ_def, Equiv.ext_iff, Nat.add_eq, Nat.add_zero,
    Prod_map, IH, Equiv.Perm.coe_mul, Function.comp_apply, Prod.eta, Equiv.symm_apply_apply,
    MiddlePerm_apply, FirstControl_def,
    LastControl_def, resCondFlip_resCondFlip, forall_const]

def weaveControlBits :  ControlBitsLayer (m + 1) ≃ (ControlBitsLayer m × ControlBitsLayer m) :=
calc
  _ ≃ ((Bool × Fin (2^m)) → Bool) := Equiv.arrowCongr (getBitRes 0) (Equiv.refl _)
  _ ≃ (Fin (2^m) ⊕ Fin (2^m) → Bool) := Equiv.arrowCongr (Equiv.boolProdEquivSum _) (Equiv.refl _)
  _ ≃ _ := (Equiv.sumArrowEquivProdArrow _ _ _)

abbrev LayerTupleControlBits (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

abbrev BitTupleControlBits (m : ℕ) := Fin ((2*m + 1)*(2^m)) → Bool

abbrev PairPairsControlBits (m : ℕ) :=
((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (LayerTupleControlBits m × LayerTupleControlBits m))

def bitTupleEquivLayerTuple : BitTupleControlBits m ≃ LayerTupleControlBits m :=
calc
  _ ≃ ((Fin (2*m + 1) × Fin (2^m)) → Bool) := Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl _)
  _ ≃ _ := Equiv.curry _ _ _

def layerTupleSuccEquivPairPairs : LayerTupleControlBits (m + 1) ≃ PairPairsControlBits m :=
calc
  _ ≃ _ := (Equiv.piFinSucc _ _)
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (calc
                                            _ ≃ _ := (finCongr (mul_add 2 m 1)).arrowCongr (Equiv.refl _)
                                            _ ≃ _ := Equiv.piFinSuccAboveEquiv (fun _ => _) (Fin.last _))
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (calc
                                            _ ≃ _ := Equiv.arrowCongr (Equiv.refl _)
                                              (calc
                                                _ ≃ _ := Equiv.arrowCongr (getBitRes 0) (Equiv.refl _)
                                                _ ≃ _ := Equiv.arrowCongr (Equiv.boolProdEquivSum _) (Equiv.refl _)
                                                _ ≃ _ := (Equiv.sumArrowEquivProdArrow _ _ _))
                                            _ ≃ _ := Equiv.arrowProdEquivProdArrow _ _ _)

def layerTupleEquivInductive : LayerTupleControlBits m ≃ InductiveControlBits m :=
  match m with
  | 0 => (Equiv.funUnique (Fin 1) _)
  | (_ + 1) => calc
                _ ≃ _ := layerTupleSuccEquivPairPairs
                _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr layerTupleEquivInductive layerTupleEquivInductive)

def bitTupleEquivInductive : BitTupleControlBits m ≃ InductiveControlBits m :=
bitTupleEquivLayerTuple.trans layerTupleEquivInductive

def permToLayerTuple (π : Equiv.Perm (Fin (2^(m + 1)))) : LayerTupleControlBits m :=
layerTupleEquivInductive.symm (permToIndCBits m π)

def permToBitTuple (π : Equiv.Perm (Fin (2^(m + 1)))) : BitTupleControlBits m :=
bitTupleEquivInductive.symm (permToIndCBits m π)

def layerTupleToPerm (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
indCBitsToPerm m (layerTupleEquivInductive cb)

def bitTupleToPerm (cb : BitTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
indCBitsToPerm m (bitTupleEquivInductive cb)

def layerTupleToPerm' (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => resCondFlip (foldFin k) (cb k))).prod

def bitTupleToPerm' (cb : BitTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => resCondFlip (foldFin k) (bitTupleEquivLayerTuple cb k))).prod


def splitFirstLast : (Fin (2*(n + 1) + 1) → α) ≃ α × (Fin (2*n + 1) → α) × α :=
calc
  _ ≃ _ := Equiv.piFinSucc _ _
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (calc
                                            _ ≃ _ := (finCongr (mul_add 2 n 1)).arrowCongr (Equiv.refl _)
                                            _ ≃ _ := Equiv.piFinSuccAboveEquiv (fun _ => _) (Fin.last _)
                                            _ ≃ _ := Equiv.prodComm _ _)

example (n : ℕ) : n < n.succ := by exact Nat.lt.base n

def partialLayerTupleToPerm (m : ℕ) (n : ℕ) (h : n < m + 1) (cb : Fin (2*n + 1) → ControlBitsLayer m) : Equiv.Perm (Fin (2^(m + 1))) :=
match n with
| 0 => resCondFlip ⟨m, m.lt_succ_self⟩ (cb 0)
| (k + 1) =>  match splitFirstLast cb with
              | ⟨a, ⟨b, c⟩⟩ => (resCondFlip (m - (k + 1))  a) *
                (partialLayerTupleToPerm m k (lt_trans k.lt_succ_self h) b) *
                (resCondFlip (m - (k + 1)) c)

def partialLayerTupleToPerm' (m : ℕ) (cb : LayerTupleControlBits m) (n : ℕ) (h : n < m + 1) : Equiv.Perm (Fin (2^(m + 1))) :=
match n with
| 0 => resCondFlip (m - 0) (cb (m - 0))
| (k + 1) =>  (resCondFlip (m - (k + 1)) (cb (m - (k + 1)))) *
                (partialLayerTupleToPerm' m cb k (lt_trans k.lt_succ_self h)) *
                (resCondFlip (m - (k + 1)) (cb (m + (k + 1))))


def layerTupleToPerm'' (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
partialLayerTupleToPerm m m m.lt_succ_self cb

def layerTupleToPerm''' (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
partialLayerTupleToPerm' m cb m m.lt_succ_self

end ControlBits


-- Testing


def myControlBits69 := (![true, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false] : BitTupleControlBits 2)


def myControlBits1 : LayerTupleControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def myControlBits2 : LayerTupleControlBits 1 := ![![false, true], ![false, true], ![true, true]]
def myControlBits2a : BitTupleControlBits 1 := ![false, true, false, true, true, true]
def myControlBits3 : LayerTupleControlBits 0 := ![![true]]
def myControlBits4 : LayerTupleControlBits 0 := ![![false]]

#eval [0, 1, 2, 3].map (layerTupleToPerm (myControlBits2))
#eval [0, 1, 2, 3].map (layerTupleToPerm' (myControlBits2))
#eval [0, 1, 2, 3].map (layerTupleToPerm'' (myControlBits2))
#eval [0, 1, 2, 3].map (layerTupleToPerm''' (myControlBits2))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (bitTupleToPerm (m := 2) (myControlBits69))
/-
#eval bitTupleToPerm <| permToBitTuple (m := 4) (Equiv.refl _)
#eval permToLayerTuple <| (layerTupleToPerm (myControlBits1))
#eval permToLayerTuple <| (layerTupleToPerm' (myControlBits1))
#eval permToBitTuple <| (layerTupleToPerm (myControlBits1))


#eval [0, 1, 2, 3, 4, 5, 6, 7].map (bitTupleToPerm (m := 2) (myControlBits69))
-/


-- HELL
/-
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
exact cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin

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
rw [← flipBit_zero_cycleMin_apply_eq_cycleMin_apply_flipBit_zero, flipBit_mergeBitRes, Bool.not_not]

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