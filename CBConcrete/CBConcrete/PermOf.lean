import CBConcrete.Lib.MulAction
import CBConcrete.Lib.Vector
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Congruence.Basic

namespace Equiv.Perm

def NatSepAt (n : ℕ) : Subgroup (Perm ℕ) where
  carrier e := ∀ i, i < n → e i < n
  mul_mem' {a} {b} ha hb i hi := ha _ (hb _ hi)
  one_mem' i hi := by simp_rw [Perm.coe_one, id_eq, hi]
  inv_mem' {e} he i hi := by
    have hfi : Function.Injective (fun (i : Fin n) => (⟨e i, he _ i.isLt⟩ : Fin n)) :=
      fun _ _ h => Fin.eq_of_val_eq (e.injective (Fin.val_eq_of_eq h))
    have hfs := hfi.surjective_of_fintype (Equiv.refl _)
    rcases hfs ⟨i, hi⟩ with ⟨j, hj⟩
    exact j.isLt.trans_eq' (inv_eq_iff_eq.mpr (Fin.val_eq_of_eq hj).symm)

section NatSepAt

variable {e : Perm ℕ} {n m : ℕ}

theorem mem_NatSepAt_iff : e ∈ NatSepAt n ↔ ∀ i, i < n → e i < n := Iff.rfl

theorem apply_lt_of_lt_of_mem_NatSepAt (he : e ∈ NatSepAt n) :
  ∀ i, i < n → e i < n := mem_NatSepAt_iff.mp he

theorem mem_NatSepAt_iff' : e ∈ NatSepAt n ↔ ∀ i, n ≤ i → n ≤ e i :=
  ⟨fun he _ => le_imp_le_of_lt_imp_lt fun hi =>
    (((Subgroup.inv_mem_iff _).mpr he) _ hi).trans_eq' (e.inv_apply_self _).symm,
    fun he => (Subgroup.inv_mem_iff _).mp fun _ => lt_imp_lt_of_le_imp_le fun hi =>
    (he _ hi).trans_eq (e.apply_inv_self _)⟩

theorem apply_le_of_le_of_mem_NatSepAt (he : e ∈ NatSepAt n) :
  ∀ i, n ≤ i → n ≤ e i := mem_NatSepAt_iff'.mp he

end NatSepAt

def NatFixGE (n : ℕ) : Subgroup (Perm ℕ) where
  carrier e := ∀ i, n ≤ i → e i = i
  mul_mem' {a} {b} ha hb i hi := (ha (b i) ((hb i hi).symm ▸ hi)).trans (hb i hi)
  one_mem' i hi := by simp_rw [Perm.coe_one, id_eq]
  inv_mem' {a} ha i hi := EquivLike.inv_apply_eq_iff_eq_apply.mpr (ha i hi).symm

section NatFixGE

variable {e : Perm ℕ} {n m : ℕ}

@[simp] theorem mem_natFixGE_iff : e ∈ NatFixGE n ↔ ∀ i, n ≤ i → e i = i := Iff.rfl

theorem fixed_ge_of_mem_natFixGE {e : Perm ℕ} (he : e ∈ NatFixGE n) :
  ∀ i, n ≤ i → e i = i := mem_natFixGE_iff.mp he

theorem natFixGE_le_natSepAt : NatFixGE n ≤ NatSepAt n := by
  simp_rw [SetLike.le_def, mem_NatSepAt_iff']
  exact fun e he _ => fun hi => hi.trans_eq (he _ hi).symm

instance normal_natFixGE_subGroupOf_natSepAt :
    Subgroup.Normal ((NatFixGE n).subgroupOf (NatSepAt n)) where
  conj_mem := by
    simp_rw [Subtype.forall, MulMemClass.mk_mul_mk, Subgroup.mem_subgroupOf, mem_natFixGE_iff,
      Subgroup.coe_mul, InvMemClass.coe_inv, mul_apply]
    intro _ _ he _ hp _ hi
    simp_rw [he _ (apply_le_of_le_of_mem_NatSepAt (Subgroup.inv_mem _ hp) _ hi), apply_inv_self]

theorem apply_lt_of_lt_of_mem_natFixGE {e : Perm ℕ} (he : e ∈ NatFixGE n) :
    ∀ i, i < n → e i < n := natFixGE_le_natSepAt he

theorem natFixGE_mono (hnm : n ≤ m) : NatFixGE n ≤ NatFixGE m := by
  simp_rw [SetLike.le_def, mem_natFixGE_iff]
  exact fun _ H _ h => H _ (hnm.trans h)

theorem natFixGE_le_natSepAt_of_le (hnm : n ≤ m) : NatFixGE n ≤ NatSepAt m :=
  (natFixGE_mono hnm).trans natFixGE_le_natSepAt

theorem directed_natFixGE : Directed (· ≤ ·) (NatFixGE) := fun _ _ =>
  ⟨_, natFixGE_mono (le_max_left _ _), natFixGE_mono (le_max_right _ _)⟩

end NatFixGE

def NatFixLT (n : ℕ) : Subgroup (Perm ℕ) where
  carrier e := ∀ i, i < n → e i = i
  mul_mem' {a} {b} ha hb i hi := (ha (b i) ((hb i hi).symm ▸ hi)).trans (hb i hi)
  one_mem' i hi := by simp_rw [Perm.coe_one, id_eq]
  inv_mem' {a} ha i hi := EquivLike.inv_apply_eq_iff_eq_apply.mpr (ha i hi).symm

section NatFixLT

variable {e : Perm ℕ} {n m : ℕ}

@[simp] theorem mem_natFixLT_iff : e ∈ NatFixLT n ↔ ∀ i, i < n → e i = i := Iff.rfl

theorem fixed_lt_of_mem_natFixLT {e : Perm ℕ} (he : e ∈ NatFixLT n) :
  ∀ i, i < n → e i = i := mem_natFixLT_iff.mp he

theorem natFixLT_le_natSepAt : NatFixLT n ≤ NatSepAt n := by
  simp_rw [SetLike.le_def, mem_NatSepAt_iff]
  exact fun e he _ => fun hi => hi.trans_eq' (he _ hi)

instance normal_natFixLT_subGroupOf_natSepAt :
    Subgroup.Normal ((NatFixLT n).subgroupOf (NatSepAt n)) where
  conj_mem := by
    simp_rw [Subtype.forall, MulMemClass.mk_mul_mk, Subgroup.mem_subgroupOf, mem_natFixLT_iff,
      Subgroup.coe_mul, InvMemClass.coe_inv, mul_apply]
    intro _ _ he _ hp _ hi
    simp_rw [he _ (apply_lt_of_lt_of_mem_NatSepAt (Subgroup.inv_mem _ hp) _ hi), apply_inv_self]

theorem apply_lt_of_lt_of_mem_natFixLT {e : Perm ℕ} (he : e ∈ NatFixLT n) :
    ∀ i, i < n → e i < n := natFixLT_le_natSepAt he

theorem natFixLT_anti (hmn : m ≤ n) : NatFixLT n ≤ NatFixLT m := by
  simp_rw [SetLike.le_def, mem_natFixLT_iff]
  exact fun _ H _ h => H _ (h.trans_le hmn)

theorem natFixLT_le_natSepAt_of_le (hmn : m ≤ n) : NatFixLT n ≤ NatSepAt m :=
  (natFixLT_anti hmn).trans natFixLT_le_natSepAt

theorem directed_natFixLT : Directed (· ≥ ·) (NatFixLT) := fun _ _ =>
  ⟨_, natFixLT_anti (le_max_left _ _), natFixLT_anti (le_max_right _ _)⟩

theorem disjoint_natFixLT_natFixGE : Disjoint (NatFixLT n) (NatFixGE n) := by
  simp_rw [Subgroup.disjoint_def, mem_natFixLT_iff, mem_natFixGE_iff, Equiv.ext_iff, one_apply]
  exact fun hel heg i => (lt_or_le i n).elim (hel _) (heg _)

theorem eq_one_of_mem_natFixLT_natFixGE {e : Perm ℕ} (he : e ∈ NatFixLT n) (he' : e ∈ NatFixGE n) :
    e = 1 := by
  revert e
  simp_rw [← Subgroup.disjoint_def]
  exact disjoint_natFixLT_natFixGE

theorem natFixLT_natFixGE_commute {e p : Perm ℕ} (he : e ∈ NatFixLT n) (hp : p ∈ NatFixGE n) :
    Commute e p := by
  have H := Subgroup.commute_of_normal_of_disjoint _ _
    normal_natFixLT_subGroupOf_natSepAt (normal_natFixGE_subGroupOf_natSepAt (n := n))
  simp_rw [Subgroup.disjoint_def, Subtype.forall,  Subgroup.mem_subgroupOf, commute_iff_eq,
    MulMemClass.mk_mul_mk, Subtype.mk.injEq, Subgroup.mk_eq_one] at H
  exact H (fun _ _ => eq_one_of_mem_natFixLT_natFixGE) _ (natFixLT_le_natSepAt he) _
    (natFixGE_le_natSepAt hp) he hp

end NatFixLT

def NatFinitePerm : Subgroup (Perm ℕ) := ⨆ (n : ℕ), NatFixGE n

section NatFinitePerm

variable {e : Perm ℕ} {n : ℕ}

open scoped Classical

@[simp] theorem mem_natFinitePerm_iff : e ∈ NatFinitePerm ↔ ∃ n, e ∈ NatFixGE n :=
  Subgroup.mem_iSup_of_directed directed_natFixGE

theorem exists_mem_natFixGE_of_mem_natFinitePerm (he : e ∈ NatFinitePerm) :
    ∃ n, e ∈ NatFixGE n := mem_natFinitePerm_iff.mp he

theorem exists_mem_natSepAt_of_mem_natFinitePerm (he : e ∈ NatFinitePerm) :
    ∃ n, e ∈ NatSepAt n :=
  ⟨_, natFixGE_le_natSepAt ((exists_mem_natFixGE_of_mem_natFinitePerm he).choose_spec)⟩

theorem natFixGE_le_natFinitePerm :
    NatFixGE n ≤ NatFinitePerm := fun _ he => mem_natFinitePerm_iff.mpr ⟨_, he⟩

noncomputable def blahj (e : NatFinitePerm) :
  NatFixGE (exists_mem_natFixGE_of_mem_natFinitePerm e.2).choose :=
  ⟨_, (exists_mem_natFixGE_of_mem_natFinitePerm e.2).choose_spec⟩

theorem mem_natFinitePerm_of_mem_natFixGE (he : e ∈ NatFixGE n) :
    e ∈ NatFinitePerm := natFixGE_le_natFinitePerm he

@[simp] theorem mem_natFinitePerm_iff_exists_fixed_ge :
    e ∈ NatFinitePerm ↔ ∃ n, ∀ i, n ≤ i → e i = i :=
  (Subgroup.mem_iSup_of_directed directed_natFixGE).trans <|
  exists_congr (fun _ => mem_natFixGE_iff)

theorem exists_fixed_ge_of_mem_natFinitePerm {e : Perm ℕ} (he : e ∈ NatFinitePerm) :
  ∃ n, ∀ i, n ≤ i → e i = i := exists_mem_natFixGE_of_mem_natFinitePerm he

theorem exists_apply_lt_of_lt_of_mem_natFinitePerm {e : Perm ℕ} (he : e ∈ NatFinitePerm) :
    ∃ n, ∀ i, i < n → e i < n := exists_mem_natSepAt_of_mem_natFinitePerm he

end NatFinitePerm

end Equiv.Perm

/--
A `PermOf n` is a permutation on `n` elements represented by two vectors, which we can
think of as an array of values and a corresponding array of indexes which are inverse to
one another. (One can flip the interpretation of indexes and values, and this is essentially
the inversion operation.)
It is designed to be a more performant version of `Equiv.Perm`.
-/
structure PermOf (n : ℕ) where
  /--
  Gives the `PermOf` as an vector of size `n`.
  -/
  protected fwdVector : Vector ℕ n
  /--
  Gives the inverse of the `PermOf` as a vector of size `n`.
  -/
  protected bwdVector : Vector ℕ n
  getElem_fwdVector_lt :
    ∀ {i : ℕ} (hi : i < n), fwdVector[i] < n := by decide
  getElem_bwdVector_getElem_fwdVector : ∀ {i : ℕ} (hi : i < n),
      bwdVector[fwdVector[i]]'(getElem_fwdVector_lt hi) = i := by decide
  deriving DecidableEq

namespace PermOf

open Function Equiv

variable {n m : ℕ}

section GetElemVectorBijective

theorem getElem_fwdVector_injective (a : PermOf n) :
  ∀ {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n), a.fwdVector[i] = a.fwdVector[j] → i = j :=
  fun hi _ hj hij => (a.getElem_bwdVector_getElem_fwdVector hi).symm.trans
    (Eq.trans (by simp_rw [hij]) (a.getElem_bwdVector_getElem_fwdVector hj))


theorem getElem_fwdVector_surjective (a : PermOf n) :
    ∀ {i : ℕ}, i < n → ∃ (j : ℕ), ∃ (hj : j < n), a.fwdVector[j] = i := by
  have H : Surjective (fun (i : Fin n) => Fin.mk a.fwdVector[i.1] (a.getElem_fwdVector_lt i.2)) :=
    Injective.surjective_of_fintype (Equiv.refl (Fin n)) fun _ _ => by
    simp_rw [Fin.mk.injEq, Fin.ext_iff]
    exact a.getElem_fwdVector_injective _ _
  unfold Surjective at H
  simp_rw [Fin.ext_iff, Fin.forall_iff, Fin.exists_iff] at H
  exact H

theorem getElem_bwdVector_lt (a : PermOf n) {i : ℕ} (hi : i < n) : a.bwdVector[i] < n := by
  rcases a.getElem_fwdVector_surjective hi with ⟨j, hj, rfl⟩
  simp_rw [a.getElem_bwdVector_getElem_fwdVector, hj]

theorem getElem_fwdVector_getElem_bwdVector (a : PermOf n) {i : ℕ} (hi : i < n) :
    a.fwdVector[a.bwdVector[i]]'(a.getElem_bwdVector_lt hi) = i := by
  rcases a.getElem_fwdVector_surjective hi with ⟨j, hj, rfl⟩
  simp_rw [a.getElem_bwdVector_getElem_fwdVector]

theorem getElem_bwdVector_injective (a : PermOf n) :
  ∀ {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n), a.bwdVector[i] = a.bwdVector[j] → i = j :=
  fun hi _ hj hij => (a.getElem_fwdVector_getElem_bwdVector hi).symm.trans
    (Eq.trans (by simp_rw [hij]) (a.getElem_fwdVector_getElem_bwdVector hj))

theorem getElem_bwdVector_surjective (a : PermOf n) :
    ∀ {i : ℕ}, i < n → ∃ (j : ℕ), ∃ (hj : j < n), a.bwdVector[j] = i := by
  have H : Surjective (fun (i : Fin n) => Fin.mk a.bwdVector[i.1] (a.getElem_bwdVector_lt i.2)) :=
    Injective.surjective_of_fintype (Equiv.refl (Fin n)) fun _ _ => by
    simp_rw [Fin.mk.injEq, Fin.ext_iff]
    exact a.getElem_bwdVector_injective _ _
  unfold Surjective at H
  simp_rw [Fin.ext_iff, Fin.forall_iff, Fin.exists_iff] at H
  exact H

end GetElemVectorBijective

protected def mk' (fwdVector : Vector ℕ n) (bwdVector : Vector ℕ n)
    (getElem_bwdVector_lt : ∀ {i : ℕ} (hi : i < n), bwdVector[i] < n)
    (getElem_fwdVector_getElem_bwdVector : ∀ {i : ℕ} (hi : i < n),
    fwdVector[bwdVector[i]]'(getElem_bwdVector_lt hi) = i) :
  PermOf n :=
  let A : PermOf n := ⟨bwdVector, fwdVector,
    getElem_bwdVector_lt, getElem_fwdVector_getElem_bwdVector⟩
  ⟨fwdVector, bwdVector,
    A.getElem_bwdVector_lt, A.getElem_fwdVector_getElem_bwdVector⟩

section Mk'

@[simp] theorem mk'_fwdVector (a b : Vector ℕ n) {ha hab} :
    (PermOf.mk' a b ha hab).fwdVector = a := rfl

@[simp] theorem mk'_bwdVector (a b : Vector ℕ n) {ha hab} :
    (PermOf.mk' a b ha hab).bwdVector = b := rfl

end Mk'

instance : Repr (PermOf n) where
  reprPrec a _ :=
  if n = 0 then
    "#v[]" else
    Std.Format.bracketFill
    "#v[" (Std.Format.joinSep (a.fwdVector.toList) ("," ++ Std.Format.line)) "]"

instance : One (PermOf n) where
  one := PermOf.mk (Vector.range n) (Vector.range n)
    (fun _ => Vector.getElem_range_lt _) (fun _ => by simp_rw [Vector.getElem_range])

section One

instance : Inhabited (PermOf n) := ⟨1⟩

@[simp]
theorem default_eq : (default : PermOf n) = 1 := rfl

end One

instance : Inv (PermOf n) where
  inv a := PermOf.mk' a.bwdVector a.fwdVector
    a.getElem_fwdVector_lt a.getElem_bwdVector_getElem_fwdVector

section Inv

@[simp] theorem inv_fwdVector (a : PermOf n) : a⁻¹.fwdVector = a.bwdVector := rfl
@[simp] theorem inv_bwdVector (a : PermOf n) : a⁻¹.bwdVector = a.fwdVector := rfl

end Inv

instance : GetElem (PermOf n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.fwdVector[i]

section GetElem

@[simp]
theorem getElem_lt (a : PermOf n) {i : ℕ} (hi : i < n := by get_elem_tactic) : a[i] < n :=
  a.getElem_fwdVector_lt hi

@[simp]
theorem getElem_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_mk' (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk' a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_fwdVector (a : PermOf n)  {i : ℕ} (hi : i < n) : a.fwdVector[i] = a[i] := rfl

theorem fwdVector_eq_iff_forall_getElem_eq (a b : PermOf n) :
    a.fwdVector = b.fwdVector ↔ ∀ {i} (hi : i < n), a[i] = b[i] := by
  simp_rw [Vector.ext_iff, getElem_fwdVector]

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : PermOf n)[i] = i := Vector.getElem_range _ _

section GetElemBijective

theorem getElem_injective (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n)
    (hij : a[i] = a[j]) : i = j := a.getElem_fwdVector_injective hi hj hij

@[simp] theorem getElem_inj (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (a : PermOf n) {i : ℕ} (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i := a.getElem_fwdVector_surjective hi

end GetElemBijective


section GetElemInv

@[simp]
theorem getElem_inv_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_inv_mk' (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk' a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_bwdVector (a : PermOf n)  {i : ℕ} (hi : i < n) :
  a.bwdVector[i] = a⁻¹[i] := rfl

theorem bwdVector_eq_iff_forall_getElem_eq (a b : PermOf n) :
    a.bwdVector = b.bwdVector ↔ ∀ {i} (hi : i < n), a⁻¹[i] = b⁻¹[i] := by
  simp_rw [Vector.ext_iff, getElem_bwdVector]

@[simp]
theorem getElem_inv_getElem (a : PermOf n) {i : ℕ} (hi : i < n) :
    a⁻¹[a[i]] = i := a.getElem_bwdVector_getElem_fwdVector hi

@[simp]
theorem getElem_getElem_inv (a : PermOf n) {i : ℕ} (hi : i < n) :
  a[a⁻¹[i]] = i := (a⁻¹).getElem_bwdVector_getElem_fwdVector hi

theorem eq_getElem_inv_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by
  rw [← (a⁻¹).getElem_inj (a.getElem_lt) hj, getElem_inv_getElem]

theorem self_eq_getElem_inv_iff (a : PermOf n) {i : ℕ} (hi : i < n) : i = a⁻¹[i] ↔ a[i] = i := by
  rw [← (a⁻¹).getElem_inj (a.getElem_lt) hi, getElem_inv_getElem]

theorem getElem_inv_eq_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by
  rw [← a.getElem_inj (a⁻¹.getElem_lt) hj, getElem_getElem_inv]

theorem getElem_inv_eq_self_iff (a : PermOf n) {i : ℕ} (hi : i < n) :
    a⁻¹[i] = i ↔ i = a[i] := by
  rw [← a.getElem_inj (a⁻¹.getElem_lt) hi, getElem_getElem_inv]

theorem ne_getElem_inv_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := (a.eq_getElem_inv_iff _ _).ne

theorem self_ne_getElem_inv_iff (a : PermOf n) {i : ℕ} (hi : i < n) :
    i ≠ a⁻¹[i] ↔ a[i] ≠ i := (a.eq_getElem_inv_iff _ _).ne

theorem getElem_inv_ne_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := (a.getElem_inv_eq_iff _ _).ne

theorem getElem_inv_ne_self_iff (a : PermOf n) {i : ℕ} (hi : i < n):
    a⁻¹[i] ≠ i ↔ i ≠ a[i] := (a.getElem_inv_eq_iff _ _).ne

end GetElemInv

@[ext]
theorem ext {a b : PermOf n} (h : ∀ {i : ℕ} (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.fwdVector = b.fwdVector ∧ a.bwdVector = b.bwdVector by
    · rcases a ; rcases b ; simp_rw [mk.injEq]
      exact h
  simp_rw [fwdVector_eq_iff_forall_getElem_eq, bwdVector_eq_iff_forall_getElem_eq,
    a.getElem_inv_eq_iff _ (b⁻¹.getElem_lt _), h, getElem_getElem_inv, implies_true, and_self]

end GetElem

instance : Mul (PermOf n) where
  mul a b := {
    fwdVector := Vector.ofFn (fun i => a[b[i.1]])
    bwdVector := Vector.ofFn (fun i => b⁻¹[a⁻¹[i.1]])
    getElem_fwdVector_lt := fun {i} hi => by
      simp_rw [Vector.getElem_ofFn, getElem_lt]
    getElem_bwdVector_getElem_fwdVector := fun {i} hi => by
      simp_rw [Vector.getElem_ofFn, getElem_inv_getElem]}

@[simp]
theorem getElem_mul (a b : PermOf n) {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]] := Vector.getElem_ofFn _ _ _

instance : Subsingleton (PermOf 0) where
  allEq a b := by simp_rw [PermOf.ext_iff, not_lt_zero', IsEmpty.forall_iff, implies_true]

instance : Subsingleton (PermOf 1) where
  allEq a b := by
    simp_rw [PermOf.ext_iff]
    intro _ hi
    have ha := a.getElem_lt (hi := hi)
    have hb := b.getElem_lt (hi := hi)
    rw [Nat.lt_one_iff] at ha hb
    exact ha.trans hb.symm

instance : Unique (PermOf 0) := Unique.mk' _
instance : Unique (PermOf 1) := Unique.mk' _

instance : Finite (PermOf n) := Finite.of_injective
  (fun a => (fun (i : Fin n) => (⟨a[i.1], a.getElem_lt⟩ : Fin n))) <| fun a b => by
    simp only [Prod.mk.injEq, and_imp, funext_iff, Fin.forall_iff, Fin.ext_iff]
    exact ext

instance : Group (PermOf n) := Group.ofLeftAxioms
  (fun _ _ _ => ext <| fun hi => by simp_rw [getElem_mul])
  (fun _ => ext <| fun hi => by simp_rw [getElem_mul, getElem_one])
  (fun _ => ext <| fun hi => by simp_rw [getElem_mul, getElem_one, getElem_inv_getElem])

section Group

theorem getElem_pow_eq_self_of_getElem_eq_self {a : PermOf n} {i k : ℕ} {hi : i < n}
  (hia : a[i] = i) : (a^k)[i] = i := by
  induction k with | zero => _ | succ k IH => _
  · simp_rw [pow_zero, getElem_one]
  · simp_rw [pow_succ, getElem_mul, hia, IH]

theorem getElem_inv_eq_self_of_getElem_eq_self {a : PermOf n} {i : ℕ} {hi : i < n} :
  a[i] = i → (a⁻¹)[i] = i := by simp_rw [getElem_inv_eq_self_iff, eq_comm, imp_self]

theorem getElem_inv_ne_self_of_getElem_ne_self {a : PermOf n} {i : ℕ} {hi : i < n} :
  a[i] ≠ i → (a⁻¹)[i] ≠ i := by simp_rw [ne_eq, getElem_inv_eq_self_iff, eq_comm, imp_self]

theorem getElem_zpow_eq_self_of_getElem_eq_self {a : PermOf n} {k : ℤ} {i : ℕ} {hi : i < n}
    (hia : a[i] = i) : (a^k)[i] = i := by
  cases k
  · exact getElem_pow_eq_self_of_getElem_eq_self hia
  · simp_rw [zpow_negSucc]
    exact (getElem_inv_eq_self_of_getElem_eq_self (getElem_pow_eq_self_of_getElem_eq_self hia))

@[simp]
theorem getElem_pow_add (a : PermOf n) {i x y : ℕ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [pow_add, getElem_mul]

@[simp]
theorem getElem_zpow_add (a : PermOf n) {i : ℕ} {x y : ℤ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [zpow_add, getElem_mul]

lemma isOfFinOrder (a : PermOf n) : IsOfFinOrder a := isOfFinOrder_of_finite _

lemma orderOf_pos (a : PermOf n) : 0 < orderOf a := by
  rw [orderOf_pos_iff]
  exact a.isOfFinOrder

end Group


@[irreducible] def SetAt (a : PermOf n) (m : ℕ) : Prop :=
    ∀ {i : ℕ}, i < m → ∀ {hi : i < n}, a[i] < m

section SetAt

variable {a : PermOf n} {i m : ℕ}

theorem setAt_def :
    a.SetAt m ↔ ∀ {i : ℕ}, i < m → ∀ {hi : i < n}, a[i] < m := by
  unfold SetAt
  exact Iff.rfl

theorem SetAt.getElem_lt_of_lt (him : i < m) (ha : a.SetAt m)
    (hin : i < n := by get_elem_tactic) : a[i] < m := by
  unfold SetAt at ha
  exact ha him

theorem setAt_of_lt_imp_getElem_lt (ha : ∀ {i}, i < m → ∀ {hi : i < n}, a[i] < m) : a.SetAt m := by
  unfold SetAt
  exact ha

theorem setAt_eq : ∀ (a : PermOf n), a.SetAt n :=
  fun a => setAt_of_lt_imp_getElem_lt (fun _ => a.getElem_lt)

theorem setAt_ge (hnm : n ≤ m) : ∀ (a : PermOf n), a.SetAt m :=
  fun a => setAt_of_lt_imp_getElem_lt (fun _ => a.getElem_lt.trans_le hnm)

theorem setAt_succ : a.SetAt (n + 1) := a.setAt_ge (Nat.le_succ _)

theorem SetAt.getElem_eq_self {a : PermOf (n + 1)} (ha : a.SetAt n) : a[n] = n := by
  rcases a.getElem_surjective (Nat.lt_succ_self _) with ⟨k, hk, hkn⟩
  simp_rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at hk
  rcases hk with hk | rfl
  · exact ((ha.getElem_lt_of_lt hk).ne hkn).elim
  · exact hkn

theorem setAt_of_getElem_eq_self {a : PermOf (n + 1)} (ha : a[n] = n) : a.SetAt n :=
  setAt_of_lt_imp_getElem_lt (fun {i} hi =>
    (Nat.le_of_lt_succ a.getElem_lt).lt_or_eq.elim id
    (fun h => (hi.ne (a.getElem_injective _ _ (h.trans ha.symm))).elim))

theorem setAt_iff_getElem_eq_self {a : PermOf (n + 1)} : a.SetAt n ↔ a[n] = n :=
    ⟨SetAt.getElem_eq_self, setAt_of_getElem_eq_self⟩

theorem setAt_of_getElem_eq_getElem_eq {a : PermOf (n + 2)} (ha₁ : a[n + 1] = n + 1)
    (ha₂ : a[n] = n) : a.SetAt n :=
  setAt_of_lt_imp_getElem_lt (fun {i} hi {_} => by
    have H := (Nat.le_of_lt_succ a.getElem_lt)
    rcases H.lt_or_eq with H | H
    · simp_rw [Nat.lt_succ_iff] at H
      rcases H.lt_or_eq with H | H
      · exact H
      · have H := getElem_injective _ _ _ (H.trans ha₂.symm)
        cases H
        simp_rw [lt_self_iff_false] at hi
    · have H := getElem_injective _ _ _ (H.trans ha₁.symm)
      cases H
      simp_rw [add_lt_iff_neg_left, not_lt_zero'] at hi)

theorem setAt_zero : ∀ (a : PermOf n), a.SetAt 0 :=
  fun _ => setAt_of_lt_imp_getElem_lt (fun h => (Nat.not_lt_zero _ h).elim)

theorem setAt_one : (1 : PermOf n).SetAt m :=
  setAt_of_lt_imp_getElem_lt (fun him => getElem_one _ ▸ him)

theorem SetAt.mul {b : PermOf n}
    (ha : a.SetAt m) (hb : b.SetAt m) : (a * b).SetAt m :=
  setAt_of_lt_imp_getElem_lt (fun him _ => a.getElem_mul b _ ▸
    ha.getElem_lt_of_lt (hb.getElem_lt_of_lt him))

theorem SetAt.pow
    (ha : a.SetAt m) {k : ℕ} : (a^k).SetAt m := by
  induction k with | zero => _ | succ _ IH => _
  · exact pow_zero a ▸ setAt_one
  · simp_rw [pow_succ]
    exact IH.mul ha

theorem SetAt.zpow (ha : a.SetAt m) {k : ℤ} : (a^k).SetAt m := by
  have H := (a.isOfFinOrder.mem_zpowers_iff_mem_range_orderOf (y := a^k)).mp
      (zpow_mem (Subgroup.mem_zpowers _) _)
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  rcases H with ⟨_, _, hn⟩
  simp_rw [← hn]
  exact ha.pow

theorem SetAt.inv (ha : a.SetAt m) : (a⁻¹).SetAt m := by
  have H := (a.isOfFinOrder.mem_zpowers_iff_mem_range_orderOf (y := a⁻¹)).mp
      (inv_mem (Subgroup.mem_zpowers _))
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  rcases H with ⟨_, _, hn⟩
  simp_rw [← hn]
  exact ha.pow

@[simp] theorem setAt_inv_iff :
    (a⁻¹.SetAt m) ↔ (a.SetAt m) := ⟨fun ha => ha.inv, fun ha => ha.inv⟩

theorem setAt_of_le_of_lt_imp_getElem_lt (hmn : m ≤ n)
    (ha : ∀ {i} (hi : i < m), a[i] < m) : a.SetAt m :=
  setAt_of_lt_imp_getElem_lt (fun him => ha him)

@[simps!]
def setAtSubgroup (n m : ℕ) : Subgroup (PermOf n) where
  carrier a := a.SetAt m
  mul_mem' ha hb := SetAt.mul ha hb
  one_mem' := setAt_one
  inv_mem' ha := SetAt.inv ha

@[simp]
theorem mem_setAtSubgroup_iff : a ∈ setAtSubgroup n m ↔ a.SetAt m := Iff.rfl

theorem setAtSubgroup_eq_top_of_ge (hnm : n ≤ m) : setAtSubgroup n m = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_setAtSubgroup_iff, setAt_ge hnm, implies_true]

theorem setAtSubgroup_eq_eq_top : setAtSubgroup n n = ⊤ := setAtSubgroup_eq_top_of_ge le_rfl

theorem setAtSubgroup_zero_eq_top : setAtSubgroup n 0 = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_setAtSubgroup_iff, setAt_zero, implies_true]

end SetAt

def ofVector (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : PermOf n where
  fwdVector := a
  bwdVector := (Vector.range n).map a.toList.idxOf
  getElem_fwdVector_lt := hx
  getElem_bwdVector_getElem_fwdVector := fun {i} hi => by
    simp_rw [Vector.getElem_map, Vector.getElem_range]
    exact a.toList.idxOf_getElem ha _ _

section OfVector

@[simp]
theorem getElem_ofVector {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) : (ofVector a hx ha)[i] = a[i] := rfl


theorem fwdVector_toList_Nodup (a : PermOf n) : a.fwdVector.toList.Nodup := by
  simp_rw [List.nodup_iff_injective_getElem,
    Array.getElem_toList, Vector.getElem_toArray, getElem_fwdVector, Injective, Fin.ext_iff,
    Fin.forall_iff, Array.length_toList, Vector.size_toArray, getElem_inj, imp_self, implies_true]

theorem bwdVector_toList_Nodup (a : PermOf n) : a.bwdVector.toList.Nodup := by
  simp_rw [List.nodup_iff_injective_getElem,
    Array.getElem_toList, Vector.getElem_toArray, getElem_bwdVector, Injective, Fin.ext_iff,
    Fin.forall_iff, Array.length_toList, Vector.size_toArray, getElem_inj, imp_self, implies_true]

@[simp] theorem ofVector_fwdVector (a : PermOf n) :
    ofVector a.fwdVector a.getElem_fwdVector_lt a.fwdVector_toList_Nodup = a :=
  ext <| fun _ => by simp_rw [getElem_ofVector, getElem_fwdVector]

@[simp] theorem ofVector_bwdVector (a : PermOf n) :
    ofVector a.bwdVector a.getElem_bwdVector_lt a.bwdVector_toList_Nodup = a⁻¹ :=
  ext <| fun _ => by simp_rw [getElem_ofVector, getElem_bwdVector]

end OfVector


def ofVectorInv (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : PermOf n := (ofVector a hx ha)⁻¹

section OfVectorInv

theorem getElem_ofVectorInv {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) :
    (ofVectorInv a hx ha)[i] = a.toList.idxOf i := by
  unfold ofVectorInv
  unfold ofVector
  simp_rw [getElem_inv_mk, Vector.getElem_map, Vector.getElem_range]

theorem ofVectorInv_fwdVector (a : PermOf n) :
    ofVectorInv a.fwdVector a.getElem_fwdVector_lt a.fwdVector_toList_Nodup = a⁻¹ :=
  ext <| fun _ => by unfold ofVectorInv ; simp_rw [ofVector_fwdVector]

theorem ofVectorInv_bwdVector (a : PermOf n) :
    ofVectorInv a.bwdVector a.getElem_bwdVector_lt a.bwdVector_toList_Nodup = a :=
  ext <| fun _ => by unfold ofVectorInv ; simp_rw [ofVector_bwdVector, inv_inv]

end OfVectorInv

instance : SMul (PermOf n) ℕ where
  smul a i := a[i]?.getD i

section SMul

theorem smul_eq_dite (a : PermOf n) (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i :=
  apply_dite (fun (o : Option ℕ) => o.getD i) _ _ _

theorem smul_of_lt (a : PermOf n) {i : ℕ} (h : i < n) : a • i = a[i] := by
  simp_rw [smul_eq_dite, dif_pos h]

theorem smul_of_ge (a : PermOf n) {i : ℕ} (h : n ≤ i) : a • i = i := by
  simp_rw [smul_eq_dite, dif_neg h.not_lt]

@[simp] theorem smul_fin (a : PermOf n) {i : Fin n} : a • i = a[i.1] := a.smul_of_lt i.isLt

@[simp]
theorem smul_getElem (a b : PermOf n) {i : ℕ} (h : i < n) : a • b[i] = a[b[i]] :=
  a.smul_of_lt _

theorem smul_eq_iff (a : PermOf n) {i j : ℕ} :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [a.smul_of_lt hi, hi, hi.not_le, false_implies, forall_true_left, and_true]
  · simp_rw [a.smul_of_ge hi, hi, hi.not_lt, IsEmpty.forall_iff, forall_true_left, true_and]

theorem eq_smul_iff (a : PermOf n) {i j : ℕ} :
    i = a • j ↔ (∀ (hj : j < n), i = a[j]) ∧ (n ≤ j → i = j) := by
  simp_rw [eq_comm (a := i), smul_eq_iff]

theorem smul_eq_self_iff (a : PermOf n) {i : ℕ} :
    a • i = i ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [smul_eq_iff, implies_true, and_true]

theorem self_eq_smul_iff (a : PermOf n) {i : ℕ} :
    i = a • i ↔ ∀ (hi : i < n), i = a[i] := by
  simp_rw [eq_comm (a := i), smul_eq_self_iff]

@[simp]
theorem smul_lt_iff_lt (a : PermOf n) {i : ℕ} : a • i < n ↔ i < n := by
  rcases lt_or_le i n with h | h
  · simp_rw [h, iff_true, a.smul_of_lt h, getElem_lt]
  · simp_rw [h.not_lt, iff_false, not_lt, a.smul_of_ge h, h]

theorem smul_lt_of_lt (a : PermOf n) {i : ℕ} (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

theorem lt_of_smul_lt (a : PermOf n) {i : ℕ} (h : a • i < n) : i < n := a.smul_lt_iff_lt.mp h

theorem smul_fin_lt (a : PermOf n) {i : Fin n} : a • i < n := a.smul_lt_of_lt i.isLt

theorem smul_eq_smul_same_iff {a b : PermOf n} {i : ℕ} :
  a • i = b • i ↔ ∀ {hi : i < n}, a[i] = b[i] := by
  rcases lt_or_le i n with hin | hin
  · simp_rw [smul_of_lt _ hin, hin, forall_true_left]
  · simp_rw [smul_of_ge _ hin, hin.not_lt, IsEmpty.forall_iff]

theorem eq_iff_smul_eq_smul_lt {a b : PermOf n} : a = b ↔ ∀ {i : ℕ}, i < n → a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, PermOf.ext_iff, imp_forall_iff_forall]

theorem eq_iff_smul_eq_smul {a b : PermOf n} :
    a = b ↔ ∀ {i : ℕ}, a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, PermOf.ext_iff]

instance : FaithfulSMul (PermOf n) ℕ where
  eq_of_smul_eq_smul := by
    simp_rw [eq_iff_smul_eq_smul, imp_self, implies_true]

end SMul

instance : MulAction (PermOf n) ℕ where
  one_smul k := by
    rcases lt_or_le k n with hkn | hkn
    · simp_rw [smul_of_lt _ hkn, getElem_one]
    · simp_rw [smul_of_ge _ hkn]
  mul_smul a b k := by
    rcases lt_or_le k n with hkn | hkn
    · simp_rw [smul_of_lt _ hkn, smul_of_lt _ (getElem_lt _), getElem_mul]
    · simp_rw [smul_of_ge _ hkn]

section MulActionNat

theorem smul_eq_iff_eq_one (a : PermOf n) : (∀ {i : ℕ}, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul, one_smul]

theorem smul_eq_id_iff_eq_one (a : PermOf n) : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [funext_iff, id_eq, smul_eq_iff_eq_one]

theorem smul_right_inj (a : PermOf n) {i j : ℕ} : a • i = a • j ↔ i = j := by
  simp_rw [← inv_smul_eq_iff, inv_smul_smul]

theorem fixedBy_of_ge (a : PermOf n) {i : ℕ} (h : n ≤ i) :
    i ∈ MulAction.fixedBy ℕ a := by
  rw [MulAction.mem_fixedBy]
  exact a.smul_of_ge h

theorem Ici_subset_fixedBy (a : PermOf n) :
    Set.Ici n ⊆ MulAction.fixedBy ℕ a := fun _ => a.fixedBy_of_ge

theorem Ici_subset_fixedPoints :
    Set.Ici n ⊆ MulAction.fixedPoints (PermOf n) ℕ := fun _ hx a => a.smul_of_ge hx

open Pointwise in
theorem Iic_mem_set_fixedBy (a : PermOf n) :
    Set.Iio n ∈ MulAction.fixedBy (Set ℕ) a := Set.ext <| fun _ => by
  rw [← inv_inv a]
  simp_rw [Set.mem_inv_smul_set_iff, Set.mem_Iio, smul_lt_iff_lt]

theorem period_eq_one_of_ge (a : PermOf n) {i : ℕ} (hi : n ≤ i) : MulAction.period a i = 1 := by
  simp_rw [MulAction.period_eq_one_iff, a.smul_of_ge hi]

theorem period_eq_one_iff (a : PermOf n) {i : ℕ} :
    MulAction.period a i = 1 ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [MulAction.period_eq_one_iff]
  rcases lt_or_le i n with hi | hi
  · simp_rw [hi, forall_true_left, a.smul_of_lt hi]
  · simp_rw [hi.not_lt, forall_false, iff_true, a.smul_of_ge hi]

@[simp]
theorem getElem_pow_period (a : PermOf n) {i : ℕ} (hi : i < n) :
    (a ^ MulAction.period a i)[i] = i := by
  rw [← smul_of_lt _ hi, MulAction.pow_period_smul]

theorem getElem_pow_mod_period (a : PermOf n) {i : ℕ} (hi : i < n) (k : ℕ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt _ hi, MulAction.pow_mod_period_smul]

theorem getElem_zpow_mod_period (a : PermOf n) {i : ℕ} (hi : i < n) (k : ℤ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt _ hi, MulAction.zpow_mod_period_smul]

theorem period_nat_pos (a : PermOf n) {i : ℕ} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_eq_one_of_zero (a : PermOf 0) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_eq_one_of_one (a : PermOf 1) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_le_card_of_getElem_pow_mem (a : PermOf n) {i : ℕ} (hi : i < n)
  (s : Finset ℕ) : (∀ k < s.card + 1, (a ^ k)[i] ∈ s) → MulAction.period a i ≤ s.card := by
  simp_rw [← smul_of_lt _ hi]
  exact MulAction.period_le_card_of_smul_pow_mem _ _

theorem getElem_injOn_range_period (a : PermOf n) {i : ℕ} (hi : i < n) :
    Set.InjOn (fun k => (a ^ k)[i]) (Finset.range (MulAction.period a i)) := by
  simp_rw [← smul_of_lt _ hi]
  exact MulAction.smul_injOn_range_period _

theorem period_le_of_lt (a : PermOf n) {i : ℕ} (hi : i < n) : MulAction.period a i ≤ n := by
  refine (period_le_card_of_getElem_pow_mem a hi (Finset.range n) ?_).trans_eq
    (Finset.card_range _)
  simp_rw [Finset.card_range, Finset.mem_range, getElem_lt, implies_true]

theorem period_le_of_ne_zero [NeZero n] (a : PermOf n) {i : ℕ} : MulAction.period a i ≤ n := by
  rcases lt_or_le i n with hi | hi
  · exact a.period_le_of_lt hi
  · rw [a.period_eq_one_of_ge hi]
    exact NeZero.pos n

theorem exists_pos_le_pow_getElem_eq (a : PermOf n) {i : ℕ} (hi : i < n) :
    ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k)[i] = i :=
  ⟨MulAction.period a i, a.period_nat_pos, a.period_le_of_lt hi, a.getElem_pow_period _⟩

end MulActionNat

@[irreducible] def IsCongr {n m : ℕ} (a : PermOf n) (b : PermOf m) : Prop :=
  ∀ {i}, i < max m n → a • i = b • i

section IsCongr

variable {m l i : ℕ} {a : PermOf n} {b : PermOf m} {c : PermOf l}

theorem isCongr_iff_smul_eq_of_lt :
    a.IsCongr b ↔ ∀ {i}, i < max m n → a • i = b • i := by
  unfold IsCongr
  exact Iff.rfl

instance {a : PermOf n} {b : PermOf m} : Decidable (a.IsCongr b) :=
  decidable_of_decidable_of_iff isCongr_iff_smul_eq_of_lt.symm

theorem isCongr_iff_smul_eq : a.IsCongr b ↔ ∀ {i : ℕ}, a • i = b • i :=
  ⟨fun h i => (lt_or_le i (max m n)).elim (isCongr_iff_smul_eq_of_lt.mp h)
    (fun hmn => (a.smul_of_ge (le_of_max_le_right hmn)).trans
    (b.smul_of_ge (le_of_max_le_left hmn)).symm),
    fun h => isCongr_iff_smul_eq_of_lt.mpr (fun _ => h)⟩

theorem isCongr_iff_getElem_eq_getElem_and_getElem_eq_of_le (hnm : n ≤ m) :
    a.IsCongr b ↔ (∀ {i} (hi : i < n), a[i] = b[i]) ∧
    (∀ {i}, n ≤ i → ∀ (hi' : i < m), b[i] = i) := by
  simp_rw [isCongr_iff_smul_eq_of_lt, max_eq_left hnm, smul_eq_dite]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · intro i hi
    have H :=  dif_pos hi ▸ dif_pos (hi.trans_le hnm) ▸ h (hi.trans_le hnm)
    exact H
  · intro i hi hi'
    have H := dif_neg hi.not_lt ▸ dif_pos hi' ▸ h hi'
    exact H.symm
  · intro i hi'
    simp_rw [hi', dite_true]
    split_ifs with hi
    · exact h.1 _
    · exact (h.2 (le_of_not_lt hi) _).symm

theorem IsCongr.smul_eq (hab : a.IsCongr b) : ∀ {i : ℕ}, a • i = b • i :=
  isCongr_iff_smul_eq.mp hab

@[simp] theorem isCongr_refl (a : PermOf n) : a.IsCongr a := by
  simp_rw [isCongr_iff_smul_eq, implies_true]

theorem isCongr_rfl : a.IsCongr a := isCongr_refl a

theorem IsCongr.symm : a.IsCongr b → b.IsCongr a := by
  simp_rw [isCongr_iff_smul_eq, eq_comm, imp_self]

theorem isCongr_comm : a.IsCongr b ↔ b.IsCongr a :=
  ⟨IsCongr.symm, IsCongr.symm⟩

theorem isCongr_iff_getElem_eq_getElem_and_getElem_eq_of_ge (hmn : m ≤ n) :
    a.IsCongr b ↔ (∀ {i} (hi : i < m), a[i] = b[i]) ∧
    (∀ {i}, m ≤ i → ∀ (hi' : i < n), a[i] = i) := by
  refine isCongr_comm.trans
    ((isCongr_iff_getElem_eq_getElem_and_getElem_eq_of_le hmn).trans ?_)
  simp_rw [and_congr_left_iff]
  exact fun _ => ⟨fun h _ _ => (h _).symm, fun h _ _ => (h _).symm⟩

theorem IsCongr.trans : a.IsCongr b → b.IsCongr c → a.IsCongr c := by
  simp_rw [isCongr_iff_smul_eq]
  intro h₁ h₂
  exact (h₁.trans h₂)

@[simp] theorem isCongr_one_iff_eq_one : a.IsCongr (1 : PermOf m) ↔ a = 1 := by
  simp_rw [isCongr_iff_smul_eq, one_smul, smul_eq_iff_eq_one]

@[simp] theorem one_isCongr_iff_eq_one : (1 : PermOf m).IsCongr a ↔ a = 1 := by
  simp_rw [isCongr_comm, isCongr_one_iff_eq_one]

theorem isCongr_one_one : (1 : PermOf n).IsCongr (1 : PermOf m) := by
  simp_rw [isCongr_one_iff_eq_one]

theorem IsCongr.inv_inv (hab : a.IsCongr b) : a⁻¹.IsCongr b⁻¹ := by
  simp_rw [isCongr_iff_smul_eq, eq_inv_smul_iff, hab.symm.smul_eq,
    smul_inv_smul, implies_true]

theorem IsCongr.inv_right (hab : a.IsCongr b⁻¹) : a⁻¹.IsCongr b := hab.inv_inv

theorem IsCongr.inv_left (hab : a⁻¹.IsCongr b) : a.IsCongr b⁻¹ := hab.inv_inv

theorem inv_isCongr_iff_isCongr_inv : a⁻¹.IsCongr b ↔ a.IsCongr b⁻¹ :=
  ⟨fun hab => hab.inv_left, fun hab => hab.inv_right⟩

@[simp] theorem inv_isCongr_inv_iff : a⁻¹.IsCongr b⁻¹ ↔ a.IsCongr b :=
  ⟨fun hab => hab.inv_inv, fun hab => hab.inv_inv⟩

theorem IsCongr.mul_mul {a' : PermOf n} {b' : PermOf m} (hab : a.IsCongr b)
    (hab' : a'.IsCongr b') : (a*a').IsCongr (b*b') := by
  simp_rw [isCongr_iff_smul_eq, mul_smul, hab.smul_eq, hab'.smul_eq, implies_true]

theorem IsCongr.eq {a' : PermOf n} (h : a.IsCongr a') : a = a' := by
  ext i hi
  simp_rw [← smul_of_lt _ hi, h.smul_eq]

@[simp] theorem isCongr_iff_eq {a' : PermOf n} : a.IsCongr a' ↔ a = a' :=
  ⟨IsCongr.eq, fun h => h ▸ isCongr_rfl⟩

@[simps!]
def IsCongrSubgroup (n m : ℕ) : Subgroup (PermOf n × PermOf m) where
  carrier a := a.1.IsCongr a.2
  mul_mem' := IsCongr.mul_mul
  one_mem' := isCongr_one_one
  inv_mem' := IsCongr.inv_inv

@[simp] theorem mem_IsCongrSubgroup_iff (ab : PermOf n × PermOf m) :
    ab ∈ IsCongrSubgroup n m ↔ ab.1.IsCongr ab.2 := Iff.rfl

end IsCongr

/--
For `a` an `PermOf n`, `a.swap i j hi hj` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : PermOf n) (i j : ℕ) (hi : i < n) (hj : j < n) : PermOf n where
  fwdVector := a.fwdVector.swap i j
  bwdVector := a.bwdVector.map (fun k => Equiv.swap i j k)
  getElem_fwdVector_lt := fun _ => by
    simp_rw [Vector.getElem_swap_eq_getElem_swap_apply, getElem_fwdVector, getElem_lt]
  getElem_bwdVector_getElem_fwdVector := fun _ => by
    simp_rw [Vector.getElem_map, getElem_bwdVector, Vector.getElem_swap_eq_getElem_swap_apply,
      getElem_fwdVector, getElem_inv_getElem, swap_apply_self]

section Swap

variable (i j k : ℕ) (hi : i < n) (hj : j < n)

@[simp]
theorem getElem_swap (a : PermOf n) (hk : k < n) :
    (a.swap i j hi hj)[k] = a[Equiv.swap i j k]'(swap_prop (· < n) hk hi hj) :=
  Vector.getElem_swap_eq_getElem_swap_apply _ _ _ hi hj _ _

@[simp]
theorem getElem_inv_swap (a : PermOf n) (hk : k < n) :
    (a.swap i j hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.bwdVector.getElem_map _ _ _

theorem swap_smul_eq_smul_swap (a : PermOf n) :
    (a.swap i j hi hj) • k = a • (Equiv.swap i j k) := by
  rcases lt_or_ge k n with hk | hk
  · simp_rw [smul_of_lt _ (swap_prop (· < n) hk hi hj), smul_of_lt _ hk, getElem_swap]
  · simp_rw [Equiv.swap_apply_of_ne_of_ne (hk.trans_lt' hi).ne' (hk.trans_lt' hj).ne',
      smul_of_ge _ hk]

theorem swap_inv_eq_swap_apply_inv_smul (a : PermOf n) :
  (a.swap i j hi hj)⁻¹ • k = Equiv.swap i j (a⁻¹ • k) := by
  simp_rw [inv_smul_eq_iff, swap_smul_eq_smul_swap,
  ← swap_smul, smul_inv_smul, swap_apply_self]

theorem swap_smul_eq_swap_apply_smul (a : PermOf n) :
    (a.swap i j hi hj) • k = Equiv.swap (a • i) (a • j) (a • k) := by
  rw [swap_smul, swap_smul_eq_smul_swap]

theorem swap_inv_smul_eq_inv_smul_swap (a : PermOf n) : (a.swap i j hi hj)⁻¹ • k =
    a⁻¹ • (Equiv.swap (a • i) (a • j) k) := by
  simp_rw [swap_inv_eq_swap_apply_inv_smul, ← Equiv.swap_smul, inv_smul_smul]

theorem swap_smul_left (a : PermOf n) :
    (a.swap i j hi hj) • i = a • j := by rw [swap_smul_eq_smul_swap, swap_apply_left]

theorem swap_smul_right (a : PermOf n) :
  (a.swap i j hi hj) • j = a • i := by rw [swap_smul_eq_smul_swap, swap_apply_right]

theorem swap_smul_of_ne_of_ne (a : PermOf n) {k} :
  k ≠ i → k ≠ j → (a.swap i j hi hj) • k = a • k := by
  rw [swap_smul_eq_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

theorem swap_inv_smul_left (a : PermOf n) :
    (a.swap i j hi hj)⁻¹ • (a • i) = j := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_left, inv_smul_smul]

theorem swap_inv_smul_right (a : PermOf n) :
    (a.swap i j hi hj)⁻¹ • (a • j) = i := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_right, inv_smul_smul]

theorem swap_inv_smul_of_ne_of_ne (a : PermOf n) {k} :
  k ≠ a • i → k ≠ a • j → (a.swap i j hi hj)⁻¹ • k = a⁻¹ • k := by
  rw [swap_inv_smul_eq_inv_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (a : PermOf n) (i : ℕ) (hi hi' : i < n) : a.swap i i hi hi' = a := by
  ext : 1
  simp_rw [getElem_swap, Equiv.swap_self, Equiv.refl_apply]

@[simp]
theorem swap_swap (a : PermOf n) (i j : ℕ) (hi hi' : i < n) (hj hj' : j < n) :
    (a.swap i j hi hj).swap i j hi' hj' = a := by
  ext : 1
  simp_rw [getElem_swap, swap_apply_self]

theorem getElem_one_swap (hk : k < n) : (swap 1 i j hi hj)[k] = Equiv.swap i j k := by
  rw [getElem_swap, getElem_one]

theorem getElem_inv_one_swap (hk : k < n) : (swap 1 i j hi hj)⁻¹[k] = Equiv.swap i j k := by
  simp_rw [getElem_inv_swap, inv_one, getElem_one]

theorem one_swap_smul : (swap 1 i j hi hj) • k = Equiv.swap i j k := by
  rw [swap_smul_eq_smul_swap, one_smul]

theorem one_swap_inv_smul : (swap 1 i j hi hj)⁻¹ • k = Equiv.swap i j k := by
  simp_rw [swap_inv_smul_eq_inv_smul_swap, one_smul, inv_one, one_smul]

theorem one_swap_mul_self : swap 1 i j hi hj * swap 1 i j hi hj = 1 := by
  ext : 1
  simp_rw [getElem_mul, getElem_one_swap, swap_apply_self, getElem_one]

theorem one_swap_inverse : (swap 1 i j hi hj)⁻¹ = swap 1 i j hi hj := by
  ext : 1
  rw [getElem_one_swap, getElem_inv_one_swap]

theorem swap_eq_mul_one_swap (a : PermOf n) : a.swap i j hi hj = a * swap 1 i j hi hj := by
  ext : 1
  simp only [getElem_swap, getElem_mul, getElem_one]

theorem swap_eq_one_swap_mul (a : PermOf n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    a.swap i j hi hj = swap 1 _ _ hi' hj' * a := by
  rw [eq_iff_smul_eq_smul_lt]
  simp_rw [mul_smul, one_swap_smul, swap_smul_eq_smul_swap, swap_smul, implies_true]

theorem swap_inv_eq_one_swap_mul (a : PermOf n) :
    (a.swap i j hi hj)⁻¹ = swap 1 i j hi hj * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (a : PermOf n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    (a.swap i j hi hj)⁻¹ = a⁻¹ * swap 1 _ _ hi' hj' := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

end Swap

def actOnIndices {α : Type*} (a : PermOf n) (v : Vector α n) : Vector α n :=
  v.mapFinIdx (fun i _ hi => v[a[i]])

section ActOnIndices

variable {α : Type*}

@[simp] theorem getElem_actOnIndices (a : PermOf n) (v : Vector α n) {i : ℕ} (hi : i < n) :
    (a.actOnIndices v)[i] = v[a[i]] := Vector.getElem_mapFinIdx _ _ _ _

@[simp] theorem one_actOnIndices (v : Vector α n) :
    (1 : (PermOf n)).actOnIndices v = v := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, getElem_one, implies_true]

@[simp] theorem mul_actOnIndices (a b : PermOf n) (v : Vector α n) :
    (a * b).actOnIndices v = b.actOnIndices (a.actOnIndices v) := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, getElem_mul, implies_true]

@[simp] theorem actOnIndices_actOnIndices_inv (a : PermOf n) (v : Vector α n) :
    a.actOnIndices (a⁻¹.actOnIndices v) = v := by
  simp_rw [← mul_actOnIndices, inv_mul_cancel, one_actOnIndices]

@[simp] theorem actOnIndices_inv_actOnIndices (a : PermOf n) (v : Vector α n) :
    a⁻¹.actOnIndices (a.actOnIndices v) = v := by
  simp_rw [← mul_actOnIndices, mul_inv_cancel, one_actOnIndices]

theorem mem_of_mem_actOnIndices (a : PermOf n) {v : Vector α n} {x : α}
    (hx : x ∈ a.actOnIndices v) : x ∈ v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_actOnIndices] at hx
  rcases hx with ⟨i, hi, hix⟩
  exact ⟨a[i], a.getElem_lt, hix⟩

theorem mem_actOnIndices_of_mem (a : PermOf n) {v : Vector α n} {x : α}
    (hx : x ∈ v) : x ∈ a.actOnIndices v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_actOnIndices]
  rcases hx with ⟨i, hi, hix⟩
  refine ⟨a⁻¹[i], getElem_lt _, ?_⟩
  simp_rw [getElem_getElem_inv, hix]

theorem mem_onIndices_iff (a : PermOf n) {v : Vector α n} {x : α} :
    x ∈ a.actOnIndices v ↔ x ∈ v := ⟨a.mem_of_mem_actOnIndices, a.mem_actOnIndices_of_mem⟩

@[simp]
theorem actOnIndices_range (a : PermOf n) :
    a.actOnIndices (Vector.range n) = a.fwdVector := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, Vector.getElem_range,
    getElem_fwdVector, implies_true]

theorem inv_actOnIndices_range (a : PermOf n) :
    (a⁻¹).actOnIndices (Vector.range n) = a.bwdVector := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, Vector.getElem_range,
    getElem_bwdVector, implies_true]

end ActOnIndices

instance {α : Type*} : MulAction (PermOf n)ᵐᵒᵖ (Vector α n) where
  smul a v := a.unop.actOnIndices v
  one_smul _ := one_actOnIndices _
  mul_smul _ _ _ := mul_actOnIndices _ _ _

section MulActionMulOppositeVector

variable {α : Type*}

@[simp] theorem op_smul (a : PermOf n) (v : Vector α n) :
    (MulOpposite.op a) • v = a.actOnIndices v := rfl

@[simp] theorem unop_actOnIndices (a : (PermOf n)ᵐᵒᵖ) (v : Vector α n) :
    a.unop.actOnIndices v = a • v := rfl

end MulActionMulOppositeVector

def cycleOf (a : PermOf n) (x : ℕ) : Finset ℕ :=
  if h : x < n then (Finset.range n).image (fun k => (a ^ k)[x]) else {x}

theorem cycleOf_lt (a : PermOf n) {x : ℕ} (hx : x < n) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k)[x]) := by
  unfold cycleOf
  simp_rw [dif_pos hx, Finset.ext_iff, Finset.mem_image, Finset.mem_range]
  refine fun _ => ⟨fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos,
    by simp_rw [getElem_pow_mod_period, h]⟩, fun ⟨_, hlt, h⟩ =>
    ⟨_, (hlt.trans_le <| a.period_le_of_lt hx), h⟩⟩

theorem cycleOf_ge (a : PermOf n) {x : ℕ} (hx : n ≤ x) :
    a.cycleOf x = {x} := dif_neg (not_lt_of_le hx)

theorem card_cycleOf (a : PermOf n) (x : ℕ) : (a.cycleOf x).card = MulAction.period a x := by
  rcases lt_or_le x n with hx | hx
  · refine Eq.trans ?_ (Finset.card_range (MulAction.period a x))
    rw [a.cycleOf_lt hx, Finset.card_image_iff]
    exact getElem_injOn_range_period _ _
  · rw [a.cycleOf_ge hx, a.period_eq_one_of_ge hx, Finset.card_singleton]

theorem cycleOf_eq_map_smul_range_period (a : PermOf n) (x : ℕ) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k) • x) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleOf_lt hx, smul_of_lt _ hx]
  · simp_rw [a.cycleOf_ge hx, smul_of_ge _ hx, Finset.ext_iff, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range, exists_and_right]
    exact fun _ => ⟨fun h => h ▸ ⟨⟨0, a.period_nat_pos⟩, rfl⟩, fun h => h.2.symm⟩

theorem mem_cycleOf_iff_exists_pow_lt_period_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i) • x = y := by
  rw [cycleOf_eq_map_smul_range_period]
  simp_rw [Finset.mem_image, Finset.mem_range]

theorem mem_cycleOf_iff_exists_pow_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_lt_period_smul]
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩,
    fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos, ?_⟩⟩
  simp_rw [MulAction.pow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_zpow_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_smul]
  refine ⟨fun ⟨_, h⟩ => ⟨_, (zpow_natCast a _).symm ▸ h⟩,
    fun ⟨k, h⟩ => ⟨(k % MulAction.period a x).toNat, ?_⟩⟩
  simp_rw [← zpow_natCast, Int.toNat_of_nonneg
    (Int.emod_nonneg _ ((Nat.cast_ne_zero (R := ℤ)).mpr (a.period_nat_pos (i := x)).ne')),
    MulAction.zpow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_getElem_pow_lt_period (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_lt_period_smul, smul_of_lt _ hx]

theorem mem_cycleOf_iff_exists_getElem_pow (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul, smul_of_lt _ hx]

theorem mem_cycleOf_iff_exists_getElem_zpow (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul, smul_of_lt _ hx]

theorem self_mem_cycleOf (a : PermOf n) (x : ℕ) : x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨0, by simp only [pow_zero, one_smul]⟩

theorem nonempty_cycleOf (a : PermOf n) {x : ℕ} : (a.cycleOf x).Nonempty :=
  ⟨_, a.self_mem_cycleOf x⟩

theorem smul_mem_cycleOf (a : PermOf n) (x : ℕ) : (a • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨1, by simp only [pow_one]⟩

theorem smul_inv_mem_cycleOf (a : PermOf n) (x : ℕ) : (a⁻¹ • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨-1, by simp only [zpow_neg, zpow_one]⟩

theorem smul_pow_mem_cycleOf (a : PermOf n) (x k : ℕ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨k, rfl⟩

theorem smul_zpow_mem_cycleOf (a : PermOf n) (x : ℕ) (k : ℤ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨k, rfl⟩

theorem getElem_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) : a[x] ∈ a.cycleOf x := by
  convert a.smul_mem_cycleOf x
  rw [smul_of_lt _ hx]

theorem getElem_inv_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) : a⁻¹[x] ∈ a.cycleOf x := by
  convert a.smul_inv_mem_cycleOf x
  rw [smul_of_lt _ hx]

theorem getElem_pow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℕ):
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_pow_mem_cycleOf x k
  rw [smul_of_lt _ hx]

theorem getElem_zpow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℤ) :
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_zpow_mem_cycleOf x k
  rw [smul_of_lt _ hx]

theorem getElem_inv_pow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℕ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  convert a.getElem_zpow_mem_cycleOf hx (-(k : ℤ))
  simp_rw [inv_pow, zpow_neg, zpow_natCast]

theorem getElem_inv_zpow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℤ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  simp only [inv_zpow']
  exact a.getElem_zpow_mem_cycleOf hx (-k)

def CycleMinVectorAux (a : PermOf n) : ℕ → PermOf n × Vector ℕ n
  | 0 => ⟨1, Vector.range n⟩
  | 1 =>
    ⟨a, (Vector.range n).zipWith min a.fwdVector⟩
  | (i+2) =>
    let ⟨ρ, b⟩ := a.CycleMinVectorAux (i + 1)
    let ρ' := ρ ^ 2
    ⟨ρ', b.zipWith min (ρ'.actOnIndices b)⟩

@[simp]
theorem cycleMinAux_zero_fst (a : PermOf n) : (a.CycleMinVectorAux 0).1 = 1 := rfl

@[simp]
theorem cycleMinAux_succ_fst (a : PermOf n) (i : ℕ) :
    (a.CycleMinVectorAux (i + 1)).1 = a ^ (2 ^ i) := by
  induction' i with i IH
  · rw [pow_zero, pow_one]
    rfl
  · rw [pow_succ, pow_mul]
    exact IH ▸ rfl

def CycleMinVector (a : PermOf n) (i : ℕ) : Vector ℕ n := (a.CycleMinVectorAux i).2

@[simp]
theorem cycleMinAux_snd_val (a : PermOf n) {i : ℕ} :
    (a.CycleMinVectorAux i).2 = CycleMinVector a i := rfl

@[simp] theorem getElem_cycleMinVector_zero (a : PermOf n) {x : ℕ} (hx : x < n):
  (a.CycleMinVector 0)[x] = x := Vector.getElem_range _ _

theorem getElem_cycleMinVector_succ (a : PermOf n) {i x : ℕ}
    (hx : x < n) :
    (a.CycleMinVector (i + 1))[x] = min ((a.CycleMinVector i)[x])
    ((a.CycleMinVector i)[(a^2^i)[x]]) := by
  rcases i with (_ | i) <;>
  refine (Vector.getElem_zipWith _ _ _ _ _).trans ?_
  · simp_rw [Vector.getElem_range, getElem_fwdVector, pow_zero, pow_one,
      getElem_cycleMinVector_zero]
  · simp_rw [getElem_actOnIndices, cycleMinAux_snd_val,
      cycleMinAux_succ_fst, ← pow_mul, ← pow_succ]

@[simp] theorem getElem_cycleMinVector_le_self {a : PermOf n} {k i : ℕ}
    {hx : i < n}  : (a.CycleMinVector k)[i] ≤ i := by
  induction k generalizing a i with | zero => _ | succ k IH => _
  · simp_rw [getElem_cycleMinVector_zero, le_rfl]
  · simp_rw [getElem_cycleMinVector_succ, min_le_iff, IH, true_or]

theorem getElem_one_cycleMinVector {k i : ℕ} (hi : i < n) :
    ((1 : PermOf n).CycleMinVector k)[i] = i := by
  induction k generalizing n i with | zero => _ | succ k IH => _
  · simp_rw [getElem_cycleMinVector_zero]
  · simp_rw [getElem_cycleMinVector_succ, one_pow, getElem_one, IH, min_self]

theorem one_cycleMinVector {k : ℕ} : (1 : PermOf n).CycleMinVector k = Vector.range n := by
  ext i hi
  simp_rw [getElem_one_cycleMinVector, Vector.getElem_range]

@[simp]
theorem getElem_cycleMinVector_lt (a : PermOf n) {i : ℕ} {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] < n := by
  induction' i with i IH generalizing x
  · simp_rw [getElem_cycleMinVector_zero]
    exact hx
  · simp_rw [getElem_cycleMinVector_succ, min_lt_iff, IH, true_or]

theorem min_getElem_cycleMinVector_getElem_cycleMinVector_getElem (a : PermOf n)
    {i x : ℕ} (hx : x < n) :
    min x ((a.CycleMinVector i)[a[x]]) = min (a.CycleMinVector i)[x] ((a^2^i)[x]) := by
  induction i generalizing a x with | zero => _ | succ i IH => _
  · simp_rw [getElem_cycleMinVector_zero, pow_zero, pow_one]
  · simp_rw [getElem_cycleMinVector_succ, ← min_assoc, IH, min_assoc, ← getElem_mul, pow_mul_comm',
      getElem_mul, IH, ← getElem_mul, ← pow_add, ← two_mul, ← pow_succ']

theorem getElem_cycleMinVector_eq_min'_getElem_pow_image_range (a : PermOf n)
    {i x : ℕ} (hx : x < n) :
    (a.CycleMinVector i)[x] =
    ((Finset.range (2^i)).image (fun k => (a ^ k)[x])).min'
      (Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.two_pow_pos i).ne')) := by
  induction i generalizing a x with | zero => _ | succ i IH => _
  · simp_rw [getElem_cycleMinVector_zero, pow_zero, Finset.range_one, Finset.image_singleton,
      pow_zero, getElem_one, Finset.min'_singleton]
  · simp_rw [getElem_cycleMinVector_succ, IH, le_antisymm_iff, getElem_pow_add,
      le_inf_iff, Finset.le_min'_iff, inf_le_iff, Finset.mem_image, Finset.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine ⟨fun k hk => (lt_or_le k (2^i)).imp
      (fun hk' => Finset.min'_le _ _ ?_) (fun hk' => Finset.min'_le _ _ ?_),
      fun k hk => Finset.min'_le _ _ ?_, fun k hk => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [Finset.mem_image, Finset.mem_range]
    exacts [⟨k, hk', rfl⟩,
      ⟨k - 2^i, Nat.sub_lt_right_of_lt_add hk' (Nat.two_mul _ ▸ Nat.pow_succ' ▸ hk),
        (Nat.sub_add_cancel hk').symm ▸ rfl⟩,
      ⟨k, hk.trans (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _)), rfl⟩,
      ⟨k + 2^i, (Nat.pow_succ' ▸ Nat.two_mul _ ▸ (Nat.add_lt_add_right hk _)), rfl⟩]

lemma getElem_cycleMinVector_le_getElem_pow_lt (a : PermOf n) {i : ℕ} {x : ℕ}
    {k : ℕ} (hk : k < 2^i) (hx : x < n) :
    (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range]
  refine Finset.min'_le _ _ ?_
  simp_rw [Finset.mem_image, Finset.mem_range]
  exact ⟨k, hk, rfl⟩

lemma getElem_cycleMinVector_le (a : PermOf n) {i : ℕ} {x y : ℕ}
    {hx : x < n} (hk : ∃ k < 2^i, y = (a ^ k)[x]) :
    (a.CycleMinVector i)[x] ≤ y :=
  hk.choose_spec.2 ▸ a.getElem_cycleMinVector_le_getElem_pow_lt hk.choose_spec.1 _

lemma exists_lt_getElem_cycleMin_eq_getElem_pow (a : PermOf n) (i : ℕ) {x : ℕ}
      (hx : x < n) :
    ∃ k < 2^i, (a.CycleMinVector i)[x] = (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range]
  have H := Finset.min'_mem ((Finset.range (2^i)).image (fun k => (a ^ k)[x]))
    (Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.two_pow_pos i).ne'))
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  exact ⟨H.choose, H.choose_spec.1, H.choose_spec.2.symm⟩

lemma le_getElem_cycleMin_iff (a : PermOf n) (i : ℕ) {x y : ℕ}
      (hx : x < n) :
    y ≤ (a.CycleMinVector i)[x] ↔ ∀ k < 2^i, y ≤ (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range, Finset.le_min'_iff,
    Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

@[simp] theorem getElem_cycleMinVector_of_self_le_getElem {a : PermOf n} {k i : ℕ}
    {hx : i < n} (hxa : ∀ k, i ≤ (a^k)[i]) : (a.CycleMinVector k)[i] = i := by
  simp_rw [le_antisymm_iff, le_getElem_cycleMin_iff, hxa,
    getElem_cycleMinVector_le_self, implies_true, and_self]

theorem getElem_zero_cycleMinVector [NeZero n]
    {a : PermOf n} {k : ℕ} : (a.CycleMinVector k)[0]'(NeZero.pos _) = 0 :=
  getElem_cycleMinVector_of_self_le_getElem (fun _ => zero_le _)

lemma getElem_cycleMinVector_eq_min'_cycleOf (a : PermOf n) {i : ℕ} {x : ℕ}
      (hai : MulAction.period a x ≤ 2^i) (hx : x < n) :
      (a.CycleMinVector i)[x] = (a.cycleOf x).min' a.nonempty_cycleOf := by
  refine le_antisymm (getElem_cycleMinVector_le _ ?_) (Finset.min'_le _ _ ?_)
  · have H := Finset.min'_mem (a.cycleOf x) a.nonempty_cycleOf
    simp_rw [mem_cycleOf_iff_exists_getElem_pow_lt_period _ hx] at H
    exact ⟨H.choose, H.choose_spec.1.trans_le hai, H.choose_spec.2.symm⟩
  · simp_rw [a.mem_cycleOf_iff_exists_getElem_pow hx]
    exact ⟨(a.exists_lt_getElem_cycleMin_eq_getElem_pow i hx).choose,
    ((a.exists_lt_getElem_cycleMin_eq_getElem_pow i hx).choose_spec).2.symm⟩

lemma getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow (a : PermOf n) {i : ℕ} {x : ℕ}
    (hx : x < n) (hai : MulAction.period a x ≤ 2^i) :
    ∀ k, (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := fun k => by
  simp_rw [a.getElem_cycleMinVector_eq_min'_cycleOf hai,
    Finset.min'_le _ _ (a.getElem_pow_mem_cycleOf hx k)]

lemma getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow (a : PermOf n) {i : ℕ} {x : ℕ}
      (hx : x < n) (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := fun k => by
  simp_rw [a.getElem_cycleMinVector_eq_min'_cycleOf hai,
    Finset.min'_le _ _ (a.getElem_zpow_mem_cycleOf hx k)]

lemma cycleMinVector_eq_apply_cycleMinVector (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : ∀ {x : ℕ}, MulAction.period a x ≤ 2^i) (hx : x < n) :
   (a.CycleMinVector i)[x] = (a.CycleMinVector i)[a[x]] := by
  simp_rw [getElem_cycleMinVector_eq_min'_cycleOf _ hai, le_antisymm_iff, Finset.le_min'_iff]
  refine ⟨fun y hy => Finset.min'_le _ _ ?_, fun y hy => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hx,
      mem_cycleOf_iff_exists_getElem_zpow _ (getElem_lt _)] at hy ⊢
  exacts [⟨hy.choose + 1, zpow_add_one a _ ▸ getElem_mul _ _ _ ▸ hy.choose_spec⟩,
      ⟨hy.choose - 1, zpow_sub_one a _ ▸ getElem_mul _ _ _ ▸
      inv_mul_cancel_right _ a ▸ hy.choose_spec⟩]

def CycleMin (a : PermOf n) (i : ℕ) (x : ℕ) : ℕ := (a.CycleMinVector i)[x]?.getD x

theorem getElem_cycleMinVector (a : PermOf n) (i : ℕ) {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] = a.CycleMin i x :=
  (Vector.getD_of_lt _ _ _ _).symm

theorem cycleMin_of_lt (a : PermOf n) {i x : ℕ} (hx : x < n) :
    a.CycleMin i x = (a.CycleMinVector i)[x] := Vector.getD_of_lt _ _ _ _

theorem cycleMin_of_getElem {a b : PermOf n} {i x : ℕ} (hx : x < n) :
    a.CycleMin i (b[x]) = (a.CycleMinVector i)[b[x]] :=
  Vector.getD_of_lt _ _ _ _

theorem cycleMin_of_ge (a : PermOf n) {i x : ℕ} (hx : n ≤ x) :
    a.CycleMin i x = x := Vector.getD_of_ge _ _ _ hx

@[simp] theorem one_cycleMin {k x : ℕ} : (1 : PermOf n).CycleMin k x = x := by
  rcases lt_or_le x n with hx | hx
  · rw [cycleMin_of_lt _ hx, one_cycleMinVector, Vector.getElem_range]
  · rwa [cycleMin_of_ge]

@[simp]
theorem cycleMin_zero (a : PermOf n) {x : ℕ} :
  a.CycleMin 0 x = x := if hx : x < n then
    (a.cycleMin_of_lt hx).trans <| Array.getElem_range _ else a.cycleMin_of_ge (le_of_not_lt hx)

@[simp]
theorem cycleMin_succ (a : PermOf n) {i x : ℕ} :
    a.CycleMin (i + 1) x = min (a.CycleMin i x) (a.CycleMin i (a^2^i • x)) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [smul_of_lt _ hx, a.cycleMin_of_lt hx, cycleMin_of_getElem, getElem_cycleMinVector_succ]
  · simp_rw [smul_of_ge _ hx, a.cycleMin_of_ge hx, min_self]

@[simp]
theorem cycleMin_lt_iff_lt (a : PermOf n) {i : ℕ} {x : ℕ} :
    a.CycleMin i x < n ↔ x < n := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, hx, getElem_cycleMinVector_lt]
  · simp_rw [a.cycleMin_of_ge hx]

lemma cycleMin_le_smul_pow_lt_two_pow (a : PermOf n) {i : ℕ} (x : ℕ) {k : ℕ} (hk : k < 2^i) :
    a.CycleMin i x ≤ (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_pow_lt _ hk _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_pow_smul_of_period_le_two_pow (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) : ∀ k, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow _ _ hai _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_zpow_smul_of_period_le_two_pow  (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow _ _ hai _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_self (a : PermOf n) (i : ℕ) {x : ℕ} :
    a.CycleMin i x ≤ x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx]
    exact getElem_cycleMinVector_le_self
  · simp_rw [a.cycleMin_of_ge hx, le_rfl]

lemma exists_lt_cycleMin_eq_smul_pow (a : PermOf n) (i : ℕ) {x : ℕ} :
    ∃ k < 2^i, a.CycleMin i x = (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact exists_lt_getElem_cycleMin_eq_getElem_pow _ _ _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx]
    exact ⟨0, Nat.two_pow_pos _, trivial⟩

lemma cycleMin_eq_min'_cycleOf (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    a.CycleMin i x = (a.cycleOf x).min' a.nonempty_cycleOf := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx]
    exact getElem_cycleMinVector_eq_min'_cycleOf _  hai _
  · simp_rw [a.cycleMin_of_ge hx, a.cycleOf_ge hx]
    exact rfl

lemma cycleMin_eq_apply_cycleMin (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : ∀ {x : ℕ}, MulAction.period a x ≤ 2^i) :
    a.CycleMin i x = a.CycleMin i (a • x) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_eq_min'_cycleOf _ _ hai, le_antisymm_iff, Finset.le_min'_iff]
    refine ⟨fun y hy => Finset.min'_le _ _ ?_, fun y hy => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hx,
      mem_cycleOf_iff_exists_getElem_zpow _ (a.smul_lt_of_lt hx), a.smul_of_lt hx] at hy ⊢
    exacts [⟨hy.choose + 1, zpow_add_one a _ ▸ getElem_mul _ _ _ ▸ hy.choose_spec⟩,
      ⟨hy.choose - 1, zpow_sub_one a _ ▸ getElem_mul _ _ _ ▸
      inv_mul_cancel_right _ a ▸ hy.choose_spec⟩]
  · simp_rw [a.cycleMin_of_ge hx]
    rw [a.cycleMin_of_ge (le_of_not_lt (a.lt_of_smul_lt.mt hx.not_lt)), a.smul_of_ge hx]

section Cast

variable {m n o : ℕ}

/--
`PermOf.cast` re-interprets an `PermOf n` as an `PermOf m`, where `n = m`.
-/
@[inline] protected def cast (hnm : n = m) (a : PermOf n) : PermOf m where
  fwdVector := a.fwdVector.cast hnm
  bwdVector := a.bwdVector.cast hnm
  getElem_fwdVector_lt := fun _ => by
    simp_rw [Vector.getElem_cast, hnm.symm, getElem_fwdVector, getElem_lt]
  getElem_bwdVector_getElem_fwdVector :=
    fun hi => a.getElem_inv_getElem (hi.trans_eq hnm.symm)

@[simp]
theorem getElem_cast (hnm : n = m) (a : PermOf n) {i : ℕ} (hi : i < m):
    (a.cast hnm)[i] = a[i] := rfl

@[simp]
theorem getElem_inv_cast (hnm : n = m) (a : PermOf n) {i : ℕ} (hi : i < m):
    (a.cast hnm)⁻¹[i] = a⁻¹[i] := rfl

@[simp] theorem cast_rfl (a : PermOf n) : a.cast rfl = a := rfl

@[simp]
theorem cast_smul (hnm : n = m) (a : PermOf n) (i : ℕ) :
    (a.cast hnm) • i = a • i := by simp_rw [smul_eq_dite, hnm, getElem_cast]

@[simp] theorem cast_one (hnm : n = m) : (1 : PermOf n).cast hnm = 1 := by
  ext
  simp_rw [getElem_cast, getElem_one]

@[simp] theorem cast_eq_iff (hnm : n = m) {a : PermOf n} {b : PermOf m} :
    a.cast hnm = b ↔ a = b.cast hnm.symm := by
  simp_rw [PermOf.ext_iff, getElem_cast, hnm]

theorem cast_eq_one_iff (hnm : n = m) (a : PermOf n) : a.cast hnm = 1 ↔ a = 1 := by
  simp_rw [cast_eq_iff, cast_one]

@[simp]
theorem inv_cast (hnm : n = m) (a : PermOf n) :
    (a.cast hnm)⁻¹ = a⁻¹.cast hnm := rfl

@[simp]
theorem cast_mul (hnm : n = m) (a b : PermOf n) :
    a.cast hnm * b.cast hnm = (a * b).cast hnm := ext <| fun hi => by
  simp only [getElem_cast, getElem_mul]

theorem cast_eq_cast (hnm : n = m) (a : PermOf n) :
    hnm ▸ a = a.cast hnm := by cases hnm ; rfl

@[simp] theorem cast_symm {hnm : n = m} {hmb : m = n} (a : PermOf n) :
    (a.cast hnm).cast hmb = a := rfl

@[simp] theorem cast_trans {hnm : n = m} {hmo : m = o} (a : PermOf n) :
    (a.cast hnm).cast hmo = a.cast (hnm.trans hmo) := rfl

theorem cast_inj {a b : PermOf n} {hnm : n = m} : a.cast hnm = b.cast hnm ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [PermOf.ext_iff, getElem_cast]
  refine fun H _ hi => ?_
  exact H (hnm ▸ hi)

theorem cast_injective (h : n = m) : Function.Injective (PermOf.cast h) := fun _ _ => cast_inj.mp

theorem cast_surjective (h : n = m) : Function.Surjective (PermOf.cast h) :=
  fun a => ⟨a.cast h.symm, a.cast_symm⟩

/--
When `n = m`, `PermOf n` is multiplicatively IsCongralent to `PermOf m`.
-/

@[simps! apply symm_apply]
def castMulEquiv (hnm : n = m) : PermOf n ≃* PermOf m where
  toFun := PermOf.cast hnm
  invFun := PermOf.cast hnm.symm
  left_inv a := a.cast_symm
  right_inv a := a.cast_symm
  map_mul' _ _ := (cast_mul hnm _ _).symm

@[simp] theorem cast_left_isCongr {n' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n = m} :
    (a.cast hnm).IsCongr b ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, cast_smul]

@[simp] theorem cast_right_isCongr {n' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n' = m} :
    a.IsCongr (b.cast hnm) ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, cast_smul]

theorem cast_isCongr_cast_iff_isCongr {n' m' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n = m} {hnm' : n' = m'} :
    (a.cast hnm).IsCongr (b.cast hnm') ↔ a.IsCongr b := by
  simp_rw [cast_left_isCongr, cast_right_isCongr]

theorem cast_isCongr_cast {k : ℕ}  {a : PermOf n} {hnm : n = m} {hnk : n = k} :
    (a.cast hnk).IsCongr (a.cast hnm) := by
  simp_rw [cast_isCongr_cast_iff_isCongr, isCongr_iff_eq]


end Cast

def castGE {m n : ℕ} (hnm : n ≤ m) (a : PermOf n) : PermOf m where
  fwdVector := (a.fwdVector ++ (Vector.range (m - n)).map (· + n)).cast (Nat.add_sub_cancel' hnm)
  bwdVector := (a.bwdVector ++ (Vector.range (m - n)).map (· + n)).cast (Nat.add_sub_cancel' hnm)
  getElem_fwdVector_lt := fun {i} him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_append, getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range]
    rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true]
      exact a.getElem_lt.trans_le hnm
    · simp_rw [hin.not_lt, dite_false, Nat.sub_add_cancel hin, him]
  getElem_bwdVector_getElem_fwdVector := fun {i} him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_append, getElem_fwdVector, Vector.getElem_map,
      Vector.getElem_range, getElem_bwdVector]
    rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true, a.getElem_lt, dite_true, getElem_inv_getElem]
    · simp_rw [hin.not_lt, dite_false, Nat.sub_add_cancel hin, hin.not_lt, dite_false]

section CastGE

variable {n m k i : ℕ} {a : PermOf n}

theorem getElem_castGE {i : ℕ} {hi : i < m} {hnm : n ≤ m} :
    (a.castGE hnm)[i] = if hi : i < n then a[i] else i := by
  unfold castGE
  simp_rw [getElem_mk, Vector.getElem_cast, Vector.getElem_append, getElem_fwdVector,
    Vector.getElem_map, Vector.getElem_range]
  exact dite_congr rfl (fun _ => rfl) (fun hin => Nat.sub_add_cancel (le_of_not_lt hin))

theorem getElem_castGE_of_lt {hnm : n ≤ m} {i : ℕ} (hi : i < n) :
    (a.castGE hnm)[i] = a[i] := by
  simp_rw [getElem_castGE, hi, dite_true]

@[simp]
theorem getElem_castGE_of_ge {hnm : n ≤ m} {i : ℕ} (hi : n ≤ i) {h : i < m} :
    (a.castGE hnm)[i] = i := by
  simp_rw [getElem_castGE, hi.not_lt, dite_false]

@[simp]
theorem inv_castGE {hnm : n ≤ m} :
    (a.castGE hnm)⁻¹ = a⁻¹.castGE hnm := rfl

theorem getElem_inv_castGE (hnm : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castGE hnm)⁻¹[i] = if hi : i < n then a⁻¹[i] else i :=
  a.inv_castGE ▸ a⁻¹.getElem_castGE

@[simp]
theorem castGE_one {hnm : n ≤ m} : ((1 : PermOf n).castGE hnm) = 1 := by
  ext i hi : 1
  simp_rw [getElem_castGE, getElem_one, dite_eq_ite, ite_self]

@[simp]
theorem castGE_smul {i : ℕ} {hnm : n ≤ m} :
    (a.castGE hnm) • i = a • i := by
  simp_rw [smul_eq_dite, getElem_castGE, dite_eq_ite, ite_eq_left_iff, not_lt]
  intro hmi
  simp_rw [(hnm.trans hmi).not_lt, dite_false]

@[simp]
theorem castGE_mul (hnm : n ≤ m) {a b : PermOf n} :
    a.castGE hnm * b.castGE hnm = (a * b).castGE hnm := by
  simp_rw [eq_iff_smul_eq_smul, mul_smul, castGE_smul, mul_smul, implies_true]

@[simp] theorem castGE_of_eq (hnm : n = m) (hnm' : n ≤ m := hnm.le) :
    a.castGE hnm' = a.cast hnm := by
  ext i hi
  simp_rw [getElem_castGE, getElem_cast, hi.trans_eq hnm.symm, dite_true]

@[simp] theorem castGE_trans {hnm : n ≤ m} {hmk : m ≤ k} :
    (a.castGE hnm).castGE hmk = a.castGE (hnm.trans hmk) := by
  ext i hi
  simp_rw [getElem_castGE]
  rcases lt_or_le i m with him | him
  · simp_rw [him, dite_true]
  · simp_rw [him.not_lt, (hnm.trans him).not_lt, dite_false]


@[simp]
theorem castGE_castGE_mul {l : ℕ} {a : PermOf n} {b : PermOf l} {hnm : n ≤ m} {hlm : l ≤ m}
    {hmk : m ≤ k} :
    (a.castGE hnm * b.castGE hlm).castGE hmk =
    a.castGE (hnm.trans hmk) * b.castGE (hlm.trans hmk) := by
  simp only [eq_iff_smul_eq_smul, mul_smul, castGE_smul, implies_true]

theorem castGE_mul_castGE_of_le {m : ℕ} {b : PermOf m} (hnm : n ≤ m) :
    (a.castGE (le_max_left _ _)) * (b.castGE (le_max_right _ _)) =
    ((a.castGE hnm) * b).castGE (le_max_right _ _) := by
  simp only [eq_iff_smul_eq_smul, mul_smul, castGE_smul, implies_true]

theorem castGE_mul_castGE_of_ge {m : ℕ} {b : PermOf m} (hmn : m ≤ n) :
    (a.castGE (le_max_left _ _)) * (b.castGE (le_max_right _ _)) =
    (a * b.castGE hmn).castGE (le_max_left _ _) := by
  simp only [eq_iff_smul_eq_smul, mul_smul, castGE_smul, implies_true]

theorem setAt_castGE {hnm : n ≤ m} (hnk : n ≤ k) : (a.castGE hnm).SetAt k :=
  setAt_of_lt_imp_getElem_lt (fun hik => by
    simp_rw [getElem_castGE]
    split_ifs with hin
    · exact a.getElem_lt.trans_le hnk
    · exact hik)

theorem setAt_castGE_eq {hnm : n ≤ m} : (a.castGE hnm).SetAt n := a.setAt_castGE le_rfl

theorem castGE_mem_setAtSubgroup {hnm : n ≤ m} (hnk : n ≤ k) :
    (a.castGE hnm) ∈ setAtSubgroup m k := a.setAt_castGE hnk

theorem castGE_mem_setAtSubgroup_eq {hnm : n ≤ m} :
    (a.castGE hnm) ∈ setAtSubgroup m n := a.setAt_castGE_eq

theorem castLE_lt_imp_getElem_lt {hnm : n ≤ m} (him : i < n) : (a.castGE hnm)[i] < n := by
  simp_rw [getElem_castGE, him, dite_true]
  exact a.getElem_lt

theorem castGE_inj {a b : PermOf n} {hnm : n ≤ m} : castGE hnm a = castGE hnm b ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [PermOf.ext_iff, getElem_castGE]
  refine fun H _ hi => ?_
  specialize H (hi.trans_le hnm)
  simp_rw [hi, dite_true] at H
  exact H

theorem castGE_injective (hnm : n ≤ m) : Function.Injective (castGE hnm) :=
  fun _ _ => castGE_inj.mp

@[simps! apply_coe]
def castGEMonoidHom (hnm : n ≤ m) : PermOf n →* setAtSubgroup m n where
  toFun a := ⟨a.castGE hnm, a.castGE_mem_setAtSubgroup_eq⟩
  map_mul' := fun _ _ => Subtype.ext (castGE_mul hnm).symm
  map_one' := Subtype.ext <| by simp_rw [castGE_one, Subgroup.coe_one]

theorem castGEMonoidHom_injective {hnm : n ≤ m} :
    (⇑(castGEMonoidHom hnm)).Injective :=
  fun _ _ h => castGE_injective hnm (Subtype.ext_iff.mp h)

@[simp] theorem castGE_isCongr {hnm : n ≤ m} :
    (a.castGE hnm).IsCongr a := by
  simp_rw [isCongr_iff_smul_eq, castGE_smul, implies_true]

@[simp] theorem isCongr_castGE {hnm : n ≤ m} : a.IsCongr (a.castGE hnm) :=
  castGE_isCongr.symm

@[simp] theorem castGE_isCongr_castGE_iff_isCongr {n' m' : ℕ} {b : PermOf n'}
    {hnm : n ≤ m} {hnm' : n' ≤ m'} :
    (a.castGE hnm).IsCongr (b.castGE hnm') ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, castGE_smul]

@[simp] theorem IsCongr.castGE_isCongr_castGE {n' m' : ℕ} {b : PermOf n'}
    {hnm : n ≤ m} {hnm' : n' ≤ m'} (hab : a.IsCongr b) :
    (a.castGE hnm).IsCongr (b.castGE hnm') := castGE_isCongr_castGE_iff_isCongr.mpr hab

theorem castGE_isCongr_castGE_rfl {hnm : n ≤ m} {hnk : n ≤ k} :
    (a.castGE hnk).IsCongr (a.castGE hnm) := isCongr_rfl.castGE_isCongr_castGE

theorem isCongr_iff_eq_castGE_of_le {b : PermOf m} (hnm : n ≤ m) :
    a.IsCongr b ↔ b = a.castGE hnm := by
  simp_rw [PermOf.ext_iff, getElem_castGE]
  simp_rw [isCongr_iff_smul_eq_of_lt, max_eq_left hnm, smul_eq_dite]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro i hi
    have H :=  dif_pos hi ▸ h hi
    exact H.symm
  · intro i hi
    have H := h hi
    simp_rw [hi, dite_true, H]

theorem isCongr_iff_eq_castGE_of_ge {b : PermOf m} (hmn : m ≤ n) :
    a.IsCongr b ↔ a = b.castGE hmn := by
  rw [isCongr_comm, isCongr_iff_eq_castGE_of_le hmn]

end CastGE

def castLE {m n : ℕ} (hmn : m ≤ n) (a : PermOf n) (ham : a.SetAt m) : PermOf m where
  fwdVector := (a.fwdVector.take m).cast (min_eq_left hmn)
  bwdVector := (a.bwdVector.take m).cast (min_eq_left hmn)
  getElem_fwdVector_lt := fun him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_take', getElem_fwdVector, ham.getElem_lt_of_lt him]
  getElem_bwdVector_getElem_fwdVector := fun _ => by
    simp_rw [Vector.getElem_cast, Vector.getElem_take', getElem_bwdVector_getElem_fwdVector]

section CastLE

variable {m i k : ℕ} (a : PermOf n) (ham : a.SetAt m) {hmn : m ≤ n}

@[simp] theorem getElem_castLE (him : i < m) :
    (a.castLE hmn ham)[i] = a[i] := by
  unfold castLE
  simp_rw [getElem_mk, Vector.getElem_cast, Vector.getElem_take', getElem_fwdVector]

theorem inv_castLE : (a.castLE hmn ham)⁻¹ = a⁻¹.castLE hmn ham.inv := rfl

theorem getElem_inv_castLE (him : i < m) :
    (a.castLE hmn ham)⁻¹[i] = a⁻¹[i]  := by
  simp_rw [inv_castLE, getElem_castLE]

@[simp]
theorem castLE_one : ((1 : PermOf n).castLE hmn setAt_one) = (1 : PermOf m) := by
  ext i hi : 1
  simp_rw [getElem_castLE, getElem_one]

theorem castLE_mul (hmn : m ≤ n) {a b : PermOf n} (ham : a.SetAt m) (hbm : b.SetAt m) :
    (a * b).castLE hmn (ham.mul hbm) = a.castLE hmn ham * b.castLE hmn hbm := by
  ext i
  simp only [getElem_mul, getElem_castLE]

@[simp] theorem castLE_of_eq {a : PermOf n} (ham : a.SetAt m) (hnm : n = m)
    (hnm' : m ≤ n := hnm.ge) : a.castLE hnm' ham = a.cast hnm := by
  ext i hi
  simp_rw [getElem_castLE, getElem_cast]

theorem SetAt.castLE {a : PermOf n} (ham : a.SetAt m) {hkn : k ≤ n} {hak : a.SetAt k} :
    (a.castLE hkn hak).SetAt m := setAt_of_lt_imp_getElem_lt (fun hik => by
    simp_rw [getElem_castLE]
    exact ham.getElem_lt_of_lt hik)

theorem castLE_trans {a : PermOf n} (ham : a.SetAt m) {hkn : k ≤ n} {hmk : m ≤ k}
    (hak : a.SetAt k) :
    (a.castLE hkn hak).castLE hmk ham.castLE = a.castLE (hmk.trans hkn) ham := by
  ext i hi
  simp_rw [getElem_castLE]

theorem castLE_castGE {hnm : n ≤ m} :
    (a.castGE hnm).castLE hnm a.setAt_castGE_eq = a := by
  ext i hi
  simp_rw [getElem_castLE, a.getElem_castGE_of_lt hi]

theorem getElem_castGE_castLE_of_lt (hi : i < m) : ((a.castLE hmn ham).castGE hmn)[i] = a[i] := by
  simp_rw [getElem_castGE_of_lt hi, getElem_castLE]

theorem castLE_surjective (hmn : m ≤ n) (b : PermOf m) :
    ∃ (a : PermOf n), ∃ (ham : a.SetAt m), a.castLE hmn ham = b := by
  exact ⟨_, _, b.castLE_castGE⟩

@[simps! apply]
def castLEMonoidHom (hmn : m ≤ n) : setAtSubgroup n m →* PermOf m where
  toFun a := castLE hmn a.1 a.2
  map_mul' a b := castLE_mul hmn a.2 b.2
  map_one' := castLE_one

theorem castLEMonoidHom_surjective {hmn : m ≤ n} :
  (⇑(castLEMonoidHom hmn)).Surjective := fun a => Subtype.exists.mpr (a.castLE_surjective hmn)

theorem castLE_smul_of_lt {i : ℕ} (him : i < m) :
    (a.castLE hmn ham) • i = a • i := by
  simp_rw [smul_of_lt _ him, smul_of_lt _ (him.trans_le hmn), getElem_castLE]

end CastLE

def castSucc (a : PermOf n) : PermOf (n + 1) := a.castGE (Nat.le_succ _)

section CastSucc

variable {n m k i : ℕ} {a : PermOf n}

theorem getElem_castSucc {i : ℕ} {hi : i < n + 1} :
    (a.castSucc)[i] = if hi : i = n then n else a[i] := by
  unfold castSucc
  simp_rw [getElem_castGE, ← (Nat.le_of_lt_succ hi).ge_iff_eq]
  rcases lt_or_le i n with hi' | hi'
  · simp_rw [dif_pos hi', dif_neg hi'.not_le]
  · simp_rw [dif_pos hi', dif_neg hi'.not_lt, ← hi'.le_iff_eq, Nat.le_of_lt_succ hi]

theorem getElem_castSucc_of_lt {i : ℕ} (hi : i < n) :
    (a.castSucc)[i] = a[i] := by
  simp_rw [getElem_castSucc, hi.ne, dite_false]

theorem getElem_castSucc_of_eq : (a.castSucc)[n] = n := by
  simp_rw [getElem_castSucc, dite_true]

@[simp]
theorem inv_castSucc :
    (a.castSucc)⁻¹ = a⁻¹.castSucc := rfl

theorem getElem_inv_castSucc {i : ℕ} {hi : i < n + 1} :
    (a.castSucc)⁻¹[i] = if hi : i = n then n else a⁻¹[i] :=
  a.inv_castSucc ▸ a⁻¹.getElem_castSucc

@[simp]
theorem castSucc_one : (1 : PermOf n).castSucc = 1 := castGE_one

@[simp]
theorem castSucc_mul {a b : PermOf n} :
    a.castSucc * b.castSucc = (a * b).castSucc := castGE_mul _

@[simp] theorem castSucc_castSucc :
    a.castSucc.castSucc = a.castGE (by omega) := castGE_trans

@[simp] theorem castGE_castSucc (h : n ≤ m) :
    (a.castGE h).castSucc = a.castGE (h.trans (Nat.le_succ _)) := castGE_trans

@[simp] theorem castSucc_castGE (h : n + 1 ≤ m) :
    a.castSucc.castGE h = a.castGE ((Nat.le_succ _).trans h) := castGE_trans

theorem setAt_castSucc (hnk : n ≤ k) : a.castSucc.SetAt k := setAt_castGE hnk

theorem setAt_castSucc_eq : (a.castSucc).SetAt n := a.setAt_castSucc le_rfl

theorem castSucc_mem_setAtSubgroup (hnk : n ≤ k) :
    a.castSucc ∈ setAtSubgroup (n + 1) k := a.setAt_castGE hnk

theorem castSucc_mem_setAtSubgroup_eq :
    a.castSucc ∈ setAtSubgroup (n + 1) n := a.setAt_castGE_eq

theorem castSucc_lt_imp_getElem_lt (hi : i < n) : (a.castSucc)[i] < n := by
  simp_rw [getElem_castSucc, hi.ne, dite_false]
  exact a.getElem_lt

theorem castSucc_inj {a b : PermOf n} : a.castSucc = b.castSucc ↔ a = b := castGE_inj

theorem castSucc_injective : Function.Injective (castSucc (n := n)) :=
  fun _ _ => castSucc_inj.mp

@[simps! apply_coe]
def castSuccMonoidHom : PermOf n →* setAtSubgroup (n + 1) n where
  toFun a := ⟨a.castSucc, a.castSucc_mem_setAtSubgroup_eq⟩
  map_mul' := fun _ _ => Subtype.ext castSucc_mul.symm
  map_one' := Subtype.ext <| by simp_rw [castSucc_one, Subgroup.coe_one]

theorem castSuccMonoidHom_injective :
    (⇑(castSuccMonoidHom (n := n))).Injective :=
  fun _ _ h => castSucc_injective (Subtype.ext_iff.mp h)

@[simp]
theorem castSucc_smul {i : ℕ} :
    a.castSucc • i = a • i := castGE_smul

@[simp] theorem castSucc_isCongr :
  a.castSucc.IsCongr a := by simp_rw [isCongr_iff_smul_eq, castSucc_smul, implies_true]

@[simp] theorem isCongr_castSucc : a.IsCongr a.castSucc :=
  castSucc_isCongr.symm

@[simp] theorem castSucc_isCongr_castSucc_iff_isCongr {n' : ℕ} {b : PermOf n'} :
    a.castSucc.IsCongr b.castSucc ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, castSucc_smul]

theorem castSucc_isCongr_castSucc :
    a.castSucc.IsCongr a.castSucc := by
  simp_rw [castSucc_isCongr_castSucc_iff_isCongr, isCongr_iff_eq]

end CastSucc

def castPred (a : PermOf (n + 1)) (ha : a[n] = n) : PermOf n :=
    a.castLE (Nat.le_succ _) (a.setAt_of_getElem_eq_self ha)

section CastPred

variable {m i k : ℕ} (a : PermOf (n + 1)) (ha : a[n] = n)

@[simp] theorem getElem_castPred (him : i < n) :
    (a.castPred ha)[i] = a[i] := getElem_castLE _ _ _

@[simp] theorem castPred_inv {ha : a⁻¹[n] = n} : a⁻¹.castPred ha =
    (a.castPred ((a.getElem_inv_eq_iff _ _).mp ha).symm)⁻¹ := rfl

theorem getElem_inv_castPred (hi : i < n) :
    (a.castPred ha)⁻¹[i] = a⁻¹[i]  := getElem_inv_castLE _ _ _

@[simp]
theorem castPred_one :
    ((1 : PermOf (n + 1)).castPred (getElem_one _)) = (1 : PermOf n) := castLE_one

@[simp]
theorem castPred_mul' {a b : PermOf (n + 1)} (hb : b[n] = n) {hab : (a * b)[n] = n} :
    (a * b).castPred hab =
    a.castPred (by simpa only [getElem_mul, hb] using hab) * b.castPred hb :=
  castLE_mul _ _ _

theorem castPred_mul {a b : PermOf (n + 1)} (ha : a[n] = n) (hb : b[n] = n) :
    (a * b).castPred (by simp_rw [getElem_mul, hb, ha]) = a.castPred ha * b.castPred hb :=
  castLE_mul _ _ _

theorem SetAt.castPred {a : PermOf (n + 1)} (ha : a[n] = n) {hak : a.SetAt m} :
    (a.castPred ha).SetAt m := SetAt.castLE hak

theorem castPred_trans {a : PermOf (n + 2)} (ha₁ : a[n + 1] = n + 1)
    (ha₂ : a[n] = n) :
    (a.castPred ha₁).castPred (by simp_rw [getElem_castPred, ha₂]) =
    a.castLE (Nat.le_add_right _ _) (a.setAt_of_getElem_eq_getElem_eq ha₁ ha₂):= castLE_trans _ _

@[simp] theorem castPred_castSucc {a : PermOf n} :
    a.castSucc.castPred getElem_castSucc_of_eq = a := castLE_castGE _

theorem getElem_castSucc_castPred_of_lt (hi : i < n) :
    ((a.castPred ha).castSucc)[i] = a[i] := getElem_castGE_castLE_of_lt _ _ hi

theorem castPred_surjective (b : PermOf n) :
    ∃ (a : PermOf (n + 1)), ∃ (ha : a[n] = n), a.castPred ha = b :=
  ⟨_, _, b.castPred_castSucc⟩

@[simps! apply]
def castPredMonoidHom : setAtSubgroup (n + 1) n →* PermOf n where
  toFun  := fun ⟨a, h⟩ => a.castPred h.getElem_eq_self
  map_mul' a b := castPred_mul a.2.getElem_eq_self b.2.getElem_eq_self
  map_one' := by simp_rw [castPred_one]

theorem castPredMonoidHom_surjective :
  (⇑(castPredMonoidHom (n := n))).Surjective := fun a => Subtype.exists.mpr
    (by rcases a.castPred_surjective with ⟨b, hb, h⟩ ;
        exact ⟨b, setAt_of_getElem_eq_self hb, h⟩)

theorem castPred_smul_of_lt {i : ℕ} (hi : i < n) :
    (a.castPred ha) • i = a • i := castLE_smul_of_lt _ _ hi

theorem castPred_smul_of_eq : (a.castPred ha) • n = a • n := by
  rw [smul_of_ge _ le_rfl, smul_of_lt _ (Nat.lt_succ_self _), ha]

@[simp] theorem castPred_isCongr : (a.castPred ha).IsCongr a := by
  simp_rw [isCongr_iff_smul_eq_of_lt, sup_of_le_left (Nat.le_succ _), Nat.lt_succ_iff,
    le_iff_eq_or_lt]
  rintro i (rfl | hi)
  · simp_rw [castPred_smul_of_eq]
  · exact castPred_smul_of_lt _ _ hi

@[simp] theorem isCongr_castPred : a.IsCongr (a.castPred ha) :=
  (a.castPred_isCongr ha).symm

theorem castPred_cast {hnm : n + 1 = m + 1} {ha : (a.cast hnm)[m] = m} :
    (a.cast hnm).castPred ha =
    (a.castPred (by rw [getElem_cast] at ha ; simp_rw [Nat.succ_injective hnm, ha])).cast
    (Nat.succ_injective hnm) := by
  ext
  simp_rw [getElem_cast, getElem_castPred, getElem_cast]

end CastPred

def castOfSetAt {m n : ℕ} (a : PermOf n) (ham : a.SetAt m) :
    PermOf m where
  fwdVector := ((a.fwdVector.take m) ++ (Vector.range (m - n)).map (· + n)).cast
    (Nat.add_comm _ _ ▸ Nat.sub_add_min_cancel m n)
  bwdVector := ((a.bwdVector.take m) ++ (Vector.range (m - n)).map (· + n)).cast
    (Nat.add_comm _ _ ▸ Nat.sub_add_min_cancel m n)
  getElem_fwdVector_lt := fun {i} him => by
    simp_rw [Vector.getElem_cast]
    simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take', getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range, getElem_bwdVector, him, true_and]
    rcases lt_or_le m n with hmn | hmn
    · simp_rw [him.trans hmn, dite_true]
      exact ham.getElem_lt_of_lt him
    · rcases lt_or_le i n with hin | hin
      · simp_rw [hin, dite_true]
        exact a.getElem_lt.trans_le hmn
      · simp_rw [hin.not_lt, dite_false, min_eq_right hmn, Nat.sub_add_cancel hin, him]
  getElem_bwdVector_getElem_fwdVector := fun {i} him => by
    simp_rw [Vector.getElem_cast]
    simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take', getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range, getElem_bwdVector, him, true_and]
    rcases lt_or_le m n with hmn | hmn
    · simp_rw [him.trans hmn, dite_true, getElem_lt, and_true, getElem_inv_getElem,
        ham.getElem_lt_of_lt him, dite_true]
    · rcases lt_or_le i n with hin | hin
      · simp_rw [hin, dite_true, getElem_lt, and_true, getElem_inv_getElem,
          ham.getElem_lt_of_lt him, dite_true]
      · simp_rw [hin.not_lt, dite_false, min_eq_right hmn, Nat.sub_add_cancel hin,
          hin.not_lt, and_false, dite_false]

section CastOfSetAt

variable {m i : ℕ} (a : PermOf n) (ham : a.SetAt m)

@[simp] theorem getElem_castOfSetAt (him : i < m) :
    (a.castOfSetAt ham)[i] = if hin : i < n then a[i] else i := by
  unfold castOfSetAt
  simp_rw [getElem_mk, Vector.getElem_cast]
  simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take', getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range, getElem_bwdVector, him, true_and]
  rcases lt_or_le m n with hmn | hmn
  · simp_rw [him.trans hmn, dite_true]
  · rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true]
    · simp_rw [hin.not_lt, dite_false, min_eq_right hmn, Nat.sub_add_cancel hin]

@[simp] theorem castOfSmulSetAt_inv :
    (a.castOfSetAt ham)⁻¹ = a⁻¹.castOfSetAt ham.inv := by
  ext
  unfold castOfSetAt
  simp_rw [getElem_inv_mk, inv_fwdVector, inv_bwdVector, getElem_mk]

theorem getElem_castOfSetAt_inv (him : i < m) :
    (a.castOfSetAt ham)⁻¹[i] = if hin : i < n then a⁻¹[i] else i := by
  simp_rw [castOfSmulSetAt_inv, getElem_castOfSetAt]

theorem castOfSetAt_eq_cast (hnm : n = m) :
    a.castOfSetAt ham = a.cast hnm := by
  ext _ hi
  simp_rw [getElem_castOfSetAt, getElem_cast, hnm ▸ hi, dite_true]

theorem castOfSetAt_eq_castGE (hnm : n ≤ m) :
    a.castOfSetAt ham = a.castGE hnm := by
  ext _ hi
  simp_rw [getElem_castOfSetAt, getElem_castGE]

theorem castOfSetAt_eq_castLT (hmn : m ≤ n) :
    a.castOfSetAt ham = a.castLE hmn ham := by
  ext _ hi
  simp_rw [getElem_castOfSetAt, getElem_castLE, hi.trans_le hmn, dite_true]

@[simp]
theorem castOfSetAt_one : ((1 : PermOf n).castOfSetAt setAt_one) = (1 : PermOf m) := by
  ext i hi : 1
  simp_rw [getElem_castOfSetAt, getElem_one, dite_eq_ite, ite_self]

@[simp]
theorem castOfSetAt_mul {a b : PermOf n} (ham : a.SetAt m) (hbm : b.SetAt m)
    (habm := SetAt.mul ham hbm) :
    (a * b).castOfSetAt habm = a.castOfSetAt ham * b.castOfSetAt hbm := by
  ext i
  simp only [getElem_mul, getElem_castOfSetAt]
  rcases lt_or_le i n with hi | hi
  · simp only [hi, dite_true, getElem_lt]
  · simp only [hi.not_lt, dite_false]

theorem setAt_castOfSetAt {a : PermOf n} {ha : a.SetAt m} :
    (a.castOfSetAt ha).SetAt n := setAt_of_lt_imp_getElem_lt <| fun hi _ => by
  simp_rw [getElem_castOfSetAt, hi, dite_true, getElem_lt]

theorem SetAt.castOfSetAt_of_le {a : PermOf n} {ham : a.SetAt m} (hnm : n ≤ m) :
    (a.castOfSetAt ham).castOfSetAt setAt_castOfSetAt = a := ext <| fun {i} hin => by
  simp_rw [getElem_castOfSetAt, dite_eq_ite, hin, dite_true, ite_eq_left_iff, not_lt]
  intro him
  exact (hnm.not_lt (him.trans_lt hin)).elim

theorem castOfSetAt_surjective_of_le (hmn : m ≤ n) {b : PermOf m} (hbm : b.SetAt n) :
    ∃ (a : PermOf n), ∃ (han : a.SetAt m), a.castOfSetAt han = b :=
  ⟨_, _, hbm.castOfSetAt_of_le hmn⟩

theorem castOfSetAt_inj_of_ge {a b : PermOf n} (hnm : n ≤ m) :
    a.castOfSetAt (a.setAt_ge hnm) = b.castOfSetAt (b.setAt_ge hnm) ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [PermOf.ext_iff, getElem_castOfSetAt]
  refine fun H _ hi => ?_
  specialize H (hi.trans_le hnm)
  simp_rw [hi, dite_true] at H
  exact H

theorem castOfSetAt_injective_of_ge (hnm : n ≤ m) :
    Function.Injective (fun (a : PermOf n) => a.castOfSetAt (a.setAt_ge hnm)) :=
  fun _ _ => (castOfSetAt_inj_of_ge hnm).mp

theorem castOfSetAt_bijective_of_eq (hmn : m = n) :
    Function.Bijective (fun (a : PermOf n) =>
    (a.castOfSetAt (hmn ▸ a.setAt_eq) : PermOf m)) :=
  ⟨castOfSetAt_injective_of_ge hmn.ge,
    fun b => ⟨_, (hmn ▸ b.setAt_eq : b.SetAt n).castOfSetAt_of_le hmn.le⟩⟩

@[simps! apply_coe]
def castOfSetAtMonoidHom (n m : ℕ) : setAtSubgroup n m →* setAtSubgroup m n where
  toFun a := ⟨a.1.castOfSetAt a.2, setAt_castOfSetAt⟩
  map_one' := Subtype.ext castOfSetAt_one
  map_mul' a b := Subtype.ext (castOfSetAt_mul a.2 b.2)

theorem castOfSetAtMonoidHom_surjective_of_le (hmn : m ≤ n) :
    Surjective (castOfSetAtMonoidHom n m) := fun b => by
  simp_rw [Subtype.exists, mem_setAtSubgroup_iff, Subtype.ext_iff]
  exact castOfSetAt_surjective_of_le hmn b.2

theorem castOfSetAtMonoidHom_injective_of_ge (hnm : n ≤ m) :
    Injective (castOfSetAtMonoidHom n m) := fun a b => by
  simp_rw [Subtype.ext_iff, castOfSetAtMonoidHom_apply_coe,
    castOfSetAt_inj_of_ge hnm, imp_self]

theorem castOfSetAtMonoidHom_bijective_of_eq (hmn : m = n) :
    Bijective (castOfSetAtMonoidHom n m) :=
  ⟨castOfSetAtMonoidHom_injective_of_ge hmn.ge, castOfSetAtMonoidHom_surjective_of_le hmn.le⟩

@[simps! apply_coe symm_apply_coe]
def castOfSetAtMulEquivEq (hmn : m = n) : setAtSubgroup n m ≃* setAtSubgroup m n where
  toFun := castOfSetAtMonoidHom n m
  invFun := castOfSetAtMonoidHom m n
  left_inv a := Subtype.ext <| by
    simp_rw [castOfSetAtMonoidHom_apply_coe]
    exact SetAt.castOfSetAt_of_le hmn.ge
  right_inv a := Subtype.ext <| by
    simp_rw [castOfSetAtMonoidHom_apply_coe]
    exact SetAt.castOfSetAt_of_le hmn.le
  map_mul' a b := map_mul _ _ _

theorem castOfSetAt_smul_eq_smul_of_lt {i : ℕ} (hi : i < m) :
    (a.castOfSetAt ham) • i = a • i := by
  simp_rw [smul_of_lt _ hi, getElem_castOfSetAt]
  rcases lt_or_le i n with hin | hin
  · simp_rw [hin, dite_true, smul_of_lt _ hin]
  · simp_rw [hin.not_lt, dite_false, smul_of_ge _ hin]

end CastOfSetAt


open Perm in
/--
`natPerm` is the  monoid homomorphism from `PermOf n` to `Perm ℕ`.
-/
@[simps!]
def natPerm {n : ℕ} : PermOf n →* Perm ℕ where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  map_one' := by
    simp_rw [Equiv.ext_iff, inv_one, one_smul, coe_fn_mk, one_apply, implies_true]
  map_mul' := by
    simp_rw [Equiv.ext_iff, mul_inv_rev, mul_smul, mul_apply, coe_fn_mk, implies_true]

section NatPerm

open Perm

theorem natPerm_mem_natFixGE {a : PermOf n} : natPerm a ∈ NatFixGE n :=
  mem_natFixGE_iff.mpr (fun _ => smul_of_ge _)

theorem natPerm_lt_iff_lt (a : PermOf n) {i : ℕ} : natPerm a i < n ↔ i < n := by
  rw [natPerm_apply_apply, smul_lt_iff_lt]

theorem natPerm_apply_apply_of_lt (a : PermOf n) {i : ℕ} (h : i < n) :
    natPerm a i = a[i] := by rw [natPerm_apply_apply, a.smul_of_lt h]

theorem natPerm_apply_apply_of_ge (a : PermOf n) {i : ℕ} : n ≤ i → natPerm a i = i :=
  fixed_ge_of_mem_natFixGE natPerm_mem_natFixGE _

theorem natPerm_apply_symm_apply_of_lt (a : PermOf n) {i : ℕ} (h : i < n) :
    (natPerm a)⁻¹ i = a⁻¹[i] := by
  simp_rw [← MonoidHom.map_inv, natPerm_apply_apply_of_lt _ h]

theorem natPerm_apply_symm_apply_of_ge (a : PermOf n) {i : ℕ} (h : n ≤ i) :
    (natPerm a)⁻¹ i = i := by rw [← MonoidHom.map_inv, natPerm_apply_apply_of_ge _ h]

@[simp]
theorem natPerm_eq_iff_isCongr {a : PermOf n} {m : ℕ} {b : PermOf m} :
    a.natPerm = b.natPerm ↔ a.IsCongr b := by
  simp_rw [Equiv.ext_iff, natPerm_apply_apply, isCongr_iff_smul_eq]

theorem natPerm_injective : Function.Injective (natPerm (n := n)) := fun _ _ h => by
  simp_rw [natPerm_eq_iff_isCongr, isCongr_iff_eq] at h
  exact h

theorem natPerm_inj {a b : PermOf n} : natPerm a = natPerm b ↔ a = b :=
  natPerm_injective.eq_iff

theorem IsCongr.natPerm_eq {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.IsCongr b) : a.natPerm = b.natPerm := natPerm_eq_iff_isCongr.mpr hab

theorem natPerm_swap (a : PermOf n) {i j hi hj} :
    natPerm (swap a i j hi hj) = natPerm a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, natPerm_apply_apply, swap_smul_eq_smul_swap]

@[simp]
theorem natPerm_one_swap {i j hi hj} :
    natPerm (n := n) (swap 1 i j hi hj) = Equiv.swap i j := by
  simp_rw [natPerm_swap, map_one, one_mul]

end NatPerm


open Equiv.Perm in
/--
`PermOf n` is IsCongralent to `Perm (Fin n)`, and this IsCongralence respects the
multiplication (and, indeed, the scalar action on `Fin n`).
-/
@[simps! apply_apply_val apply_symm_apply_val]
def finPerm (n : ℕ) : PermOf n ≃* Perm (Fin n) where
  toFun a := ⟨(⟨a • ·, a.smul_fin_lt⟩), (⟨a⁻¹ • ·, a⁻¹.smul_fin_lt⟩),
    fun i => Fin.ext (inv_smul_smul _ _), fun i => Fin.ext (smul_inv_smul _ _)⟩
  invFun π := ⟨Vector.ofFn (Fin.val ∘ π), Vector.ofFn (Fin.val ∘ π.symm),
    fun _ => (Array.getElem_ofFn _ _ _).trans_lt (Fin.is_lt _),
    fun _ => by simp_rw [Vector.getElem_ofFn, comp_apply, Fin.eta, symm_apply_apply]⟩
  left_inv a := PermOf.ext <| fun hi => by simp_rw [coe_fn_mk, coe_fn_symm_mk, getElem_mk,
    Vector.getElem_ofFn, comp_apply, a.smul_of_lt hi]
  right_inv π := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [coe_fn_mk, smul_fin, getElem_mk,
    Vector.getElem_ofFn, Fin.eta, comp_apply]
  map_mul' a b := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [mul_inv_rev, Perm.coe_mul,
    comp_apply, coe_fn_mk, mul_smul]

section FinPerm

@[simp]
theorem finPerm_symm_apply_getElem (π : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    ((finPerm n).symm π)[i] = π ⟨i, hi⟩ := by
  unfold finPerm
  simp_rw [MulEquiv.symm_mk, MulEquiv.coe_mk, coe_fn_symm_mk, getElem_mk, Vector.getElem_ofFn,
    comp_apply]

@[simp]
theorem finPerm_symm_apply_getElem_inv (π : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    ((finPerm n).symm π)⁻¹[i] = π⁻¹ ⟨i, hi⟩ := by
  rw [← map_inv, finPerm_symm_apply_getElem]

instance : Fintype (PermOf n) := Fintype.ofEquiv (Perm (Fin n)) (finPerm n).symm.toEquiv

theorem natPerm_eq_extendDomainHom_comp_finPerm {n : ℕ} :
    natPerm (n := n) = (Perm.extendDomainHom Fin.equivSubtype).comp
    (finPerm n : PermOf _ →* Equiv.Perm (Fin n)) := by
  ext a i
  simp_rw [natPerm_apply_apply, MonoidHom.comp_apply,
    MonoidHom.coe_coe, Perm.extendDomainHom_apply]
  rcases lt_or_le i n with hi | hi
  · simp_rw [Perm.extendDomain_apply_subtype _ Fin.equivSubtype hi, a.smul_of_lt hi,
      Fin.equivSubtype_symm_apply, Fin.equivSubtype_apply, finPerm_apply_apply_val]
  · simp_rw [Perm.extendDomain_apply_not_subtype _ Fin.equivSubtype hi.not_lt, a.smul_of_ge hi]

end FinPerm

open Perm in
/--
`ofNatSepAt` maps a member of `Perm ℕ` which maps the subtype `< n` to itself to the corresponding
`PermOf n`.
-/
def ofNatSepAt : NatSepAt n →* PermOf n where
  toFun e := {
    fwdVector := (Vector.range n).map e
    bwdVector := (Vector.range n).map ⇑e.1⁻¹
    getElem_fwdVector_lt := fun {i} => by
      simp_rw [Vector.getElem_map, Vector.getElem_range]
      exact e.2 _
    getElem_bwdVector_getElem_fwdVector := by
      simp only [Vector.getElem_map, Vector.getElem_range, Perm.inv_apply_self, implies_true]}
  map_one' := by
    simp_rw [PermOf.ext_iff, getElem_mk, OneMemClass.coe_one, Vector.getElem_map, one_apply,
      Vector.getElem_range, getElem_one, implies_true]
  map_mul' a b := by
    simp_rw [PermOf.ext_iff, getElem_mul, getElem_mk, Vector.getElem_map,
      Vector.getElem_range, Subgroup.coe_mul, mul_apply, implies_true]

section ofNatSepAt

open Perm

@[simp]
theorem getElem_ofNatSepAt {e : NatSepAt n} {i : ℕ}
    (hi : i < n) : (ofNatSepAt e)[i] = e.1 i := by
  unfold ofNatSepAt
  simp_rw [MonoidHom.coe_mk, OneHom.coe_mk, getElem_mk,
    Vector.getElem_map, Vector.getElem_range]

@[simp]
theorem getElem_ofNatSepAt_inv {e : NatSepAt n} {i : ℕ} (hi : i < n) :
    (ofNatSepAt e)⁻¹[i] = e.1⁻¹ i := by
  unfold ofNatSepAt
  simp_rw [MonoidHom.coe_mk, OneHom.coe_mk, getElem_inv_mk,
    Vector.getElem_map, Vector.getElem_range]

theorem ofNatSepAt_smul {e : NatSepAt n} {i : ℕ} :
    (ofNatSepAt e) • i = if i < n then e.1 i else i := by
  simp_rw [smul_eq_dite, getElem_ofNatSepAt, dite_eq_ite]

theorem ofNatSepAt_surjective : Function.Surjective (ofNatSepAt (n := n)) := by
  intro a
  let b : NatSepAt n := ⟨⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩,
    fun _ => a.smul_lt_of_lt⟩
  refine ⟨b, PermOf.ext ?_⟩
  simp_rw [getElem_ofNatSepAt]
  exact a.smul_of_lt

theorem ker_ofNatSepAt : (ofNatSepAt (n := n)).ker = (NatFixLT n).subgroupOf (NatSepAt n) := by
  simp_rw [SetLike.ext_iff, MonoidHom.mem_ker, Subgroup.mem_subgroupOf, PermOf.ext_iff,
    getElem_one, getElem_ofNatSepAt, mem_natFixLT_iff, implies_true]

theorem natPerm_ofNatSepAt_apply {e : NatSepAt n} (i : ℕ) :
    natPerm (ofNatSepAt e) i = if i < n then e.1 i else i := by
  simp_rw [natPerm_apply_apply, ofNatSepAt_smul]

theorem natPerm_ofNatSepAt_of_mem_natFixGE {e : Perm ℕ} :
   (he : e ∈ NatFixGE n) → natPerm (ofNatSepAt ⟨e, natFixGE_le_natSepAt he⟩) = e := by
  simp_rw [Equiv.ext_iff, natPerm_ofNatSepAt_apply, ite_eq_left_iff, not_lt,
    eq_comm (b := e _)]
  exact fixed_ge_of_mem_natFixGE

theorem ofNatSepAt_natPerm {a : PermOf n} :
    ofNatSepAt ⟨natPerm a, natFixGE_le_natSepAt natPerm_mem_natFixGE⟩ = a := by
  ext i hi
  simp_rw [getElem_ofNatSepAt, a.natPerm_apply_apply_of_lt hi]

theorem exists_natPerm_apply_iff_mem_natFixGE {e : Perm ℕ} :
    (∃ a : PermOf n, natPerm a = e) ↔ e ∈ NatFixGE n := by
  refine ⟨?_, fun he => ?_⟩
  · rintro ⟨a, rfl⟩ _ hi
    exact a.natPerm_apply_apply_of_ge hi
  · exact ⟨ofNatSepAt ⟨e, natFixGE_le_natSepAt he⟩, natPerm_ofNatSepAt_of_mem_natFixGE he⟩

theorem range_natPerm : MonoidHom.range (natPerm (n := n)) = NatFixGE n := by
  simp_rw [SetLike.ext_iff, MonoidHom.mem_range,
    exists_natPerm_apply_iff_mem_natFixGE, implies_true]

end ofNatSepAt

open Perm in
@[simps! apply symm_apply]
def mulEquivNatFixGE : PermOf n ≃* NatFixGE n :=
  MonoidHom.toMulEquiv
  (natPerm.codRestrict _ (fun _ => natPerm_mem_natFixGE))
  (ofNatSepAt.comp (SubgroupClass.inclusion natFixGE_le_natSepAt))
  (by simp_rw [MonoidHom.ext_iff, MonoidHom.comp_apply,
      MonoidHom.codRestrict_apply, SubgroupClass.inclusion_mk,
      MonoidHom.id_apply, ofNatSepAt_natPerm, implies_true])
  (by simp_rw [MonoidHom.ext_iff, MonoidHom.comp_apply,
      MonoidHom.codRestrict_apply, Subtype.forall,
      SubgroupClass.inclusion_mk, MonoidHom.id_apply, Subtype.mk.injEq]
      exact fun _ => natPerm_ofNatSepAt_of_mem_natFixGE)

section MulEquivNatFixGE

open Equiv.Perm

theorem mulEquivNatFixGE_castGE {a : PermOf n} (hnm : n ≤ m) :
    (mulEquivNatFixGE (a.castGE hnm)) =
    Subgroup.inclusion (natFixGE_mono hnm) (mulEquivNatFixGE a) := by
  simp_rw [mulEquivNatFixGE_apply, Subtype.ext_iff, Subgroup.coe_inclusion,
    natPerm_eq_iff_isCongr, castGE_isCongr]

@[simp]
theorem getElem_mulEquivNatFixGE_symm_mk {e : Perm ℕ} (he : e ∈ NatFixGE n) {i : ℕ} (hi : i < n) :
    (mulEquivNatFixGE.symm ⟨e, he⟩)[i] = e i := by
  unfold mulEquivNatFixGE
  simp_rw [MonoidHom.toMulEquiv_symm_apply, MonoidHom.comp_apply,
    SubgroupClass.inclusion_mk, getElem_ofNatSepAt]

@[simp]
theorem getElem_mulEquivNatFixGE_symm_inv_mk {e : Perm ℕ} (he : e ∈ NatFixGE n)
    {i : ℕ} (hi : i < n) : (mulEquivNatFixGE.symm ⟨e, he⟩)⁻¹[i] = e⁻¹ i := by
  unfold mulEquivNatFixGE
  simp_rw [MonoidHom.toMulEquiv_symm_apply, MonoidHom.comp_apply,
    SubgroupClass.inclusion_mk, getElem_ofNatSepAt_inv]

end MulEquivNatFixGE

def minLen {n : ℕ} (a : PermOf n) : ℕ := match n with
  | 0 => 0
  | (n + 1) => if ha : a[n] = n then (a.castPred ha).minLen else n + 1

section MinLen

@[simp] theorem minLen_zero {a : PermOf 0} : a.minLen = 0 := rfl

theorem minLen_succ {a : PermOf (n + 1)} :
    a.minLen = if ha : a[n] = n then (a.castPred ha).minLen else n + 1 := rfl

theorem minLen_succ_of_getElem_eq {a : PermOf (n + 1)} (ha : a[n] = n) :
    a.minLen = (a.castPred ha).minLen := by
  simp_rw [minLen_succ, ha, dite_true]

theorem minLen_succ_of_getElem_ne {a : PermOf (n + 1)} (ha : a[n] ≠ n) :
    a.minLen = n + 1 := by
  simp_rw [minLen_succ, ha, dite_false]

@[simp] theorem minLen_le {a : PermOf n} : a.minLen ≤ n := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero, le_rfl]
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha]
      exact IH.trans (Nat.le_succ _)
    · simp_rw [minLen_succ_of_getElem_ne ha, le_rfl]

@[simp] theorem minLen_eq_iff {a : PermOf n} : a.minLen = n ↔ ∀ (hn : n ≠ 0),
    a[n - 1]'(Nat.pred_lt hn) ≠ n - 1 := by
  simp_rw [← minLen_le.ge_iff_eq]
  cases n with | zero => _ | succ n => _
  · simp_rw [minLen_zero, le_rfl, ne_eq, not_true_eq_false, IsEmpty.forall_iff]
  · simp_rw [Nat.add_sub_cancel, ne_eq, Nat.succ_ne_zero, not_false_eq_true, forall_true_left]
    by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha, ha, not_true_eq_false, iff_false, not_le,
        Nat.lt_succ_iff]
      exact minLen_le
    · simp_rw [minLen_succ_of_getElem_ne ha, le_rfl, ha, not_false_eq_true]

@[simp] theorem succ_minLen_le_of_getElem_eq {a : PermOf (n + 1)} (ha : a[n] = n) :
    a.minLen ≤ n := by simp_rw [minLen_succ_of_getElem_eq ha, minLen_le]

@[simp] theorem minLen_one : (1 : PermOf n).minLen = 0 := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · rw [minLen_succ_of_getElem_eq (getElem_one _), castPred_one, IH]

theorem eq_one_of_minLen_eq_zero {a : PermOf n} (ha : a.minLen = 0) : a = 1 := by
  induction n with | zero => _ | succ n IH => _
  · exact Subsingleton.elim _ _
  · by_cases ha' : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha'] at ha
      have ha := IH ha
      simp_rw [PermOf.ext_iff, getElem_one, getElem_castPred] at ha
      simp_rw [PermOf.ext_iff, getElem_one, Nat.lt_succ_iff, le_iff_lt_or_eq]
      exact fun _ hi => hi.elim ha (fun hi => hi ▸ ha')
    · simp_rw [minLen_succ_of_getElem_ne ha', Nat.succ_ne_zero] at ha

@[simp] theorem minLen_eq_zero_iff_eq_one {a : PermOf n} : a.minLen = 0 ↔ a = 1 :=
  ⟨eq_one_of_minLen_eq_zero, fun h => h ▸ minLen_one⟩

@[simp] theorem minLen_inv {a : PermOf n} : a⁻¹.minLen = a.minLen := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha,
        minLen_succ_of_getElem_eq (getElem_inv_eq_self_of_getElem_eq_self ha), castPred_inv, IH]
    · simp_rw [minLen_succ_of_getElem_ne ha,
        minLen_succ_of_getElem_ne (getElem_inv_ne_self_of_getElem_ne_self ha)]

@[simp] theorem minLen_cast {m : ℕ} {a : PermOf n} {hnm : n = m} :
    (a.cast hnm).minLen = a.minLen := by
  cases hnm
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · simp_rw [minLen_succ, getElem_cast, castPred_cast, IH]

theorem minLen_castPred {a : PermOf (n + 1)} {ha : a[n] = n} :
    (a.castPred ha).minLen = a.minLen := (minLen_succ_of_getElem_eq _).symm

theorem minLen_castSucc {a : PermOf n} :
    a.castSucc.minLen = a.minLen := by
  rw [minLen_succ_of_getElem_eq (getElem_castSucc_of_eq), castPred_castSucc]

@[simp] theorem minLen_castGE {m : ℕ} {a : PermOf n} {hnm : n ≤ m} :
    (a.castGE hnm).minLen = a.minLen := by
  induction m generalizing n with | zero => _ | succ m IH => _
  · simp_rw [nonpos_iff_eq_zero] at hnm
    cases hnm
    simp_rw [minLen_zero]
  · rcases hnm.eq_or_lt with rfl | hnm
    · simp_rw [castGE_of_eq, minLen_cast]
    · simp_rw [Nat.lt_succ_iff] at hnm
      simp_rw [← castGE_castSucc hnm, minLen_castSucc, IH]

@[simp] theorem getElem_of_ge_minLen {a : PermOf n} {i : ℕ} (hi : a.minLen ≤ i) {hi' : i < n} :
    a[i] = i := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [not_lt_zero'] at hi'
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha] at hi
      simp_rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at hi'
      rcases hi' with hi' | rfl
      · exact ((a.getElem_castPred ha hi').symm).trans (IH hi)
      · exact ha
    · simp_rw [minLen_succ_of_getElem_ne ha] at hi
      exact (hi'.not_le hi).elim

@[simp] theorem smul_of_ge_minLen {a : PermOf n} {i : ℕ} (hi : a.minLen ≤ i) : a • i = i := by
  simp_rw [smul_eq_dite, dite_eq_right_iff]
  exact fun _ => getElem_of_ge_minLen hi

theorem IsCongr.minLen_eq {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.IsCongr b) : a.minLen = b.minLen := by
  rcases Nat.le_or_le m n with hmn | hnm
  · simp_rw [isCongr_iff_eq_castGE_of_ge hmn] at hab
    simp_rw [hab, minLen_castGE]
  · simp_rw [isCongr_iff_eq_castGE_of_le hnm] at hab
    simp_rw [hab, minLen_castGE]

theorem IsCongr.minLen_le {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.IsCongr b) : a.minLen ≤ m := hab.minLen_eq ▸ b.minLen_le

theorem IsCongr.minLen_le_min {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.IsCongr b) : a.minLen ≤ n ⊓ m := le_inf a.minLen_le hab.minLen_le

end MinLen

def minPerm {n : ℕ} (a : PermOf n) : PermOf a.minLen := match n with
  | 0 => 1
  | (n + 1) =>
    if ha : a[n] = n
    then (a.castPred ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm
    else a.cast (minLen_succ_of_getElem_ne ha).symm

section MinPerm

variable {m : ℕ}

@[simp] theorem minPerm_zero {a : PermOf 0} : a.minPerm = 1 := rfl

theorem minPerm_succ {a : PermOf (n + 1)} :
    a.minPerm = if ha : a[n] = n
    then (a.castPred ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm
    else a.cast (minLen_succ_of_getElem_ne ha).symm := rfl

@[simp] theorem minPerm_succ_of_getElem_eq {a : PermOf (n + 1)}  (ha : a[n] = n) :
    a.minPerm = (a.castPred ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm := by
  simp_rw [minPerm_succ, ha, dite_true]

@[simp] theorem minPerm_succ_of_getElem_ne {a : PermOf (n + 1)} (ha : a[n] ≠ n) :
    a.minPerm = a.cast (minLen_succ_of_getElem_ne ha).symm := by
  simp_rw [minPerm_succ, ha, dite_false]

@[simp] theorem getElem_minPerm {a : PermOf n} {i : ℕ} (hi : i < a.minLen) :
    (a.minPerm)[i] = a[i]'(hi.trans_le minLen_le) := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minPerm_zero, Unique.eq_default a, default_eq, getElem_one]
  · by_cases ha : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha, getElem_cast, IH, getElem_castPred]
    · simp_rw [minPerm_succ_of_getElem_ne ha, getElem_cast]

@[simp] theorem getElem_inv_minPerm {a : PermOf n} {i : ℕ} (hi : i < a.minLen) :
    (a.minPerm)⁻¹[i] = a⁻¹[i]'(hi.trans_le minLen_le) := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minPerm_zero, Unique.eq_default a, default_eq, inv_one, getElem_one]
  · by_cases ha : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha, getElem_inv_cast, IH, getElem_inv_castPred]
    · simp_rw [minPerm_succ_of_getElem_ne ha, getElem_inv_cast]

@[simp]
theorem castGE_minPerm_minLen_le {a : PermOf n} : a.minPerm.castGE minLen_le = a := by
  ext i
  rcases lt_or_ge i (a.minLen) with hi | hi
  · simp_rw [getElem_castGE_of_lt hi, getElem_minPerm]
  · simp_rw [getElem_castGE_of_ge hi, getElem_of_ge_minLen hi]

@[simp] theorem minPerm_isCongr {a : PermOf n} : a.minPerm.IsCongr a := by
  simp_rw [isCongr_iff_eq_castGE_of_le minLen_le, castGE_minPerm_minLen_le]

@[simp] theorem isCongr_minPerm {a : PermOf n} : a.IsCongr a.minPerm :=
  minPerm_isCongr.symm

theorem minPerm_smul {a : PermOf n} {i : ℕ} : a.minPerm • i = a • i := minPerm_isCongr.smul_eq

theorem natPerm_minPerm {a : PermOf n} : natPerm a.minPerm = natPerm a := by
  simp_rw [natPerm_eq_iff_isCongr, minPerm_isCongr]

theorem isCongr_minPerm_right {a : PermOf n} {b : PermOf m} :
    a.IsCongr b.minPerm ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, minPerm_smul]

theorem isCongr_minPerm_left {a : PermOf n} {b : PermOf m} :
    a.minPerm.IsCongr b ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, minPerm_smul]

@[simp] theorem isCongr_minPerm_minPerm {a : PermOf n} {b : PermOf m} :
    a.minPerm.IsCongr b.minPerm ↔ a.IsCongr b := by
  simp_rw [isCongr_minPerm_right, isCongr_minPerm_left]

theorem IsCongr.minPerm_left {a : PermOf n} {b : PermOf m}
    (hab : a.IsCongr b) : a.minPerm.IsCongr b :=
  isCongr_minPerm_left.mpr hab

theorem IsCongr.minPerm_right {a : PermOf n} {b : PermOf m}
    (hab : a.IsCongr b) : a.IsCongr b.minPerm :=
  isCongr_minPerm_right.mpr hab

theorem IsCongr.minPerm_minPerm {a : PermOf n} {b : PermOf m}
    (hab : a.IsCongr b) : a.minPerm.IsCongr b.minPerm :=
  isCongr_minPerm_minPerm.mpr hab

theorem isCongr_minPerm_inv_inv_minPerm {a : PermOf n} : a⁻¹.minPerm.IsCongr (a.minPerm)⁻¹ := by
  simp_rw [isCongr_minPerm_left, inv_isCongr_inv_iff, isCongr_minPerm_right, isCongr_iff_eq]

@[simp] theorem minPerm_one : (1 : PermOf n).minPerm = 1 := by
  ext
  simp_rw [getElem_minPerm, getElem_one]

theorem castGE_mul_castGE_isCongr_castGE_minPerm_mul_castGE_minPerm
    {a : PermOf n} {b : PermOf m} :
    (a.castGE (le_max_left _ _) * b.castGE (le_max_right _ _)).IsCongr
    ((a.minPerm.castGE (le_max_left _ _)) * (b.minPerm.castGE (le_max_right _ _))) :=
  isCongr_minPerm.castGE_isCongr_castGE.mul_mul isCongr_minPerm.castGE_isCongr_castGE

@[simp] theorem minPerm_inv {a : PermOf n} :
    a⁻¹.minPerm = a.minPerm⁻¹.cast minLen_inv.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_inv_minPerm]

@[simp] theorem minPerm_cast {m : ℕ} {a : PermOf n} (hnm : n = m) :
    (a.cast hnm).minPerm = a.minPerm.cast minLen_cast.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_minPerm]

@[simp] theorem minPerm_castPred {a : PermOf (n + 1)} {ha : a[n] = n} :
    (a.castPred ha).minPerm = a.minPerm.cast (minLen_succ_of_getElem_eq _) := by
  ext
  simp_rw [getElem_minPerm, getElem_castPred, getElem_cast, getElem_minPerm]

theorem minPerm_castSucc {a : PermOf n} :
    a.castSucc.minPerm = a.minPerm.cast minLen_castSucc.symm := by
  ext i hi
  simp_rw [minLen_castSucc] at hi
  simp_rw [getElem_minPerm, getElem_cast,
    getElem_castSucc_of_lt (hi.trans_le minLen_le), getElem_minPerm]

@[simp] theorem minPerm_castGE {m : ℕ} {a : PermOf n} (hnm : n ≤ m) :
    (a.castGE hnm).minPerm = a.minPerm.cast minLen_castGE.symm := by
  ext i hi
  simp_rw [minLen_castGE] at hi
  simp_rw [getElem_minPerm, getElem_cast,
    getElem_castGE_of_lt (hi.trans_le minLen_le), getElem_minPerm]

theorem eq_one_of_minPerm_eq_one {a : PermOf n} (ha : a.minPerm = 1) : a = 1 := by
  induction n with | zero => _ | succ n IH => _
  · exact Subsingleton.elim _ _
  · by_cases ha' : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha', cast_eq_one_iff] at ha
      have ha := IH ha
      simp_rw [PermOf.ext_iff, getElem_one, getElem_castPred] at ha
      simp_rw [PermOf.ext_iff, getElem_one, Nat.lt_succ_iff, le_iff_lt_or_eq]
      exact fun _ hi => hi.elim ha (fun hi => hi ▸ ha')
    · simp_rw [minPerm_succ_of_getElem_ne ha', cast_eq_one_iff] at ha
      exact ha

@[simp]
theorem minPerm_eq_one_iff_eq_one {a : PermOf n} : a.minPerm = 1 ↔ a = 1 :=
  ⟨eq_one_of_minPerm_eq_one, fun h => h ▸ minPerm_one⟩

@[simp] theorem minLen_minPerm {a : PermOf n} : a.minPerm.minLen = a.minLen := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minPerm_zero, Unique.eq_default, Unique.default_eq (1 : PermOf 0)]
  · by_cases ha : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha, minLen_cast, IH, minLen_castPred]
    · simp_rw [minPerm_succ_of_getElem_ne ha, minLen_cast]

@[simp] theorem minPerm_minPerm {a : PermOf n} :
    a.minPerm.minPerm = a.minPerm.cast minLen_minPerm.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_minPerm]

end MinPerm

end PermOf

@[reducible] def SigmaPermOf := Σ n, PermOf n

namespace SigmaPermOf


end SigmaPermOf


namespace SigmaPermOf

open PermOf Equiv

theorem sigma_eq_of_eq_of_eq_cast : ∀ {a b : SigmaPermOf} (h : a.1 = b.1),
    a.2 = b.2.cast h.symm → a = b
  | ⟨n, a⟩, ⟨m, b⟩, hab, heq => by
    dsimp only at hab heq
    simp_rw [Sigma.mk.inj_iff]
    subst hab heq
    simp_rw [heq_eq_eq, cast_rfl, true_and]

theorem sigma_eq_iff_fst_eq_fst_and_snd_eq_cast_snd {a b : SigmaPermOf} :
    a = b ↔ ∃ (h : a.1 = b.1), a.2 = b.2.cast h.symm :=
  ⟨fun h => h ▸ ⟨rfl, a.snd.cast_rfl⟩, fun h => sigma_eq_of_eq_of_eq_cast h.1 h.2⟩


theorem sigma_eq_of_eq_of_isCongr : ∀ {a b : SigmaPermOf}, a.1 = b.1 → a.2.IsCongr b.2 → a = b
  | ⟨n, a⟩, ⟨m, b⟩, hab, heq => by
    dsimp only at hab
    simp_rw [Sigma.mk.inj_iff]
    subst hab
    simp_rw [isCongr_iff_eq] at heq
    subst heq
    simp_rw [heq_eq_eq, and_self]

theorem sigma_eq_iff_eq_and_isCongr {a b : SigmaPermOf} : a = b ↔ a.1 = b.1 ∧ a.2.IsCongr b.2 :=
  ⟨fun h => h ▸ ⟨rfl, isCongr_rfl⟩, fun h => sigma_eq_of_eq_of_isCongr h.1 h.2⟩

instance : Mul SigmaPermOf where
  mul := fun ⟨n, a⟩ ⟨m, b⟩ =>
  ⟨max n m, (a.castGE (le_max_left _ _)) * (b.castGE (le_max_right _ _))⟩

theorem mul_def {a b : SigmaPermOf} : a * b =
    ⟨max a.1 b.1, (a.2.castGE (le_max_left _ _)) * (b.2.castGE (le_max_right _ _))⟩ := rfl

@[simp] theorem mk_mul {n : ℕ} {a b : PermOf n} :
    (⟨n, a * b⟩ : SigmaPermOf) = ⟨n, a⟩ * ⟨n, b⟩ := by
  simp_rw [sigma_eq_iff_eq_and_isCongr, mul_def, castGE_mul, isCongr_castGE,
    max_self, true_and]

@[simp] theorem mul_mk_one {a : SigmaPermOf} {n : ℕ} :
    a * ⟨n, 1⟩ = ⟨a.1 ⊔ n, a.2.castGE (le_max_left _ _)⟩ := by
  simp_rw [sigma_eq_iff_eq_and_isCongr, mul_def, castGE_one,
    mul_one, isCongr_rfl, true_and]

@[simp] theorem mk_one_mul {a : SigmaPermOf} {n : ℕ} :
    ⟨n, 1⟩ * a = ⟨n ⊔ a.1, a.2.castGE (le_max_right _ _)⟩ := by
  simp_rw [sigma_eq_iff_eq_and_isCongr, mul_def, castGE_one,
    one_mul, isCongr_rfl, true_and]

instance : One SigmaPermOf where
  one := ⟨0, 1⟩

theorem one_def : (1 : SigmaPermOf) = ⟨0, 1⟩ := rfl

instance : Inv SigmaPermOf where
  inv := fun ⟨_, a⟩ => ⟨_, a⁻¹⟩

theorem inv_def {a : SigmaPermOf} : a⁻¹ = ⟨a.1, a.2⁻¹⟩ := rfl

@[simp] theorem mul_inv_self {a : SigmaPermOf} : a * a⁻¹ = ⟨a.fst, 1⟩ := by
  simp_rw [sigma_eq_iff_eq_and_isCongr, isCongr_one_iff_eq_one, mul_def, inv_def,
    max_self, castGE_of_eq (max_self _).symm, cast_mul, mul_inv_cancel, cast_one, and_self]

@[simp] theorem inv_self_mul {a : SigmaPermOf} : a⁻¹ * a = ⟨a.fst, 1⟩ := by
  simp_rw [sigma_eq_iff_eq_and_isCongr, isCongr_one_iff_eq_one, mul_def, inv_def,
    max_self, castGE_of_eq (max_self _).symm, cast_mul, inv_mul_cancel, cast_one, and_self]

instance : DivisionMonoid SigmaPermOf where
  mul_assoc := (fun ⟨n, a⟩ ⟨m, b⟩ ⟨l, c⟩ => by
    simp_rw [sigma_eq_iff_eq_and_isCongr, mul_def, castGE_castGE_mul, mul_assoc]
    exact ⟨max_assoc _ _ _,
      castGE_isCongr_castGE_rfl.mul_mul
      (castGE_isCongr_castGE_rfl.mul_mul castGE_isCongr_castGE_rfl)⟩)
  one_mul := (fun ⟨n, a⟩ => by
    simp_rw [one_def, mk_one_mul, sigma_eq_iff_eq_and_isCongr]
    exact ⟨Nat.zero_max _, castGE_isCongr⟩)
  mul_one := (fun ⟨n, a⟩ => by
    simp_rw [one_def, mul_mk_one, sigma_eq_iff_eq_and_isCongr]
    exact ⟨Nat.max_zero _, castGE_isCongr⟩)
  inv_inv _ := rfl
  mul_inv_rev _ _ := by
    simp_rw [sigma_eq_iff_eq_and_isCongr, mul_def, inv_def, mul_inv_rev,
      inv_castGE]
    exact ⟨max_comm _ _, castGE_isCongr_castGE_rfl.mul_mul castGE_isCongr_castGE_rfl⟩
  inv_eq_of_mul _ _ := by
    simp_rw [sigma_eq_iff_eq_and_isCongr, mul_def, inv_def, one_def,
      Nat.max_eq_zero_iff, and_imp, isCongr_iff_smul_eq, one_smul, mul_smul, castGE_smul,
      inv_smul_eq_iff]
    exact fun ha hb hab => ⟨ha.trans hb.symm, hab.symm⟩

@[simps! apply]
def natPerm : SigmaPermOf →* Perm ℕ where
  toFun a := a.2.natPerm
  map_one' := by simp_rw [one_def, map_one]
  map_mul' := by
    simp_rw [mul_def, map_mul, Equiv.ext_iff, Perm.mul_apply,
      natPerm_apply_apply, castGE_smul, implies_true]

theorem natPerm_eq_iff_snd_isCongr_snd {a b : SigmaPermOf} :
    natPerm a = natPerm b ↔ a.snd.IsCongr b.snd := by
  simp_rw [natPerm_apply, natPerm_eq_iff_isCongr]

theorem natPerm_apply_apply_of_ge_fst {a : SigmaPermOf} {i : ℕ} (hi : a.fst ≤ i) :
    a.natPerm i = i := by
  simp_rw [natPerm_apply, natPerm_apply_apply, smul_of_ge a.snd hi]

theorem lt_fst_of_natPerm_unfix {a : SigmaPermOf} {i : ℕ} (hi : a.natPerm i ≠ i) : i < a.fst :=
  lt_of_not_le (Function.mt natPerm_apply_apply_of_ge_fst hi)

instance IsCongr : Con SigmaPermOf := Con.ker natPerm

@[simp] theorem isCongr_iff_snd_isCongr_snd {a b : SigmaPermOf} :
    IsCongr a b ↔ a.2.IsCongr b.2 := by
  unfold IsCongr
  simp_rw [Con.ker_rel, natPerm_eq_iff_snd_isCongr_snd]

theorem IsCongr_mul {a b c d : SigmaPermOf} :
    IsCongr a b → IsCongr c d → IsCongr (a*c) (b*d) := IsCongr.mul

instance {a b : SigmaPermOf} : Decidable (IsCongr a b) :=
  decidable_of_decidable_of_iff isCongr_iff_snd_isCongr_snd.symm

theorem isCongr_mk_one_iff_snd_eq_one {a : SigmaPermOf} {n : ℕ} :
    IsCongr a ⟨n, 1⟩ ↔ a.2 = 1 := by
  simp_rw [isCongr_iff_snd_isCongr_snd, isCongr_one_iff_eq_one]

theorem isCongr_one_iff_snd_eq_one {a : SigmaPermOf} :
    IsCongr a 1 ↔ a.2 = 1 := isCongr_mk_one_iff_snd_eq_one

theorem mk_one_isCongr_one {n : ℕ} : IsCongr (⟨n, 1⟩ : SigmaPermOf) 1 := by
  simp_rw [isCongr_one_iff_snd_eq_one]

@[simp] theorem mul_inv_isCongr_one {a : SigmaPermOf} : IsCongr (a * a⁻¹) 1 := by
  simp_rw [mul_inv_self, mk_one_isCongr_one]

@[simp] theorem inv_mul_isCongr_one {a : SigmaPermOf} : IsCongr (a⁻¹ * a) 1 := by
  simp_rw [inv_self_mul, mk_one_isCongr_one]

@[simp]
theorem inv_isCongr_inv_iff_isCongr {a b : SigmaPermOf} : IsCongr a⁻¹ b⁻¹ ↔ IsCongr a b := by
    simp_rw [isCongr_iff_snd_isCongr_snd, inv_def, inv_isCongr_inv_iff]

theorem inv_isCongr_inv_of_isCongr {a b : SigmaPermOf} : IsCongr a b → IsCongr a⁻¹ b⁻¹ :=
  inv_isCongr_inv_iff_isCongr.mpr

theorem isCongr_iff_mul_inv_isCongr_one {a b : SigmaPermOf} :
    IsCongr a b ↔ IsCongr (a * b⁻¹) 1 := by
  simp_rw [isCongr_one_iff_snd_eq_one, mul_def, inv_def, mul_eq_one_iff_eq_inv,
    inv_castGE, inv_inv, ← isCongr_iff_eq, castGE_isCongr_castGE_iff_isCongr,
    isCongr_iff_snd_isCongr_snd]

theorem isCongr_iff_inv_mul_isCongr_one {a b : SigmaPermOf} : IsCongr a b ↔ IsCongr (b⁻¹ * a) 1 := by
  simp_rw [isCongr_one_iff_snd_eq_one, mul_def, inv_def, mul_eq_one_iff_eq_inv',
    inv_castGE, inv_inv, ← isCongr_iff_eq, castGE_isCongr_castGE_iff_isCongr,
    isCongr_iff_snd_isCongr_snd]

@[simps!]
def isCongrSubmonoid : Submonoid (SigmaPermOf × SigmaPermOf) := IsCongr.submonoid

@[simps!]
def minRep (a : SigmaPermOf) : SigmaPermOf := ⟨a.2.minLen, a.2.minPerm⟩

section MinRep

variable {n : ℕ}

@[simp] theorem minRep_mk {a : PermOf n} : minRep ⟨n, a⟩ = ⟨a.minLen, a.minPerm⟩ := rfl

theorem minRep_eq_iff_isCongr {a b : SigmaPermOf} : minRep a = minRep b ↔ IsCongr a b := by
  simp_rw [sigma_eq_iff_eq_and_isCongr, isCongr_iff_snd_isCongr_snd, minRep_fst, minRep_snd,
    isCongr_minPerm_minPerm, and_iff_right_iff_imp]
  exact IsCongr.minLen_eq

theorem minRep_eq_self_iff {a : SigmaPermOf} : minRep a = a ↔
    (∀ (hn : a.fst ≠ 0), a.snd[a.fst - 1] ≠ a.fst - 1) := by
  simp_rw [sigma_eq_iff_eq_and_isCongr, minRep_fst, minRep_snd,
    minPerm_isCongr, PermOf.minLen_eq_iff, and_true]

@[simp] theorem isCongr_minRep {a : SigmaPermOf} : IsCongr (minRep a) a := by
  simp_rw [isCongr_iff_snd_isCongr_snd]
  exact minPerm_isCongr

theorem minRep_minRep {a : SigmaPermOf} : minRep (minRep a) = minRep a := by
  simp_rw [minRep_eq_iff_isCongr, isCongr_minRep]

@[simp] theorem minRep_eq_one_iff {a : SigmaPermOf} : minRep a = 1 ↔ IsCongr a 1 := by
  simp_rw [sigma_eq_iff_eq_and_isCongr, one_def, isCongr_mk_one_iff_snd_eq_one,
    isCongr_one_iff_eq_one, minRep_fst, minRep_snd, minLen_eq_zero_iff_eq_one,
    minPerm_eq_one_iff_eq_one, and_self]

@[simp] theorem minRep_one : minRep (1 : SigmaPermOf) = 1 := by
  simp_rw [minRep_eq_one_iff, IsCongr.refl]

theorem minRep_mul {a b : SigmaPermOf} :
    (a * b).minRep = (minRep a * minRep b).minRep := by
  simp_rw [minRep_eq_iff_isCongr, isCongr_iff_snd_isCongr_snd]
  exact castGE_mul_castGE_isCongr_castGE_minPerm_mul_castGE_minPerm

@[simp] theorem minRep_inv {a : SigmaPermOf} : minRep a⁻¹ = (minRep a)⁻¹ := by
  cases a
  simp_rw [inv_def, minRep_mk, sigma_eq_iff_eq_and_isCongr, minLen_inv,
    isCongr_minPerm_inv_inv_minPerm, and_self]

@[simp] theorem minRep_mul_IsCongr {a b : SigmaPermOf} :
    IsCongr (minRep (a * b)) (minRep a * minRep b) := by
  rw [minRep_mul]
  exact isCongr_minRep

end MinRep

end SigmaPermOf

structure FinitePerm where
  len : ℕ
  toPermOf : PermOf len
  toPermOf_minLen : toPermOf.minLen = len
  deriving DecidableEq

instance : Repr FinitePerm := ⟨fun a i => reprPrec (a.toPermOf) i⟩

namespace FinitePerm

open PermOf Equiv Equiv.Perm

variable {n m : ℕ}

@[ext] theorem ext {a b : FinitePerm} (hab : a.toPermOf.IsCongr b.toPermOf) : a = b := by
  cases a with | mk n a hna => _
  cases b with | mk m b hmb => _
  simp_rw [mk.injEq]
  have hnm : n = m := hna.symm.trans (hab.minLen_eq.trans hmb)
  subst hnm
  simp_rw [isCongr_iff_eq] at hab
  simp_rw [heq_eq_eq, true_and, hab]

instance : One FinitePerm := ⟨⟨0, 1, minLen_zero⟩⟩

theorem one_len : (1 : FinitePerm).len = 0 := rfl

theorem one_toPermOf : (1 : FinitePerm).toPermOf = 1 := rfl

instance mul : Mul FinitePerm where
  mul a b :=
  let ab := ((a.toPermOf.castGE (le_max_left a.len b.len)) *
    (b.toPermOf.castGE (le_max_right a.len b.len)))
  ⟨ab.minLen, ab.minPerm, minLen_minPerm⟩

theorem mul_len (a b : FinitePerm): (a * b).len =
      ( a.toPermOf.castGE (le_max_left a.len b.len) * b.toPermOf.castGE
      (le_max_right a.len b.len)).minLen := rfl

theorem mul_toPermOf (a b : FinitePerm): (a * b).toPermOf =
      ( a.toPermOf.castGE (le_max_left a.len b.len) * b.toPermOf.castGE
      (le_max_right a.len b.len)).minPerm := rfl

instance : Inv FinitePerm where
  inv a := ⟨a.len, a.toPermOf⁻¹, minLen_inv.trans a.toPermOf_minLen⟩

theorem inv_len (a : FinitePerm): (a⁻¹).len = a.len := rfl

theorem inv_toPermof (a : FinitePerm) : (a⁻¹).toPermOf = a.toPermOf⁻¹ := rfl

instance : Group FinitePerm where
  mul_assoc a b c := by
    ext
    simp_rw [mul_toPermOf, isCongr_minPerm_minPerm, isCongr_iff_smul_eq]
    simp only [minPerm_isCongr.smul_eq, mul_smul, castGE_smul, implies_true]
  mul_one a := by
    ext
    simp_rw [mul_toPermOf, one_toPermOf,  isCongr_minPerm_left,
      castGE_one, mul_one, castGE_isCongr]
  one_mul a := by
    ext
    simp_rw [mul_toPermOf, one_toPermOf,  isCongr_minPerm_left,
      castGE_one, one_mul, castGE_isCongr]
  inv_mul_cancel a := by
    ext
    simp_rw [mul_toPermOf, one_toPermOf, inv_toPermof, ← inv_castGE,
      isCongr_one_iff_eq_one]
    exact minPerm_eq_one_iff_eq_one.mpr (inv_mul_cancel _)

instance : SMul FinitePerm ℕ where smul a i := a.toPermOf • i

theorem smul_eq_dite (a : FinitePerm) (i : ℕ) :
    a • i = if h : i < a.len then a.toPermOf[i] else i := PermOf.smul_eq_dite _ _

theorem smul_of_lt (a : FinitePerm) {i : ℕ} (h : i < a.len) :
    a • i = a.toPermOf[i] := PermOf.smul_of_lt _ _

theorem smul_of_ge (a : FinitePerm) {i : ℕ} : a.len ≤ i → a • i = i := PermOf.smul_of_ge _

@[simp]
theorem toPermOf_smul {a : FinitePerm} {i : ℕ} : a.toPermOf • i = a • i := rfl

@[simp]
theorem mk_smul {a : PermOf n} (ha : a.minLen = n) {i : ℕ} :
    (⟨n, a, ha⟩ : FinitePerm) • i = a • i := rfl

theorem eq_iff_smul_eq_smul {a b : FinitePerm} :
    a = b ↔ ∀ {i : ℕ}, a • i = b • i := by
  simp_rw [FinitePerm.ext_iff, isCongr_iff_smul_eq, toPermOf_smul]

instance : FaithfulSMul FinitePerm ℕ where
  eq_of_smul_eq_smul := by
    simp_rw [eq_iff_smul_eq_smul, imp_self, implies_true]

instance : MulAction FinitePerm ℕ where
  smul a i := a.toPermOf • i
  one_smul := by
    simp_rw [← toPermOf_smul, one_toPermOf, one_smul, implies_true]
  mul_smul := by
    simp_rw [← toPermOf_smul, mul_toPermOf, minPerm_isCongr.smul_eq,
      mul_smul, castGE_smul, implies_true]

@[simps!]
def natPerm : FinitePerm →* Perm ℕ where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  map_one' := by
    simp_rw [Equiv.ext_iff, inv_one, one_smul, coe_fn_mk, one_apply, implies_true]
  map_mul' := by
    simp_rw [Equiv.ext_iff, mul_inv_rev, mul_smul, mul_apply, coe_fn_mk, implies_true]

theorem natPerm_injective : Function.Injective natPerm := fun a b => by
  simp_rw [Equiv.ext_iff, natPerm_apply_apply, eq_iff_smul_eq_smul, imp_self]

theorem natPerm_inj {a b : FinitePerm} : natPerm a = natPerm b ↔ a = b :=
  natPerm_injective.eq_iff

theorem ker_natPerm : natPerm.ker = ⊥ := by
  simp_rw [MonoidHom.ker_eq_bot_iff,  natPerm_injective]

theorem natPerm_toPermOf {a : FinitePerm} :
    a.toPermOf.natPerm = a.natPerm := by
  simp_rw [Equiv.ext_iff, natPerm_apply_apply,
    PermOf.natPerm_apply_apply, toPermOf_smul, implies_true]

theorem natPerm_mem_natFixGE {a : FinitePerm} : a.natPerm ∈ NatFixGE a.len :=
  PermOf.natPerm_mem_natFixGE

theorem natPerm_mem_natFinitePerm {a : FinitePerm} : a.natPerm ∈ NatFinitePerm :=
  natFixGE_le_natFinitePerm natPerm_mem_natFixGE

def FixGE (n : ℕ) : Subgroup FinitePerm where
  carrier := {a : FinitePerm | a.len ≤ n}
  mul_mem' := by
    simp_rw [Set.mem_setOf_eq, mul_len]
    exact fun ha hb => (minLen_le.trans (sup_le ha hb))
  one_mem' := by
    simp_rw [Set.mem_setOf_eq, one_len]
    exact zero_le _
  inv_mem' := by
    simp_rw [Set.mem_setOf_eq, inv_len, imp_self, implies_true]

theorem mem_fixGE_iff {n : ℕ} {a : FinitePerm} : a ∈ FixGE n ↔ a.len ≤ n := Iff.rfl

theorem len_le_of_mem_fixGE {n : ℕ} {a : FinitePerm} (ha : a ∈ FixGE n) : a.len ≤ n :=
  mem_fixGE_iff.mp ha

theorem mem_fixGE_of_len_le {n : ℕ} {a : FinitePerm} (ha : a.len ≤ n) : a ∈ FixGE n :=
  mem_fixGE_iff.mpr ha

theorem mem_fixGE_len {a : FinitePerm} : a ∈ FixGE a.len := mem_fixGE_of_len_le le_rfl

theorem fixGE_mono (hnm : n ≤ m) : FixGE n ≤ FixGE m := by
  simp_rw [SetLike.le_def, mem_fixGE_iff]
  exact fun _ h => h.trans hnm

theorem directed_fixGE : Directed (· ≤ ·) (FixGE) := fun _ _ =>
  ⟨_, fixGE_mono (le_max_left _ _), fixGE_mono (le_max_right _ _)⟩

theorem sup_fixGE : ⨆ (n : ℕ), FixGE n = ⊤ := by
  simp_rw [Subgroup.ext_iff, Subgroup.mem_top, iff_true,
    Subgroup.mem_iSup_of_directed directed_fixGE]
  exact fun _ => ⟨_, mem_fixGE_len⟩

@[simps apply_coe_len apply_coe_toPermOf symm_apply]
def permOfMulEquivFixGE : PermOf n ≃* FixGE n where
  toFun a := ⟨⟨a.minLen, a.minPerm, minLen_minPerm⟩, minLen_le⟩
  invFun a := a.1.toPermOf.castGE a.2
  left_inv a := castGE_minPerm_minLen_le
  right_inv a := by
    simp_rw [Subtype.ext_iff, FinitePerm.ext_iff, minPerm_castGE,
      cast_left_isCongr, minPerm_isCongr]
  map_mul' a b := by
    simp_rw [Subtype.ext_iff, Subgroup.coe_mul, FinitePerm.ext_iff, mul_toPermOf,
      isCongr_minPerm_minPerm]
    exact (isCongr_minPerm.trans isCongr_castGE).mul_mul (isCongr_minPerm.trans isCongr_castGE)

theorem permOfMulEquivFixGE_apply_coe_smul {a : PermOf n} {i : ℕ} :
  (permOfMulEquivFixGE a : FinitePerm) • i = a • i := by
  unfold permOfMulEquivFixGE
  simp_rw [MulEquiv.coe_mk, coe_fn_mk, mk_smul, minPerm_smul]

@[simps! apply symm_apply]
def fixGEMulEquivNatFixGE : FixGE n ≃* NatFixGE n :=
  permOfMulEquivFixGE.symm.trans mulEquivNatFixGE

theorem fixGEMulEquivNatFixGE_commutes (hnm : n ≤ m) :
    (MonoidHom.comp fixGEMulEquivNatFixGE.toMonoidHom
      (Subgroup.inclusion (fixGE_mono hnm))) =
    (MonoidHom.comp (Subgroup.inclusion (natFixGE_mono hnm))
      fixGEMulEquivNatFixGE.toMonoidHom) := by
  unfold Subgroup.inclusion
  simp_rw [MonoidHom.ext_iff]
  simp_rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.comp_apply, MonoidHom.coe_coe,
    MonoidHom.mk'_apply, fixGEMulEquivNatFixGE_apply, Subtype.mk.injEq,
    natPerm_eq_iff_isCongr, castGE_isCongr_castGE_iff_isCongr, isCongr_refl, implies_true]

theorem exists_natPerm_apply_iff_mem_natFinitePerm {e : Perm ℕ} :
    (∃ a : FinitePerm, natPerm a = e) ↔ e ∈ NatFinitePerm := by
  refine ⟨?_, fun he => ?_⟩
  · rintro ⟨a, rfl⟩
    exact natPerm_mem_natFinitePerm
  · rw [mem_natFinitePerm_iff] at he
    rcases he with ⟨n, he⟩
    use fixGEMulEquivNatFixGE.symm ⟨e, he⟩
    simp_rw [Equiv.ext_iff, fixGEMulEquivNatFixGE_symm_apply, natPerm_apply_apply,
      permOfMulEquivFixGE_apply_coe_smul, ofNatSepAt_smul, SubgroupClass.coe_inclusion,
      ite_eq_left_iff, not_lt]
    exact fun _ h => (fixed_ge_of_mem_natFixGE he _ h).symm

theorem range_natPerm : natPerm.range = NatFinitePerm := by
  simp_rw [SetLike.ext_iff, MonoidHom.mem_range,
    exists_natPerm_apply_iff_mem_natFinitePerm, implies_true]

noncomputable def mulEquivNatFinitePerm : FinitePerm ≃* NatFinitePerm :=
  (MulEquiv.ofBijective (MonoidHom.rangeRestrict natPerm)
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr natPerm_injective,
    MonoidHom.rangeRestrict_surjective _⟩).trans (MulEquiv.subgroupCongr range_natPerm)

end FinitePerm
