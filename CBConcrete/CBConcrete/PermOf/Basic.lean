import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Perm

namespace Equiv

variable {α : Type*} [DecidableEq α]

theorem coe_swap {n : ℕ} {i j k : Fin n} : swap (i : ℕ) (j : ℕ) (k : ℕ) = swap i j k :=
  Fin.val_injective.swap_apply _ _ _

theorem swap_smul {R : Type*} [Group R] [MulAction R α] {i j k : α} {r : R} :
    swap (r • i) (r • j) (r • k) = r • swap i j k :=
  (MulAction.injective r).swap_apply _ _ _

theorem swap_prop (p : α → Prop) {i j k : α} (hk : k ≠ i → k ≠ j → p k)
    (hi : k = j → p i) (hj : k = i → p j) : p (swap i j k) := by
  rcases eq_or_ne k i with rfl | hik
  · simp_rw [swap_apply_left, hj]
  · rcases eq_or_ne k j with rfl | hjk
    · simp_rw [swap_apply_right, hi]
    · simp_rw [swap_apply_of_ne_of_ne hik hjk, hk hik hjk]

theorem swap_prop_const (p : α → Prop) {i j k : α} (hk : p k)
    (hi : p i) (hj : p j) : p (swap i j k) :=
  swap_prop _ (fun _ _ => hk) (fun _ => hi) (fun _ => hj)

namespace Perm

def NatFixLTOfLT (n : ℕ) : Subgroup (Perm ℕ) where
  carrier e := ∀ i, i < n → e i < n
  mul_mem' {a} {b} ha hb i hi := ha _ (hb _ hi)
  one_mem' i hi := by simp_rw [Perm.coe_one, id_eq, hi]
  inv_mem' {e} he i hi := by
    have hfi : Function.Injective (fun (i : Fin n) => (⟨e i, he _ i.isLt⟩ : Fin n)) :=
      fun _ _ h => Fin.eq_of_val_eq (e.injective (Fin.val_eq_of_eq h))
    have hfs := hfi.surjective_of_fintype (Equiv.refl _)
    rcases hfs ⟨i, hi⟩ with ⟨j, hj⟩
    exact j.isLt.trans_eq' (inv_eq_iff_eq.mpr (Fin.val_eq_of_eq hj).symm)

section NatFixLTOfLT

variable {e : Perm ℕ} {n m : ℕ}

theorem mem_NatFixLTOfLT_iff : e ∈ NatFixLTOfLT n ↔ ∀ i, i < n → e i < n := Iff.rfl

theorem apply_lt_of_lt_of_mem_NatFixLTOfLT (he : e ∈ NatFixLTOfLT n) :
  ∀ i, i < n → e i < n := mem_NatFixLTOfLT_iff.mp he

theorem mem_NatFixLTOfLT_iff' : e ∈ NatFixLTOfLT n ↔ ∀ i, n ≤ i → n ≤ e i :=
  ⟨fun he _ => le_imp_le_of_lt_imp_lt fun hi =>
    (((Subgroup.inv_mem_iff _).mpr he) _ hi).trans_eq' (e.inv_apply_self _).symm,
    fun he => (Subgroup.inv_mem_iff _).mp fun _ => lt_imp_lt_of_le_imp_le fun hi =>
    (he _ hi).trans_eq (e.apply_inv_self _)⟩

theorem apply_le_of_le_of_mem_NatFixLTOfLT (he : e ∈ NatFixLTOfLT n) :
  ∀ i, n ≤ i → n ≤ e i := mem_NatFixLTOfLT_iff'.mp he

end NatFixLTOfLT

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

theorem natFixGE_le_NatFixLTOfLT : NatFixGE n ≤ NatFixLTOfLT n := by
  simp_rw [SetLike.le_def, mem_NatFixLTOfLT_iff']
  exact fun e he _ => fun hi => hi.trans_eq (he _ hi).symm

instance normal_natFixGE_subGroupOf_NatFixLTOfLT :
    Subgroup.Normal ((NatFixGE n).subgroupOf (NatFixLTOfLT n)) where
  conj_mem := by
    simp_rw [Subtype.forall, MulMemClass.mk_mul_mk, Subgroup.mem_subgroupOf, mem_natFixGE_iff,
      Subgroup.coe_mul, InvMemClass.coe_inv, mul_apply]
    intro _ _ he _ hp _ hi
    simp_rw [he _ (apply_le_of_le_of_mem_NatFixLTOfLT (Subgroup.inv_mem _ hp) _ hi), apply_inv_self]

theorem apply_lt_of_lt_of_mem_natFixGE {e : Perm ℕ} (he : e ∈ NatFixGE n) :
    ∀ i, i < n → e i < n := natFixGE_le_NatFixLTOfLT he

theorem natFixGE_mono (hnm : n ≤ m) : NatFixGE n ≤ NatFixGE m := by
  simp_rw [SetLike.le_def, mem_natFixGE_iff]
  exact fun _ H _ h => H _ (hnm.trans h)

theorem natFixGE_le_NatFixLTOfLT_of_le (hnm : n ≤ m) : NatFixGE n ≤ NatFixLTOfLT m :=
  (natFixGE_mono hnm).trans natFixGE_le_NatFixLTOfLT

theorem directed_natFixGE : Directed (· ≤ ·) (NatFixGE) := fun _ _ =>
  ⟨_, natFixGE_mono (le_max_left _ _), natFixGE_mono (le_max_right _ _)⟩

end NatFixGE

def NatFinitePerm : Subgroup (Perm ℕ) := ⨆ (n : ℕ), NatFixGE n

section NatFinitePerm

variable {e : Perm ℕ} {n : ℕ}

@[simp] theorem mem_natFinitePerm_iff : e ∈ NatFinitePerm ↔ ∃ n, e ∈ NatFixGE n :=
  Subgroup.mem_iSup_of_directed directed_natFixGE

theorem exists_mem_natFixGE_of_mem_natFinitePerm (he : e ∈ NatFinitePerm) :
    ∃ n, e ∈ NatFixGE n := mem_natFinitePerm_iff.mp he

theorem exists_mem_NatFixLTOfLT_of_mem_natFinitePerm (he : e ∈ NatFinitePerm) :
    ∃ n, e ∈ NatFixLTOfLT n :=
  ⟨_, natFixGE_le_NatFixLTOfLT ((exists_mem_natFixGE_of_mem_natFinitePerm he).choose_spec)⟩

theorem natFixGE_le_natFinitePerm :
    NatFixGE n ≤ NatFinitePerm := fun _ he => mem_natFinitePerm_iff.mpr ⟨_, he⟩

theorem mem_natFinitePerm_of_mem_natFixGE (he : e ∈ NatFixGE n) :
    e ∈ NatFinitePerm := natFixGE_le_natFinitePerm he

@[simp] theorem mem_natFinitePerm_iff_exists_fixed_ge :
    e ∈ NatFinitePerm ↔ ∃ n, ∀ i, n ≤ i → e i = i :=
  (Subgroup.mem_iSup_of_directed directed_natFixGE).trans <|
  exists_congr (fun _ => mem_natFixGE_iff)

theorem exists_fixed_ge_of_mem_natFinitePerm {e : Perm ℕ} (he : e ∈ NatFinitePerm) :
  ∃ n, ∀ i, n ≤ i → e i = i := exists_mem_natFixGE_of_mem_natFinitePerm he

theorem exists_apply_lt_of_lt_of_mem_natFinitePerm {e : Perm ℕ} (he : e ∈ NatFinitePerm) :
    ∃ n, ∀ i, i < n → e i < n := exists_mem_NatFixLTOfLT_of_mem_natFinitePerm he

end NatFinitePerm

end Perm

end Equiv

namespace Vector

variable {α β γ : Type*} {n m k i j : ℕ}

theorem getElem_swap_eq_getElem_swap_apply (as : Vector α n) (i j : ℕ) (hi : i < n)
    (hj : j < n)
    (k : ℕ) (hk : k < n) :
    (as.swap i j hi hj)[k] =
    as[Equiv.swap i j k]'(Equiv.swap_prop_const (· < n) hk hi hj) := by
  simp_rw [getElem_swap, Equiv.swap_apply_def]
  split_ifs <;> rfl

@[simp] theorem getElem_take' (xs : Vector α n) (j : Nat) (hi : i < min j n) :
    (xs.take j)[i] = xs[i] := getElem_take _ _ (hi.trans_eq (min_comm _ _))

end Vector

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
  protected toVector : Vector ℕ n
  /--
  Gives the inverse of the `PermOf` as a vector of size `n`.
  -/
  protected invVector : Vector ℕ n
  getElem_toVector_lt :
    ∀ {i : ℕ} (hi : i < n), toVector[i] < n := by decide
  getElem_invVector_getElem_toVector : ∀ {i : ℕ} (hi : i < n),
      invVector[toVector[i]]'(getElem_toVector_lt hi) = i := by decide
  deriving DecidableEq

namespace PermOf

open Function Equiv

variable {n m : ℕ}

section GetElemVectorBijective

theorem getElem_toVector_injective (a : PermOf n) :
  ∀ {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n), a.toVector[i] = a.toVector[j] → i = j :=
  fun hi _ hj hij => (a.getElem_invVector_getElem_toVector hi).symm.trans
    (Eq.trans (by simp_rw [hij]) (a.getElem_invVector_getElem_toVector hj))

theorem toVector_toList_Nodup (a : PermOf n) : a.toVector.toList.Nodup := by
  simp_rw [List.nodup_iff_injective_getElem,
    Array.getElem_toList, Vector.getElem_toArray,  Injective, Fin.ext_iff,
    Fin.forall_iff, Array.length_toList, Vector.size_toArray]
  exact fun _ => a.getElem_toVector_injective

theorem getElem_toVector_surjective (a : PermOf n) :
    ∀ {i : ℕ}, i < n → ∃ (j : ℕ), ∃ (hj : j < n), a.toVector[j] = i := by
  have H : Surjective (fun (i : Fin n) => Fin.mk a.toVector[i.1] (a.getElem_toVector_lt i.2)) :=
    Injective.surjective_of_fintype (Equiv.refl (Fin n)) fun _ _ => by
    simp_rw [Fin.mk.injEq, Fin.ext_iff]
    exact a.getElem_toVector_injective _ _
  unfold Surjective at H
  simp_rw [Fin.ext_iff, Fin.forall_iff, Fin.exists_iff] at H
  exact H

theorem getElem_invVector_lt (a : PermOf n) {i : ℕ} (hi : i < n) : a.invVector[i] < n := by
  rcases a.getElem_toVector_surjective hi with ⟨j, hj, rfl⟩
  simp_rw [a.getElem_invVector_getElem_toVector, hj]

theorem getElem_toVector_getElem_invVector (a : PermOf n) {i : ℕ} (hi : i < n) :
    a.toVector[a.invVector[i]]'(a.getElem_invVector_lt hi) = i := by
  rcases a.getElem_toVector_surjective hi with ⟨j, hj, rfl⟩
  simp_rw [a.getElem_invVector_getElem_toVector]

theorem getElem_invVector_injective (a : PermOf n) :
  ∀ {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n), a.invVector[i] = a.invVector[j] → i = j :=
  fun hi _ hj hij => (a.getElem_toVector_getElem_invVector hi).symm.trans
    (Eq.trans (by simp_rw [hij]) (a.getElem_toVector_getElem_invVector hj))

theorem invVector_toList_Nodup (a : PermOf n) : a.invVector.toList.Nodup := by
  simp_rw [List.nodup_iff_injective_getElem,
    Array.getElem_toList, Vector.getElem_toArray, Injective, Fin.ext_iff,
    Fin.forall_iff, Array.length_toList, Vector.size_toArray]
  exact fun _ => a.getElem_invVector_injective

theorem getElem_invVector_surjective (a : PermOf n) :
    ∀ {i : ℕ}, i < n → ∃ (j : ℕ), ∃ (hj : j < n), a.invVector[j] = i := by
  have H : Surjective (fun (i : Fin n) => Fin.mk a.invVector[i.1] (a.getElem_invVector_lt i.2)) :=
    Injective.surjective_of_fintype (Equiv.refl (Fin n)) fun _ _ => by
    simp_rw [Fin.mk.injEq, Fin.ext_iff]
    exact a.getElem_invVector_injective _ _
  unfold Surjective at H
  simp_rw [Fin.ext_iff, Fin.forall_iff, Fin.exists_iff] at H
  exact H

end GetElemVectorBijective

protected def mk' (toVector : Vector ℕ n) (invVector : Vector ℕ n)
    (getElem_invVector_lt : ∀ {i : ℕ} (hi : i < n), invVector[i] < n)
    (getElem_toVector_getElem_invVector : ∀ {i : ℕ} (hi : i < n),
    toVector[invVector[i]]'(getElem_invVector_lt hi) = i) :
  PermOf n :=
  let A : PermOf n := ⟨invVector, toVector,
    getElem_invVector_lt, getElem_toVector_getElem_invVector⟩
  ⟨toVector, invVector,
    A.getElem_invVector_lt, A.getElem_toVector_getElem_invVector⟩

section Mk'

@[simp] theorem mk'_toVector (a b : Vector ℕ n) {ha hab} :
    (PermOf.mk' a b ha hab).toVector = a := rfl

@[simp] theorem mk'_invVector (a b : Vector ℕ n) {ha hab} :
    (PermOf.mk' a b ha hab).invVector = b := rfl

end Mk'

instance : GetElem (PermOf n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.toVector[i]

section GetElem

@[simp]
theorem getElem_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_mk' (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk' a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_lt (a : PermOf n) {i : ℕ} (hi : i < n := by get_elem_tactic) : a[i] < n :=
  a.getElem_toVector_lt hi

@[simp]
theorem getElem_toVector (a : PermOf n)  {i : ℕ} (hi : i < n := by get_elem_tactic) :
  a.toVector[i] = a[i] := rfl

theorem toVector_eq_iff_forall_getElem_eq (a b : PermOf n) :
    a.toVector = b.toVector ↔ ∀ {i} (hi : i < n), a[i] = b[i] := by
  simp_rw [Vector.ext_iff, getElem_toVector]

section GetElemBijective

theorem getElem_injective (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n)
    (hij : a[i] = a[j]) : i = j := a.getElem_toVector_injective hi hj hij

@[simp] theorem getElem_inj (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (a : PermOf n) {i : ℕ} (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i := a.getElem_toVector_surjective hi

end GetElemBijective

end GetElem

instance : Inv (PermOf n) where
  inv a := PermOf.mk' a.invVector a.toVector
    a.getElem_toVector_lt a.getElem_invVector_getElem_toVector

section GetElemInv

@[simp]
theorem getElem_inv_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_inv_mk' (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk' a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_invVector (a : PermOf n)  {i : ℕ} (hi : i < n) :
  a.invVector[i] = a⁻¹[i] := rfl

theorem invVector_eq_iff_forall_getElem_eq (a b : PermOf n) :
    a.invVector = b.invVector ↔ ∀ {i} (hi : i < n), a⁻¹[i] = b⁻¹[i] := by
  simp_rw [Vector.ext_iff, getElem_invVector]

@[simp]
theorem getElem_inv_getElem (a : PermOf n) {i : ℕ} (hi : i < n) :
    a⁻¹[a[i]] = i := a.getElem_invVector_getElem_toVector hi

@[simp]
theorem getElem_getElem_inv (a : PermOf n) {i : ℕ} (hi : i < n) :
  a[a⁻¹[i]] = i := (a⁻¹).getElem_invVector_getElem_toVector hi

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
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by
    · rcases a ; rcases b ; simp_rw [mk.injEq]
      exact h
  simp_rw [toVector_eq_iff_forall_getElem_eq, invVector_eq_iff_forall_getElem_eq,
    a.getElem_inv_eq_iff _ (b⁻¹.getElem_lt _), h,
    getElem_getElem_inv, implies_true, and_self]

instance : Subsingleton (PermOf 0) where
  allEq a b := by simp_rw [PermOf.ext_iff, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true]

instance : Subsingleton (PermOf 1) where
  allEq a b := by
    simp_rw [PermOf.ext_iff]
    intro _ hi
    have ha := a.getElem_lt (hi := hi)
    have hb := b.getElem_lt (hi := hi)
    rw [Nat.lt_one_iff] at ha hb
    exact ha.trans hb.symm

instance : Finite (PermOf n) := Finite.of_injective
  (fun a => (fun (i : Fin n) => (⟨a[i.1], a.getElem_lt⟩ : Fin n))) <| fun a b => by
    simp only [Prod.mk.injEq, and_imp, funext_iff, Fin.forall_iff, Fin.ext_iff]
    exact ext

def shuffle {α : Type*} (a : PermOf n) (v : Vector α n) : Vector α n :=
  v.mapFinIdx (fun i _ hi => v[a[i]])

section shuffle

variable {α : Type*}

@[simp] theorem getElem_shuffle (a : PermOf n) (v : Vector α n) {i : ℕ} (hi : i < n) :
    (a.shuffle v)[i] = v[a[i]] := Vector.getElem_mapFinIdx _ _ _ _

@[simp] theorem shuffle_shuffle_inv (a : PermOf n) (v : Vector α n) :
    a.shuffle (a⁻¹.shuffle v) = v := by
  simp_rw [Vector.ext_iff, getElem_shuffle, getElem_inv_getElem, implies_true]

@[simp] theorem shuffle_inv_shuffle (a : PermOf n) (v : Vector α n) :
    a⁻¹.shuffle (a.shuffle v) = v := by
  simp_rw [Vector.ext_iff, getElem_shuffle, getElem_getElem_inv, implies_true]

theorem mem_of_mem_shuffle (a : PermOf n) {v : Vector α n} {x : α}
    (hx : x ∈ a.shuffle v) : x ∈ v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_shuffle] at hx
  rcases hx with ⟨i, hi, hix⟩
  exact ⟨a[i], a.getElem_lt, hix⟩

theorem mem_shuffle_of_mem (a : PermOf n) {v : Vector α n} {x : α}
    (hx : x ∈ v) : x ∈ a.shuffle v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_shuffle]
  rcases hx with ⟨i, hi, hix⟩
  refine ⟨a⁻¹[i], getElem_lt _, ?_⟩
  simp_rw [getElem_getElem_inv, hix]

theorem mem_onIndices_iff (a : PermOf n) {v : Vector α n} {x : α} :
    x ∈ a.shuffle v ↔ x ∈ v := ⟨a.mem_of_mem_shuffle, a.mem_shuffle_of_mem⟩

@[simp]
theorem shuffle_range (a : PermOf n) :
    a.shuffle (Vector.range n) = a.toVector := by
  simp_rw [Vector.ext_iff, getElem_shuffle, Vector.getElem_range,
    getElem_toVector, implies_true]

theorem inv_shuffle_range (a : PermOf n) :
    (a⁻¹).shuffle (Vector.range n) = a.invVector := by
  simp_rw [Vector.ext_iff, getElem_shuffle, Vector.getElem_range,
    getElem_invVector, implies_true]

end shuffle

instance {α : Type*} : SMul  (PermOf n)ᵐᵒᵖ (Vector α n) where
  smul a v := a.unop.shuffle v

section SMulOp

variable {α : Type*}

@[simp] theorem op_smul (a : PermOf n) (v : Vector α n) :
    (MulOpposite.op a) • v = a.shuffle v := rfl

@[simp] theorem unop_shuffle (a : (PermOf n)ᵐᵒᵖ) (v : Vector α n) :
    a.unop.shuffle v = a • v := rfl

end SMulOp

instance : One (PermOf n) where
  one := PermOf.mk (Vector.range n) (Vector.range n)
    (fun h => by simp_rw [Vector.getElem_range, h])
    (fun _ => by simp_rw [Vector.getElem_range])

section One

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : PermOf n)[i] = i := Vector.getElem_range _ _

@[simp] theorem one_shuffle {α : Type*} (v : Vector α n) :
    (1 : (PermOf n)).shuffle v = v := by
  simp_rw [Vector.ext_iff, getElem_shuffle, getElem_one, implies_true]

instance : Inhabited (PermOf n) := ⟨1⟩

@[simp]
theorem default_eq : (default : PermOf n) = 1 := rfl

end One

instance : Unique (PermOf 0) := Unique.mk' _
instance : Unique (PermOf 1) := Unique.mk' _

instance : Mul (PermOf n) where
  mul a b := {
    toVector := b.shuffle a.toVector
    invVector := a⁻¹.shuffle b⁻¹.toVector
    getElem_toVector_lt := fun {i} hi => by
      simp_rw [getElem_shuffle, getElem_toVector, getElem_lt]
    getElem_invVector_getElem_toVector := fun {i} hi => by
      simp_rw [getElem_shuffle, getElem_toVector, getElem_inv_getElem]}

section Mul

@[simp]
theorem getElem_mul (a b : PermOf n) {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]] := getElem_shuffle _ _ _

@[simp] theorem mul_shuffle (a b : PermOf n) {α : Type*} (v : Vector α n) :
    (a * b).shuffle v = b.shuffle (a.shuffle v) := by
  simp_rw [Vector.ext_iff, getElem_shuffle, getElem_mul, implies_true]

end Mul

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

instance {α : Type*} : MulAction (PermOf n)ᵐᵒᵖ (Vector α n) where
  one_smul _ := one_shuffle _
  mul_smul _ _ _ := mul_shuffle _ _ _

end Group

def ofVector (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : PermOf n where
  toVector := a
  invVector := (Vector.range n).map a.toList.idxOf
  getElem_toVector_lt := hx
  getElem_invVector_getElem_toVector := fun {i} hi => by
    simp_rw [Vector.getElem_map, Vector.getElem_range]
    exact a.toList.idxOf_getElem ha _ _

section OfVector

@[simp]
theorem getElem_ofVector {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) : (ofVector a hx ha)[i] = a[i] := rfl

@[simp] theorem ofVector_toVector (a : PermOf n) :
    ofVector a.toVector a.getElem_toVector_lt a.toVector_toList_Nodup = a :=
  ext <| fun _ => by simp_rw [getElem_ofVector, getElem_toVector]

@[simp] theorem ofVector_invVector (a : PermOf n) :
    ofVector a.invVector a.getElem_invVector_lt a.invVector_toList_Nodup = a⁻¹ :=
  ext <| fun _ => by simp_rw [getElem_ofVector, getElem_invVector]

end OfVector

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

theorem smul_right_inj (a : PermOf n) {i j : ℕ} : a • i = a • j ↔ i = j := by
  rcases lt_or_le i n with hin | hin <;>
  rcases lt_or_le j n with hjn | hjn
  · simp_rw [a.smul_of_lt hin, a.smul_of_lt hjn, a.getElem_inj]
  · simp_rw [a.smul_of_lt hin, a.smul_of_ge hjn, (hin.trans_le hjn).ne, iff_false]
    exact ne_of_lt (hjn.trans_lt' a.getElem_lt)
  · simp_rw [a.smul_of_ge hin, a.smul_of_lt hjn, (hjn.trans_le hin).ne', iff_false]
    exact ne_of_gt (hin.trans_lt' a.getElem_lt)
  · simp_rw [a.smul_of_ge hin, a.smul_of_ge hjn]

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

section MulAction

theorem smul_eq_iff_eq_one (a : PermOf n) : (∀ {i : ℕ}, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul, one_smul]

theorem smul_eq_id_iff_eq_one (a : PermOf n) : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [funext_iff, id_eq, smul_eq_iff_eq_one]

end MulAction

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
  toVector := a.toVector.swap i j
  invVector := a.invVector.map (fun k => Equiv.swap i j k)
  getElem_toVector_lt := fun _ => by
    simp_rw [Vector.getElem_swap_eq_getElem_swap_apply, getElem_toVector, getElem_lt]
  getElem_invVector_getElem_toVector := fun _ => by
    simp_rw [Vector.getElem_map, getElem_invVector, Vector.getElem_swap_eq_getElem_swap_apply,
      getElem_toVector, getElem_inv_getElem, swap_apply_self]

section Swap

variable (i j k : ℕ) (hi : i < n) (hj : j < n)

@[simp]
theorem getElem_swap (a : PermOf n) (hk : k < n) :
    (a.swap i j hi hj)[k] = a[Equiv.swap i j k]'(swap_prop_const (· < n) hk hi hj) :=
  Vector.getElem_swap_eq_getElem_swap_apply _ _ _ hi hj _ _

@[simp]
theorem getElem_inv_swap (a : PermOf n) (hk : k < n) :
    (a.swap i j hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.invVector.getElem_map _ _ _

theorem swap_smul_eq_smul_swap (a : PermOf n) :
    (a.swap i j hi hj) • k = a • (Equiv.swap i j k) := by
  rcases lt_or_ge k n with hk | hk
  · simp_rw [smul_of_lt _ (swap_prop_const (· < n) hk hi hj), smul_of_lt _ hk, getElem_swap]
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

section Cast

variable {m n o : ℕ}

/--
`PermOf.cast` re-interprets an `PermOf n` as an `PermOf m`, where `n = m`.
-/
@[inline] protected def cast (hnm : n = m) (a : PermOf n) : PermOf m where
  toVector := a.toVector.cast hnm
  invVector := a.invVector.cast hnm
  getElem_toVector_lt := fun _ => by
    simp_rw [Vector.getElem_cast, hnm.symm, getElem_toVector, getElem_lt]
  getElem_invVector_getElem_toVector :=
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

@[irreducible] def FixLTOfLT (a : PermOf n) (m : ℕ) : Prop :=
    ∀ {i : ℕ}, i < m → ∀ {hi : i < n}, a[i] < m

section FixLTOfLT

variable {a : PermOf n} {i m : ℕ}

theorem fixLTOfLT_def :
    a.FixLTOfLT m ↔ ∀ {i : ℕ}, i < m → ∀ {hi : i < n}, a[i] < m := by
  unfold FixLTOfLT
  exact Iff.rfl

theorem FixLTOfLT.getElem_lt_of_lt (him : i < m) (ha : a.FixLTOfLT m)
    (hin : i < n := by get_elem_tactic) : a[i] < m := by
  unfold FixLTOfLT at ha
  exact ha him

theorem fixLTOfLT_of_lt_imp_getElem_lt (ha : ∀ {i}, i < m → ∀ {hi : i < n}, a[i] < m) :
    a.FixLTOfLT m := by
  unfold FixLTOfLT
  exact ha

theorem fixLTOfLT_eq : ∀ (a : PermOf n), a.FixLTOfLT n :=
  fun a => fixLTOfLT_of_lt_imp_getElem_lt (fun _ => a.getElem_lt)

theorem fixLTOfLT_ge (hnm : n ≤ m) : ∀ (a : PermOf n), a.FixLTOfLT m :=
  fun a => fixLTOfLT_of_lt_imp_getElem_lt (fun _ => a.getElem_lt.trans_le hnm)

theorem fixLTOfLT_succ : a.FixLTOfLT (n + 1) := a.fixLTOfLT_ge (Nat.le_succ _)

theorem FixLTOfLT.getElem_eq_self {a : PermOf (n + 1)} (ha : a.FixLTOfLT n) : a[n] = n := by
  rcases a.getElem_surjective (Nat.lt_succ_self _) with ⟨k, hk, hkn⟩
  simp_rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at hk
  rcases hk with hk | rfl
  · exact ((ha.getElem_lt_of_lt hk).ne hkn).elim
  · exact hkn

theorem fixLTOfLT_of_getElem_eq_self {a : PermOf (n + 1)} (ha : a[n] = n) :
    a.FixLTOfLT n :=
  fixLTOfLT_of_lt_imp_getElem_lt (fun {i} hi =>
    (Nat.le_of_lt_succ a.getElem_lt).lt_or_eq.elim id
    (fun h => (hi.ne (a.getElem_injective _ _ (h.trans ha.symm))).elim))

theorem fixLTOfLT_iff_getElem_eq_self {a : PermOf (n + 1)} : a.FixLTOfLT n ↔ a[n] = n :=
    ⟨FixLTOfLT.getElem_eq_self, fixLTOfLT_of_getElem_eq_self⟩

theorem fixLTOfLT_of_getElem_eq_getElem_eq {a : PermOf (n + 2)} (ha₁ : a[n + 1] = n + 1)
    (ha₂ : a[n] = n) : a.FixLTOfLT n :=
  fixLTOfLT_of_lt_imp_getElem_lt (fun {i} hi {_} => by
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
      simp_rw [(Nat.lt_succ_self _).not_lt] at hi)

theorem fixLTOfLT_zero : ∀ (a : PermOf n), a.FixLTOfLT 0 :=
  fun _ => fixLTOfLT_of_lt_imp_getElem_lt (fun h => (Nat.not_lt_zero _ h).elim)

theorem fixLTOfLT_one : (1 : PermOf n).FixLTOfLT m :=
  fixLTOfLT_of_lt_imp_getElem_lt (fun him => getElem_one _ ▸ him)

theorem FixLTOfLT.mul {b : PermOf n}
    (ha : a.FixLTOfLT m) (hb : b.FixLTOfLT m) : (a * b).FixLTOfLT m :=
  fixLTOfLT_of_lt_imp_getElem_lt (fun him _ => a.getElem_mul b _ ▸
    ha.getElem_lt_of_lt (hb.getElem_lt_of_lt him))

theorem FixLTOfLT.pow
    (ha : a.FixLTOfLT m) {k : ℕ} : (a^k).FixLTOfLT m := by
  induction k with | zero => _ | succ _ IH => _
  · exact pow_zero a ▸ fixLTOfLT_one
  · simp_rw [pow_succ]
    exact IH.mul ha

theorem FixLTOfLT.inv (ha : a.FixLTOfLT m) : a⁻¹.FixLTOfLT m := by
  rcases lt_or_le m n with hnm | hnm
  · have H : Surjective (fun (i : Fin m) =>
      Fin.mk (n := m) a[i.1] (ha.getElem_lt_of_lt i.isLt)) :=
      Injective.surjective_of_fintype (Equiv.refl (Fin m)) fun _ _ => by
      simp_rw [Fin.mk.injEq, Fin.ext_iff, getElem_inj, imp_self]
    refine fixLTOfLT_of_lt_imp_getElem_lt (fun {i} him hin => ?_)
    rcases H ⟨i, him⟩ with ⟨⟨j, hj⟩, haj⟩
    simp_rw [Fin.ext_iff] at haj
    subst haj
    refine hj.trans_eq' (a.getElem_inv_getElem _)
  · exact a⁻¹.fixLTOfLT_ge hnm

theorem FixLTOfLT.zpow (ha : a.FixLTOfLT m) {k : ℤ} : (a^k).FixLTOfLT m := by
  rcases k
  · simp_rw [Int.ofNat_eq_coe, zpow_natCast]
    exact ha.pow
  · simp_rw [zpow_negSucc]
    exact ha.pow.inv

@[simp] theorem fixLTOfLT_inv_iff :
    (a⁻¹.FixLTOfLT m) ↔ (a.FixLTOfLT m) := ⟨fun ha => ha.inv, fun ha => ha.inv⟩

theorem fixLTOfLT_of_le_of_lt_imp_getElem_lt (hmn : m ≤ n)
    (ha : ∀ {i} (hi : i < m), a[i] < m) : a.FixLTOfLT m :=
  fixLTOfLT_of_lt_imp_getElem_lt (fun him => ha him)

@[simps!]
def fixLTOfLTSubgroup (n m : ℕ) : Subgroup (PermOf n) where
  carrier a := a.FixLTOfLT m
  mul_mem' ha hb := FixLTOfLT.mul ha hb
  one_mem' := fixLTOfLT_one
  inv_mem' ha := FixLTOfLT.inv ha

@[simp]
theorem mem_fixLTOfLTSubgroup_iff : a ∈ fixLTOfLTSubgroup n m ↔ a.FixLTOfLT m := Iff.rfl

theorem fixLTOfLTSubgroup_eq_top_of_ge (hnm : n ≤ m) : fixLTOfLTSubgroup n m = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_fixLTOfLTSubgroup_iff, fixLTOfLT_ge hnm, implies_true]

theorem fixLTOfLTSubgroup_eq_eq_top : fixLTOfLTSubgroup n n = ⊤ := fixLTOfLTSubgroup_eq_top_of_ge le_rfl

theorem fixLTOfLTSubgroup_zero_eq_top : fixLTOfLTSubgroup n 0 = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_fixLTOfLTSubgroup_iff, fixLTOfLT_zero, implies_true]

end FixLTOfLT

def castGE {m n : ℕ} (hnm : n ≤ m) (a : PermOf n) : PermOf m where
  toVector := (a.toVector ++ (Vector.range (m - n)).map (· + n)).cast (Nat.add_sub_cancel' hnm)
  invVector := (a.invVector ++ (Vector.range (m - n)).map (· + n)).cast (Nat.add_sub_cancel' hnm)
  getElem_toVector_lt := fun {i} him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_append, getElem_toVector,
      Vector.getElem_map, Vector.getElem_range]
    rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true]
      exact a.getElem_lt.trans_le hnm
    · simp_rw [hin.not_lt, dite_false, Nat.sub_add_cancel hin, him]
  getElem_invVector_getElem_toVector := fun {i} him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_append, getElem_toVector, Vector.getElem_map,
      Vector.getElem_range, getElem_invVector]
    rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true, a.getElem_lt, dite_true, getElem_inv_getElem]
    · simp_rw [hin.not_lt, dite_false, Nat.sub_add_cancel hin, hin.not_lt, dite_false]

section CastGE

variable {n m k i : ℕ} {a : PermOf n}

theorem getElem_castGE {i : ℕ} {hi : i < m} {hnm : n ≤ m} :
    (a.castGE hnm)[i] = if hi : i < n then a[i] else i := by
  unfold castGE
  simp_rw [getElem_mk, Vector.getElem_cast, Vector.getElem_append, getElem_toVector,
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
    (a * b).castGE hnm = a.castGE hnm * b.castGE hnm := by
  simp_rw [eq_iff_smul_eq_smul, mul_smul, castGE_smul, mul_smul, implies_true]

theorem castGE_of_eq (hnm : n = m) (hnm' : n ≤ m := hnm.le) :
    a.castGE hnm' = a.cast hnm := by
  ext i hi
  simp_rw [getElem_castGE, getElem_cast, hi.trans_eq hnm.symm, dite_true]

@[simp] theorem castGE_rfl  :
    a.castGE le_rfl = a := by
  simp_rw [castGE_of_eq, cast_rfl]

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

theorem fixLTOfLT_castGE {hnm : n ≤ m} (hnk : n ≤ k) : (a.castGE hnm).FixLTOfLT k :=
  fixLTOfLT_of_lt_imp_getElem_lt (fun hik => by
    simp_rw [getElem_castGE]
    split_ifs with hin
    · exact a.getElem_lt.trans_le hnk
    · exact hik)

theorem fixLTOfLT_castGE_eq {hnm : n ≤ m} : (a.castGE hnm).FixLTOfLT n := a.fixLTOfLT_castGE le_rfl

theorem castGE_mem_fixLTOfLTSubgroup {hnm : n ≤ m} (hnk : n ≤ k) :
    (a.castGE hnm) ∈ fixLTOfLTSubgroup m k := a.fixLTOfLT_castGE hnk

theorem castGE_mem_fixLTOfLTSubgroup_eq {hnm : n ≤ m} :
    (a.castGE hnm) ∈ fixLTOfLTSubgroup m n := a.fixLTOfLT_castGE_eq

theorem castGE_lt_of_lt {hnm : n ≤ m} (him : i < n) : (a.castGE hnm)[i] < n := by
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

@[simps! apply]
def castGEMonoidHom (hnm : n ≤ m) : PermOf n →* PermOf m where
  toFun a := a.castGE hnm
  map_mul' _ _ := castGE_mul hnm
  map_one' := castGE_one

theorem castGEMonoidHom_injective {hnm : n ≤ m} :
    (⇑(castGEMonoidHom hnm)).Injective :=
  fun _ _ h => castGE_injective hnm h

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

def castLE {m n : ℕ} (hmn : m ≤ n) (a : PermOf n) (ham : a.FixLTOfLT m) : PermOf m where
  toVector := (a.toVector.take m).cast (min_eq_left hmn)
  invVector := (a.invVector.take m).cast (min_eq_left hmn)
  getElem_toVector_lt := fun him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_take', getElem_toVector, ham.getElem_lt_of_lt him]
  getElem_invVector_getElem_toVector := fun _ => by
    simp_rw [Vector.getElem_cast, Vector.getElem_take', getElem_invVector_getElem_toVector]

section CastLE

variable {m i k : ℕ} (a : PermOf n) (ham : a.FixLTOfLT m) {hmn : m ≤ n}

@[simp] theorem getElem_castLE (him : i < m) :
    (a.castLE hmn ham)[i] = a[i] := by
  unfold castLE
  simp_rw [getElem_mk, Vector.getElem_cast, Vector.getElem_take', getElem_toVector]

theorem inv_castLE : (a.castLE hmn ham)⁻¹ = a⁻¹.castLE hmn ham.inv := rfl

theorem getElem_inv_castLE (him : i < m) :
    (a.castLE hmn ham)⁻¹[i] = a⁻¹[i]  := by
  simp_rw [inv_castLE, getElem_castLE]

@[simp]
theorem castLE_one : ((1 : PermOf n).castLE hmn fixLTOfLT_one) = (1 : PermOf m) := by
  ext i hi : 1
  simp_rw [getElem_castLE, getElem_one]

theorem castLE_mul (hmn : m ≤ n) {a b : PermOf n} (ham : a.FixLTOfLT m) (hbm : b.FixLTOfLT m) :
    (a * b).castLE hmn (ham.mul hbm) = a.castLE hmn ham * b.castLE hmn hbm := by
  ext i
  simp only [getElem_mul, getElem_castLE]

@[simp] theorem castLE_of_eq {a : PermOf n} (ham : a.FixLTOfLT m) (hnm : n = m)
    (hnm' : m ≤ n := hnm.ge) : a.castLE hnm' ham = a.cast hnm := by
  ext i hi
  simp_rw [getElem_castLE, getElem_cast]

theorem FixLTOfLT.castLE {a : PermOf n} (ham : a.FixLTOfLT m) {hkn : k ≤ n} {hak : a.FixLTOfLT k} :
    (a.castLE hkn hak).FixLTOfLT m := fixLTOfLT_of_lt_imp_getElem_lt (fun hik => by
    simp_rw [getElem_castLE]
    exact ham.getElem_lt_of_lt hik)

theorem castLE_trans {a : PermOf n} (ham : a.FixLTOfLT m) {hkn : k ≤ n} {hmk : m ≤ k}
    (hak : a.FixLTOfLT k) :
    (a.castLE hkn hak).castLE hmk ham.castLE = a.castLE (hmk.trans hkn) ham := by
  ext i hi
  simp_rw [getElem_castLE]

theorem castLE_castGE {hnm : n ≤ m} :
    (a.castGE hnm).castLE hnm a.fixLTOfLT_castGE_eq = a := by
  ext i hi
  simp_rw [getElem_castLE, a.getElem_castGE_of_lt hi]

theorem getElem_castGE_castLE_of_lt (hi : i < m) : ((a.castLE hmn ham).castGE hmn)[i] = a[i] := by
  simp_rw [getElem_castGE_of_lt hi, getElem_castLE]

theorem castLE_surjective (hmn : m ≤ n) (b : PermOf m) :
    ∃ (a : PermOf n), ∃ (ham : a.FixLTOfLT m), a.castLE hmn ham = b := by
  exact ⟨_, _, b.castLE_castGE⟩

@[simps! apply]
def castLEMonoidHom (hmn : m ≤ n) : fixLTOfLTSubgroup n m →* PermOf m where
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
    (a * b).castSucc = a.castSucc * b.castSucc := castGE_mul _

@[simp] theorem castSucc_castSucc :
    a.castSucc.castSucc = a.castGE (by omega) := castGE_trans

@[simp] theorem castGE_castSucc (h : n ≤ m) :
    (a.castGE h).castSucc = a.castGE (h.trans (Nat.le_succ _)) := castGE_trans

@[simp] theorem castSucc_castGE (h : n + 1 ≤ m) :
    a.castSucc.castGE h = a.castGE ((Nat.le_succ _).trans h) := castGE_trans

theorem fixLTOfLT_castSucc (hnk : n ≤ k) : a.castSucc.FixLTOfLT k := fixLTOfLT_castGE hnk

theorem fixLTOfLT_castSucc_eq : (a.castSucc).FixLTOfLT n := a.fixLTOfLT_castSucc le_rfl

theorem castSucc_mem_fixLTOfLTSubgroup (hnk : n ≤ k) :
    a.castSucc ∈ fixLTOfLTSubgroup (n + 1) k := a.fixLTOfLT_castGE hnk

theorem castSucc_mem_fixLTOfLTSubgroup_eq :
    a.castSucc ∈ fixLTOfLTSubgroup (n + 1) n := a.fixLTOfLT_castGE_eq

theorem castSucc_lt_imp_getElem_lt (hi : i < n) : (a.castSucc)[i] < n := by
  simp_rw [getElem_castSucc, hi.ne, dite_false]
  exact a.getElem_lt

theorem castSucc_inj {a b : PermOf n} : a.castSucc = b.castSucc ↔ a = b := castGE_inj

theorem castSucc_injective : Function.Injective (castSucc (n := n)) :=
  fun _ _ => castSucc_inj.mp

@[simps! apply]
def castSuccMonoidHom : PermOf n →* PermOf (n + 1) where
  toFun a := a.castSucc
  map_mul' _ _ := castSucc_mul
  map_one' := castSucc_one

theorem castSuccMonoidHom_injective :
    (⇑(castSuccMonoidHom (n := n))).Injective :=
  fun _ _ h => castSucc_injective h

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
    a.castLE (Nat.le_succ _) (a.fixLTOfLT_of_getElem_eq_self ha)
/-
def castPred (a : PermOf (n + 1)) (ha : a[n] = n) : PermOf n where
  toVector := a.toVector.pop
  invVector := a.invVector.pop
  getElem_toVector_lt := by
    simp_rw [Vector.getElem_pop', getElem_toVector]
  getElem_invVector_getElem_toVector := by
    simp_rw [Vector.getElem_pop', getElem_toVector, getElem_invVector,
      getElem_inv_getElem, implies_true]
-/

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

theorem FixLTOfLT.castPred {a : PermOf (n + 1)} (ha : a[n] = n) {hak : a.FixLTOfLT m} :
    (a.castPred ha).FixLTOfLT m := FixLTOfLT.castLE hak

theorem castPred_trans {a : PermOf (n + 2)} (ha₁ : a[n + 1] = n + 1)
    (ha₂ : a[n] = n) :
    (a.castPred ha₁).castPred (by simp_rw [getElem_castPred, ha₂]) =
    a.castLE (Nat.le_add_right _ _) (a.fixLTOfLT_of_getElem_eq_getElem_eq ha₁ ha₂):= castLE_trans _ _

@[simp] theorem castPred_castSucc {a : PermOf n} :
    a.castSucc.castPred getElem_castSucc_of_eq = a := castLE_castGE _

theorem getElem_castSucc_castPred_of_lt (hi : i < n) :
    ((a.castPred ha).castSucc)[i] = a[i] := getElem_castGE_castLE_of_lt _ _ hi

theorem castPred_surjective (b : PermOf n) :
    ∃ (a : PermOf (n + 1)), ∃ (ha : a[n] = n), a.castPred ha = b :=
  ⟨_, _, b.castPred_castSucc⟩

@[simps! apply]
def castPredMonoidHom : fixLTOfLTSubgroup (n + 1) n →* PermOf n where
  toFun  := fun ⟨a, h⟩ => a.castPred h.getElem_eq_self
  map_mul' a b := castPred_mul a.2.getElem_eq_self b.2.getElem_eq_self
  map_one' := by simp_rw [castPred_one]

theorem castPredMonoidHom_surjective :
  (⇑(castPredMonoidHom (n := n))).Surjective := fun a => Subtype.exists.mpr
    (by rcases a.castPred_surjective with ⟨b, hb, h⟩ ;
        exact ⟨b, fixLTOfLT_of_getElem_eq_self hb, h⟩)

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
`PermOf n` is congruent to `Perm (Fin n)`, and this respects the
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
`ofNatFixLTOfLT` maps a member of `Perm ℕ` which maps the subtype `< n` to itself to the corresponding
`PermOf n`.
-/
def ofNatFixLTOfLT : NatFixLTOfLT n →* PermOf n where
  toFun e := {
    toVector := (Vector.range n).map e
    invVector := (Vector.range n).map ⇑e.1⁻¹
    getElem_toVector_lt := fun {i} => by
      simp_rw [Vector.getElem_map, Vector.getElem_range]
      exact e.2 _
    getElem_invVector_getElem_toVector := by
      simp only [Vector.getElem_map, Vector.getElem_range, Perm.inv_apply_self, implies_true]}
  map_one' := by
    simp_rw [PermOf.ext_iff, getElem_mk, OneMemClass.coe_one, Vector.getElem_map, one_apply,
      Vector.getElem_range, getElem_one, implies_true]
  map_mul' a b := by
    simp_rw [PermOf.ext_iff, getElem_mul, getElem_mk, Vector.getElem_map,
      Vector.getElem_range, Subgroup.coe_mul, mul_apply, implies_true]

section ofNatFixLTOfLT

open Perm

@[simp]
theorem getElem_ofNatFixLTOfLT {e : NatFixLTOfLT n} {i : ℕ}
    (hi : i < n) : (ofNatFixLTOfLT e)[i] = e.1 i := by
  unfold ofNatFixLTOfLT
  simp_rw [MonoidHom.coe_mk, OneHom.coe_mk, getElem_mk,
    Vector.getElem_map, Vector.getElem_range]

@[simp]
theorem getElem_ofNatFixLTOfLT_inv {e : NatFixLTOfLT n} {i : ℕ} (hi : i < n) :
    (ofNatFixLTOfLT e)⁻¹[i] = e.1⁻¹ i := by
  unfold ofNatFixLTOfLT
  simp_rw [MonoidHom.coe_mk, OneHom.coe_mk, getElem_inv_mk,
    Vector.getElem_map, Vector.getElem_range]

theorem ofNatFixLTOfLT_smul {e : NatFixLTOfLT n} {i : ℕ} :
    (ofNatFixLTOfLT e) • i = if i < n then e.1 i else i := by
  simp_rw [smul_eq_dite, getElem_ofNatFixLTOfLT, dite_eq_ite]

theorem ofNatFixLTOfLT_surjective : Function.Surjective (ofNatFixLTOfLT (n := n)) := by
  intro a
  let b : NatFixLTOfLT n := ⟨⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩,
    fun _ => a.smul_lt_of_lt⟩
  refine ⟨b, PermOf.ext ?_⟩
  simp_rw [getElem_ofNatFixLTOfLT]
  exact a.smul_of_lt

theorem natPerm_ofNatFixLTOfLT_apply {e : NatFixLTOfLT n} (i : ℕ) :
    natPerm (ofNatFixLTOfLT e) i = if i < n then e.1 i else i := by
  simp_rw [natPerm_apply_apply, ofNatFixLTOfLT_smul]

theorem natPerm_ofNatFixLTOfLT_of_mem_natFixGE {e : Perm ℕ} :
   (he : e ∈ NatFixGE n) → natPerm (ofNatFixLTOfLT ⟨e, natFixGE_le_NatFixLTOfLT he⟩) = e := by
  simp_rw [Equiv.ext_iff, natPerm_ofNatFixLTOfLT_apply, ite_eq_left_iff, not_lt,
    eq_comm (b := e _)]
  exact fixed_ge_of_mem_natFixGE

theorem ofNatFixLTOfLT_natPerm {a : PermOf n} :
    ofNatFixLTOfLT ⟨natPerm a, natFixGE_le_NatFixLTOfLT natPerm_mem_natFixGE⟩ = a := by
  ext i hi
  simp_rw [getElem_ofNatFixLTOfLT, a.natPerm_apply_apply_of_lt hi]

theorem exists_natPerm_apply_iff_mem_natFixGE {e : Perm ℕ} :
    (∃ a : PermOf n, natPerm a = e) ↔ e ∈ NatFixGE n := by
  refine ⟨?_, fun he => ?_⟩
  · rintro ⟨a, rfl⟩ _ hi
    exact a.natPerm_apply_apply_of_ge hi
  · exact ⟨ofNatFixLTOfLT ⟨e, natFixGE_le_NatFixLTOfLT he⟩,
      natPerm_ofNatFixLTOfLT_of_mem_natFixGE he⟩

theorem range_natPerm : natPerm (n := n).range = NatFixGE n := by
  simp_rw [SetLike.ext_iff, MonoidHom.mem_range,
    exists_natPerm_apply_iff_mem_natFixGE, implies_true]

end ofNatFixLTOfLT

open Perm in
@[simps! apply symm_apply]
def mulEquivNatFixGE : PermOf n ≃* NatFixGE n :=
  MonoidHom.toMulEquiv
  (natPerm.codRestrict _ (fun _ => natPerm_mem_natFixGE))
  (ofNatFixLTOfLT.comp (SubgroupClass.inclusion natFixGE_le_NatFixLTOfLT))
  (by simp_rw [MonoidHom.ext_iff, MonoidHom.comp_apply,
      MonoidHom.codRestrict_apply, SubgroupClass.inclusion_mk,
      MonoidHom.id_apply, ofNatFixLTOfLT_natPerm, implies_true])
  (by simp_rw [MonoidHom.ext_iff, MonoidHom.comp_apply,
      MonoidHom.codRestrict_apply, Subtype.forall,
      SubgroupClass.inclusion_mk, MonoidHom.id_apply, Subtype.mk.injEq]
      exact fun _ => natPerm_ofNatFixLTOfLT_of_mem_natFixGE)

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
    SubgroupClass.inclusion_mk, getElem_ofNatFixLTOfLT]

@[simp]
theorem getElem_mulEquivNatFixGE_symm_inv_mk {e : Perm ℕ} (he : e ∈ NatFixGE n)
    {i : ℕ} (hi : i < n) : (mulEquivNatFixGE.symm ⟨e, he⟩)⁻¹[i] = e⁻¹ i := by
  unfold mulEquivNatFixGE
  simp_rw [MonoidHom.toMulEquiv_symm_apply, MonoidHom.comp_apply,
    SubgroupClass.inclusion_mk, getElem_ofNatFixLTOfLT_inv]

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

theorem minLen_one : (1 : PermOf n).minLen = 0 := by
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
  · simp_rw [Nat.le_zero] at hnm
    cases hnm
    simp_rw [minLen_zero]
  · rcases hnm.eq_or_lt with rfl | hnm
    · simp_rw [castGE_of_eq, minLen_cast]
    · simp_rw [Nat.lt_succ_iff] at hnm
      simp_rw [← castGE_castSucc hnm, minLen_castSucc, IH]

@[simp] theorem getElem_of_ge_minLen {a : PermOf n} {i : ℕ} (hi : a.minLen ≤ i) {hi' : i < n} :
    a[i] = i := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [Nat.not_lt_zero] at hi'
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

structure FinitePerm where
  len : ℕ
  toPermOf : PermOf len
  toPermOf_minLen : toPermOf.minLen = len
  deriving DecidableEq

namespace FinitePerm

open PermOf Equiv Equiv.Perm

variable {n m : ℕ}

@[ext] theorem ext {a b : FinitePerm} (hab : a.toPermOf.IsCongr b.toPermOf) : a = b := by
  cases a with | mk n a hna => _
  cases b with | mk m b hmb => _
  simp_rw [FinitePerm.mk.injEq]
  have hnm : n = m := hna.symm.trans (hab.minLen_eq.trans hmb)
  subst hnm
  simp_rw [isCongr_iff_eq] at hab
  simp_rw [heq_eq_eq, true_and, hab]

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

instance : One FinitePerm := ⟨⟨0, 1, minLen_zero⟩⟩

theorem one_len : (1 : FinitePerm).len = 0 := rfl

@[simp]
theorem one_toPermOf : (1 : FinitePerm).toPermOf = 1 := rfl

instance mul : Mul FinitePerm where
  mul a b :=
  let ab := ((a.toPermOf.castGE (le_max_left a.len b.len)) *
    (b.toPermOf.castGE (le_max_right a.len b.len)))
  ⟨ab.minLen, ab.minPerm, minLen_minPerm⟩

theorem mul_len (a b : FinitePerm): (a * b).len =
      (a.toPermOf.castGE (le_max_left a.len b.len) * b.toPermOf.castGE
      (le_max_right a.len b.len)).minLen := rfl

theorem mul_toPermOf (a b : FinitePerm): (a * b).toPermOf =
      ( a.toPermOf.castGE (le_max_left a.len b.len) * b.toPermOf.castGE
      (le_max_right a.len b.len)).minPerm := rfl

instance : Inv FinitePerm where
  inv a := ⟨a.len, a.toPermOf⁻¹, minLen_inv.trans a.toPermOf_minLen⟩

theorem inv_len (a : FinitePerm): (a⁻¹).len = a.len := rfl

theorem inv_toPermOf (a : FinitePerm) : (a⁻¹).toPermOf = a.toPermOf⁻¹ := rfl

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
    simp_rw [mul_toPermOf, one_toPermOf, inv_toPermOf, ← inv_castGE,
      isCongr_one_iff_eq_one]
    exact minPerm_eq_one_iff_eq_one.mpr (inv_mul_cancel _)

instance : MulAction FinitePerm ℕ where
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

section NatPerm

theorem natPerm_injective : Function.Injective natPerm := fun a b => by
  simp_rw [Equiv.ext_iff, natPerm_apply_apply, eq_iff_smul_eq_smul, imp_self]

theorem natPerm_inj {a b : FinitePerm} : natPerm a = natPerm b ↔ a = b :=
  natPerm_injective.eq_iff

theorem natPerm_toPermOf {a : FinitePerm} :
    a.toPermOf.natPerm = a.natPerm := by
  simp_rw [Equiv.ext_iff, natPerm_apply_apply,
    PermOf.natPerm_apply_apply, toPermOf_smul, implies_true]

theorem natPerm_mem_natFixGE {a : FinitePerm} : a.natPerm ∈ NatFixGE a.len :=
  PermOf.natPerm_mem_natFixGE

theorem natPerm_mem_natFinitePerm {a : FinitePerm} : a.natPerm ∈ NatFinitePerm :=
  natFixGE_le_natFinitePerm natPerm_mem_natFixGE

end NatPerm

end FinitePerm

namespace PermOf

variable {n m : ℕ}

@[simps! apply_toPermOf]
def ofPermOf : PermOf n →* FinitePerm where
  toFun a := ⟨a.minLen, a.minPerm, minLen_minPerm⟩
  map_one' := by
    ext
    simp_rw [ minPerm_one,  one_isCongr_iff_eq_one, FinitePerm.one_toPermOf]
  map_mul' a b := by
    ext
    simp_rw [FinitePerm.mul_toPermOf, isCongr_minPerm_minPerm]
    exact (isCongr_minPerm.trans isCongr_castGE).mul_mul
      (isCongr_minPerm.trans isCongr_castGE)

section OfPermOf

variable {a : PermOf n} {b : PermOf m} {i : ℕ}

@[simp]
theorem smul_ofPermOf : a.ofPermOf • i = a • i := minPerm_smul

@[simp]
theorem toPermOf_ofPermOf {a : FinitePerm} : a.toPermOf.ofPermOf = a := by
  ext
  simp_rw [ofPermOf_apply_toPermOf, minPerm_isCongr]

theorem ofPermOf_len_le : a.ofPermOf.len ≤ n := minLen_le

theorem IsCongr.ofPermOf (hab : a.IsCongr b) : a.ofPermOf = b.ofPermOf := by
  ext
  exact hab.minPerm_minPerm

theorem ofPermOf_eq_iff_isCongr : a.ofPermOf = b.ofPermOf ↔ a.IsCongr b :=
  ⟨by simp_rw [FinitePerm.ext_iff, ofPermOf_apply_toPermOf, isCongr_minPerm_minPerm,
    imp_self], IsCongr.ofPermOf⟩

theorem ofPermOf_inj {b : PermOf n} : a.ofPermOf = b.ofPermOf ↔ a = b := by
  simp_rw [ofPermOf_eq_iff_isCongr, isCongr_iff_eq]

theorem ofPermOf_injective : Function.Injective (ofPermOf (n := n)) := fun a b => by
  simp_rw [ofPermOf_inj, imp_self]

@[simp]
theorem castGE_ofPermOf (hnm : n ≤ m) : (a.castGE hnm).ofPermOf = a.ofPermOf := by
  simp_rw [ofPermOf_eq_iff_isCongr, castGE_isCongr]

theorem natPerm_ofPermOf : a.ofPermOf.natPerm = a.natPerm := by
  simp_rw [Equiv.ext_iff, FinitePerm.natPerm_apply_apply, smul_ofPermOf,
    natPerm_apply_apply, implies_true]

theorem natPerm_eq_ofPermOf_comp_natPerm :
    natPerm (n := n) = FinitePerm.natPerm.comp ofPermOf := by
  simp_rw [MonoidHom.ext_iff, MonoidHom.comp_apply, natPerm_ofPermOf, implies_true]

end OfPermOf

end PermOf

namespace FinitePerm

open PermOf Equiv Equiv.Perm

variable {n m : ℕ}

def FixGE (n : ℕ) : Subgroup FinitePerm where
  carrier := {a : FinitePerm | a.len ≤ n}
  mul_mem' := by
    simp_rw [Set.mem_setOf_eq, mul_len]
    exact fun ha hb => (minLen_le.trans (sup_le ha hb))
  one_mem' := by
    simp_rw [Set.mem_setOf_eq, one_len]
    exact Nat.zero_le _
  inv_mem' := by
    simp_rw [Set.mem_setOf_eq, inv_len, imp_self, implies_true]

section FixGE

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

@[simps apply_coe symm_apply]
def permOfMulEquivFixGE : PermOf n ≃* FixGE n where
  toFun a := ⟨a.ofPermOf, ofPermOf_len_le⟩
  invFun a := a.1.toPermOf.castGE a.2
  left_inv a := by simp_rw [ofPermOf_apply_toPermOf, castGE_minPerm_minLen_le]
  right_inv a := by simp_rw [castGE_ofPermOf, toPermOf_ofPermOf]
  map_mul' a b := by simp_rw [Subtype.ext_iff, Subgroup.coe_mul, map_mul]

theorem permOfMulEquivFixGE_apply_coe_smul {a : PermOf n} {i : ℕ} :
    (permOfMulEquivFixGE a : FinitePerm) • i = a • i := by
  simp_rw [permOfMulEquivFixGE_apply_coe, smul_ofPermOf]

@[simps! apply symm_apply]
def fixGEMulEquivNatFixGE : FixGE n ≃* NatFixGE n :=
  permOfMulEquivFixGE.symm.trans mulEquivNatFixGE

end FixGE

theorem exists_natPerm_apply_iff_mem_natFinitePerm {e : Perm ℕ} :
    (∃ a : FinitePerm, natPerm a = e) ↔ e ∈ NatFinitePerm := by
  refine ⟨?_, fun he => ?_⟩
  · rintro ⟨a, rfl⟩
    exact natPerm_mem_natFinitePerm
  · rw [mem_natFinitePerm_iff] at he
    rcases he with ⟨n, he⟩
    use fixGEMulEquivNatFixGE.symm ⟨e, he⟩
    simp_rw [Equiv.ext_iff, fixGEMulEquivNatFixGE_symm_apply, natPerm_apply_apply,
      permOfMulEquivFixGE_apply_coe_smul, ofNatFixLTOfLT_smul, SubgroupClass.coe_inclusion,
      ite_eq_left_iff, not_lt]
    exact fun _ h => (fixed_ge_of_mem_natFixGE he _ h).symm

theorem range_natPerm : natPerm.range = NatFinitePerm := by
  simp_rw [SetLike.ext_iff, MonoidHom.mem_range,
    exists_natPerm_apply_iff_mem_natFinitePerm, implies_true]

noncomputable def mulEquivNatFinitePerm : FinitePerm ≃* NatFinitePerm :=
  (MulEquiv.ofBijective (MonoidHom.rangeRestrict natPerm)
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr natPerm_injective,
    MonoidHom.rangeRestrict_surjective _⟩).trans (MulEquiv.subgroupCongr range_natPerm)

def ofArray (a : Array ℕ) (hx : ∀ {x} (hx : x < a.size), a[x] < a.size := by decide)
  (ha : a.toList.Nodup := by decide) : FinitePerm := (ofVector ⟨a, rfl⟩ hx ha).ofPermOf

end FinitePerm
