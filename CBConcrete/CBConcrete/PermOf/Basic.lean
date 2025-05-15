import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Perm

namespace Equiv

variable {α β : Type*} [DecidableEq α]

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
    (a.shuffle v)[i] = v[a[i]] := Vector.getElem_mapFinIdx _

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

instance {α : Type*} : SMul (PermOf n)ᵐᵒᵖ (Vector α n) where
  smul a v := a.unop.shuffle v

section SMulOp

variable {α : Type*}

@[simp] theorem op_smul (a : PermOf n) (v : Vector α n) :
    (MulOpposite.op a) • v = a.shuffle v := rfl

@[simp] theorem unop_shuffle (a : (PermOf n)ᵐᵒᵖ) (v : Vector α n) :
    a.unop.shuffle v = a • v := rfl

end SMulOp

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

instance : One (PermOf n) where
  one := PermOf.mk (Vector.range n) (Vector.range n)
    (fun h => by simp_rw [Vector.getElem_range, h])
    (fun _ => by simp_rw [Vector.getElem_range])

section One

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : PermOf n)[i] = i := Vector.getElem_range _

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

instance {α : Type*} : MulAction (PermOf n)ᵐᵒᵖ (Vector α n) where
  one_smul _ := one_shuffle _
  mul_smul _ _ _ := mul_shuffle _ _ _

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

def ofFn (f g : Fin n → ℕ) (hf : ∀ i, f i < n)
    (hfg : ∀ i, g ⟨f i, hf _⟩ = i) : PermOf n where
  toVector := Vector.ofFn f
  invVector := Vector.ofFn g
  getElem_toVector_lt := fun _ => by simp_rw [Vector.getElem_ofFn, hf]
  getElem_invVector_getElem_toVector := fun _ => by simp_rw [Vector.getElem_ofFn, hfg]

section OfFn

@[simp]
theorem getElem_ofFn {f g : Fin n → ℕ} {hf : ∀ i, f i < n}
    {hfg : ∀ i, g ⟨f i, hf _⟩ = i} {i : ℕ} (hi : i < n) :
    (ofFn f g hf hfg)[i] = f ⟨i, hi⟩ := by
  unfold ofFn
  simp_rw [getElem_mk, Vector.getElem_ofFn]

@[simp]
theorem getElem_inv_ofFn {f g : Fin n → ℕ} {hf : ∀ i, f i < n}
    {hfg : ∀ i, g ⟨f i, hf _⟩ = i} {i : ℕ} (hi : i < n) :
    (ofFn f g hf hfg)⁻¹[i] = g ⟨i, hi⟩ := by
  unfold ofFn
  simp_rw [getElem_inv_mk, Vector.getElem_ofFn]

@[simp] theorem ofFn_getElem (a : PermOf n) :
    ofFn (fun i => a[i.1]) (fun i => a⁻¹[i.1])
    (fun _ => a.getElem_lt) (fun _ => a.getElem_inv_getElem _) = a :=
  ext <| fun _ => by simp_rw [getElem_ofFn]

@[simp] theorem ofFn_getElem_inv (a : PermOf n) :
    ofFn (fun i => a⁻¹[i.1]) (fun i => a[i.1])
    (fun _ => a⁻¹.getElem_lt) (fun _ => a.getElem_getElem_inv _) = a⁻¹ :=
  ext <| fun _ => by simp_rw [getElem_ofFn]

end OfFn

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
    (a.swap i j hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.invVector.getElem_map _ _

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

end PermOf
