import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Algebra.Group.MinimalAxioms

namespace Equiv

variable {α : Type*} [DecidableEq α]

theorem coe_swap {n : ℕ} {i j k : Fin n} : swap (i : ℕ) (j : ℕ) (k : ℕ) = swap i j k :=
  Fin.val_injective.swap_apply _ _ _

theorem swap_smul {R : Type*} [Group R] [MulAction R α] {i j k : α} {r : R} :
    swap (r • i) (r • j) (r • k) = r • swap i j k :=
  (MulAction.injective r).swap_apply _ _ _

theorem swap_prop (p : α → Prop) {i j k : α} (hk : p k) (hi : p i) (hj : p j) :
    p (swap i j k) := by
  simp_rw [swap_apply_def, apply_ite p, hi, hj, hk, ite_self]

end Equiv

namespace Array

@[simp] theorem size_finRange {n : ℕ} : (Array.finRange n).size = n := size_ofFn _
@[simp] theorem getElem_finRange {n i : ℕ} {hi : i < (Array.finRange n).size} :
    (Array.finRange n)[i] = ⟨i, hi.trans_eq size_finRange⟩ := getElem_ofFn _ _ _


theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith bs f).size) : i < as.size := by
  rw [Array.size_eq_length_toList] at h ⊢
  rw [Array.toList_zipWith] at h
  exact List.lt_length_left_of_zipWith h

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith bs f).size) : i < bs.size := by
  rw [Array.size_eq_length_toList] at h ⊢
  rw [Array.toList_zipWith] at h
  exact List.lt_length_right_of_zipWith h

theorem lt_length_left_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < as.size := lt_length_left_of_zipWith h

theorem lt_length_right_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < bs.size := lt_length_right_of_zipWith h

@[simp]
theorem getElem_zipWith {as : Array α} {bs : Array β} {f : α → β → γ} {i : ℕ}
    (h : i < (as.zipWith bs f).size) : (as.zipWith bs f)[i] =
    f (as[i]'(lt_length_left_of_zipWith h)) (bs[i]'(lt_length_right_of_zipWith h)) := by
  simp_rw [getElem_eq_getElem_toList, Array.toList_zipWith, List.getElem_zipWith]

@[simp]
theorem getElem_zip {as : Array α} {bs : Array β} {i : ℕ}
    (h : i < (as.zip bs).size) : (as.zip bs)[i] =
    (as[i]'(lt_length_left_of_zip h), bs[i]'(lt_length_right_of_zip h)) := by
  simp_rw [getElem_eq_getElem_toList, Array.toList_zip, List.getElem_zip]

@[simp]
theorem getElem_zipWithIndex {as : Array α} {i : ℕ}
    (h : i < (as.zipWithIndex).size) :
    (as.zipWithIndex)[i] = (as[i]'(h.trans_eq as.size_zipWithIndex), i) := by
  unfold zipWithIndex
  simp_rw [Array.getElem_mapIdx]

theorem getElem_swapIfInBounds_of_ge_left {as : Array α} {i j k : ℕ} (h : as.size ≤ i)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq <| as.size_swapIfInBounds _ _) := by
  unfold swapIfInBounds
  simp_rw [h.not_lt, dite_false]

theorem getElem_swapIfInBounds_of_ge_right {as : Array α} {i j k : ℕ} (h : as.size ≤ j)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq <| as.size_swapIfInBounds _ _) := by
  unfold swapIfInBounds
  simp_rw [h.not_lt, dite_false, dite_eq_ite, ite_self]

@[simp]
theorem getElem_swapIfInBounds_left {as : Array α} {i j : ℕ} (hj : j < as.size)
    (hi : i < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[i] = as[j] := by
  simp_rw [size_swapIfInBounds] at hi
  unfold swapIfInBounds
  simp_rw [hi, hj, dite_true]
  exact getElem_swap_left _

@[simp]
theorem getElem_swapIfInBounds_right {as : Array α} {i j : ℕ} (hi : i < as.size)
    (hj : j < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[j] = as[i] := by
  simp_rw [size_swapIfInBounds] at hj
  unfold swapIfInBounds
  simp_rw [hi, hj, dite_true]
  exact getElem_swap_right _

theorem getElem_swapIfInBounds_of_ne_ne {as : Array α} {i j k : ℕ} (hi : k ≠ i) (hj : k ≠ j)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq <| as.size_swapIfInBounds _ _) := by
  simp_rw [size_swapIfInBounds] at hk
  unfold swapIfInBounds
  split_ifs <;> try {rfl}
  exact Array.getElem_swap_of_ne _ _ hi hj

theorem getElem_swapIfInBounds {as : Array α} {i j k : ℕ} (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] =
    if h : k = i ∧ j < as.size then as[j]'h.2 else if h₂ : k = j ∧ i < as.size then as[i]'h₂.2
    else as[k]'(hk.trans_eq <| as.size_swapIfInBounds _ _) := by
  rcases eq_or_ne k i with rfl | hi
  · simp_rw [true_and]
    rcases lt_or_le j as.size with hj | hj
    · simp_rw [hj, dite_true, getElem_swapIfInBounds_left hj]
    · simp_rw [hj.not_lt, dite_false, getElem_swapIfInBounds_of_ge_right hj]
      split_ifs <;> rfl
  · rcases eq_or_ne k j with rfl | hj
    · simp_rw [hi, false_and, dite_false, true_and]
      rcases lt_or_le i as.size with hi | hi
      · simp_rw [hi, dite_true, getElem_swapIfInBounds_right hi]
      · simp_rw [hi.not_lt, dite_false, getElem_swapIfInBounds_of_ge_left hi]
    · simp_rw [hi, hj, false_and, dite_false, getElem_swapIfInBounds_of_ne_ne hi hj]

end Array

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α]

theorem period_le_card_of_smul_pow_mem (a : G) {i : α}
  (s : Finset α) (hia : ∀ k < s.card + 1, (a ^ k) • i ∈ s) : MulAction.period a i ≤ s.card := by
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (f := (fun (k : Fin (s.card + 1)) => (a ^ k.1) • i))
    ((Nat.lt_succ_self _).trans_eq (Finset.card_fin _).symm) (fun _ _ => hia _ (Fin.is_lt _))
    with ⟨x, _, y, _, hxy, ha⟩
  wlog hxy' : x < y with H
  · exact H _ _ hia _ (Finset.mem_univ _) _ (Finset.mem_univ _)
      hxy.symm ha.symm (hxy.symm.lt_of_le (le_of_not_lt hxy'))
  · rw [← inv_smul_eq_iff, ← mul_smul, ← inv_pow_sub _ hxy'.le, inv_pow, inv_smul_eq_iff] at ha
    rw [Fin.lt_iff_val_lt_val, ← Nat.sub_pos_iff_lt] at hxy'
    exact (MulAction.period_le_of_fixed hxy' ha.symm).trans
      ((Nat.sub_le _ _).trans y.is_le)

theorem smul_injOn_range_period (a : G) {x : α} :
    Set.InjOn (fun k => a ^ k • x) (Finset.range (MulAction.period a x)) := by
  intro i hi j hj ha
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj ha
  by_contra hij'
  wlog hij : i < j with H
  · exact (H a ha.symm hj hi (Ne.symm hij') ((Ne.symm hij').lt_of_le (le_of_not_lt hij)))
  · rw [← inv_smul_eq_iff, ← mul_smul, ← inv_pow_sub _ hij.le, inv_pow, inv_smul_eq_iff] at ha
    exact (lt_irrefl (period a x)) ((MulAction.period_le_of_fixed (Nat.sub_pos_of_lt hij)
      ha.symm).trans_lt ((Nat.sub_le _ _).trans_lt hj))

end MulAction

namespace Vector

@[simp]
theorem getD_of_lt (a : Vector α n) (x : α) (i : ℕ) (h : i < n) : a[i]?.getD x = a[i] := by
  simp_rw [getElem?_pos a i h, Option.getD_some]

@[simp]
theorem getD_of_ge (a : Vector α n) (x : α) (i : ℕ) (h : n ≤ i) : a[i]?.getD x = x := by
  rw [getElem?_neg a i h.not_lt, Option.getD_none]

@[simp] theorem getElem_map {n i : ℕ} (hi : i < n) (f : α → β) (v : Vector α n) :
    (v.map f)[i] = f v[i] := by
  cases v ; simp_rw [map_mk, getElem_mk, Array.getElem_map]

@[simp] theorem getElem_range {n i : ℕ} (hi : i < n) : (range n)[i] = i := by
  unfold range
  simp_rw [getElem_mk, Array.getElem_range]

@[simp] theorem getElem_cast {n m i : ℕ} (hnm : n = m) (v : Vector α n) (hi : i < m)  :
  (v.cast hnm)[i] = v[i] := rfl

@[simp] theorem getElem_range_lt {n i : ℕ} (hi : i < n) : (range n)[i] < n := getElem_range _ ▸ hi

@[simp]
theorem getElem_zipWith  {n i : ℕ} (hi : i < n) {as : Vector α n} {bs : Vector β n}
    {f : α → β → γ} : (as.zipWith bs f)[i] = f (as[i]) (bs[i]) := by
  cases as ; cases bs ; simp_rw [mk_zipWith_mk, getElem_mk, Array.getElem_zipWith]

theorem getElem_swap {α : Type u_1} (a : Vector α n) (i j : ℕ) (hi : i < n)
    {hj : j < n} (k : ℕ) (hk : k < n) :
    (a.swap i j hi hj)[k] = if k = i then a[j] else if k = j then a[i] else a[k] := by
  cases a
  simp_rw [swap_mk, getElem_mk, Array.getElem_swap]

theorem getElem_swap_eq_getElem_swap_apply (as : Vector α n) (i j : ℕ) (hi : i < n)
    (hj : j < n)
    (k : ℕ) (hk : k < n) :
    (as.swap i j hi hj)[k] =
    as[Equiv.swap i j k]'(Equiv.swap_prop (· < n) hk hi hj) := by
  simp_rw [getElem_swap, Equiv.swap_apply_def]
  split_ifs <;> rfl

theorem getElem_swapIfInBounds {as : Vector α n} {i j k : ℕ} (hk : k < n) :
    (as.swapIfInBounds i j)[k] =
    if h : i < n ∧ j < n then (as.swap i j)[k] else as[k] := by
  unfold swapIfInBounds
  simp_rw [getElem_mk, Array.getElem_swapIfInBounds, Vector.size_toArray, getElem_swap,
    Vector.getElem_toArray]
  rcases eq_or_ne k i with rfl | hi
  · simp_rw [hk, true_and, and_true, ite_true]
    exact dite_congr rfl (fun _ => rfl) (fun _ => by simp_rw [dite_eq_right_iff, implies_true])
  · simp_rw [hi, false_and, dite_false, ite_false]
    rcases eq_or_ne k j with rfl | hj
    · simp_rw [ite_true, true_and, hk, and_true]
    · simp_rw [hj, false_and, dite_false, ite_false, dite_eq_ite, ite_self]

protected def finRange (n : ℕ) : Vector (Fin n) n := ⟨Array.finRange n, Array.size_finRange⟩

@[simp] theorem getElem_finRange (hi : i < n) : (Vector.finRange n)[i] = ⟨i, hi⟩ := by
  unfold Vector.finRange
  simp_rw [getElem_mk, Array.getElem_finRange]

@[simp] theorem getElem_mkVector {a : α} (hi : i < n) : (Vector.mkVector n a)[i] = a := by
  unfold Vector.mkVector
  simp_rw [getElem_mk, Array.getElem_mkArray]

def mapIdx (f : Fin n → α → β) (v : Vector α n) : Vector β n :=
  ⟨v.toArray.mapFinIdx fun i a => f (i.cast v.size_toArray) a,
  (Array.size_mapFinIdx _ _).trans v.size_toArray⟩

@[simp] theorem getElem_mapIdx (f : Fin n → α → β) (v : Vector α n) {i : ℕ} (hi : i < n) :
    (v.mapIdx f)[i] = f ⟨i, hi⟩ v[i] := by
  unfold mapIdx
  simp_rw [getElem_mk, Array.getElem_mapFinIdx, Fin.cast_mk, getElem_toArray]

structure Mem (v : Vector α n) (a : α) : Prop where
  val : a ∈ v.toArray

instance : Membership α (Vector α n) where
  mem := Mem

theorem mem_def {a : α} (v : Vector α n) : a ∈ v ↔ a ∈ v.toArray :=
  ⟨fun | .mk h => h, Vector.Mem.mk⟩

@[simp] theorem getElem_mem (v : Vector α n) {i : ℕ} (h : i < n) : v[i] ∈ v := by
  rw [Vector.mem_def, ← getElem_toArray]
  exact Array.getElem_mem (h.trans_eq v.size_toArray.symm)

theorem getElem_of_mem {a} (v : Vector α n) : a ∈ v → ∃ (i : Nat) (h : i < n), v[i]'h = a := by
  simp_rw [mem_def, Array.mem_iff_getElem, v.size_toArray, getElem_toArray, imp_self]

theorem getElem?_of_mem {a} (v : Vector α n) (h : a ∈ v) : ∃ i : Nat, v[i]? = some a := by
  simp_rw [getElem?_def]
  rcases (v.getElem_of_mem h) with ⟨i, hi, hiv⟩
  exact ⟨i, hiv ▸ dif_pos _⟩

theorem mem_of_getElem? (v : Vector α n) {i : Nat} {a : α} : v[i]? = some a → a ∈ v := by
  simp_rw [getElem?_def, Option.dite_none_right_eq_some, Option.some.injEq, forall_exists_index]
  exact fun _ h => h ▸ v.getElem_mem _

theorem mem_iff_getElem {a} (v : Vector α n) : a ∈ v ↔ ∃ (i : Nat) (h : i < n), v[i]'h = a :=
  ⟨v.getElem_of_mem, fun ⟨_, _, e⟩ => e ▸ getElem_mem ..⟩

theorem mem_iff_getElem? {a} (v : Vector α n) : a ∈ v ↔ ∃ i : Nat, v[i]? = some a := by
  simp_rw [mem_iff_getElem, getElem?_def, Option.dite_none_right_eq_some, Option.some.injEq]

@[simp] theorem getElem_take (a : Vector α n) (m : Nat) (hi : i < min m n) :
    (a.take m)[i] = a[i] := by
  cases a
  simp_rw [take_mk, getElem_mk, Array.getElem_take]

theorem getElem_append (a : Vector α n) (b : Vector α m) (i : Nat) (hi : i < n + m) :
    (a ++ b)[i] = if h : i < n then a[i] else b[i - n] := by
  rcases a with ⟨a, rfl⟩
  rcases b with ⟨b, rfl⟩
  simp [Array.getElem_append, hi]

theorem getElem_append_left {a : Vector α n} {b : Vector α m} {i : Nat} (hi : i < n) :
    (a ++ b)[i] = a[i] := by simp [getElem_append, hi]

theorem getElem_append_right {a : Vector α n} {b : Vector α m} {i : Nat} (h : i < n + m)
    (hi : n ≤ i) : (a ++ b)[i] = b[i - n] := by
  rw [getElem_append, dif_neg (by omega)]

end Vector

/--
A `VectorPerm n` is a permutation on `n` elements represented by two vectors, which we can
think of as an array of values and a corresponding array of indexes which are inverse to
one another. (One can flip the interpretation of indexes and values, and this is essentially
the inversion operation.)
It is designed to be a more performant version of `Equiv.Perm`.
-/
structure VectorPerm (n : ℕ) where
  /--
  Gives the `VectorPerm` as an vector of size `n`.
  -/
  protected fwdVector : Vector ℕ n
  /--
  Gives the inverse of the `VectorPerm` as a vector of size `n`.
  -/
  protected bwdVector : Vector ℕ n
  getElem_fwdVector_lt :
    ∀ {i : ℕ} (hi : i < n), fwdVector[i] < n := by decide
  getElem_bwdVector_getElem_fwdVector : ∀ {i : ℕ} (hi : i < n),
      bwdVector[fwdVector[i]]'(getElem_fwdVector_lt hi) = i := by decide
  deriving DecidableEq

namespace VectorPerm

open Function Equiv --Fin Equiv List

variable {n : ℕ}

instance : Repr (VectorPerm n) where
  reprPrec a _ := repr (a.fwdVector.toArray, a.bwdVector.toArray)

instance : One (VectorPerm n) where
  one := VectorPerm.mk (Vector.range n) (Vector.range n)
    (fun _ => Vector.getElem_range_lt _) (fun _ => by simp_rw [Vector.getElem_range])

instance : Inhabited (VectorPerm n) := ⟨1⟩

@[simp]
theorem default_eq : (default : VectorPerm n) = 1 := rfl

instance : Mul (VectorPerm n) where
  mul a b := {
    fwdVector := b.fwdVector.map (fun i => a.fwdVector[i]?.getD i)
    bwdVector := a.bwdVector.map (fun i => b.bwdVector[i]?.getD i)
    getElem_fwdVector_lt := fun {i} hi => by
      simp_rw [Vector.getElem_map,
        getElem?_pos a.fwdVector (b.fwdVector[i]) (b.getElem_fwdVector_lt hi),
        Option.getD_some, a.getElem_fwdVector_lt]
    getElem_bwdVector_getElem_fwdVector := fun {i} hi => by
      simp_rw [Vector.getElem_map,
        getElem?_pos a.fwdVector (b.fwdVector[i]) (b.getElem_fwdVector_lt hi),
        Option.getD_some, a.getElem_bwdVector_getElem_fwdVector,
        getElem?_pos b.bwdVector (b.fwdVector[i]) (b.getElem_fwdVector_lt hi),
        Option.getD_some, b.getElem_bwdVector_getElem_fwdVector]}

section GetElemVectorBijective

theorem getElem_fwdVector_injective (a : VectorPerm n) :
  ∀ {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n), a.fwdVector[i] = a.fwdVector[j] → i = j :=
  fun hi _ hj hij => (a.getElem_bwdVector_getElem_fwdVector hi).symm.trans
    (Eq.trans (by simp_rw [hij]) (a.getElem_bwdVector_getElem_fwdVector hj))

theorem fwdVector_toList_Nodup (a : VectorPerm n) : a.fwdVector.toList.Nodup := by
  rw [List.nodup_iff_injective_get]
  unfold Injective
  simp_rw [Fin.ext_iff, Fin.forall_iff, Array.length_toList, Vector.size_toArray,
    List.get_eq_getElem, Array.getElem_toList, Vector.getElem_toArray]
  exact fun _ hi _ hj => a.getElem_fwdVector_injective hi hj

theorem getElem_fwdVector_surjective (a : VectorPerm n) :
    ∀ {i : ℕ}, i < n → ∃ (j : ℕ), ∃ (hj : j < n), a.fwdVector[j] = i := by
  have H : Surjective (fun (i : Fin n) => Fin.mk a.fwdVector[i.1] (a.getElem_fwdVector_lt i.2)) :=
    Injective.surjective_of_fintype (Equiv.refl (Fin n)) fun _ _ => by
    simp_rw [Fin.mk.injEq, Fin.ext_iff]
    exact a.getElem_fwdVector_injective _ _
  unfold Surjective at H
  simp_rw [Fin.ext_iff, Fin.forall_iff, Fin.exists_iff] at H
  exact H

theorem getElem_bwdVector_lt (a : VectorPerm n) {i : ℕ} (hi : i < n) : a.bwdVector[i] < n := by
  rcases a.getElem_fwdVector_surjective hi with ⟨j, hj, rfl⟩
  simp_rw [a.getElem_bwdVector_getElem_fwdVector, hj]

theorem getElem_fwdVector_getElem_bwdVector (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    a.fwdVector[a.bwdVector[i]]'(a.getElem_bwdVector_lt hi) = i := by
  rcases a.getElem_fwdVector_surjective hi with ⟨j, hj, rfl⟩
  simp_rw [a.getElem_bwdVector_getElem_fwdVector]

theorem getElem_bwdVector_injective (a : VectorPerm n) :
  ∀ {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n), a.bwdVector[i] = a.bwdVector[j] → i = j :=
  fun hi _ hj hij => (a.getElem_fwdVector_getElem_bwdVector hi).symm.trans
    (Eq.trans (by simp_rw [hij]) (a.getElem_fwdVector_getElem_bwdVector hj))

theorem bwdVector_toList_Nodup (a : VectorPerm n) : a.bwdVector.toList.Nodup := by
  rw [List.nodup_iff_injective_get]
  unfold Injective
  simp_rw [Fin.ext_iff, Fin.forall_iff, Array.length_toList, Vector.size_toArray,
    List.get_eq_getElem, Array.getElem_toList, Vector.getElem_toArray]
  exact fun _ hi _ hj => a.getElem_bwdVector_injective hi hj

theorem getElem_bwdVector_surjective (a : VectorPerm n) :
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
  VectorPerm n :=
  let A : VectorPerm n := ⟨bwdVector, fwdVector,
    getElem_bwdVector_lt, getElem_fwdVector_getElem_bwdVector⟩
  ⟨fwdVector, bwdVector,
    A.getElem_bwdVector_lt, A.getElem_fwdVector_getElem_bwdVector⟩

section Mk'

@[simp] theorem mk'_fwdVector (a b : Vector ℕ n) {ha hab} :
    (VectorPerm.mk' a b ha hab).fwdVector = a := rfl

@[simp] theorem mk'_bwdVector (a b : Vector ℕ n) {ha hab} :
    (VectorPerm.mk' a b ha hab).bwdVector = b := rfl

instance : Inv (VectorPerm n) where
  inv a := VectorPerm.mk' a.bwdVector a.fwdVector
    a.getElem_fwdVector_lt a.getElem_bwdVector_getElem_fwdVector

@[simp] theorem inv_fwdVector (a : VectorPerm n) : a⁻¹.fwdVector = a.bwdVector := rfl
@[simp] theorem inv_bwdVector (a : VectorPerm n) : a⁻¹.bwdVector = a.fwdVector := rfl

end Mk'

instance : GetElem (VectorPerm n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.fwdVector[i]

section GetElem

@[simp]
theorem getElem_lt (a : VectorPerm n) {i : ℕ} (hi : i < n := by get_elem_tactic) : a[i] < n :=
  a.getElem_fwdVector_lt hi

@[simp]
theorem getElem_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (VectorPerm.mk a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_mk' (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (VectorPerm.mk' a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_fwdVector (a : VectorPerm n)  {i : ℕ} (hi : i < n) : a.fwdVector[i] = a[i] := rfl

theorem fwdVector_eq_iff_forall_getElem_eq (a b : VectorPerm n) :
    a.fwdVector = b.fwdVector ↔ ∀ {i} (hi : i < n), a[i] = b[i] := by
  simp_rw [Vector.ext_iff, getElem_fwdVector]

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : VectorPerm n)[i] = i := Vector.getElem_range _

@[simp]
theorem getElem_mul (a b : VectorPerm n) {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]] := by
  refine (Vector.getElem_map _ _ _).trans ?_
  simp_rw [getElem?_pos a.fwdVector (b.fwdVector[i]) (b.getElem_fwdVector_lt hi),
    Option.getD_some, getElem_fwdVector]


section GetElemBijective

theorem getElem_injective (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n)
    (hij : a[i] = a[j]) : i = j := a.getElem_fwdVector_injective hi hj hij

@[simp] theorem getElem_inj (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i := a.getElem_fwdVector_surjective hi

end GetElemBijective


section GetElemInv

@[simp]
theorem getElem_inv_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (VectorPerm.mk a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_inv_mk' (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (VectorPerm.mk' a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_bwdVector (a : VectorPerm n)  {i : ℕ} (hi : i < n) :
  a.bwdVector[i] = a⁻¹[i] := rfl

theorem bwdVector_eq_iff_forall_getElem_eq (a b : VectorPerm n) :
    a.bwdVector = b.bwdVector ↔ ∀ {i} (hi : i < n), a⁻¹[i] = b⁻¹[i] := by
  simp_rw [Vector.ext_iff, getElem_bwdVector]

@[simp]
theorem getElem_inv_getElem (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    a⁻¹[a[i]] = i := a.getElem_bwdVector_getElem_fwdVector hi

@[simp]
theorem getElem_getElem_inv (a : VectorPerm n) {i : ℕ} (hi : i < n) :
  a[a⁻¹[i]] = i := (a⁻¹).getElem_bwdVector_getElem_fwdVector hi

theorem eq_getElem_inv_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by
  rw [← (a⁻¹).getElem_inj (a.getElem_lt) hj, getElem_inv_getElem]

theorem self_eq_getElem_inv_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) : i = a⁻¹[i] ↔ a[i] = i := by
  rw [← (a⁻¹).getElem_inj (a.getElem_lt) hi, getElem_inv_getElem]

theorem getElem_inv_eq_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by
  rw [← a.getElem_inj (a⁻¹.getElem_lt) hj, getElem_getElem_inv]

theorem getElem_inv_eq_self_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    a⁻¹[i] = i ↔ i = a[i] := by
  rw [← a.getElem_inj (a⁻¹.getElem_lt) hi, getElem_getElem_inv]

theorem ne_getElem_inv_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := (a.eq_getElem_inv_iff _ _).ne

theorem self_ne_getElem_inv_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    i ≠ a⁻¹[i] ↔ a[i] ≠ i := (a.eq_getElem_inv_iff _ _).ne

theorem getElem_inv_ne_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := (a.getElem_inv_eq_iff _ _).ne

theorem getElem_inv_ne_self_iff (a : VectorPerm n) {i : ℕ} (hi : i < n):
    a⁻¹[i] ≠ i ↔ i ≠ a[i] := (a.getElem_inv_eq_iff _ _).ne

end GetElemInv

@[ext]
theorem ext {a b : VectorPerm n} (h : ∀ {i : ℕ} (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.fwdVector = b.fwdVector ∧ a.bwdVector = b.bwdVector by
    · rcases a ; rcases b ; simp_rw [mk.injEq]
      exact h
  simp_rw [fwdVector_eq_iff_forall_getElem_eq, bwdVector_eq_iff_forall_getElem_eq,
    a.getElem_inv_eq_iff _ (b⁻¹.getElem_lt _), h, getElem_getElem_inv, implies_true, and_self]

end GetElem

instance : Subsingleton (VectorPerm 0) where
  allEq a b := by simp_rw [VectorPerm.ext_iff, not_lt_zero', IsEmpty.forall_iff, implies_true]

instance : Subsingleton (VectorPerm 1) where
  allEq a b := by
    simp_rw [VectorPerm.ext_iff]
    intro _ hi
    have ha := a.getElem_lt (hi := hi)
    have hb := b.getElem_lt (hi := hi)
    rw [Nat.lt_one_iff] at ha hb
    exact ha.trans hb.symm

instance : Unique (VectorPerm 0) := Unique.mk' _
instance : Unique (VectorPerm 1) := Unique.mk' _

instance : Finite (VectorPerm n) := Finite.of_injective
  (fun a => (fun (i : Fin n) => (⟨a[i.1], a.getElem_lt⟩ : Fin n))) <| fun a b => by
    simp only [Prod.mk.injEq, and_imp, funext_iff, Fin.forall_iff, Fin.ext_iff]
    exact ext

instance : Group (VectorPerm n) := Group.ofLeftAxioms
  (fun _ _ _ => ext <| fun hi => by simp_rw [getElem_mul])
  (fun _ => ext <| fun hi => by simp_rw [getElem_mul, getElem_one])
  (fun _ => ext <| fun hi => by simp_rw [getElem_mul, getElem_one, getElem_inv_getElem])

section Group

@[simp]
theorem getElem_pow_add (a : VectorPerm n) {i x y : ℕ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [pow_add, getElem_mul]

@[simp]
theorem getElem_zpow_add (a : VectorPerm n) {i : ℕ} {x y : ℤ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [zpow_add, getElem_mul]

lemma isOfFinOrder (a : VectorPerm n) : IsOfFinOrder a := isOfFinOrder_of_finite _

lemma orderOf_pos (a : VectorPerm n) : 0 < orderOf a := by
  rw [orderOf_pos_iff]
  exact a.isOfFinOrder

end Group


@[irreducible] def FixLT (a : VectorPerm n) (m : ℕ) : Prop :=
    ∀ {i : ℕ}, i < m → ∀ {hi : i < n}, a[i] < m

section FixLT

variable {a : VectorPerm n}

theorem fixLT_def :
    a.FixLT m ↔ ∀ {i : ℕ}, i < m → ∀ {hi : i < n}, a[i] < m := by
  unfold FixLT
  exact Iff.rfl

theorem FixLT.getElem_lt_of_lt (him : i < m) (ha : a.FixLT m)
    (hin : i < n := by get_elem_tactic) : a[i] < m := by
  unfold FixLT at ha
  exact ha him

theorem fixLT_of_lt_imp_getElem_lt (ha : ∀ {i}, i < m → ∀ {hi : i < n}, a[i] < m) : a.FixLT m := by
  unfold FixLT
  exact ha

theorem fixLT_eq : ∀ (a : VectorPerm n), a.FixLT n :=
  fun a => fixLT_of_lt_imp_getElem_lt (fun _ => a.getElem_lt)

theorem fixLT_ge (hnm : n ≤ m) : ∀ (a : VectorPerm n), a.FixLT m :=
  fun a => fixLT_of_lt_imp_getElem_lt (fun _ => a.getElem_lt.trans_le hnm)

theorem fixLT_zero : ∀ (a : VectorPerm n), a.FixLT 0 :=
  fun _ => fixLT_of_lt_imp_getElem_lt (fun h => (Nat.not_lt_zero _ h).elim)

theorem fixLT_one : (1 : VectorPerm n).FixLT m :=
  fixLT_of_lt_imp_getElem_lt (fun him => getElem_one _ ▸ him)

theorem FixLT.mul {b : VectorPerm n}
    (ha : a.FixLT m) (hb : b.FixLT m) : (a * b).FixLT m :=
  fixLT_of_lt_imp_getElem_lt (fun him _ => a.getElem_mul b _ ▸
    ha.getElem_lt_of_lt (hb.getElem_lt_of_lt him))

theorem FixLT.pow
    (ha : a.FixLT m) {k : ℕ} : (a^k).FixLT m := by
  induction k with | zero => _ | succ _ IH => _
  · exact pow_zero a ▸ fixLT_one
  · simp_rw [pow_succ]
    exact IH.mul ha

theorem FixLT.zpow (ha : a.FixLT m) {k : ℤ} : (a^k).FixLT m := by
  have H := (a.isOfFinOrder.mem_zpowers_iff_mem_range_orderOf (y := a^k)).mp
      (zpow_mem (Subgroup.mem_zpowers _) _)
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  rcases H with ⟨_, _, hn⟩
  simp_rw [← hn]
  exact ha.pow

theorem FixLT.inv (ha : a.FixLT m) : (a⁻¹).FixLT m := by
  have H := (a.isOfFinOrder.mem_zpowers_iff_mem_range_orderOf (y := a⁻¹)).mp
      (inv_mem (Subgroup.mem_zpowers _))
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  rcases H with ⟨_, _, hn⟩
  simp_rw [← hn]
  exact ha.pow

@[simp] theorem fixLT_inv_iff :
    (a⁻¹.FixLT m) ↔ (a.FixLT m) := ⟨fun ha => ha.inv, fun ha => ha.inv⟩

theorem fixLT_of_le_of_lt_imp_getElem_lt (hmn : m ≤ n)
    (ha : ∀ {i} (hi : i < m), a[i] < m) : a.FixLT m :=
  fixLT_of_lt_imp_getElem_lt (fun him => ha him)

@[simps!]
def fixLTSubgroup (n m : ℕ) : Subgroup (VectorPerm n) where
  carrier a := a.FixLT m
  mul_mem' ha hb := FixLT.mul ha hb
  one_mem' := fixLT_one
  inv_mem' ha := FixLT.inv ha

@[simp]
theorem mem_fixLTSubgroup_iff : a ∈ fixLTSubgroup n m ↔ a.FixLT m := Iff.rfl

theorem fixLTSubgroup_eq_top_of_ge (hnm : n ≤ m) : fixLTSubgroup n m = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_fixLTSubgroup_iff, fixLT_ge hnm, implies_true]

theorem fixLTSubgroup_eq_eq_top : fixLTSubgroup n n = ⊤ := fixLTSubgroup_eq_top_of_ge le_rfl

theorem fixLTSubgroup_zero_eq_top : fixLTSubgroup n 0 = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_fixLTSubgroup_iff, fixLT_zero, implies_true]

end FixLT

def ofVector (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : VectorPerm n where
  fwdVector := a
  bwdVector := (Vector.range n).map a.toList.indexOf
  getElem_fwdVector_lt := hx
  getElem_bwdVector_getElem_fwdVector := fun {i} hi => by
    simp_rw [Vector.getElem_map, Vector.getElem_range]
    exact a.toList.indexOf_getElem ha _ _

section OfVector

@[simp]
theorem getElem_ofVector {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) : (ofVector a hx ha)[i] = a[i] := rfl

@[simp] theorem ofVector_fwdVector (a : VectorPerm n) :
    ofVector a.fwdVector a.getElem_fwdVector_lt a.fwdVector_toList_Nodup = a :=
  ext <| fun _ => by simp_rw [getElem_ofVector, getElem_fwdVector]

@[simp] theorem ofVector_bwdVector (a : VectorPerm n) :
    ofVector a.bwdVector a.getElem_bwdVector_lt a.bwdVector_toList_Nodup = a⁻¹ :=
  ext <| fun _ => by simp_rw [getElem_ofVector, getElem_bwdVector]

end OfVector


def ofVectorInv (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : VectorPerm n := (ofVector a hx ha)⁻¹

section OfVectorInv

theorem getElem_ofVectorInv {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) :
    (ofVectorInv a hx ha)[i] = a.toList.indexOf i := by
  unfold ofVectorInv
  unfold ofVector
  simp_rw [getElem_inv_mk, Vector.getElem_map, Vector.getElem_range]

theorem ofVectorInv_fwdVector (a : VectorPerm n) :
    ofVectorInv a.fwdVector a.getElem_fwdVector_lt a.fwdVector_toList_Nodup = a⁻¹ :=
  ext <| fun _ => by unfold ofVectorInv ; simp_rw [ofVector_fwdVector]

theorem ofVectorInv_bwdVector (a : VectorPerm n) :
    ofVectorInv a.bwdVector a.getElem_bwdVector_lt a.bwdVector_toList_Nodup = a :=
  ext <| fun _ => by unfold ofVectorInv ; simp_rw [ofVector_bwdVector, inv_inv]

end OfVectorInv


instance : MulAction (VectorPerm n) (Fin n) where
  smul a i := ⟨a[i.1], a.getElem_lt⟩
  one_smul _ := Fin.ext <| getElem_one _
  mul_smul _ _ _ := Fin.ext <| getElem_mul _ _ _

section MulActionFin

@[simp]
theorem val_smul (a : VectorPerm n) {i : Fin n} : (a • i : Fin n) = a[i.1] := rfl

@[simp]
theorem smul_mk (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    (a • (⟨i, hi⟩ : Fin n)) = ⟨a[i], a.getElem_lt⟩ := Fin.ext a.val_smul

theorem getElem_eq_val_smul_mk (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    a[i] = ↑(a • Fin.mk i hi) := by rw [smul_mk]

theorem smul_right_inj (a : VectorPerm n) {i j : Fin n} : a • i = a • j ↔ i = j := by
  simp_rw [Fin.ext_iff, val_smul, getElem_inj]

instance : FaithfulSMul (VectorPerm n) (Fin n) where
  eq_of_smul_eq_smul := by
    simp_rw [VectorPerm.ext_iff, Fin.ext_iff, Fin.forall_iff, val_smul, imp_self, implies_true]

section FaithfulSMul

theorem eq_iff_smul_eq_smul {a b : VectorPerm n} : a = b ↔ ∀ i : Fin n, a • i = b • i :=
  ⟨fun h _ => h ▸ rfl, eq_of_smul_eq_smul⟩

end FaithfulSMul

theorem period_pos (a : VectorPerm n) {i : Fin n} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

end MulActionFin

open Equiv.Perm in
/--
`VectorPerm n` is equivalent to `Perm (Fin n)`, and this equivalence respects the
multiplication (and, indeed, the scalar action on `Fin n`).
-/
@[simps! apply_apply_val apply_symm_apply_val]
def finPerm (n : ℕ) : VectorPerm n ≃* Perm (Fin n) where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  invFun π := ⟨Vector.ofFn (Fin.val ∘ π), Vector.ofFn (Fin.val ∘ π.symm),
    fun _ => (Array.getElem_ofFn _ _ _).trans_lt (Fin.is_lt _),
    fun _ => by simp_rw [Vector.getElem_ofFn, comp_apply, Fin.eta, symm_apply_apply]⟩
  left_inv a := VectorPerm.ext <| fun _ => by simp_rw [coe_fn_mk, coe_fn_symm_mk, getElem_mk,
    Vector.getElem_ofFn, comp_apply, val_smul]
  right_inv π := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [coe_fn_mk, val_smul, getElem_mk,
    Vector.getElem_ofFn, Fin.eta, comp_apply]
  map_mul' a b := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [mul_inv_rev, Perm.coe_mul,
    comp_apply, coe_fn_mk, val_smul, getElem_mul]

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

instance : Fintype (VectorPerm n) := Fintype.ofEquiv (Perm (Fin n)) (finPerm n).symm.toEquiv

end FinPerm

instance : MulAction (VectorPerm n) ℕ where
  smul a i := a[i]?.getD i
  one_smul k := by
    unfold HSMul.hSMul instHSMul
    rcases lt_or_le k n with hkn | hkn
    · simp_rw [getElem?_pos (1 : VectorPerm n) k hkn, Option.getD_some, getElem_one]
    · simp_rw [getElem?_neg (1 : VectorPerm n) k hkn.not_lt, Option.getD_none]
  mul_smul a b k := by
    unfold HSMul.hSMul instHSMul
    rcases lt_or_le k n with hkn | hkn
    · simp_rw [getElem?_pos (a * b) k hkn, getElem?_pos b k hkn, Option.getD_some,
        getElem?_pos a b[k] b.getElem_lt, Option.getD_some, getElem_mul]
    · simp_rw [getElem?_neg (a * b) k hkn.not_lt, getElem?_neg b k hkn.not_lt,
        Option.getD_none, getElem?_neg a k hkn.not_lt, Option.getD_none]

section MulActionNat

theorem smul_nat_def (a : VectorPerm n) (i : ℕ) :
    a • i = a[i]?.getD i := rfl

theorem smul_nat_eq_dite (a : VectorPerm n) (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i := by
  simp_rw [smul_nat_def, getElem?_def, apply_dite (fun (o : Option ℕ) => o.getD i),
    Option.getD_some, Option.getD_none]

theorem smul_of_lt (a : VectorPerm n) {i : ℕ} (h : i < n) : a • i = a[i] := by
  simp_rw [smul_nat_def, getElem?_pos a i h, Option.getD_some]

theorem smul_of_ge (a : VectorPerm n) {i : ℕ} (h : n ≤ i) : a • i = i := by
  simp_rw [smul_nat_def, getElem?_neg a i h.not_lt, Option.getD_none]

theorem smul_val (a : VectorPerm n) {i : Fin n} :
    a • i.1 = ((a • i) : Fin n) := a.smul_of_lt _

@[simp]
theorem smul_getElem (a b : VectorPerm n) {i : ℕ} (h : i < n) : a • b[i] = a[b[i]] :=
  a.smul_of_lt _

theorem smul_eq_iff (a : VectorPerm n) {i j : ℕ} :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [a.smul_of_lt hi, hi, hi.not_le, false_implies, forall_true_left, and_true]
  · simp_rw [a.smul_of_ge hi, hi, hi.not_lt, IsEmpty.forall_iff, forall_true_left, true_and]

theorem eq_smul_iff (a : VectorPerm n) {i j : ℕ} :
    i = a • j ↔ (∀ (hj : j < n), i = a[j]) ∧ (n ≤ j → i = j) := by
  simp_rw [eq_comm (a := i), smul_eq_iff]

theorem smul_eq_self_iff (a : VectorPerm n) {i : ℕ} :
    a • i = i ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [smul_eq_iff, implies_true, and_true]

theorem self_eq_smul_iff (a : VectorPerm n) {i : ℕ} :
    i = a • i ↔ ∀ (hi : i < n), i = a[i] := by
  simp_rw [eq_comm (a := i), smul_eq_self_iff]

theorem smul_eq_smul_same_iff {a b : VectorPerm n} {i : ℕ} :
  a • i = b • i ↔ ∀ (hi : i < n), a[i] = b[i] := by
  simp_rw [← inv_smul_eq_iff, ← mul_smul, smul_eq_self_iff, getElem_mul,
  forall_congr' fun h => b.getElem_inv_eq_iff (a.getElem_lt) h]

theorem eq_iff_smul_eq_smul_lt {a b : VectorPerm n} : a = b ↔ ∀ i < n, a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, VectorPerm.ext_iff]
  refine forall_congr' fun i => ?_
  rw [Classical.imp_iff_left_iff]
  exact (lt_or_le i n).imp id fun h => by simp_rw [h.not_lt, forall_false]

instance : FaithfulSMul (VectorPerm n) ℕ where
  eq_of_smul_eq_smul := by
    simp_rw [eq_iff_smul_eq_smul_lt]
    exact fun h _ _ => h _

theorem smul_nat_right_inj (a : VectorPerm n) {i j : ℕ} : a • i = a • j ↔ i = j := by
  simp_rw [← inv_smul_eq_iff, inv_smul_smul]

@[simp]
theorem smul_lt_iff_lt (a : VectorPerm n) {i : ℕ} : a • i < n ↔ i < n := by
  rcases lt_or_le i n with h | h
  · simp_rw [h, iff_true, a.smul_of_lt h, getElem_lt]
  · simp_rw [h.not_lt, iff_false, not_lt, a.smul_of_ge h, h]

theorem smul_lt_of_lt (a : VectorPerm n) {i : ℕ} (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

theorem lt_of_smul_lt (a : VectorPerm n) {i : ℕ} (h : a • i < n) : i < n := a.smul_lt_iff_lt.mp h

theorem smul_eq_iff_eq_one (a : VectorPerm n) : (∀ i < n, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul_lt, one_smul]

theorem smul_eq_id_iff_eq_one (a : VectorPerm n) : ((a • ·) : Fin n → Fin n) = id ↔ a = 1 := by
  simp_rw [← one_smul_eq_id (VectorPerm n), funext_iff, eq_iff_smul_eq_smul]

theorem smul_nat_eq_iff_eq_one (a : VectorPerm n) : (∀ i : ℕ, a • i = i) ↔ a = 1 := by
  simp_rw [← smul_eq_iff_eq_one]
  exact ⟨fun h => fun _ _ => h _, fun h i => (i.lt_or_ge n).elim (h _) a.smul_of_ge⟩

theorem smul_nat_eq_id_iff_eq_one (a : VectorPerm n) : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [funext_iff, id_eq, smul_nat_eq_iff_eq_one]

theorem fixedBy_of_ge (a : VectorPerm n) {i : ℕ} (h : n ≤ i) :
    i ∈ MulAction.fixedBy ℕ a := by
  rw [MulAction.mem_fixedBy]
  exact a.smul_of_ge h

theorem Ici_subset_fixedBy (a : VectorPerm n) :
    Set.Ici n ⊆ MulAction.fixedBy ℕ a := fun _ => a.fixedBy_of_ge

theorem Ici_subset_fixedPoints :
    Set.Ici n ⊆ MulAction.fixedPoints (VectorPerm n) ℕ := fun _ hx a => a.smul_of_ge hx

open Pointwise in
theorem Iic_mem_set_fixedBy (a : VectorPerm n) :
    Set.Iio n ∈ MulAction.fixedBy (Set ℕ) a := Set.ext <| fun _ => by
  rw [← inv_inv a]
  simp_rw [Set.mem_inv_smul_set_iff, Set.mem_Iio, smul_lt_iff_lt]

theorem fixedBy_image_val_subset (a : VectorPerm n) :
    (MulAction.fixedBy (Fin n) a).image (Fin.val) ⊆ MulAction.fixedBy ℕ a := fun _ => by
  simp_rw [Set.mem_image, MulAction.mem_fixedBy, forall_exists_index, and_imp,
  Fin.forall_iff, Fin.ext_iff, smul_mk]
  rintro _ h ha rfl
  exact (a.smul_of_lt h).trans ha


theorem period_eq_one_of_ge (a : VectorPerm n) {i : ℕ} (hi : n ≤ i) : MulAction.period a i = 1 := by
  simp_rw [MulAction.period_eq_one_iff, a.smul_of_ge hi]

theorem period_eq_one_iff (a : VectorPerm n) {i : ℕ} :
    MulAction.period a i = 1 ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [MulAction.period_eq_one_iff]
  rcases lt_or_le i n with hi | hi
  · simp_rw [hi, forall_true_left, a.smul_of_lt hi]
  · simp_rw [hi.not_lt, forall_false, iff_true, a.smul_of_ge hi]

@[simp]
theorem getElem_pow_period (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    (a ^ MulAction.period a i)[i] = i := by
  rw [← smul_of_lt _ hi, MulAction.pow_period_smul]

theorem getElem_pow_mod_period (a : VectorPerm n) {i : ℕ} (hi : i < n) (k : ℕ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt _ hi, MulAction.pow_mod_period_smul]

theorem getElem_zpow_mod_period (a : VectorPerm n) {i : ℕ} (hi : i < n) (k : ℤ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt _ hi, MulAction.zpow_mod_period_smul]

theorem period_nat_pos (a : VectorPerm n) {i : ℕ} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_fin (a : VectorPerm n) {i : Fin n} :
    MulAction.period a i = MulAction.period a (i : ℕ) := by
  rw [le_antisymm_iff]
  refine ⟨MulAction.period_le_of_fixed (period_nat_pos _) (Fin.ext ?_),
    MulAction.period_le_of_fixed (period_pos _) ?_⟩
  · simp_rw [val_smul, getElem_pow_period]
  · simp_rw [smul_val, MulAction.pow_period_smul]

@[simp]
theorem period_mk (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    MulAction.period a (Fin.mk i hi) = MulAction.period a i := a.period_fin

theorem period_eq_one_of_zero (a : VectorPerm 0) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_eq_one_of_one (a : VectorPerm 1) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_le_card_of_getElem_pow_mem (a : VectorPerm n) {i : ℕ} (hi : i < n)
  (s : Finset ℕ) : (∀ k < s.card + 1, (a ^ k)[i] ∈ s) → MulAction.period a i ≤ s.card := by
  simp_rw [← smul_of_lt _ hi]
  exact MulAction.period_le_card_of_smul_pow_mem _ _

theorem getElem_injOn_range_period (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    Set.InjOn (fun k => (a ^ k)[i]) (Finset.range (MulAction.period a i)) := by
  simp_rw [← smul_of_lt _ hi]
  exact MulAction.smul_injOn_range_period _

theorem period_le_of_lt (a : VectorPerm n) {i : ℕ} (hi : i < n) : MulAction.period a i ≤ n := by
  refine (period_le_card_of_getElem_pow_mem a hi (Finset.range n) ?_).trans_eq
    (Finset.card_range _)
  simp_rw [Finset.card_range, Finset.mem_range, getElem_lt, implies_true]

theorem period_le_of_ne_zero [NeZero n] (a : VectorPerm n) {i : ℕ} : MulAction.period a i ≤ n := by
  rcases lt_or_le i n with hi | hi
  · exact a.period_le_of_lt hi
  · rw [a.period_eq_one_of_ge hi]
    exact NeZero.pos n

theorem exists_pos_le_pow_getElem_eq (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k)[i] = i :=
  ⟨MulAction.period a i, a.period_nat_pos, a.period_le_of_lt hi, a.getElem_pow_period _⟩

end MulActionNat


/--
`ofNatPerm` maps a member of `Perm ℕ` which maps the subtype `< n` to itself to the corresponding
`VectorPerm n`.
-/
def ofNatPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) : VectorPerm n where
  fwdVector := (Vector.range n).map f
  bwdVector := (Vector.range n).map ⇑f⁻¹
  getElem_fwdVector_lt := fun {i} => by
    simp_rw [Vector.getElem_map, Vector.getElem_range, hf, imp_self]
  getElem_bwdVector_getElem_fwdVector := by
    simp only [Vector.getElem_map, Vector.getElem_range, Perm.inv_apply_self, implies_true]

section ofNatPerm

@[simp]
theorem getElem_ofNatPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {i : ℕ}
    (hi : i < n) : (ofNatPerm f hf)[i] = f i := by
  unfold ofNatPerm
  simp_rw [getElem_mk, Vector.getElem_map, Vector.getElem_range]

@[simp]
theorem getElem_ofNatPerm_inv {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {i : ℕ} (hi : i < n) :
    (ofNatPerm f hf)⁻¹[i] = f⁻¹ i := by
  unfold ofNatPerm
  simp_rw [getElem_inv_mk, Vector.getElem_map, Vector.getElem_range]

@[simp]
theorem ofNatPerm_inv {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} :
    (ofNatPerm f hf)⁻¹ =
    ofNatPerm f⁻¹ (fun x => (hf (f⁻¹ x)).symm.trans (Perm.apply_inv_self _ _ ▸ Iff.rfl)) := rfl

@[simp]
theorem mul_ofNatPerm {f g : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {hg : ∀ i, g i < n ↔ i < n} :
    (ofNatPerm f hf) * (ofNatPerm g hg) =
    ofNatPerm (f * g) (fun x => (hf (g x)).trans (hg x)) := by
  simp only [VectorPerm.ext_iff, getElem_mul, getElem_ofNatPerm, Perm.mul_apply, implies_true]

end ofNatPerm

/--
`natPerm` is the injective monoid homomorphism from `VectorPerm n` to `Perm ℕ`.
-/

def natPerm (n : ℕ) : VectorPerm n →* Perm ℕ :=
  (Perm.extendDomainHom Fin.equivSubtype).comp (finPerm n : VectorPerm _ →* Equiv.Perm (Fin n))

section NatPerm

@[simp]
theorem natPerm_apply_apply (a : VectorPerm n) {i : ℕ} : natPerm n a i = a • i := by
  unfold natPerm
  simp_rw [MonoidHom.comp_apply, MonoidHom.coe_coe, Perm.extendDomainHom_apply]
  rcases lt_or_le i n with hi | hi
  · simp_rw [Perm.extendDomain_apply_subtype _ Fin.equivSubtype hi, a.smul_of_lt hi,
      Fin.equivSubtype_symm_apply, Fin.equivSubtype_apply, finPerm_apply_apply_val]
  · simp_rw [Perm.extendDomain_apply_not_subtype _ Fin.equivSubtype hi.not_lt, a.smul_of_ge hi]

@[simp]
theorem natPerm_apply_symm_apply (a : VectorPerm n) {i : ℕ} : (natPerm n a).symm i = a⁻¹ • i := by
  rw [← Perm.inv_def, ← map_inv, natPerm_apply_apply]

@[simp]
theorem natPerm_lt_iff_lt (a : VectorPerm n) {i : ℕ} : natPerm n a i < n ↔ i < n := by
  rw [natPerm_apply_apply, smul_lt_iff_lt]

theorem natPerm_apply_apply_of_lt (a : VectorPerm n) {i : ℕ} (h : i < n) :
    natPerm n a i = a[i] := by rw [natPerm_apply_apply, a.smul_of_lt h]

theorem natPerm_apply_apply_of_ge (a : VectorPerm n) {i : ℕ} (h : n ≤ i) : natPerm n a i = i := by
  rw [natPerm_apply_apply, a.smul_of_ge h]

theorem natPerm_apply_symm_apply_of_lt (a : VectorPerm n) {i : ℕ} (h : i < n) :
    (natPerm n a)⁻¹ i = a⁻¹[i] := by
  simp_rw [← MonoidHom.map_inv, natPerm_apply_apply_of_lt _ h]

theorem natPerm_apply_symm_apply_of_ge (a : VectorPerm n) {i : ℕ} (h : n ≤ i) :
    (natPerm n a)⁻¹ i = i := by rw [← MonoidHom.map_inv, natPerm_apply_apply_of_ge _ h]

theorem natPerm_injective : Function.Injective (natPerm n) :=
  (Equiv.Perm.extendDomainHom_injective Fin.equivSubtype).comp (finPerm n).injective

theorem natPerm_inj {a b : VectorPerm n} : natPerm n a = natPerm n b ↔ a = b :=
  natPerm_injective.eq_iff

theorem natPerm_ofNatPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) (i : ℕ) :
    natPerm n (ofNatPerm f hf) i = if i < n then f i else i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [natPerm_apply_apply_of_lt _ hi, getElem_ofNatPerm, hi, if_true]
  · simp_rw [natPerm_apply_apply_of_ge _ hi, hi.not_lt, if_false]

theorem ofNatPerm_natPerm (a : VectorPerm n) :
    ofNatPerm (natPerm n a) (fun _ => a.natPerm_lt_iff_lt) = a := by
  ext i hi
  simp_rw [getElem_ofNatPerm, a.natPerm_apply_apply_of_lt hi]

theorem apply_eq_of_ge_iff_exists_natPerm_apply (e : Perm ℕ) :
    (∀ i ≥ n, e i = i) ↔ ∃ a : VectorPerm n, natPerm n a = e := by
  refine ⟨fun h => ?_, ?_⟩
  · have H : ∀ i, e i < n ↔ i < n := fun i => by
      simp_rw [← not_le, not_iff_not]
      exact ⟨fun hi => by rwa [e.injective (h _ hi).symm], fun hi => (h _ hi).symm ▸ hi⟩
    use ofNatPerm e H
    simp_rw [Equiv.ext_iff, natPerm_ofNatPerm e H, ite_eq_left_iff, not_lt]
    exact fun _ hi => (h _ hi).symm
  · rintro ⟨a, rfl⟩ i hi
    exact a.natPerm_apply_apply_of_ge hi

theorem coe_natPerm_range : MonoidHom.range (natPerm (n := n)) =
    {e : Perm ℕ | ∀ i ≥ n, e i = i} := by
  simp_rw [Set.ext_iff, MonoidHom.coe_range, Set.mem_range, ge_iff_le, Set.mem_setOf_eq,
  apply_eq_of_ge_iff_exists_natPerm_apply, implies_true]

end NatPerm

def actOnIndices (a : VectorPerm n) (v : Vector α n) : Vector α n :=
  v.mapIdx (fun i _ => v[a[i.1]])

section ActOnIndices

variable {α : Type*}

@[simp] theorem getElem_actOnIndices (a : VectorPerm n) (v : Vector α n) {i : ℕ} (hi : i < n) :
    (a.actOnIndices v)[i] = v[a[i]] := Vector.getElem_mapIdx _ _ _

@[simp] theorem one_actOnIndices (v : Vector α n) :
    (1 : (VectorPerm n)).actOnIndices v = v := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, getElem_one, implies_true]

@[simp] theorem mul_actOnIndices (a b : VectorPerm n) (v : Vector α n) :
    (a * b).actOnIndices v = b.actOnIndices (a.actOnIndices v) := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, getElem_mul, implies_true]

@[simp] theorem actOnIndices_actOnIndices_inv (a : VectorPerm n) (v : Vector α n) :
    a.actOnIndices (a⁻¹.actOnIndices v) = v := by
  simp_rw [← mul_actOnIndices, inv_mul_cancel, one_actOnIndices]

@[simp] theorem actOnIndices_inv_actOnIndices (a : VectorPerm n) (v : Vector α n) :
    a⁻¹.actOnIndices (a.actOnIndices v) = v := by
  simp_rw [← mul_actOnIndices, mul_inv_cancel, one_actOnIndices]

theorem mem_of_mem_actOnIndices (a : VectorPerm n) {v : Vector α n} {x : α}
    (hx : x ∈ a.actOnIndices v) : x ∈ v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_actOnIndices] at hx
  rcases hx with ⟨i, hi, hix⟩
  exact ⟨a[i], a.getElem_lt, hix⟩

theorem mem_actOnIndices_of_mem (a : VectorPerm n) {v : Vector α n} {x : α}
    (hx : x ∈ v) : x ∈ a.actOnIndices v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_actOnIndices]
  rcases hx with ⟨i, hi, hix⟩
  refine ⟨a⁻¹[i], getElem_lt _, ?_⟩
  simp_rw [getElem_getElem_inv, hix]

theorem mem_onIndices_iff (a : VectorPerm n) {v : Vector α n} {x : α} :
    x ∈ a.actOnIndices v ↔ x ∈ v := ⟨a.mem_of_mem_actOnIndices, a.mem_actOnIndices_of_mem⟩

@[simp]
theorem actOnIndices_range (a : VectorPerm n) :
    a.actOnIndices (Vector.range n) = a.fwdVector := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, Vector.getElem_range,
    getElem_fwdVector, implies_true]

@[simp]
theorem inv_actOnIndices_range (a : VectorPerm n) :
    (a⁻¹).actOnIndices (Vector.range n) = a.bwdVector := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, Vector.getElem_range,
    getElem_bwdVector, implies_true]

end ActOnIndices

instance {α : Type u} : MulAction (VectorPerm n)ᵐᵒᵖ (Vector α n) where
  smul a v := a.unop.actOnIndices v
  one_smul _ := one_actOnIndices _
  mul_smul _ _ _ := mul_actOnIndices _ _ _

section MulActionMulOppositeVector

@[simp] theorem op_smul (a : VectorPerm n) (v : Vector α n) :
    (MulOpposite.op a) • v = a.actOnIndices v := rfl

@[simp] theorem unop_actOnIndices (a : (VectorPerm n)ᵐᵒᵖ) (v : Vector α n) :
    a.unop.actOnIndices v = a • v := rfl

end MulActionMulOppositeVector

def cycleOfAux (a : VectorPerm n) :
    ℕ → Finset (Fin n) × Fin n × Fin n → Finset (Fin n) × Fin n × Fin n
  | 0, p => p
  | (k + 1), (s, y, x) =>
    let s' := insert y s
    let z := a[y];
    if z = x then (s', ⟨z, a.getElem_lt⟩, x) else cycleOfAux a k (s', ⟨z, a.getElem_lt⟩, x)

def cycleOf (a : VectorPerm n) (x : ℕ) : Finset ℕ :=
  if h : x < n then (Finset.range n).image (fun k => (a ^ k)[x]) else {x}

theorem cycleOf_lt (a : VectorPerm n) {x : ℕ} (hx : x < n) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k)[x]) := by
  unfold cycleOf
  simp_rw [dif_pos hx, Finset.ext_iff, Finset.mem_image, Finset.mem_range]
  refine fun _ => ⟨fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos,
    by simp_rw [getElem_pow_mod_period, h]⟩, fun ⟨_, hlt, h⟩ =>
    ⟨_, (hlt.trans_le <| a.period_le_of_lt hx), h⟩⟩

theorem cycleOf_ge (a : VectorPerm n) {x : ℕ} (hx : n ≤ x) :
    a.cycleOf x = {x} := dif_neg (not_lt_of_le hx)

theorem card_cycleOf (a : VectorPerm n) (x : ℕ) : (a.cycleOf x).card = MulAction.period a x := by
  rcases lt_or_le x n with hx | hx
  · refine Eq.trans ?_ (Finset.card_range (MulAction.period a x))
    rw [a.cycleOf_lt hx, Finset.card_image_iff]
    exact getElem_injOn_range_period _ _
  · rw [a.cycleOf_ge hx, a.period_eq_one_of_ge hx, Finset.card_singleton]

theorem cycleOf_eq_map_smul_range_period (a : VectorPerm n) (x : ℕ) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k) • x) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleOf_lt hx, smul_of_lt _ hx]
  · simp_rw [a.cycleOf_ge hx, smul_of_ge _ hx, Finset.ext_iff, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range, exists_and_right]
    exact fun _ => ⟨fun h => h ▸ ⟨⟨0, a.period_nat_pos⟩, rfl⟩, fun h => h.2.symm⟩

theorem mem_cycleOf_iff_exists_pow_lt_period_smul (a : VectorPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i) • x = y := by
  rw [cycleOf_eq_map_smul_range_period]
  simp_rw [Finset.mem_image, Finset.mem_range]

theorem mem_cycleOf_iff_exists_pow_smul (a : VectorPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_lt_period_smul]
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩,
    fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos, ?_⟩⟩
  simp_rw [MulAction.pow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_zpow_smul (a : VectorPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_smul]
  refine ⟨fun ⟨_, h⟩ => ⟨_, (zpow_natCast a _).symm ▸ h⟩,
    fun ⟨k, h⟩ => ⟨(k % MulAction.period a x).toNat, ?_⟩⟩
  simp_rw [← zpow_natCast, Int.toNat_of_nonneg
    (Int.emod_nonneg _ ((Nat.cast_ne_zero (R := ℤ)).mpr (a.period_nat_pos (i := x)).ne')),
    MulAction.zpow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_getElem_pow_lt_period (a : VectorPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_lt_period_smul, smul_of_lt _ hx]

theorem mem_cycleOf_iff_exists_getElem_pow (a : VectorPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul, smul_of_lt _ hx]

theorem mem_cycleOf_iff_exists_getElem_zpow (a : VectorPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul, smul_of_lt _ hx]

theorem self_mem_cycleOf (a : VectorPerm n) (x : ℕ) : x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨0, by simp only [pow_zero, one_smul]⟩

theorem nonempty_cycleOf (a : VectorPerm n) {x : ℕ} : (a.cycleOf x).Nonempty :=
  ⟨_, a.self_mem_cycleOf x⟩

theorem smul_mem_cycleOf (a : VectorPerm n) (x : ℕ) : (a • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨1, by simp only [pow_one]⟩

theorem smul_inv_mem_cycleOf (a : VectorPerm n) (x : ℕ) : (a⁻¹ • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨-1, by simp only [zpow_neg, zpow_one]⟩

theorem smul_pow_mem_cycleOf (a : VectorPerm n) (x k : ℕ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨k, rfl⟩

theorem smul_zpow_mem_cycleOf (a : VectorPerm n) (x : ℕ) (k : ℤ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨k, rfl⟩

theorem getElem_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) : a[x] ∈ a.cycleOf x := by
  convert a.smul_mem_cycleOf x
  rw [smul_of_lt _ hx]

theorem getElem_inv_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) : a⁻¹[x] ∈ a.cycleOf x := by
  convert a.smul_inv_mem_cycleOf x
  rw [smul_of_lt _ hx]

theorem getElem_pow_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) (k : ℕ):
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_pow_mem_cycleOf x k
  rw [smul_of_lt _ hx]

theorem getElem_zpow_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) (k : ℤ) :
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_zpow_mem_cycleOf x k
  rw [smul_of_lt _ hx]

theorem getElem_inv_pow_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) (k : ℕ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  convert a.getElem_zpow_mem_cycleOf hx (-(k : ℤ))
  simp_rw [inv_pow, zpow_neg, zpow_natCast]

theorem getElem_inv_zpow_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) (k : ℤ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  simp only [inv_zpow']
  exact a.getElem_zpow_mem_cycleOf hx (-k)

def CycleMinVectorAux (a : VectorPerm n) : ℕ → VectorPerm n × Vector ℕ n
  | 0 => ⟨1, Vector.range n⟩
  | 1 =>
    ⟨a, (Vector.range n).zipWith a.fwdVector min⟩
  | (i+2) =>
    let ⟨ρ, b⟩ := a.CycleMinVectorAux (i + 1)
    let ρ' := ρ ^ 2
    ⟨ρ', b.zipWith (ρ'.actOnIndices b) min⟩

@[simp]
theorem cycleMinAux_zero_fst (a : VectorPerm n) : (a.CycleMinVectorAux 0).1 = 1 := rfl

@[simp]
theorem cycleMinAux_succ_fst (a : VectorPerm n) (i : ℕ) :
    (a.CycleMinVectorAux (i + 1)).1 = a ^ (2 ^ i) := by
  induction' i with i IH
  · rw [pow_zero, pow_one]
    rfl
  · rw [pow_succ, pow_mul]
    exact IH ▸ rfl

def CycleMinVector (a : VectorPerm n) (i : ℕ) : Vector ℕ n := (a.CycleMinVectorAux i).2

@[simp]
theorem cycleMinAux_snd_val (a : VectorPerm n) {i : ℕ} :
    (a.CycleMinVectorAux i).2 = CycleMinVector a i := rfl

@[simp] theorem getElem_cycleMinVector_zero (a : VectorPerm n) {x : ℕ} (hx : x < n):
  (a.CycleMinVector 0)[x] = x := Vector.getElem_range _

theorem getElem_cycleMinVector_succ (a : VectorPerm n) {i x : ℕ}
    (hx : x < n) :
    (a.CycleMinVector (i + 1))[x] = min ((a.CycleMinVector i)[x])
    ((a.CycleMinVector i)[(a^2^i)[x]]) := by
  rcases i with (_ | i) <;>
  refine (Vector.getElem_zipWith _).trans ?_
  · simp_rw [Vector.getElem_range, getElem_fwdVector, pow_zero, pow_one,
      getElem_cycleMinVector_zero]
  · simp_rw [getElem_actOnIndices, cycleMinAux_snd_val,
      cycleMinAux_succ_fst, ← pow_mul, ← pow_succ]

@[simp] theorem getElem_one_cycleMinVector (hi : i < n) :
    ((1 : VectorPerm n).CycleMinVector k)[i] = i := by
  induction k generalizing n i with | zero => _ | succ k IH => _
  · simp_rw [getElem_cycleMinVector_zero]
  · simp_rw [getElem_cycleMinVector_succ, one_pow, getElem_one, IH, min_self]

theorem one_cycleMinVector : (1 : VectorPerm n).CycleMinVector k = Vector.range n := by
  ext i hi
  simp_rw [getElem_one_cycleMinVector, Vector.getElem_range]

@[simp]
theorem getElem_cycleMinVector_lt (a : VectorPerm n) {i : ℕ} {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] < n := by
  induction' i with i IH generalizing x
  · simp_rw [getElem_cycleMinVector_zero]
    exact hx
  · simp_rw [getElem_cycleMinVector_succ, min_lt_iff, IH, true_or]

lemma getElem_cycleMinVector_le_getElem_pow_lt (a : VectorPerm n) {i : ℕ} {x : ℕ}
    {hx : x < n} {k : ℕ} (hk : k < 2^i) :
    (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := by
  induction' i with i IH generalizing x k
  · simp_rw [pow_zero, Nat.lt_one_iff] at hk
    simp_rw [getElem_cycleMinVector_zero, hk, pow_zero, getElem_one, le_rfl]
  · simp_rw [getElem_cycleMinVector_succ, min_le_iff]
    by_cases hk' : k < 2^i
    · exact Or.inl (IH hk')
    · rw [pow_succ', Nat.two_mul, ← Nat.sub_lt_iff_lt_add (le_of_not_lt hk')] at hk
      exact Or.inr ((IH hk).trans_eq <| by
        rw [getElem_pow_add, Nat.sub_add_cancel (le_of_not_lt hk')])

lemma getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hx : x < n) (hai : MulAction.period a x ≤ 2^i) :
    ∀ k, (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := fun k => by
  have H := a.getElem_pow_mem_cycleOf hx k
  rw [mem_cycleOf_iff_exists_getElem_pow_lt_period] at H
  rcases H with ⟨_, hk₁, hk₂⟩
  exact (a.getElem_cycleMinVector_le_getElem_pow_lt (hk₁.trans_le hai)).trans_eq hk₂

lemma getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow (a : VectorPerm n) (i : ℕ) {x : ℕ}
      (hx : x < n) (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := fun k => by
  have H := a.getElem_zpow_mem_cycleOf hx k
  rw [mem_cycleOf_iff_exists_getElem_pow_lt_period] at H
  rcases H with ⟨_, hk₁, hk₂⟩
  exact (a.getElem_cycleMinVector_le_getElem_pow_lt (hk₁.trans_le hai)).trans_eq hk₂

lemma getElem_cycleMinVector_le_self (a : VectorPerm n) (i : ℕ) {x : ℕ}
      (hx : x < n) : (a.CycleMinVector i)[x] ≤ x :=
  (a.getElem_cycleMinVector_le_getElem_pow_lt (Nat.two_pow_pos _)).trans_eq
      (by simp_rw [pow_zero, getElem_one])

lemma exists_lt_getElem_cycleMin_eq_getElem_pow (a : VectorPerm n) (i : ℕ) {x : ℕ}
      (hx : x < n) :
    ∃ k < 2^i, (a.CycleMinVector i)[x] = (a ^ k)[x] := by
  induction' i with i IH generalizing x
  · simp_rw [getElem_cycleMinVector_zero]
    exact ⟨0, Nat.two_pow_pos _, pow_zero a ▸ (getElem_one _).symm⟩
  · rcases IH hx with ⟨k, hk, hπk⟩
    rcases (IH (x := (a ^ (2 ^ i))[x]) (getElem_lt _)) with ⟨k', hk', hπk'⟩
    simp_rw [getElem_cycleMinVector_succ, hπk, hπk', getElem_pow_add,
    pow_succ', Nat.two_mul]
    rcases lt_or_le ((a ^ k)[x]) ((a ^ (k' + 2 ^ i))[x]) with hkk' | hkk'
    · rw [min_eq_left hkk'.le]
      exact ⟨k, hk.trans (Nat.lt_add_of_pos_right (Nat.two_pow_pos _)), rfl⟩
    · rw [min_eq_right hkk']
      exact ⟨k' + 2^i, Nat.add_lt_add_right hk' _, rfl⟩

lemma getElem_cycleMinVector_eq_min'_cycleOf (a : VectorPerm n) (i : ℕ) {x : ℕ}
      (hx : x < n) (hai : MulAction.period a x ≤ 2^i) :
      (a.CycleMinVector i)[x] = (a.cycleOf x).min' a.nonempty_cycleOf := by
  refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ ?_) <;>
  simp_rw [mem_cycleOf_iff_exists_getElem_pow _ hx]
  · simp_rw [forall_exists_index, forall_apply_eq_imp_iff]
    exact getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow _ _ _ hai
  · rcases a.exists_lt_getElem_cycleMin_eq_getElem_pow i (x := x) (by assumption) with ⟨k, _, hk⟩
    exact ⟨_, hk.symm⟩

def CycleMin (a : VectorPerm n) (i : ℕ) (x : ℕ) : ℕ := (a.CycleMinVector i)[x]?.getD x

theorem getElem_cycleMinVector (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] = a.CycleMin i x :=
  (Vector.getD_of_lt _ _ _ _).symm

theorem cycleMin_of_lt (a : VectorPerm n) {i x : ℕ} (hx : x < n) :
    a.CycleMin i x = (a.CycleMinVector i)[x] := Vector.getD_of_lt _ _ _ _

theorem cycleMin_of_getElem {a b : VectorPerm n} {i x : ℕ} (hx : x < n) :
    a.CycleMin i (b[x]) = (a.CycleMinVector i)[b[x]] :=
  Vector.getD_of_lt _ _ _ _

theorem cycleMin_of_ge (a : VectorPerm n) {i x : ℕ} (hx : n ≤ x) :
    a.CycleMin i x = x := Vector.getD_of_ge _ _ _ hx

@[simp] theorem one_cycleMin : (1 : VectorPerm n).CycleMin k x = x := by
  rcases lt_or_le x n with hx | hx
  · rw [cycleMin_of_lt _ hx, one_cycleMinVector, Vector.getElem_range]
  · rwa [cycleMin_of_ge]

@[simp]
theorem cycleMin_zero (a : VectorPerm n) {x : ℕ} :
  a.CycleMin 0 x = x := if hx : x < n then
    (a.cycleMin_of_lt hx).trans <| Array.getElem_range _ else a.cycleMin_of_ge (le_of_not_lt hx)

@[simp]
theorem cycleMin_succ (a : VectorPerm n) {i x : ℕ} :
    a.CycleMin (i + 1) x = min (a.CycleMin i x) (a.CycleMin i (a^2^i • x)) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [smul_of_lt _ hx, a.cycleMin_of_lt hx, cycleMin_of_getElem, getElem_cycleMinVector_succ]
  · simp_rw [smul_of_ge _ hx, a.cycleMin_of_ge hx, min_self]

@[simp]
theorem cycleMin_lt_iff_lt (a : VectorPerm n) {i : ℕ} {x : ℕ} :
    a.CycleMin i x < n ↔ x < n := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, hx, getElem_cycleMinVector_lt]
  · simp_rw [a.cycleMin_of_ge hx]

lemma cycleMin_le_smul_pow_lt_two_pow (a : VectorPerm n) {i : ℕ} (x : ℕ) {k : ℕ} (hk : k < 2^i) :
    a.CycleMin i x ≤ (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_pow_lt _ hk
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_pow_smul_of_period_le_two_pow (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) : ∀ k, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow _ _ _ hai _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_zpow_smul_of_period_le_two_pow  (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow _ _ _ hai _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_self (a : VectorPerm n) (i : ℕ) {x : ℕ} :
    a.CycleMin i x ≤ x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx]
    exact getElem_cycleMinVector_le_self _ _ _
  · simp_rw [a.cycleMin_of_ge hx, le_rfl]

lemma exists_lt_cycleMin_eq_smul_pow (a : VectorPerm n) (i : ℕ) {x : ℕ} :
    ∃ k < 2^i, a.CycleMin i x = (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact exists_lt_getElem_cycleMin_eq_getElem_pow _ _ _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx]
    exact ⟨0, Nat.two_pow_pos _, trivial⟩

lemma cycleMin_eq_min'_cycleOf (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    a.CycleMin i x = (a.cycleOf x).min' a.nonempty_cycleOf := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx]
    exact getElem_cycleMinVector_eq_min'_cycleOf _ _ _ hai
  · simp_rw [a.cycleMin_of_ge hx, a.cycleOf_ge hx]
    exact rfl

section Cast

variable {m : ℕ}

/--
`VectorPerm.cast` re-interprets an `VectorPerm n` as an `VectorPerm m`, where `n = m`.
-/
def cast (hnm : n = m) (a : VectorPerm n) : VectorPerm m where
  fwdVector := a.fwdVector.cast hnm
  bwdVector := a.bwdVector.cast hnm
  getElem_fwdVector_lt := fun _ => by
    simp_rw [Vector.getElem_cast, hnm.symm, getElem_fwdVector, getElem_lt]
  getElem_bwdVector_getElem_fwdVector :=
    fun hi => a.getElem_inv_getElem (hi.trans_eq hnm.symm)

@[simp]
theorem getElem_cast (hnm : n = m) (a : VectorPerm n) {i : ℕ} (hi : i < m):
    (a.cast hnm)[i] = a[i] := rfl

@[simp]
theorem getElem_inv_cast (hnm : n = m) (a : VectorPerm n) {i : ℕ} (hi : i < m):
    (a.cast hnm)⁻¹[i] = a⁻¹[i] := rfl

@[simp]
theorem cast_smul (hnm : n = m) (a : VectorPerm n) (i : ℕ) :
    (a.cast hnm) • i = a • i := by simp only [smul_nat_def, getElem?_def, getElem_cast, hnm]

@[simp]
theorem cast_inv (hnm : n = m) (a : VectorPerm n) :
    (a.cast hnm)⁻¹ = a⁻¹.cast h := rfl

@[simp]
theorem cast_mul (hnm : n = m) (a b : VectorPerm n) :
    (a * b).cast hnm = a.cast hnm * b.cast hnm := ext <| fun hi => by
  simp only [getElem_cast, getElem_mul]

theorem cast_eq_cast (hnm : n = m) (a : VectorPerm n) :
    hnm ▸ a = a.cast hnm := by cases hnm ; rfl

@[simp] theorem cast_symm {hnm : n = m} {hmb : m = n} (a : VectorPerm n) :
    (a.cast hnm).cast hmb = a := rfl

@[simp] theorem cast_trans {hnm : n = m} {hmo : m = o} (a : VectorPerm n) :
    (a.cast hnm).cast hmo = a.cast (hnm.trans hmo) := rfl


theorem cast_inj {a b : VectorPerm n} {hnm : n = m} : a.cast hnm = b.cast hnm ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [VectorPerm.ext_iff, getElem_cast]
  refine fun H _ hi => ?_
  exact H (hnm ▸ hi)

theorem cast_injective (h : n = m) : Function.Injective (cast h) := fun _ _ => cast_inj.mp

theorem cast_surjective (h : n = m) : Function.Surjective (cast h) :=
  fun a => ⟨a.cast h.symm, a.cast_symm⟩

/--
When `n = m`, `VectorPerm n` is multiplicatively equivalent to `VectorPerm m`.
-/

@[simps! apply symm_apply]
def castMulEquiv (hnm : n = m) : VectorPerm n ≃* VectorPerm m where
  toFun := cast hnm
  invFun := cast hnm.symm
  left_inv a := a.cast_symm
  right_inv a := a.cast_symm
  map_mul' := cast_mul hnm

end Cast

def castGE (hnm : n ≤ m) (a : VectorPerm n) : VectorPerm m where
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

variable {n m : ℕ} (a : VectorPerm n)

@[simp]
theorem getElem_castGE {i : ℕ} {hi : i < m} :
    (a.castGE hnm)[i] = if hi : i < n then a[i] else i := by
  unfold castGE
  simp_rw [getElem_mk, Vector.getElem_cast, Vector.getElem_append, getElem_fwdVector,
    Vector.getElem_map, Vector.getElem_range]
  exact dite_congr rfl (fun _ => rfl) (fun hin => Nat.sub_add_cancel (le_of_not_lt hin))

@[simp]
theorem getElem_castGE_of_lt {hnm : n ≤ m} {i : ℕ} (hi : i < n) :
    (a.castGE hnm)[i] = a[i] := by
  simp_rw [getElem_castGE, hi, dite_true]

@[simp]
theorem castGE_inv :
    (a.castGE hnm)⁻¹ = a⁻¹.castGE hnm := rfl

theorem getElem_inv_castGE (hnm : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castGE hnm)⁻¹[i] = if hi : i < n then a⁻¹[i] else i :=
  a.castGE_inv ▸ a⁻¹.getElem_castGE

@[simp]
theorem castGE_one {hnm : n ≤ m} : ((1 : VectorPerm n).castGE hnm) = 1 := by
  ext i hi : 1
  simp_rw [getElem_castGE, getElem_one, dite_eq_ite, ite_self]

@[simp]
theorem castGE_mul (hnm : n ≤ m) {a b : VectorPerm n} :
    (a * b).castGE hnm = a.castGE hnm * b.castGE hnm := by
  ext i
  simp_rw [getElem_castGE, getElem_mul, getElem_castGE]
  rcases lt_or_le i n with hi | hi
  · simp only [hi, dite_true, getElem_lt]
  · simp only [hi.not_lt, dite_false]

@[simp] theorem castGE_of_eq (hnm : n = m) (hnm' : n ≤ m := hnm.le) :
    a.castGE hnm' = a.cast hnm := by
  ext i hi
  simp_rw [getElem_castGE, getElem_cast, hi.trans_eq hnm.symm, dite_true]

@[simp] theorem castGE_trans {hmk : m ≤ k} :
    (a.castGE hnm).castGE hmk = a.castGE (hnm.trans hmk) := by
  ext i hi
  simp_rw [getElem_castGE]
  rcases lt_or_le i m with him | him
  · simp_rw [him, dite_true]
  · simp_rw [him.not_lt, (hnm.trans him).not_lt, dite_false]

theorem fixLT_castGE {hnm : n ≤ m} (hnk : n ≤ k) : (a.castGE hnm).FixLT k :=
  fixLT_of_lt_imp_getElem_lt (fun hik => by
    simp_rw [getElem_castGE]
    split_ifs with hin
    · exact a.getElem_lt.trans_le hnk
    · exact hik)

theorem fixLT_castGE_eq {hnm : n ≤ m} : (a.castGE hnm).FixLT n := a.fixLT_castGE le_rfl

theorem castGE_mem_fixLTSubgroup {hnm : n ≤ m} (hnk : n ≤ k) :
    (a.castGE hnm) ∈ fixLTSubgroup m k := a.fixLT_castGE hnk

theorem castGE_mem_fixLTSubgroup_eq {hnm : n ≤ m} :
    (a.castGE hnm) ∈ fixLTSubgroup m n := a.fixLT_castGE_eq

theorem castLE_lt_imp_getElem_lt {hnm : n ≤ m} (him : i < n) : (a.castGE hnm)[i] < n := by
  simp_rw [getElem_castGE, him, dite_true]
  exact a.getElem_lt

theorem castGE_inj {a b : VectorPerm n} {hnm : n ≤ m} : castGE hnm a = castGE hnm b ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [VectorPerm.ext_iff, getElem_castGE]
  refine fun H _ hi => ?_
  specialize H (hi.trans_le hnm)
  simp_rw [hi, dite_true] at H
  exact H

theorem castGE_injective (hnm : n ≤ m) : Function.Injective (castGE hnm) :=
  fun _ _ => castGE_inj.mp

@[simps! apply_coe]
def castGEMonoidHom (hnm : n ≤ m) : VectorPerm n →* fixLTSubgroup m n where
  toFun a := ⟨a.castGE hnm, a.castGE_mem_fixLTSubgroup_eq⟩
  map_mul' := fun _ _ => Subtype.ext (castGE_mul hnm)
  map_one' := Subtype.ext <| by simp_rw [castGE_one, Subgroup.coe_one]

theorem castGEMonoidHom_injective {hnm : n ≤ m} :
    (⇑(castGEMonoidHom hnm)).Injective :=
  fun _ _ h => castGE_injective hnm (Subtype.ext_iff.mp h)

@[simp]
theorem castGE_smul {i : ℕ} :
    (a.castGE hnm) • i = a • i := by
  simp_rw [smul_nat_eq_dite, getElem_castGE, dite_eq_ite, ite_eq_left_iff, not_lt]
  intro hmi
  simp_rw [(hnm.trans hmi).not_lt, dite_false]

end CastGE

def castLE (hmn : m ≤ n) (a : VectorPerm n) (ham : a.FixLT m) : VectorPerm m where
  fwdVector := (a.fwdVector.take m).cast (min_eq_left hmn)
  bwdVector := (a.bwdVector.take m).cast (min_eq_left hmn)
  getElem_fwdVector_lt := fun him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_take, getElem_fwdVector, ham.getElem_lt_of_lt him]
  getElem_bwdVector_getElem_fwdVector := fun _ => by
    simp_rw [Vector.getElem_cast, Vector.getElem_take, getElem_bwdVector_getElem_fwdVector]

section CastLE

variable (a : VectorPerm n) (ham : a.FixLT m) {hmn : m ≤ n}

@[simp] theorem getElem_castLE (him : i < m) :
    (a.castLE hmn ham)[i] = a[i] := by
  unfold castLE
  simp_rw [getElem_mk, Vector.getElem_cast, Vector.getElem_take, getElem_fwdVector]

@[simp] theorem castLE_inv : (a.castLE hmn ham)⁻¹ = a⁻¹.castLE hmn ham.inv := rfl

theorem getElem_inv_castLE (him : i < m) :
    (a.castLE hnm ham)⁻¹[i] = a⁻¹[i]  := by
  simp_rw [castLE_inv, getElem_castLE]

@[simp]
theorem castLE_one  : ((1 : VectorPerm n).castLE hnm fixLT_one) = (1 : VectorPerm m) := by
  ext i hi : 1
  simp_rw [getElem_castLE, getElem_one]

@[simp]
theorem castLE_mul (hmn : m ≤ n) {a b : VectorPerm n} (ham : a.FixLT m) (hbm : b.FixLT m) :
    (a * b).castLE hmn (ham.mul hbm) = a.castLE hmn ham * b.castLE hmn hbm := by
  ext i
  simp only [getElem_mul, getElem_castLE]

@[simp] theorem castLE_of_eq {a : VectorPerm n} (ham : a.FixLT m) (hnm : n = m)
    (hnm' : m ≤ n := hnm.ge) : a.castLE hnm' ham = a.cast hnm := by
  ext i hi
  simp_rw [getElem_castLE, getElem_cast]

theorem FixLT.castLE {a : VectorPerm n} (ham : a.FixLT m) {hkn : k ≤ n} {hak : a.FixLT k} :
    (a.castLE hkn hak).FixLT m := fixLT_of_lt_imp_getElem_lt (fun hik => by
    simp_rw [getElem_castLE]
    exact ham.getElem_lt_of_lt hik)

@[simp] theorem castLE_trans {a : VectorPerm n} (ham : a.FixLT m) {hkn : k ≤ n} {hmk : m ≤ k}
    (hak : a.FixLT k) :
    (a.castLE hkn hak).castLE hmk ham.castLE = a.castLE (hmk.trans hnm) ham := by
  ext i hi
  simp_rw [getElem_castLE]

theorem castLE_castGE {hnm : n ≤ m} :
    (a.castGE hnm).castLE hnm a.fixLT_castGE_eq = a := by
  ext i hi
  simp_rw [getElem_castLE, a.getElem_castGE_of_lt hi]

theorem getElem_castGE_castLE_of_lt (hi : i < m) : ((a.castLE hmn ham).castGE hmn)[i] = a[i] := by
  simp_rw [getElem_castGE_of_lt _ hi, getElem_castLE]

theorem castLE_surjective (hmn : m ≤ n) (b : VectorPerm m) :
    ∃ (a : VectorPerm n), ∃ (ham : a.FixLT m), a.castLE hmn ham = b := by
  exact ⟨_, _, b.castLE_castGE⟩

@[simps! apply]
def castLEMonoidHom (hmn : m ≤ n) : fixLTSubgroup n m →* VectorPerm m where
  toFun a := castLE hmn a.1 a.2
  map_mul' a b := castLE_mul hmn a.2 b.2
  map_one' := castLE_one

theorem castLEMonoidHom_surjective {hmn : m ≤ n} :
  (⇑(castLEMonoidHom hmn)).Surjective := fun a => Subtype.exists.mpr (a.castLE_surjective hmn)

theorem castLE_smul_of_lt {i : ℕ} (him : i < m) :
    (a.castLE hmn ham) • i = a • i := by
  simp_rw [smul_of_lt _ him, smul_of_lt _ (him.trans_le hmn), getElem_castLE]

end CastLE

def castOfFixLT (a : VectorPerm n) (ham : a.FixLT m) :
    VectorPerm m where
  fwdVector := ((a.fwdVector.take m) ++ (Vector.range (m - n)).map (· + n)).cast
    (Nat.add_comm _ _ ▸ Nat.sub_add_min_cancel m n)
  bwdVector := ((a.bwdVector.take m) ++ (Vector.range (m - n)).map (· + n)).cast
    (Nat.add_comm _ _ ▸ Nat.sub_add_min_cancel m n)
  getElem_fwdVector_lt := fun {i} him => by
    simp_rw [Vector.getElem_cast]
    simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take, getElem_fwdVector,
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
    simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take, getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range, getElem_bwdVector, him, true_and]
    rcases lt_or_le m n with hmn | hmn
    · simp_rw [him.trans hmn, dite_true, getElem_lt, and_true, getElem_inv_getElem,
        ham.getElem_lt_of_lt him, dite_true]
    · rcases lt_or_le i n with hin | hin
      · simp_rw [hin, dite_true, getElem_lt, and_true, getElem_inv_getElem,
          ham.getElem_lt_of_lt him, dite_true]
      · simp_rw [hin.not_lt, dite_false, min_eq_right hmn, Nat.sub_add_cancel hin,
          hin.not_lt, and_false, dite_false]

section CastOfFixLT

variable (a : VectorPerm n) (ham : a.FixLT m)

@[simp] theorem getElem_castOfFixLT (him : i < m) :
    (a.castOfFixLT ham)[i] = if hin : i < n then a[i] else i := by
  unfold castOfFixLT
  simp_rw [getElem_mk, Vector.getElem_cast]
  simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take, getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range, getElem_bwdVector, him, true_and]
  rcases lt_or_le m n with hmn | hmn
  · simp_rw [him.trans hmn, dite_true]
  · rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true]
    · simp_rw [hin.not_lt, dite_false, min_eq_right hmn, Nat.sub_add_cancel hin]

@[simp] theorem castOfSmulLtOfLt_inv :
    (a.castOfFixLT ham)⁻¹ = a⁻¹.castOfFixLT ham.inv := by
  ext
  unfold castOfFixLT
  simp_rw [getElem_inv_mk, inv_fwdVector, inv_bwdVector, getElem_mk]

theorem getElem_castOfFixLT_inv (him : i < m) :
    (a.castOfFixLT ham)⁻¹[i] = if hin : i < n then a⁻¹[i] else i := by
  simp_rw [castOfSmulLtOfLt_inv, getElem_castOfFixLT]

theorem castOfFixLT_eq_cast (hnm : n = m) :
    a.castOfFixLT ham = a.cast hnm := by
  ext _ hi
  simp_rw [getElem_castOfFixLT, getElem_cast, hnm ▸ hi, dite_true]

theorem castOfFixLT_eq_castGE (hnm : n ≤ m) :
    a.castOfFixLT ham = a.castGE hnm := by
  ext _ hi
  simp_rw [getElem_castOfFixLT, getElem_castGE]

theorem castOfFixLT_eq_castLT (hmn : m ≤ n) :
    a.castOfFixLT ham = a.castLE hmn ham := by
  ext _ hi
  simp_rw [getElem_castOfFixLT, getElem_castLE, hi.trans_le hmn, dite_true]

@[simp]
theorem castOfFixLT_one : ((1 : VectorPerm n).castOfFixLT fixLT_one) = (1 : VectorPerm m) := by
  ext i hi : 1
  simp_rw [getElem_castOfFixLT, getElem_one, dite_eq_ite, ite_self]

@[simp]
theorem castOfFixLT_mul {a b : VectorPerm n} (ham : a.FixLT m) (hbm : b.FixLT m)
    (habm := FixLT.mul ham hbm) :
    (a * b).castOfFixLT habm = a.castOfFixLT ham * b.castOfFixLT hbm := by
  ext i
  simp only [getElem_mul, getElem_castOfFixLT]
  rcases lt_or_le i n with hi | hi
  · simp only [hi, dite_true, getElem_lt]
  · simp only [hi.not_lt, dite_false]

theorem fixLT_castOfFixLT {a : VectorPerm n} {ha : a.FixLT m} :
    (a.castOfFixLT ha).FixLT n := fixLT_of_lt_imp_getElem_lt <| fun hi _ => by
  simp_rw [getElem_castOfFixLT, hi, dite_true, getElem_lt]

theorem FixLT.castOfFixLT_of_le {a : VectorPerm n} {ham : a.FixLT m} (hnm : n ≤ m) :
    (a.castOfFixLT ham).castOfFixLT fixLT_castOfFixLT = a := ext <| fun {i} hin => by
  simp_rw [getElem_castOfFixLT, dite_eq_ite, hin, dite_true, ite_eq_left_iff, not_lt]
  intro him
  exact (hnm.not_lt (him.trans_lt hin)).elim

theorem castOfFixLT_surjective_of_le (hmn : m ≤ n) {b : VectorPerm m} (hbm : b.FixLT n) :
    ∃ (a : VectorPerm n), ∃ (han : a.FixLT m), a.castOfFixLT han = b :=
  ⟨_, _, hbm.castOfFixLT_of_le hmn⟩

theorem castOfFixLT_inj_of_ge {a b : VectorPerm n} (hnm : n ≤ m) :
    a.castOfFixLT (a.fixLT_ge hnm) = b.castOfFixLT (b.fixLT_ge hnm) ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [VectorPerm.ext_iff, getElem_castOfFixLT]
  refine fun H _ hi => ?_
  specialize H (hi.trans_le hnm)
  simp_rw [hi, dite_true] at H
  exact H

theorem castOfFixLT_injective_of_ge (hnm : n ≤ m) :
    Function.Injective (fun (a : VectorPerm n) => a.castOfFixLT (a.fixLT_ge hnm)) :=
  fun _ _ => (castOfFixLT_inj_of_ge hnm).mp

theorem castOfFixLT_bijective_of_eq (hmn : m = n) :
    Function.Bijective (fun (a : VectorPerm n) =>
    (a.castOfFixLT (hmn ▸ a.fixLT_eq) : VectorPerm m)) :=
  ⟨castOfFixLT_injective_of_ge hmn.ge,
    fun b => ⟨_, (hmn ▸ b.fixLT_eq : b.FixLT n).castOfFixLT_of_le hmn.le⟩⟩

@[simps! apply_coe]
def castOfFixLTMonoidHom (n m : ℕ) : fixLTSubgroup n m →* fixLTSubgroup m n where
  toFun a := ⟨a.1.castOfFixLT a.2, fixLT_castOfFixLT⟩
  map_one' := Subtype.ext castOfFixLT_one
  map_mul' a b := Subtype.ext (castOfFixLT_mul a.2 b.2)

theorem castOfFixLTMonoidHom_surjective_of_le (hmn : m ≤ n) :
    Surjective (castOfFixLTMonoidHom n m) := fun b => by
  simp_rw [Subtype.exists, mem_fixLTSubgroup_iff, Subtype.ext_iff]
  exact castOfFixLT_surjective_of_le hmn b.2

theorem castOfFixLTMonoidHom_injective_of_ge (hnm : n ≤ m) :
    Injective (castOfFixLTMonoidHom n m) := fun a b => by
  simp_rw [Subtype.ext_iff, castOfFixLTMonoidHom_apply_coe,
    castOfFixLT_inj_of_ge hnm, imp_self]

theorem castOfFixLTMonoidHom_bijective_of_eq (hmn : m = n) :
    Bijective (castOfFixLTMonoidHom n m) :=
  ⟨castOfFixLTMonoidHom_injective_of_ge hmn.ge, castOfFixLTMonoidHom_surjective_of_le hmn.le⟩

@[simps! apply_coe symm_apply_coe]
def castOfFixLTMulEquivEq (hmn : m = n) : fixLTSubgroup n m ≃* fixLTSubgroup m n where
  toFun := castOfFixLTMonoidHom n m
  invFun := castOfFixLTMonoidHom m n
  left_inv a := Subtype.ext <| by
    simp_rw [castOfFixLTMonoidHom_apply_coe]
    exact FixLT.castOfFixLT_of_le hmn.ge
  right_inv a := Subtype.ext <| by
    simp_rw [castOfFixLTMonoidHom_apply_coe]
    exact FixLT.castOfFixLT_of_le hmn.le
  map_mul' a b := map_mul _ _ _

theorem castOfFixLT_smul_eq_smul_of_lt {i : ℕ} (hi : i < m) :
    (a.castOfFixLT ham) • i = a • i := by
  simp_rw [smul_of_lt _ hi, getElem_castOfFixLT]
  rcases lt_or_le i n with hin | hin
  · simp_rw [hin, dite_true, smul_of_lt _ hin]
  · simp_rw [hin.not_lt, dite_false, smul_of_ge _ hin]

end CastOfFixLT

/--
For `a` an `VectorPerm n`, `a.swap i j hi hj` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : VectorPerm n) (i j : ℕ) (hi : i < n) (hj : j < n) : VectorPerm n where
  fwdVector := a.fwdVector.swap i j
  bwdVector := a.bwdVector.map (fun k => Equiv.swap i j k)
  getElem_fwdVector_lt := fun _ => by
    simp_rw [Vector.getElem_swap_eq_getElem_swap_apply, getElem_fwdVector, getElem_lt]
  getElem_bwdVector_getElem_fwdVector := fun _ => by
    simp_rw [Vector.getElem_map, getElem_bwdVector, Vector.getElem_swap_eq_getElem_swap_apply,
      getElem_fwdVector, getElem_inv_getElem, swap_apply_self]

variable (i j k : ℕ) (hi : i < n) (hj : j < n)

@[simp]
theorem getElem_swap (a : VectorPerm n) (hk : k < n) :
    (a.swap i j hi hj)[k] = a[Equiv.swap i j k]'(swap_prop (· < n) hk hi hj) :=
  Vector.getElem_swap_eq_getElem_swap_apply _ _ _ hi hj _ _

@[simp]
theorem getElem_inv_swap (a : VectorPerm n) (hk : k < n) :
    (a.swap i j hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.bwdVector.getElem_map _ _

theorem swap_smul_eq_smul_swap (a : VectorPerm n) :
    (a.swap i j hi hj) • k = a • (Equiv.swap i j k) := by
  rcases lt_or_ge k n with hk | hk
  · simp_rw [smul_of_lt _ (swap_prop (· < n) hk hi hj), smul_of_lt _ hk, getElem_swap]
  · simp_rw [Equiv.swap_apply_of_ne_of_ne (hk.trans_lt' hi).ne' (hk.trans_lt' hj).ne',
      smul_of_ge _ hk]

theorem swap_inv_eq_swap_apply_inv_smul (a : VectorPerm n) :
  (a.swap i j hi hj)⁻¹ • k = Equiv.swap i j (a⁻¹ • k) := by
  simp_rw [inv_smul_eq_iff, swap_smul_eq_smul_swap,
  ← swap_smul, smul_inv_smul, swap_apply_self]

theorem swap_smul_eq_swap_apply_smul (a : VectorPerm n) :
    (a.swap i j hi hj) • k = Equiv.swap (a • i) (a • j) (a • k) := by
  rw [swap_smul, swap_smul_eq_smul_swap]

theorem swap_inv_smul_eq_inv_smul_swap (a : VectorPerm n) : (a.swap i j hi hj)⁻¹ • k =
    a⁻¹ • (Equiv.swap (a • i) (a • j) k) := by
  simp_rw [swap_inv_eq_swap_apply_inv_smul, ← Equiv.swap_smul, inv_smul_smul]

theorem swap_smul_left (a : VectorPerm n) :
    (a.swap i j hi hj) • i = a • j := by rw [swap_smul_eq_smul_swap, swap_apply_left]

theorem swap_smul_right (a : VectorPerm n) :
  (a.swap i j hi hj) • j = a • i := by rw [swap_smul_eq_smul_swap, swap_apply_right]

theorem swap_smul_of_ne_of_ne (a : VectorPerm n) {k} :
  k ≠ i → k ≠ j → (a.swap i j hi hj) • k = a • k := by
  rw [swap_smul_eq_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

theorem swap_inv_smul_left (a : VectorPerm n) :
    (a.swap i j hi hj)⁻¹ • (a • i) = j := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_left, inv_smul_smul]

theorem swap_inv_smul_right (a : VectorPerm n) :
    (a.swap i j hi hj)⁻¹ • (a • j) = i := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_right, inv_smul_smul]

theorem swap_inv_smul_of_ne_of_ne (a : VectorPerm n) {k} :
  k ≠ a • i → k ≠ a • j → (a.swap i j hi hj)⁻¹ • k = a⁻¹ • k := by
  rw [swap_inv_smul_eq_inv_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (a : VectorPerm n) (i : ℕ) (hi hi' : i < n) : a.swap i i hi hi' = a := by
  ext : 1
  simp_rw [getElem_swap, Equiv.swap_self, Equiv.refl_apply]

@[simp]
theorem swap_swap (a : VectorPerm n) (i j : ℕ) (hi hi' : i < n) (hj hj' : j < n) :
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

theorem swap_eq_mul_one_swap (a : VectorPerm n) : a.swap i j hi hj = a * swap 1 i j hi hj := by
  ext : 1
  simp only [getElem_swap, getElem_mul, getElem_one]

theorem swap_eq_one_swap_mul (a : VectorPerm n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    a.swap i j hi hj = swap 1 _ _ hi' hj' * a := by
  rw [eq_iff_smul_eq_smul_lt]
  simp_rw [mul_smul, one_swap_smul, swap_smul_eq_smul_swap, swap_smul, implies_true]

theorem swap_inv_eq_one_swap_mul (a : VectorPerm n) :
    (a.swap i j hi hj)⁻¹ = swap 1 i j hi hj * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (a : VectorPerm n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    (a.swap i j hi hj)⁻¹ = a⁻¹ * swap 1 _ _ hi' hj' := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

theorem natPerm_swap (a : VectorPerm n) :
    natPerm n (swap a i j hi hj) = natPerm n a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, natPerm_apply_apply, swap_smul_eq_smul_swap]

@[simp]
theorem natPerm_one_swap  :
    natPerm n (swap 1 i j hi hj) = Equiv.swap i j := by simp_rw [natPerm_swap, map_one, one_mul]

end VectorPerm
