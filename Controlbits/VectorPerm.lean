import Batteries.Data.Vector.Lemmas
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.GroupTheory.GroupAction.Period

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

@[simp] theorem getElem_cast {n m i : ℕ} (h : n = m) (v : Vector α n) (hi : i < m)  :
  (v.cast h)[i] = v[i]'(h ▸ hi) := rfl

@[simp] theorem getElem_range_lt {n i : ℕ} {hi : i < n} : (range n)[i] < n := getElem_range _ ▸ hi

@[simp]
theorem getElem_zipWith  {n i : ℕ} (hi : i < n) {as : Vector α n} {bs : Vector β n}
    {f : α → β → γ} : (as.zipWith bs f)[i] = f (as[i]) (bs[i]) := by
  cases as ; cases bs ; simp_rw [mk_zipWith_mk, getElem_mk, Array.getElem_zipWith]

theorem getElem_swap {α : Type u_1} (a : Vector α n) (i j : ℕ) {hi : i < n}
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
  protected getElem_fwdVector_lt' :
    ∀ {i : ℕ} (hi : i < n), fwdVector[i] < n := by decide
  protected getElem_bwdVector_lt' :
  ∀ {i : ℕ} (hi : i < n), bwdVector[i] < n := by decide
  protected left_inv' : ∀ {i : ℕ} (hi : i < n),
      bwdVector[fwdVector[i]]'(getElem_fwdVector_lt' hi) = i :=
    by decide

namespace VectorPerm

open Function Fin Equiv List Vector Array

variable {n : ℕ}

instance : Repr (VectorPerm n) where
  reprPrec a _ := repr (a.fwdVector.toArray, a.bwdVector.toArray)

instance : GetElem (VectorPerm n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.fwdVector[i]

section GetElem

@[simp]
theorem getElem_lt {a : VectorPerm n} {i : ℕ} {hi : i < n} : a[i] < n :=
  a.getElem_fwdVector_lt' hi

@[simp]
theorem getElem_fwdVector {a : VectorPerm n} {i : ℕ} {hi : i < n} : a.fwdVector[i] = a[i] := rfl

@[simp]
theorem getElem_mk (a a' : Vector ℕ n) {getl geil geiageta} {i : ℕ} (hi : i < n) :
  (VectorPerm.mk a a' getl geil geiageta)[i] = a[i] := rfl

theorem fwdVector_eq_iff_forall_getElem_eq (a b : VectorPerm n) :
    a.fwdVector = b.fwdVector ↔ ∀ i (hi : i < n), a[i] = b[i] := by
  simp_rw [Vector.ext_iff, getElem_fwdVector]

end GetElem

def ofVector (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : VectorPerm n where
  fwdVector := a
  bwdVector := (Vector.range n).map a.toList.indexOf
  getElem_fwdVector_lt' := hx
  getElem_bwdVector_lt' := fun {i} hi => by
    have H : Surjective (fun (i : Fin n) => Fin.mk a[i.1] (hx i.2)) :=
      Injective.surjective_of_fintype (Equiv.refl (Fin n)) fun _ _ => by
      simp_rw [Fin.mk.injEq, Fin.ext_iff]
      exact ha.getElem_inj_iff.mp
    simp_rw [Surjective, Fin.ext_iff, Fin.forall_iff] at H
    rcases H _ hi with ⟨_, rfl⟩
    simp_rw [Vector.getElem_map, Vector.getElem_range]
    exact (indexOf_lt_length.mpr (List.getElem_mem _)).trans_eq a.length_toList
  left_inv' := fun {i} hi => by
    simp_rw [Vector.getElem_map, Vector.getElem_range]
    exact a.toList.indexOf_getElem ha _ _

section OfVector

@[simp]
theorem getElem_ofVector {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) : (ofVector a hx ha)[i] = a[i] := rfl

end OfVector

instance : One (VectorPerm n) where
  one := {
    fwdVector := range n
    bwdVector := range n
    getElem_fwdVector_lt' := fun _ => getElem_range_lt
    getElem_bwdVector_lt' := fun _ => getElem_range_lt
    left_inv' := fun _ => by simp_rw [Vector.getElem_range]}

section One

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : VectorPerm n)[i] = i := Vector.getElem_range _

end One

instance : Inv (VectorPerm n) where
  inv a := {
    fwdVector := a.bwdVector
    bwdVector := a.fwdVector
    getElem_fwdVector_lt' := a.getElem_bwdVector_lt'
    getElem_bwdVector_lt' := a.getElem_fwdVector_lt'
    left_inv' := fun hi => by
      rw [getElem_fwdVector]
      have H : Injective (fun (i : Fin n) => Fin.mk
      (a.bwdVector[i]) (a.getElem_bwdVector_lt' i.isLt)) :=
        Surjective.injective_of_fintype (Equiv.refl _)
        (fun i => ⟨⟨a[i], getElem_lt⟩, Fin.ext <| a.left_inv' i.isLt⟩)
      unfold Injective at H
      simp_rw [Fin.forall_iff, Fin.ext_iff] at H
      exact H _ getElem_lt _ hi (a.left_inv' <| a.getElem_bwdVector_lt' hi)}

section Inv

@[simp]
theorem getElem_bwdVector {a : VectorPerm n} {i : ℕ} {hi : i < n} :
  a.bwdVector[i] = a⁻¹[i] := rfl

@[simp]
theorem getElem_inv_getElem (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    a⁻¹[a[i]]'getElem_lt = i := a.left_inv' hi

@[simp]
theorem getElem_getElem_inv (a : VectorPerm n) {i : ℕ} (hi : i < n) :
  a[a⁻¹[i]]'getElem_lt = i := (a⁻¹).left_inv' hi

@[simp]
theorem getElem_inv_ofVector {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) : (ofVector a hx ha)⁻¹[i] = a.toList.indexOf i :=
  (Vector.getElem_map _ _ _).trans (by simp_rw [Vector.getElem_range])

@[simp]
theorem getElem_inv_mk (a a' : Vector ℕ n) {getl geil geiageta} {i : ℕ} (hi : i < n) :
  (VectorPerm.mk a a' getl geil geiageta)⁻¹[i] = a'[i] := rfl

theorem getElem_injective (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n)
    (hij : a[i] = a[j]) : i = j := (a.getElem_inv_getElem hi).symm.trans
    (by simp_rw [hij, a.getElem_inv_getElem])

theorem getElem_inj (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff (a : VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i :=
  ⟨a⁻¹[i], getElem_lt, a.getElem_getElem_inv _⟩

theorem eq_getElem_inv_iff (a: VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by
  rw [← (a⁻¹).getElem_inj (getElem_lt) hj, getElem_inv_getElem]

theorem self_eq_getElem_inv_iff (a: VectorPerm n) {i : ℕ} {hi : i < n} : i = a⁻¹[i] ↔ a[i] = i := by
  rw [← (a⁻¹).getElem_inj (getElem_lt) hi, getElem_inv_getElem]

theorem getElem_inv_eq_iff (a: VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by
  rw [← a.getElem_inj (getElem_lt) hj, getElem_getElem_inv]

theorem getElem_inv_eq_self_iff (a : VectorPerm n) {i : ℕ} {hi : i < n} :
    a⁻¹[i] = i ↔ i = a[i] := by
  rw [← a.getElem_inj (getElem_lt) hi, getElem_getElem_inv]

theorem ne_getElem_inv_iff (a: VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := (a.eq_getElem_inv_iff _ _).ne

theorem self_ne_getElem_inv_iff (a: VectorPerm n) {i : ℕ} {hi : i < n} :
    i ≠ a⁻¹[i] ↔ a[i] ≠ i := (a.eq_getElem_inv_iff _ _).ne

theorem getElem_inv_ne_iff (a: VectorPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := (a.getElem_inv_eq_iff _ _).ne

theorem getElem_inv_ne_self_iff (a: VectorPerm n) {i : ℕ} {hi : i < n}:
    a⁻¹[i] ≠ i ↔ i ≠ a[i] := (a.getElem_inv_eq_iff _ _).ne

theorem bwdVector_eq_iff_forall_getElem_eq (a b : VectorPerm n) :
    a.bwdVector = b.bwdVector ↔ ∀ i (hi : i < n), a⁻¹[i] = b⁻¹[i] :=
  fwdVector_eq_iff_forall_getElem_eq a⁻¹ b⁻¹

end Inv

section MemToArray

theorem lt_of_mem_fwdVector_toArray {a : VectorPerm n} {x : ℕ} :
    x ∈ a.fwdVector.toArray → x < n := by
  simp_rw [Array.mem_iff_getElem, Vector.getElem_toArray, getElem_fwdVector,
    Vector.size_toArray, forall_exists_index]
  rintro _ _ ⟨_, rfl⟩
  exact getElem_lt

theorem lt_of_mem_bwdVector_toArray {a : VectorPerm n} {x : ℕ} :
    x ∈ a.bwdVector.toArray → x < n := by
  simp_rw [Array.mem_iff_getElem, Vector.getElem_toArray, getElem_bwdVector,
    Vector.size_toArray, forall_exists_index]
  rintro _ _ ⟨_, rfl⟩
  exact getElem_lt

theorem mem_fwdVector_toArray_of_lt {a : VectorPerm n} {x : ℕ} (hx : x < n) :
    x ∈ a.fwdVector.toArray := by
  simp_rw [Array.mem_iff_getElem, Vector.getElem_toArray, getElem_fwdVector, Vector.size_toArray]
  exact ⟨a⁻¹[x], getElem_lt, a.getElem_getElem_inv _⟩

theorem mem_bwdVector_toArray_of_lt {a : VectorPerm n} {x : ℕ} (hx : x < n) :
    x ∈ a.bwdVector.toArray := by
  simp_rw [Array.mem_iff_getElem, Vector.getElem_toArray, getElem_bwdVector, Vector.size_toArray]
  exact ⟨a[x], getElem_lt, a.getElem_inv_getElem _⟩

@[simp]
theorem mem_fwdVector_toArray_iff_lt {a : VectorPerm n} {x : ℕ} :
    x ∈ a.fwdVector.toArray ↔ x < n :=
  ⟨lt_of_mem_fwdVector_toArray, mem_fwdVector_toArray_of_lt⟩

@[simp]
theorem mem_bwdVector_toArray_iff_lt {a : VectorPerm n} {x : ℕ} :
    x ∈ a.bwdVector.toArray ↔ x < n :=
  ⟨lt_of_mem_bwdVector_toArray, mem_bwdVector_toArray_of_lt⟩

end MemToArray

def finFwdVector (a : VectorPerm n) : Vector (Fin n) n :=
  ⟨a.fwdVector.attach.map fun x => ⟨x.1, lt_of_mem_fwdVector_toArray x.2⟩, by
    simp_rw [size_map, size_attach, Vector.size_toArray]⟩

section FinFwdVector

@[simp]
theorem getElem_finFwdVector {a : VectorPerm n} {x : ℕ} (hx : x < n) :
    a.finFwdVector[x] = ⟨a[x], getElem_lt⟩ := by
  unfold finFwdVector
  simp_rw [Vector.getElem_mk, Array.getElem_map, Array.getElem_attach, Vector.getElem_toArray,
    getElem_fwdVector]

theorem fwdVector_eq_finFwdVector_map_val {a : VectorPerm n} :
    a.fwdVector = a.finFwdVector.map Fin.val := by
  ext
  simp_rw [getElem_fwdVector, Vector.getElem_map, getElem_finFwdVector]

theorem fin_mem_finFwdVector_toArray {a : VectorPerm n} {x : Fin n} :
    x ∈ a.finFwdVector.toArray := by
  simp_rw [Array.mem_iff_getElem, Vector.getElem_toArray, getElem_finFwdVector, Fin.ext_iff,
    Vector.size_toArray]
  exact ⟨a⁻¹[x.1], getElem_lt, a.getElem_getElem_inv _⟩

end FinFwdVector

def finBwdVector (a : VectorPerm n) : Vector (Fin n) n :=
  ⟨a.bwdVector.attach.map fun x => ⟨x.1, lt_of_mem_bwdVector_toArray x.2⟩, by
    simp_rw [size_map, size_attach, Vector.size_toArray]⟩

section FinBwdVector

@[simp]
theorem getElem_finBwdVector {a : VectorPerm n} {x : ℕ} (hx : x < n) :
    a.finBwdVector[x] = ⟨a⁻¹[x], getElem_lt⟩ := by
  unfold finBwdVector
  simp_rw [Vector.getElem_mk, Array.getElem_map, Array.getElem_attach, Vector.getElem_toArray,
    getElem_bwdVector]

theorem bwdVector_eq_finBwdVector_map_val {a : VectorPerm n} :
    a.bwdVector = a.finBwdVector.map Fin.val := by
  ext
  simp_rw [getElem_bwdVector, Vector.getElem_map, getElem_finBwdVector]

theorem fin_mem_finBwdVector_toArray {a : VectorPerm n} {x : Fin n} :
    x ∈ a.finBwdVector.toArray := by
  simp_rw [Array.mem_iff_getElem, Vector.getElem_toArray, getElem_finBwdVector, Fin.ext_iff,
    Vector.size_toArray]
  exact ⟨a[x.1], getElem_lt, a.getElem_inv_getElem _⟩

end FinBwdVector

instance : Mul (VectorPerm n) where
  mul a b := {
    fwdVector := b.finFwdVector.map (fun (i : Fin n) => a[(i : ℕ)])
    bwdVector := a.finBwdVector.map (fun (i : Fin n) => b⁻¹[(i : ℕ)])
    getElem_fwdVector_lt' := fun hi => by
      simp_rw [Vector.getElem_map, getElem_finFwdVector, getElem_lt]
    getElem_bwdVector_lt' := fun hi => by
      simp_rw [Vector.getElem_map, getElem_finBwdVector, getElem_lt]
    left_inv' := fun hi => by
      simp_rw [Vector.getElem_map, getElem_finFwdVector, getElem_finBwdVector, getElem_inv_getElem]}

section Mul

@[simp]
theorem getElem_mul (a b : VectorPerm n) {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]] := by
  refine (Vector.getElem_map _ _ _).trans ?_
  simp_rw [getElem_finFwdVector]

end Mul

@[ext]
theorem ext {a b : VectorPerm n} (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.fwdVector = b.fwdVector ∧ a.bwdVector = b.bwdVector by
    · rcases a ; rcases b ; simp_rw [mk.injEq]
      exact h
  simp_rw [fwdVector_eq_iff_forall_getElem_eq, h,
    bwdVector_eq_iff_forall_getElem_eq, implies_true, true_and]
  refine fun _ _ => a.getElem_injective getElem_lt getElem_lt ?_
  simp_rw [getElem_getElem_inv, h, getElem_getElem_inv]

instance : Group (VectorPerm n) where
  mul_assoc a b c := ext <| fun _ hi => by
    simp_rw [getElem_mul]
  one_mul a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one]
  mul_one a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one]
  inv_mul_cancel a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one, getElem_inv_getElem]

section Group

@[simp]
theorem getElem_pow_add (a : VectorPerm n) {i x y : ℕ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [pow_add, getElem_mul]

@[simp]
theorem getElem_zpow_add (a : VectorPerm n) {i : ℕ} {x y : ℤ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [zpow_add, getElem_mul]

end Group

instance : MulAction (VectorPerm n) (Fin n) where
  smul a i := ⟨a[i.1], getElem_lt⟩
  one_smul _ := Fin.ext <| getElem_one _
  mul_smul _ _ _ := Fin.ext <| getElem_mul _ _ _

section MulAction

@[simp]
theorem val_smul (a : VectorPerm n) {i : Fin n} : (a • i : Fin n) = a[i.1] := rfl

@[simp]
theorem smul_mk (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    (a • (⟨i, hi⟩ : Fin n)) = ⟨a[i], getElem_lt⟩ := Fin.ext a.val_smul

theorem getElem_eq_val_smul_mk (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    a[i] = ↑(a • Fin.mk i hi) := by rw [smul_mk]

theorem smul_right_inj (a : VectorPerm n) {i j : Fin n} : a • i = a • j ↔ i = j := by
  simp_rw [Fin.ext_iff, val_smul, getElem_inj]

end MulAction

instance : FaithfulSMul (VectorPerm n) (Fin n) where
  eq_of_smul_eq_smul := by
    simp_rw [VectorPerm.ext_iff, Fin.ext_iff, Fin.forall_iff, val_smul, imp_self, implies_true]

section FaithfulSMul

theorem eq_iff_smul_eq_smul {a b : VectorPerm n} : a = b ↔ ∀ i : Fin n, a • i = b • i :=
  ⟨fun h _ => h ▸ rfl, eq_of_smul_eq_smul⟩

end FaithfulSMul


open Equiv.Perm in
/--
`VectorPerm n` is equivalent to `Perm (Fin n)`, and this equivalence respects the
multiplication (and, indeed, the scalar action on `Fin n`).
-/
@[simps! apply_apply_val apply_symm_apply_val]
def finPerm (n : ℕ) : VectorPerm n ≃* Perm (Fin n) where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  invFun π := ⟨Vector.ofFn (val ∘ π), Vector.ofFn (val ∘ π.symm),
  fun _ => (Array.getElem_ofFn _ _ _).trans_lt (is_lt _),
  fun _ => (Array.getElem_ofFn _ _ _).trans_lt (is_lt _),
  fun _ => by simp_rw [Vector.getElem_ofFn, comp_apply, Fin.eta, symm_apply_apply]⟩
  left_inv a := VectorPerm.ext <| fun _ _ => by simp_rw [coe_fn_mk, coe_fn_symm_mk, getElem_mk,
    Vector.getElem_ofFn, comp_apply, val_smul]
  right_inv π := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [coe_fn_mk, val_smul, getElem_mk,
    Vector.getElem_ofFn, Fin.eta, comp_apply]
  map_mul' a b := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [mul_inv_rev, Perm.coe_mul,
    comp_apply, coe_fn_mk, val_smul, getElem_mul]

section FinPerm

@[simp]
theorem finPerm_symm_apply_getElem (π : Perm (Fin n)) {i : ℕ} {hi : i < n} :
    ((finPerm n).symm π)[i] = π ⟨i, hi⟩ := by
  unfold finPerm
  simp_rw [MulEquiv.symm_mk, MulEquiv.coe_mk, coe_fn_symm_mk, getElem_mk, Vector.getElem_ofFn,
    comp_apply]

@[simp]
theorem finPerm_symm_apply_getElem_inv (π : Perm (Fin n)) {i : ℕ} {hi : i < n} :
    ((finPerm n).symm π)⁻¹[i] = π⁻¹ ⟨i, hi⟩ := by
  rw [← map_inv, finPerm_symm_apply_getElem]

instance : Fintype (VectorPerm n) := Fintype.ofEquiv (Perm (Fin n)) (finPerm n).symm.toEquiv

instance : Inhabited (VectorPerm n) := Equiv.inhabited (finPerm n).toEquiv

@[simp]
theorem default_eq : (default : VectorPerm n) = 1 := map_one ((finPerm n).symm)

instance : Unique (VectorPerm 0) := Equiv.unique (finPerm 0).toEquiv

instance : Unique (VectorPerm 1) := Equiv.unique (finPerm 1).toEquiv

instance : DecidableEq (VectorPerm n) := Equiv.decidableEq (finPerm n).toEquiv

lemma isOfFinOrder (a : VectorPerm n) : IsOfFinOrder a := isOfFinOrder_of_finite _

lemma orderOf_pos (a : VectorPerm n) : 0 < orderOf a := by
  rw [orderOf_pos_iff]
  exact a.isOfFinOrder

end FinPerm


instance : SMul (VectorPerm n) ℕ where
  smul a i := if h : i < n then a[i]'h else i

theorem smul_nat_eq_dite (a : VectorPerm n) (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i := rfl

theorem smul_of_lt {a : VectorPerm n} {i : ℕ} (h : i < n) : a • i = a[i] := dif_pos h

theorem smul_of_ge {a : VectorPerm n} {i : ℕ} (h : n ≤ i) : a • i = i := dif_neg (not_lt_of_le h)

theorem getElem_eq_smul {a : VectorPerm n} {i : ℕ} (h : i < n) : a[i] = a • i := (dif_pos _).symm

theorem smul_val (a : VectorPerm n) {i : Fin n} :
    a • i.1 = ((a • i) : Fin n) := smul_of_lt _

@[simp]
theorem smul_getElem {a b : VectorPerm n} {i : ℕ} (h : i < n) : a • b[i] = a[b[i]] := smul_of_lt _

theorem smul_eq_iff {a : VectorPerm n} {i j : ℕ} :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by
  rw [smul_nat_eq_dite, dite_eq_iff', not_lt]

theorem eq_smul_iff {a : VectorPerm n} {i j : ℕ} :
    i = a • j ↔ (∀ (hj : j < n), i = a[j]) ∧ (n ≤ j → i = j) := by
  simp_rw [eq_comm (a := i), smul_eq_iff]

theorem smul_eq_self_iff {a : VectorPerm n} {i : ℕ} :
  a • i = i ↔ ∀ (hi : i < n), a[i] = i := dite_eq_right_iff

theorem self_eq_smul_iff {a : VectorPerm n} {i : ℕ} :
    i = a • i ↔ ∀ (hi : i < n), i = a[i] := by
  simp_rw [eq_comm (a := i), smul_eq_self_iff]

instance : MulAction (VectorPerm n) ℕ where
  one_smul k := (lt_or_le k n).by_cases
    (fun hk => smul_of_lt hk ▸ getElem_one _) (fun hk => smul_of_ge hk)
  mul_smul _ _ k := (lt_or_le k n).by_cases
    (fun hk => by simp_rw [smul_of_lt hk, getElem_mul, smul_of_lt getElem_lt])
    (fun hk => by simp_rw [smul_of_ge hk])

theorem smul_eq_smul_same_iff {a b : VectorPerm n} {i : ℕ} :
  a • i = b • i ↔ ∀ (hi : i < n), a[i] = b[i] := by
  simp_rw [← inv_smul_eq_iff, ← mul_smul, smul_eq_self_iff, getElem_mul,
  forall_congr' fun h => b.getElem_inv_eq_iff getElem_lt h]

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
  · simp_rw [h, iff_true, smul_of_lt h, getElem_lt]
  · simp_rw [h.not_lt, iff_false, not_lt, smul_of_ge h, h]

theorem smul_lt_of_lt {a : VectorPerm n} {i : ℕ} (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

theorem lt_of_smul_lt {a : VectorPerm n} {i : ℕ} (h : a • i < n) : i < n := a.smul_lt_iff_lt.mp h

theorem smul_eq_iff_eq_one (a : VectorPerm n) : (∀ i < n, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul_lt, one_smul]

theorem smul_eq_id_iff_eq_one (a : VectorPerm n) : ((a • ·) : Fin n → Fin n) = id ↔ a = 1 := by
  simp_rw [← one_smul_eq_id (VectorPerm n), funext_iff, eq_iff_smul_eq_smul]

theorem smul_nat_eq_iff_eq_one (a : VectorPerm n) : (∀ i : ℕ, a • i = i) ↔ a = 1 := by
  simp_rw [← smul_eq_iff_eq_one, smul_nat_eq_dite, dite_eq_right_iff]
  exact forall₂_congr (fun a ha => ⟨fun h _ => h, fun h => h _⟩)

theorem smul_nat_eq_id_iff_eq_one (a : VectorPerm n) : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [funext_iff, id_eq, smul_nat_eq_iff_eq_one]

theorem fixedBy_of_ge {a : VectorPerm n} {i : ℕ} (h : n ≤ i) :
    i ∈ MulAction.fixedBy ℕ a := by
  rw [MulAction.mem_fixedBy]
  exact smul_of_ge h

theorem Ici_subset_fixedBy {a : VectorPerm n} :
    Set.Ici n ⊆ MulAction.fixedBy ℕ a := fun _ => fixedBy_of_ge

theorem Ici_subset_fixedPoints :
    Set.Ici n ⊆ MulAction.fixedPoints (VectorPerm n) ℕ := fun _ hx _ => smul_of_ge hx

open Pointwise in
theorem Iic_mem_set_fixedBy {a : VectorPerm n} :
    Set.Iio n ∈ MulAction.fixedBy (Set ℕ) a := Set.ext <| fun _ => by
  rw [← inv_inv a]
  simp_rw [Set.mem_inv_smul_set_iff, Set.mem_Iio, smul_lt_iff_lt]

theorem fixedBy_image_val_subset {a : VectorPerm n} :
    (MulAction.fixedBy (Fin n) a).image (Fin.val) ⊆ MulAction.fixedBy ℕ a := fun _ => by
  simp_rw [Set.mem_image, MulAction.mem_fixedBy, forall_exists_index, and_imp,
  Fin.forall_iff, Fin.ext_iff, smul_mk]
  rintro _ h ha rfl
  exact (smul_of_lt h).trans ha


theorem period_eq_one_of_ge {a : VectorPerm n} {i : ℕ} (hi : n ≤ i) : MulAction.period a i = 1 := by
  simp_rw [MulAction.period_eq_one_iff, smul_of_ge hi]

theorem period_eq_one_iff (a : VectorPerm n) {i : ℕ} :
    MulAction.period a i = 1 ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [MulAction.period_eq_one_iff]
  rcases lt_or_le i n with hi | hi
  · simp_rw [hi, forall_true_left, smul_of_lt hi]
  · simp_rw [hi.not_lt, forall_false, iff_true, smul_of_ge hi]

@[simp]
theorem getElem_pow_period {a : VectorPerm n} {i : ℕ} {hi : i < n} :
    (a ^ MulAction.period a i)[i] = i := by
  rw [← smul_of_lt hi, MulAction.pow_period_smul]

theorem getElem_pow_mod_period {a : VectorPerm n} {i : ℕ} {hi : i < n} (k : ℕ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt hi, MulAction.pow_mod_period_smul]

theorem getElem_zpow_mod_period {a : VectorPerm n} {i : ℕ} {hi : i < n} (k : ℤ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt hi, MulAction.zpow_mod_period_smul]

theorem period_ℕ_pos (a : VectorPerm n) {i : ℕ} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_pos (a : VectorPerm n) {i : Fin n} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_fin {a : VectorPerm n} {i : Fin n} :
    MulAction.period a i = MulAction.period a (i : ℕ) := by
  rw [le_antisymm_iff]
  refine ⟨MulAction.period_le_of_fixed (period_ℕ_pos _) (Fin.ext ?_),
    MulAction.period_le_of_fixed (period_pos _) ?_⟩
  · simp_rw [val_smul, getElem_pow_period]
  · simp_rw [smul_val, MulAction.pow_period_smul]

@[simp]
theorem period_mk {a : VectorPerm n} {i : ℕ} {hi : i < n} :
    MulAction.period a (Fin.mk i hi) = MulAction.period a i := period_fin

theorem period_eq_one_of_zero (a : VectorPerm 0) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_eq_one_of_one (a : VectorPerm 1) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_le_card_of_getElem_pow_mem (a : VectorPerm n) {i : ℕ} (hi : i < n)
  (s : Finset ℕ) : (∀ k < s.card + 1, (a ^ k)[i] ∈ s) → MulAction.period a i ≤ s.card := by
  simp_rw [← smul_of_lt hi]
  exact MulAction.period_le_card_of_smul_pow_mem _ _

theorem getElem_injOn_range_period (a : VectorPerm n) {i : ℕ} (hi : i < n) :
    Set.InjOn (fun k => (a ^ k)[i]) (Finset.range (MulAction.period a i)) := by
  simp_rw [← smul_of_lt hi]
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
  ⟨MulAction.period a i, a.period_ℕ_pos, a.period_le_of_lt hi, getElem_pow_period⟩

/--
`ofPerm` maps a member of `Perm ℕ` which maps the subtype `< n` to itself to the corresponding
`VectorPerm n`.
-/
def ofPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) : VectorPerm n where
  fwdVector := (Vector.range n).map f
  bwdVector := (Vector.range n).map ⇑f⁻¹
  getElem_fwdVector_lt' := fun {i} => by
    simp_rw [Vector.getElem_map, Vector.getElem_range, hf, imp_self]
  getElem_bwdVector_lt' := fun {i} => by
    simp_rw [Vector.getElem_map, Vector.getElem_range,
    (hf (f⁻¹ i)).symm, Perm.apply_inv_self, imp_self]
  left_inv' := by
    simp only [Vector.getElem_map, Vector.getElem_range, Perm.inv_apply_self, implies_true]

section OfPerm

@[simp]
theorem getElem_ofPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {i : ℕ}
    {hi : i < n} : (ofPerm f hf)[i] = f i := by
  unfold ofPerm
  simp_rw [getElem_mk, Vector.getElem_map, Vector.getElem_range]

@[simp]
theorem getElem_inv_ofPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {i : ℕ} {hi : i < n} :
    (ofPerm f hf)⁻¹[i] = f⁻¹ i := by
  unfold ofPerm
  simp_rw [getElem_inv_mk, Vector.getElem_map, Vector.getElem_range]

@[simp]
theorem inv_ofPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} :
    (ofPerm f hf)⁻¹ =
    ofPerm f⁻¹ (fun x => (hf (f⁻¹ x)).symm.trans (Perm.apply_inv_self _ _ ▸ Iff.rfl)) := rfl

@[simp]
theorem mul_ofPerm {f g : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {hg : ∀ i, g i < n ↔ i < n} :
    (ofPerm f hf) * (ofPerm g hg) =
    ofPerm (f * g) (fun x => (hf (g x)).trans (hg x)) := by
  simp only [VectorPerm.ext_iff, getElem_mul, getElem_ofPerm, Perm.mul_apply, implies_true]

end OfPerm

/--
`natPerm` is the injective monoid homomorphism from `VectorPerm n` to `Perm ℕ`.
-/

def natPerm (n : ℕ) : VectorPerm n →* Perm ℕ :=
  (Perm.extendDomainHom equivSubtype).comp (finPerm n : VectorPerm _ →* Equiv.Perm (Fin n))

section NatPerm

@[simp]
theorem natPerm_apply_apply (a : VectorPerm n) {i : ℕ} : natPerm n a i = a • i := by
  unfold natPerm
  simp_rw [MonoidHom.comp_apply, MonoidHom.coe_coe, Perm.extendDomainHom_apply]
  rcases lt_or_le i n with hi | hi
  · simp_rw [Perm.extendDomain_apply_subtype _ equivSubtype hi, smul_of_lt hi,
      equivSubtype_symm_apply, equivSubtype_apply, finPerm_apply_apply_val]
  · simp_rw [Perm.extendDomain_apply_not_subtype _ equivSubtype hi.not_lt, smul_of_ge hi]

@[simp]
theorem natPerm_apply_symm_apply (a : VectorPerm n) {i : ℕ} : (natPerm n a).symm i = a⁻¹ • i := by
  rw [← Perm.inv_def, ← map_inv, natPerm_apply_apply]

@[simp]
theorem natPerm_lt_iff_lt (a : VectorPerm n) {i : ℕ} : natPerm n a i < n ↔ i < n := by
  rw [natPerm_apply_apply, smul_lt_iff_lt]

theorem natPerm_apply_apply_of_lt (a : VectorPerm n) {i : ℕ} (h : i < n) :
    natPerm n a i = a[i] := by rw [natPerm_apply_apply, smul_of_lt h]

theorem natPerm_apply_apply_of_ge (a : VectorPerm n) {i : ℕ} (h : n ≤ i) : natPerm n a i = i := by
  rw [natPerm_apply_apply, smul_of_ge h]

theorem natPerm_apply_symm_apply_of_lt (a : VectorPerm n) {i : ℕ} (h : i < n) :
    (natPerm n a)⁻¹ i = a⁻¹[i] := by
  simp_rw [← MonoidHom.map_inv, natPerm_apply_apply_of_lt _ h]

theorem natPerm_apply_symm_apply_of_ge (a : VectorPerm n) {i : ℕ} (h : n ≤ i) :
    (natPerm n a)⁻¹ i = i := by rw [← MonoidHom.map_inv, natPerm_apply_apply_of_ge _ h]

theorem natPerm_injective : Function.Injective (natPerm n) :=
  (Equiv.Perm.extendDomainHom_injective equivSubtype).comp (finPerm n).injective

theorem natPerm_inj {a b : VectorPerm n} : natPerm n a = natPerm n b ↔ a = b :=
  natPerm_injective.eq_iff

theorem natPerm_ofPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) (i : ℕ) :
    natPerm n (ofPerm f hf) i = if i < n then f i else i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [natPerm_apply_apply_of_lt _ hi, getElem_ofPerm, hi, if_true]
  · simp_rw [natPerm_apply_apply_of_ge _ hi, hi.not_lt, if_false]

theorem ofPerm_natPerm (a : VectorPerm n) :
    ofPerm (natPerm n a) (fun _ => a.natPerm_lt_iff_lt) = a := by
  ext i hi
  simp_rw [getElem_ofPerm, a.natPerm_apply_apply_of_lt hi]

theorem apply_eq_of_ge_iff_exists_natPerm_apply (e : Perm ℕ) :
    (∀ i ≥ n, e i = i) ↔ ∃ a : VectorPerm n, natPerm n a = e := by
  refine ⟨fun h => ?_, ?_⟩
  · have H : ∀ i, e i < n ↔ i < n := fun i => by
      simp_rw [← not_le, not_iff_not]
      exact ⟨fun hi => by rwa [e.injective (h _ hi).symm], fun hi => (h _ hi).symm ▸ hi⟩
    use ofPerm e H
    simp_rw [Equiv.ext_iff, natPerm_ofPerm e H, ite_eq_left_iff, not_lt]
    exact fun _ hi => (h _ hi).symm
  · rintro ⟨a, rfl⟩ i hi
    exact a.natPerm_apply_apply_of_ge hi

theorem coe_natPerm_range : MonoidHom.range (natPerm (n := n)) =
    {e : Perm ℕ | ∀ i ≥ n, e i = i} := by
  simp_rw [Set.ext_iff, MonoidHom.coe_range, Set.mem_range, ge_iff_le, Set.mem_setOf_eq,
  apply_eq_of_ge_iff_exists_natPerm_apply, implies_true]

end NatPerm

def onIndices (a : VectorPerm n) (as : Array α) (has : n ≤ as.size) : Array α :=
    as.mapFinIdx (fun i _ => if hi : i < n then as[a[i]]'
      ((getElem_lt (hi := hi) (a := a)).trans_le has) else as[i])

section OnIndices

variable {α : Type*}

@[simp]
theorem size_onIndices {a : VectorPerm n} {as : Array α} {has : n ≤ as.size} :
    size (a.onIndices as has) = as.size := size_mapFinIdx _ _

@[simp]
theorem getElem_onIndices {a : VectorPerm n} {as : Array α} {has : n ≤ as.size} {i : ℕ}
    {hi : i < (a.onIndices as has).size} :
    (a.onIndices as has)[i] =
    if h : i < n then as[a[i]]'(getElem_lt.trans_le has) else as[i]'(hi.trans_eq size_onIndices) :=
  Array.getElem_mapFinIdx _ _ _ _

theorem getElem_onIndices_getElem_inv {a : VectorPerm n} {as : Array α} {has : n ≤ as.size}
    {i : ℕ} {hi : i < n} : (a.onIndices as has)[a⁻¹[i]]'
    (getElem_lt.trans_le <| has.trans_eq size_onIndices.symm) = as[i] := by
  simp_rw [getElem_onIndices, getElem_lt, dite_true, getElem_getElem_inv]

@[simp]
theorem one_onIndices {as : Array α} {has : n ≤ as.size} :
    (1 : VectorPerm n).onIndices as has = as := by
  simp_rw [Array.ext_iff, size_onIndices, getElem_onIndices, getElem_one, dite_eq_right_iff,
    implies_true, and_self]

theorem mul_onIndices {a b : VectorPerm n} {as : Array α} {has : n ≤ as.size} :
    (a * b).onIndices as has = b.onIndices (a.onIndices as has)
    (has.trans_eq size_onIndices.symm) := by
  simp_rw [Array.ext_iff, size_onIndices, getElem_onIndices, getElem_mul,
    getElem_lt, dite_true, true_and]
  intros i _ _
  rcases lt_or_le i n with hin | hin
  · simp_rw [hin, dite_true]
  · simp_rw [hin.not_lt, dite_false]

theorem mem_of_mem_onIndices {a : VectorPerm n} {as : Array α} {has : n ≤ as.size} {x : α}
    (hx : x ∈ a.onIndices as has) : x ∈ as := by
  simp_rw [Array.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_onIndices, size_onIndices] at hx
  rcases hx with ⟨i, hi, hix⟩
  rcases lt_or_le i n with hin | hin
  · simp_rw [hin, dite_true] at hix
    exact ⟨a[i], getElem_lt.trans_le has, hix⟩
  · simp_rw [hin.not_lt, dite_false] at hix
    exact ⟨i, hi, hix⟩

theorem mem_onIndices_of_mem {a : VectorPerm n} {as : Array α} {has : n ≤ as.size} {x : α}
    (hx : x ∈ as) : x ∈ a.onIndices as has := by
  simp_rw [Array.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_onIndices, size_onIndices]
  rcases hx with ⟨i, hi, hix⟩
  rcases lt_or_le i n with hin | hin
  · refine ⟨a⁻¹[i], getElem_lt.trans_le has, ?_⟩
    simp_rw [getElem_lt, dite_true, getElem_getElem_inv, hix]
  · refine ⟨i, hi, ?_⟩
    simp_rw [hin.not_lt, dite_false, hix]

theorem mem_onIndices_iff {a : VectorPerm n} {as : Array α} {has : n ≤ as.size} {x : α} :
    x ∈ a.onIndices as has ↔ x ∈ as := ⟨mem_of_mem_onIndices, mem_onIndices_of_mem⟩

@[simp]
theorem onIndices_range (a : VectorPerm n) :
    a.onIndices (Array.range n) size_range.ge = a.fwdVector.toArray := by
  simp_rw [Array.ext_iff, size_onIndices, size_range, Vector.size_toArray, getElem_onIndices,
    Array.getElem_range, Vector.getElem_toArray, getElem_fwdVector, true_and]
  exact fun _ hin => by simp_rw [hin, dite_true, implies_true]

@[simp]
theorem onIndices_finRange (a : VectorPerm n) :
    a.onIndices (Array.finRange n) size_finRange.ge = a.finFwdVector.toArray := by
  simp_rw [Array.ext_iff, size_onIndices, Vector.size_toArray, getElem_onIndices,
    Array.getElem_finRange, Vector.getElem_toArray,
    getElem_finFwdVector, size_finRange, true_and]
  exact fun _ hin => by simp_rw [hin, dite_true, implies_true]

end OnIndices

def cycleOf (a : VectorPerm n) (x : ℕ) : Finset ℕ :=
  if h : x < n then (Finset.range n).image (fun k => (a ^ k)[x]) else {x}

theorem cycleOf_lt {a : VectorPerm n} {x : ℕ} (hx : x < n) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k)[x]) := by
  unfold cycleOf
  simp_rw [dif_pos hx, Finset.ext_iff, Finset.mem_image, Finset.mem_range]
  refine fun _ => ⟨fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_ℕ_pos,
    by simp_rw [getElem_pow_mod_period, h]⟩, fun ⟨_, hlt, h⟩ =>
    ⟨_, (hlt.trans_le <| a.period_le_of_lt hx), h⟩⟩

theorem cycleOf_ge {a : VectorPerm n} {x : ℕ} (hx : n ≤ x) :
    a.cycleOf x = {x} := dif_neg (not_lt_of_le hx)

theorem card_cycleOf (a : VectorPerm n) (x : ℕ) : (a.cycleOf x).card = MulAction.period a x := by
  rcases lt_or_le x n with hx | hx
  · refine Eq.trans ?_ (Finset.card_range (MulAction.period a x))
    rw [cycleOf_lt hx, Finset.card_image_iff]
    exact getElem_injOn_range_period _ _
  · rw [cycleOf_ge hx, period_eq_one_of_ge hx, Finset.card_singleton]

theorem cycleOf_eq_map_smul_range_period (a : VectorPerm n) (x : ℕ) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k) • x) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleOf_lt hx, smul_of_lt hx]
  · simp_rw [cycleOf_ge hx, smul_of_ge hx, Finset.ext_iff, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range, exists_and_right]
    exact fun _ => ⟨fun h => h ▸ ⟨⟨0, a.period_ℕ_pos⟩, rfl⟩, fun h => h.2.symm⟩

theorem mem_cycleOf_iff_exists_pow_lt_period_smul (a : VectorPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i) • x = y := by
  rw [cycleOf_eq_map_smul_range_period]
  simp_rw [Finset.mem_image, Finset.mem_range]

theorem mem_cycleOf_iff_exists_pow_smul (a : VectorPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_lt_period_smul]
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩,
    fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_ℕ_pos, ?_⟩⟩
  simp_rw [MulAction.pow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_zpow_smul (a : VectorPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_smul]
  refine ⟨fun ⟨_, h⟩ => ⟨_, (zpow_natCast a _).symm ▸ h⟩,
    fun ⟨k, h⟩ => ⟨(k % MulAction.period a x).toNat, ?_⟩⟩
  simp_rw [← zpow_natCast, Int.toNat_of_nonneg
    (Int.emod_nonneg _ ((Nat.cast_ne_zero (R := ℤ)).mpr (a.period_ℕ_pos (i := x)).ne')),
    MulAction.zpow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_getElem_pow_lt_period (a : VectorPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_lt_period_smul, smul_of_lt hx]

theorem mem_cycleOf_iff_exists_getElem_pow (a : VectorPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul, smul_of_lt hx]

theorem mem_cycleOf_iff_exists_getElem_zpow (a : VectorPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul, smul_of_lt hx]

theorem self_mem_cycleOf (a : VectorPerm n) (x : ℕ) : x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨0, by simp only [pow_zero, one_smul]⟩

theorem nonempty_cycleOf {a : VectorPerm n} {x : ℕ} : (a.cycleOf x).Nonempty :=
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
  rw [smul_of_lt hx]

theorem getElem_inv_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) : a⁻¹[x] ∈ a.cycleOf x := by
  convert a.smul_inv_mem_cycleOf x
  rw [smul_of_lt hx]

theorem getElem_pow_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) (k : ℕ):
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_pow_mem_cycleOf x k
  rw [smul_of_lt hx]

theorem getElem_zpow_mem_cycleOf (a : VectorPerm n) {x : ℕ} (hx : x < n) (k : ℤ) :
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_zpow_mem_cycleOf x k
  rw [smul_of_lt hx]

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
    let ⟨ρ, b, hb⟩ := a.CycleMinVectorAux (i + 1)
    let ρ' := ρ ^ 2
    ⟨ρ', b.zipWith (ρ'.onIndices b hb.ge) min,
    by simp_rw [Array.size_zipWith, size_onIndices, min_self, hb]⟩

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
theorem cycleMinAux_snd_val {a : VectorPerm n} {i : ℕ} :
    (a.CycleMinVectorAux i).2 = CycleMinVector a i := rfl

@[simp]
theorem size_cycleMinVector {a : VectorPerm n} {i : ℕ} :
    (a.CycleMinVector i).size = n := (a.CycleMinVectorAux i).2.2

@[simp] theorem getElem_cycleMinVector_zero {a : VectorPerm n} {x : ℕ} (hx : x < n):
  (a.CycleMinVector 0)[x] = x := Vector.getElem_range _

theorem getElem_cycleMinVector_succ {a : VectorPerm n} {i x : ℕ}
    (hx : x < n) :
    (a.CycleMinVector (i + 1))[x] = min ((a.CycleMinVector i)[x])
    ((a.CycleMinVector i)[(a^2^i)[x]]) := by
  rcases i with (_ | i) <;>
  refine (Array.getElem_zipWith _).trans ?_
  · simp_rw [Vector.toArray_range, Nat.reduceAdd, cast_mk, Array.getElem_range,
    Vector.getElem_toArray, getElem_fwdVector, pow_zero, pow_one, getElem_cycleMinVector_zero]
  · simp_rw [getElem_onIndices, cycleMinAux_snd_val, cast_mk, Vector.getElem_toArray,
      cycleMinAux_succ_fst, hx, dite_true, ← pow_mul, ← pow_succ]

@[simp]
theorem getElem_cycleMinVector_lt {a : VectorPerm n} {i : ℕ} {x : ℕ}
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
    rcases (IH (x := (a ^ (2 ^ i))[x]) getElem_lt) with ⟨k', hk', hπk'⟩
    simp_rw [getElem_cycleMinVector_succ, hπk, hπk', getElem_pow_add,
    pow_succ', Nat.two_mul]
    rcases lt_or_le ((a ^ k)[x]) ((a ^ (k' + 2 ^ i))[x]) with hkk' | hkk'
    · rw [min_eq_left hkk'.le]
      exact ⟨k, hk.trans (Nat.lt_add_of_pos_right (Nat.two_pow_pos _)), rfl⟩
    · rw [min_eq_right hkk']
      exact ⟨k' + 2^i, Nat.add_lt_add_right hk' _, rfl⟩

lemma getElem_cycleMinVector_eq_min'_cycleOf (a : VectorPerm n) (i : ℕ) {x : ℕ}
      (hx : x < n) (hai : MulAction.period a x ≤ 2^i) :
      (a.CycleMinVector i)[x] = (a.cycleOf x).min' nonempty_cycleOf := by
  refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ ?_) <;>
  simp_rw [mem_cycleOf_iff_exists_getElem_pow _ hx]
  · simp_rw [forall_exists_index, forall_apply_eq_imp_iff]
    exact getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow _ _ _ hai
  · rcases a.exists_lt_getElem_cycleMin_eq_getElem_pow i (x := x) (by assumption) with ⟨k, _, hk⟩
    exact ⟨_, hk.symm⟩

def CycleMin (a : VectorPerm n) (i : ℕ) (x : ℕ) : ℕ := (a.CycleMinVector i)[x]?.getD x

theorem getElem_cycleMinVector (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] = a.CycleMin i x :=
  (getD_of_lt _ _ _ _).symm

theorem cycleMin_of_lt {a : VectorPerm n} {i x : ℕ} (hx : x < n) :
    a.CycleMin i x = (a.CycleMinVector i)[x] := getD_of_lt _ _ _ _

theorem cycleMin_of_getElem {a b : VectorPerm n} {i x : ℕ} (hx : x < n) :
    a.CycleMin i (b[x]) = (a.CycleMinVector i)[b[x]] :=
  getD_of_lt _ _ _ _

theorem cycleMin_of_ge {a : VectorPerm n} {i x : ℕ} (hx : n ≤ x) :
    a.CycleMin i x = x := getD_of_ge _ _ _ hx

@[simp]
theorem cycleMin_zero {a : VectorPerm n} {x : ℕ} :
  a.CycleMin 0 x = x := if hx : x < n then
    (cycleMin_of_lt hx).trans <| Array.getElem_range _ else cycleMin_of_ge (le_of_not_lt hx)

@[simp]
theorem cycleMin_succ {a : VectorPerm n} {i x : ℕ} :
    a.CycleMin (i + 1) x = min (a.CycleMin i x) (a.CycleMin i (a^2^i • x)) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [smul_of_lt hx, cycleMin_of_lt hx, cycleMin_of_getElem, getElem_cycleMinVector_succ]
  · simp_rw [smul_of_ge hx, cycleMin_of_ge hx, min_self]

@[simp]
theorem cycleMin_lt_iff_lt {a : VectorPerm n} {i : ℕ} {x : ℕ} :
    a.CycleMin i x < n ↔ x < n := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, hx, getElem_cycleMinVector_lt]
  · simp_rw [cycleMin_of_ge hx]

lemma cycleMin_le_smul_pow_lt_two_pow (a : VectorPerm n) {i : ℕ} (x : ℕ) {k : ℕ} (hk : k < 2^i) :
    a.CycleMin i x ≤ (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinVector_le_getElem_pow_lt _ hk
  · simp_rw [cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_pow_smul_of_period_le_two_pow (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) : ∀ k, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow _ _ _ hai _
  · simp_rw [cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_zpow_smul_of_period_le_two_pow  (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow _ _ _ hai _
  · simp_rw [cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_self (a : VectorPerm n) (i : ℕ) {x : ℕ} :
    a.CycleMin i x ≤ x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx]
    exact getElem_cycleMinVector_le_self _ _ _
  · simp_rw [cycleMin_of_ge hx, le_rfl]

lemma exists_lt_cycleMin_eq_smul_pow (a : VectorPerm n) (i : ℕ) {x : ℕ} :
    ∃ k < 2^i, a.CycleMin i x = (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, smul_of_lt hx]
    exact exists_lt_getElem_cycleMin_eq_getElem_pow _ _ _
  · simp_rw [cycleMin_of_ge hx, smul_of_ge hx]
    exact ⟨0, Nat.two_pow_pos _, trivial⟩

lemma cycleMin_eq_min'_cycleOf (a : VectorPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    a.CycleMin i x = (a.cycleOf x).min' nonempty_cycleOf := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx]
    exact getElem_cycleMinVector_eq_min'_cycleOf _ _ _ hai
  · simp_rw [cycleMin_of_ge hx, cycleOf_ge hx]
    exact rfl

section Cast

variable {m : ℕ}

/--
`VectorPerm.cast` re-interprets an `VectorPerm n` as an `VectorPerm m`, where `n = m`.
-/
def cast (h : n = m) (a : VectorPerm n) : VectorPerm m where
  fwdVector := a.fwdVector.cast h
  bwdVector := a.bwdVector.cast h
  getElem_fwdVector_lt' := fun _ => by
    simp_rw [getElem_cast, h.symm, getElem_fwdVector, getElem_lt]
  getElem_bwdVector_lt' := fun _ => by
    simp_rw [getElem_cast, h.symm, getElem_bwdVector, getElem_lt]
  left_inv' :=
    fun hi => a.getElem_inv_getElem (hi.trans_eq h.symm)

@[simp]
theorem getElem_cast (h : n = m) (a : VectorPerm n) {i : ℕ} (hi : i < m):
    (a.cast h)[i] = a[i] := rfl

@[simp]
theorem getElem_inv_cast (h : n = m) (a : VectorPerm n) {i : ℕ} (hi : i < m):
    (a.cast h)⁻¹[i] = a⁻¹[i] := rfl

@[simp]
theorem cast_smul (h : n = m) (a : VectorPerm n) (i : ℕ) :
    (a.cast h) • i = a • i := by simp only [smul_nat_eq_dite, getElem_cast, h]

@[simp]
theorem cast_inv (h : n = m) (a : VectorPerm n) :
    (a.cast h)⁻¹ = a⁻¹.cast h := rfl

@[simp]
theorem cast_mul (h : n = m) (a b : VectorPerm n) :
    (a * b).cast h = a.cast h * b.cast h := ext <| fun _ hi => by
  simp only [smul_of_lt hi, getElem_mul, getElem_cast]

/--
When `n = m`, `VectorPerm n` is multiplicatively equivalent to `VectorPerm m`.
-/

def vectorPermCongr (h : n = m) : VectorPerm n ≃* VectorPerm m where
  toFun := cast h
  invFun := cast h.symm
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := cast_mul h

/-
theorem getElem_fwdVector_append_range_sub (a : VectorPerm n) {i : ℕ}
    {h : i < n} :
    (a.fwdVector ++ (Vector.range (m - n)).map ((· + n)))[i] = a • i := by
  rcases lt_or_le i n with hi | hi
  · rw [Array.getElem_append_left (hi.trans_eq a.size_fwdVector.symm), a.smul_of_lt hi, getElem_fwdVector]
  · simp_rw [Array.getElem_append_right (hi.trans_eq' a.size_fwdVector), size_fwdVector,
    Array.getElem_map, Array.getElem_range, Nat.sub_add_cancel hi, a.smul_of_ge hi]

theorem getElem_bwdVector_append_range_sub (a : VectorPerm n) {i : ℕ}
    {h : i < (a.bwdVector ++ Array.map (fun x => x + n) (Array.range (m - n))).size} :
    haveI := a.size_bwdVector
    (a.bwdVector ++ (Array.range (m - n)).map ((· + n)))[i] = a⁻¹ • i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [Array.getElem_append_left (hi.trans_eq a.size_bwdVector.symm),
    (a⁻¹).smul_of_lt hi, getElem_bwdVector]
  · simp_rw [Array.getElem_append_right (hi.trans_eq' a.size_bwdVector), size_bwdVector,
    Array.getElem_map, Array.getElem_range, Nat.sub_add_cancel hi, (a⁻¹).smul_of_ge hi]

/--
`VectorPerm.castLE` re-interprets an `VectorPerm n` as an `VectorPerm m`, where `n ≤ m`.
-/
def castLE (h : n ≤ m) (a : VectorPerm n) : VectorPerm m where
  fwdVector := (a.fwdVector ++ (Vector.range (m - n)).map ((· + n))).cast (Nat.add_sub_cancel' h)
  bwdVector := (a.bwdVector ++ (Vector.range (m - n)).map ((· + n))).cast (Nat.add_sub_cancel' h)
  getElem_fwdVector_lt' := fun _ => by
    simp_rw [Vector.getElem_cast]
    rw [getElem_fwdVector_append_range_sub, smul_nat_eq_dite]
    split_ifs with hin
    · exact getElem_lt.trans_le h
    · assumption
  getElem_bwdVector_lt' := fun _ => by
    rw [getElem_bwdVector_append_range_sub, smul_nat_eq_dite]
    split_ifs with hin
    · exact getElem_lt.trans_le h
    · assumption
  left_inv' := fun {i} hi => by
    simp_rw [getElem_fwdVector_append_range_sub, getElem_bwdVector_append_range_sub, inv_smul_smul]

@[simp]
theorem getElem_castLE (a : VectorPerm n) (h : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castLE h)[i] = if hi : i < n then a[i] else i := a.getElem_fwdVector_append_range_sub

@[simp]
theorem getElem_inv_castLE (a : VectorPerm n) (h : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castLE h)⁻¹[i] = if hi : i < n then a⁻¹[i] else i := a.getElem_bwdVector_append_range_sub

theorem getElem_castLE_of_lt (a : VectorPerm n) (h : n ≤ m) {i : ℕ} (hi : i < n) :
    (a.castLE h)[i] = a[i] := by simp_rw [getElem_castLE, hi, dite_true]

@[simp]
theorem castLE_smul (a : VectorPerm n) {i : ℕ} {h : n ≤ m} :
    (a.castLE h) • i = a • i := by
  simp_rw [smul_nat_eq_dite, a.getElem_castLE h, dite_eq_ite, ite_eq_left_iff]
  intro hi
  simp_rw [(h.trans (le_of_not_lt hi)).not_lt, dite_false]

@[simp]
theorem castLE_inv (a : VectorPerm n) {h : n ≤ m} :
    (a.castLE h)⁻¹ = a⁻¹.castLE h := rfl

theorem castLE_mul (a b : VectorPerm n) (h : n ≤ m) :
    (a * b).castLE h = a.castLE h * b.castLE h := by
  ext i
  simp only [getElem_castLE, getElem_mul, mul_smul]
  rcases lt_or_le i n with hi | hi
  · simp only [hi, dite_true, getElem_lt]
  · simp only [hi.not_lt, dite_false]

theorem castLE_inj {a b : VectorPerm n} {h : n ≤ m} : castLE h a = castLE h b ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [VectorPerm.ext_iff, getElem_castLE]
  refine fun H _ hi => ?_
  specialize H _ (hi.trans_le h)
  simp_rw [hi, dite_true] at H
  exact H

theorem castLE_injective (h : n ≤ m) : Function.Injective (castLE h) := fun _ _ => castLE_inj.mp

@[simp]
theorem castLE_one {h : n ≤ m} : ((1 : VectorPerm n).castLE h) = 1 := by
  ext i hi : 1
  simp_rw [getElem_castLE, getElem_one, dite_eq_ite, ite_self]


def vectorPermMonoidHom (h : n ≤ m) : VectorPerm n →* VectorPerm m where
  toFun := castLE h
  map_mul' a b := a.castLE_mul b h
  map_one' := castLE_one

theorem vectorPermMonoidHom_injective {h : n ≤ m} :
  (⇑(vectorPermMonoidHom h)).Injective := castLE_injective h

theorem castLE_of_eq (h : n = m) (h' : n ≤ m := h.le) (a : VectorPerm n) :
    a.castLE h' = a.cast h := by
  ext i hi : 1
  simp_rw [getElem_castLE, getElem_cast, hi.trans_eq h.symm, dite_true]
-/

end Cast

/--
For `a` an `VectorPerm n`, `a.swap i j hi hj` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : VectorPerm n) (i j : ℕ) (hi : i < n) (hj : j < n) : VectorPerm n where
  fwdVector := a.fwdVector.swap i j
  bwdVector := a.bwdVector.map (fun k => Equiv.swap i j k)
  getElem_fwdVector_lt' := fun _ => by
    simp_rw [getElem_swap_eq_getElem_swap_apply, getElem_fwdVector, getElem_lt]
  getElem_bwdVector_lt' := fun _ => by
    simp_rw [Vector.getElem_map, getElem_bwdVector]
    exact swap_prop (· < n) getElem_lt hi hj
  left_inv' := fun _ => by
    simp_rw [Vector.getElem_map, getElem_bwdVector, getElem_swap_eq_getElem_swap_apply,
      getElem_fwdVector, getElem_inv_getElem, swap_apply_self]

variable (i j k : ℕ) (hi : i < n) (hj : j < n)

@[simp]
theorem getElem_swap (a : VectorPerm n) (hk : k < n) :
    (a.swap i j hi hj)[k] = a[Equiv.swap i j k]'(swap_prop (· < n) hk hi hj) :=
  getElem_swap_eq_getElem_swap_apply _ _ _ hi hj _ _

@[simp]
theorem getElem_inv_swap (a : VectorPerm n) (hk : k < n) :
    (a.swap i j hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.bwdVector.getElem_map _ _

theorem swap_smul_eq_smul_swap (a : VectorPerm n) :
    (a.swap i j hi hj) • k = a • (Equiv.swap i j k) := by
  rcases lt_or_ge k n with hk | hk
  · simp_rw [smul_of_lt (swap_prop (· < n) hk hi hj), smul_of_lt hk, getElem_swap]
  · simp_rw [Equiv.swap_apply_of_ne_of_ne (hk.trans_lt' hi).ne' (hk.trans_lt' hj).ne',
      smul_of_ge hk]

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
