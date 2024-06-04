import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.Indexes

set_option autoImplicit false

structure ArrayPerm (n : ℕ) where
  toArray : Array (Fin n)
  invArray : Array (Fin n)
  sizeTo : toArray.size = n := by rfl
  sizeInv : invArray.size = n := by rfl
  left_inv' : ∀ i : Fin n, invArray[(toArray[(i : ℕ)] : ℕ)] = i := by decide

namespace ArrayPerm

open Function Fin Equiv List Array

variable {n : ℕ}

theorem toArray_size_eq_invArray_size (a : ArrayPerm n) :
    a.toArray.size = a.invArray.size := a.sizeTo.trans a.sizeInv.symm

theorem lt_of_lt_toArray_size {a : ArrayPerm n} {i : ℕ} (h : i < a.toArray.size) :
    i < n := a.sizeTo.trans_gt h

theorem coe_lt_toArray_size (a : ArrayPerm n) {i : Fin n} :
  i < a.toArray.size := i.val_lt_of_le a.sizeTo.ge

theorem lt_of_lt_invArray_size {a : ArrayPerm n} {i : ℕ} (h : i < a.invArray.size) :
  i < n := a.sizeInv.trans_gt h

theorem coe_lt_invArray_size (a : ArrayPerm n) {i : Fin n} :
  i < a.invArray.size := i.val_lt_of_le a.sizeInv.ge

def getAt (a : ArrayPerm n) : Fin n → Fin n :=
  fun i => have := a.sizeTo ; a.toArray[(i : ℕ)]

theorem getAt_def (a : ArrayPerm n) {i : Fin n} :
  a.getAt i = a.toArray[(i : ℕ)]'a.coe_lt_toArray_size := rfl

theorem toArray_get (a : ArrayPerm n) {i : ℕ} (h : i < a.toArray.size) :
  a.toArray[i] = a.getAt ⟨i, lt_of_lt_toArray_size h⟩ := rfl

theorem getAt_eq_iff {a b : ArrayPerm n} : a.getAt = b.getAt ↔ a.toArray = b.toArray := by
  refine' ⟨fun h => (Array.ext _ _ (a.sizeTo.trans b.sizeTo.symm) (fun _ _ _ => by
    simp_rw [toArray_get, h])),
  fun h => funext (fun i => by
    simp_rw [getAt_def, h])⟩

def getInv (a : ArrayPerm n) : Fin n → Fin n :=
  fun i => have := a.sizeInv ; a.invArray[(i : ℕ)]

theorem getInv_def (a : ArrayPerm n) {i : Fin n} :
  a.getInv i = a.invArray[(i : ℕ)]'a.coe_lt_invArray_size := rfl

theorem invArray_get (a : ArrayPerm n) {i : ℕ} (h : i < a.invArray.size) :
  a.invArray[i] = a.getInv ⟨i, lt_of_lt_invArray_size h⟩ := rfl

theorem getInv_eq_iff {a b : ArrayPerm n} : a.getInv = b.getInv ↔ a.invArray = b.invArray := by
  refine' ⟨fun h => (Array.ext _ _ (a.sizeInv.trans b.sizeInv.symm) (fun _ _ _ => by
    simp_rw [invArray_get, h])),
    fun h => funext (fun i => by
      simp_rw [getInv_def, h])⟩

@[simp]
theorem getInv_getAt (a : ArrayPerm n) : ∀ i, a.getInv (a.getAt i) = i := a.left_inv'

@[simp]
theorem invArray_get_getAt (a : ArrayPerm n) {i : Fin n} :
    a.invArray[(a.getAt i : ℕ)]'a.coe_lt_invArray_size = i := a.getInv_getAt _

@[simp]
theorem getInv_toArray_get (a : ArrayPerm n) {i : ℕ} (h : i < a.toArray.size) :
    a.getInv a.toArray[i] = ⟨i, lt_of_lt_toArray_size h⟩ :=
  a.getInv_getAt ⟨i, lt_of_lt_toArray_size h⟩

@[simp]
theorem invArray_get_toArray_get (a : ArrayPerm n) {i : ℕ} (h : i < a.toArray.size) :
    a.invArray[(a.toArray[i] : ℕ)]'a.coe_lt_invArray_size = ⟨i, lt_of_lt_toArray_size h⟩ :=
  a.getInv_toArray_get h

@[simp]
theorem getAt_leftInverse (a : ArrayPerm n) :
    LeftInverse a.getInv a.getAt := a.getInv_getAt

@[simp]
theorem getInv_rightInverse (a : ArrayPerm n) :
    RightInverse a.getAt a.getInv := a.getInv_getAt

@[simp]
theorem getInv_comp_getAt (a : ArrayPerm n) : a.getInv ∘ a.getAt = id :=
  a.getInv_rightInverse.comp_eq_id

@[simp]
theorem getAt_getInv (a : ArrayPerm n) :
    ∀ i, a.getAt (a.getInv i) = i := a.getAt_leftInverse.rightInverse_of_card_le le_rfl

@[simp]
theorem toArray_get_getInv (a : ArrayPerm n) {i : Fin n} :
    a.toArray[(a.getInv i : ℕ)]'a.coe_lt_toArray_size = i := a.getAt_getInv _

@[simp]
theorem getAt_invArray_get (a : ArrayPerm n) {i : ℕ} (h : i < a.invArray.size):
    a.getAt a.invArray[i] = ⟨i, lt_of_lt_invArray_size h⟩ :=
  a.getAt_getInv ⟨_, lt_of_lt_invArray_size h⟩

@[simp]
theorem toArray_get_invArray_get (a : ArrayPerm n) {i : ℕ} (h : i < a.invArray.size) :
    a.toArray[(a.invArray[i] : ℕ)]'a.coe_lt_toArray_size = ⟨i, lt_of_lt_invArray_size h⟩ :=
  a.getAt_invArray_get h

@[simp]
theorem getAt_rightInverse (a : ArrayPerm n) :
    RightInverse a.getInv a.getAt := a.getAt_getInv

@[simp]
theorem getAt_comp_getInv (a : ArrayPerm n) : a.getAt ∘ a.getInv = id :=
  a.getAt_rightInverse.comp_eq_id

@[simp]
theorem getInv_leftInverse (a : ArrayPerm n) :
    LeftInverse a.getAt a.getInv := a.getAt_getInv

theorem getAt_bijective (a : ArrayPerm n) : Bijective a.getAt :=
  ⟨a.getAt_leftInverse.injective, a.getAt_rightInverse.surjective⟩

theorem getInv_bijective (a : ArrayPerm n) : Bijective a.getInv :=
  ⟨a.getInv_leftInverse.injective, a.getInv_rightInverse.surjective⟩

theorem getInv_apply_eq (a : ArrayPerm n) {i j : Fin n} : a.getInv i = j ↔ i = a.getAt j := by
  rw [← a.getAt_leftInverse.injective.eq_iff, getAt_getInv]

theorem getAt_apply_eq (a : ArrayPerm n) {i j : Fin n} : a.getAt i = j ↔ i = a.getInv j := by
  rw [← a.getInv_leftInverse.injective.eq_iff, getInv_getAt]

theorem getInv_apply_ne (a : ArrayPerm n) {i j : Fin n} : a.getInv i ≠ j ↔ i ≠ a.getAt j :=
  a.getInv_apply_eq.not

theorem getAt_apply_ne (a : ArrayPerm n) (i j : Fin n) : a.getAt i ≠ j ↔ i ≠ a.getInv j :=
  a.getAt_apply_eq.not

theorem toArray_injective (a : ArrayPerm n) {i j} (hi : i < a.toArray.size)
    (hj : j < a.toArray.size) (hij : a.toArray[i] = a.toArray[j]) : i = j := by
  rw [← Fin.mk_eq_mk (h := a.sizeTo.trans_gt hi) (h' := a.sizeTo.trans_gt hj)]
  exact a.getAt_bijective.injective hij

theorem toArray_surjective (a : ArrayPerm n) {i} (hi : i < a.invArray.size) :
  ∃ (j : ℕ) (h : j < a.toArray.size), a.toArray[j] = ⟨i, lt_of_lt_invArray_size hi⟩ :=
  ⟨a.invArray[i], a.coe_lt_toArray_size, a.toArray_get_invArray_get _⟩

theorem invArray_injective (a : ArrayPerm n) {i j} (hi : i < a.invArray.size)
    (hj : j < a.invArray.size) (hij : a.invArray[i] = a.invArray[j]) : i = j :=
  (Fin.mk_eq_mk (h := a.sizeInv.trans_gt hi) (h' := a.sizeInv.trans_gt hj)).mp
  (a.getInv_bijective.injective hij)

theorem invArray_surjective (a : ArrayPerm n) {i} (hi : i < a.toArray.size) :
  ∃ (j : ℕ) (h : j < a.invArray.size), a.invArray[j] = ⟨i, lt_of_lt_toArray_size hi⟩ :=
  ⟨a.toArray[i], a.coe_lt_invArray_size, a.invArray_get_toArray_get _⟩

theorem getInv_eq_iff_getAt_eq (a b : ArrayPerm n) : a.getInv = b.getInv ↔ a.getAt = b.getAt :=
  ⟨fun h => a.getInv_leftInverse.eq_rightInverse (h ▸ b.getInv_rightInverse),
  fun h => a.getAt_leftInverse.eq_rightInverse (h ▸ b.getAt_rightInverse)⟩

theorem invArray_eq_iff_toArray_eq (a b : ArrayPerm n) :
    a.invArray = b.invArray ↔ a.toArray = b.toArray := by
  rw [← getInv_eq_iff, getInv_eq_iff_getAt_eq, getAt_eq_iff]

theorem ext'_iff (a b : ArrayPerm n) : a = b ↔ a.toArray = b.toArray := by
  trans (a.toArray = b.toArray ∧ a.invArray = b.invArray)
  · rcases a ; rcases b ; simp_rw [mk.injEq]
  · rw [invArray_eq_iff_toArray_eq, and_self]

theorem ext' (a b : ArrayPerm n) (h : a.toArray = b.toArray) : a = b := by rwa [ext'_iff]

instance : EquivLike (ArrayPerm n) (Fin n) (Fin n) where
  coe a := a.getAt
  inv a := a.getInv
  left_inv a := a.getInv_getAt
  right_inv a := a.getAt_getInv
  coe_injective' _ _ hAt _ := by rwa [ext'_iff, ← getAt_eq_iff]

@[simp]
theorem coeFn_eq_getAt (a : ArrayPerm n) : a = a.getAt := rfl

@[ext]
theorem ext (a b : ArrayPerm n) (h : a.getAt = b.getAt) : a = b := DFunLike.ext' h

theorem ext_iff (a b : ArrayPerm n) : a = b ↔ a.getAt = b.getAt := DFunLike.ext'_iff

instance : One (ArrayPerm n) :=
⟨enum n, enum n, size_enum _, size_enum _, fun h => by simp only [Fin.getElem_fin, getElem_enum]⟩

@[simp]
theorem one_toArray : (1 : ArrayPerm n).toArray = enum n := rfl
@[simp]
theorem one_invArray : (1 : ArrayPerm n).invArray = enum n := rfl
@[simp]
theorem one_getAt : (1 : ArrayPerm n).getAt = id := funext fun _ => by
  simp_rw [id_eq, getAt_def, one_toArray, getElem_enum]
@[simp]
theorem one_getInv : (1 : ArrayPerm n).getInv = id := funext fun _ => by
  simp_rw [id_eq, getInv_def, one_invArray, getElem_enum]

instance : Inv (ArrayPerm n) :=
⟨fun a => ⟨a.invArray, a.toArray, a.sizeInv, a.sizeTo, a.getAt_getInv⟩⟩

@[simp]
theorem inv_toArray (a : ArrayPerm n) : a⁻¹.toArray = a.invArray := rfl
@[simp]
theorem inv_invArray (a : ArrayPerm n) : a⁻¹.invArray = a.toArray := rfl
@[simp]
theorem inv_getAt (a : ArrayPerm n) : a⁻¹.getAt = a.getInv := rfl
@[simp]
theorem inv_getInv (a : ArrayPerm n) : a⁻¹.getInv = a.getAt := rfl

instance : Mul (ArrayPerm n) := ⟨fun a b =>
  ⟨b.toArray.map a.getAt,
    a.invArray.map b.getInv,
    (b.toArray.size_map _).trans b.sizeTo,
    (a.invArray.size_map _).trans a.sizeInv, fun h => by
      simp_rw [Array.getElem_map, invArray_get_getAt, getInv_toArray_get]⟩⟩

@[simp]
theorem mul_toArray (a b : ArrayPerm n) : (a * b).toArray = b.toArray.map a.getAt := rfl
@[simp]
theorem mul_invArray (a b : ArrayPerm n) : (a * b).invArray = a.invArray.map b.getInv := rfl
@[simp]
theorem mul_getAt (a b : ArrayPerm n) : (a * b).getAt = a.getAt ∘ b.getAt := funext fun _ => by
  simp_rw [getAt_def, mul_toArray, comp_apply, Array.getElem_map, getAt_def]
@[simp]
theorem mul_getInv (a b : ArrayPerm n) : (a * b).getInv = b.getInv ∘ a.getInv := funext fun _ => by
  simp_rw [getInv_def, mul_invArray, comp_apply, Array.getElem_map, getInv_def]

theorem coeFn_mul_eq_comp (a b : ArrayPerm n) : (a * b : ArrayPerm n) = a ∘ b := by
  simp_rw [coeFn_eq_getAt, mul_getAt]

@[simp]
theorem coe_mul (a b : ArrayPerm n) : (a * b : ArrayPerm n) = (a : Perm (Fin n)) * b := by
  simp_rw [DFunLike.ext'_iff, Equiv.Perm.coe_mul, EquivLike.coe_coe, coeFn_mul_eq_comp]

instance : Group (ArrayPerm n) where
  mul_assoc f g h := by simp_rw [ext_iff, mul_getAt, comp.assoc]
  one_mul a := by rw [ext_iff, mul_getAt, one_getAt, id_comp]
  mul_one a := by rw [ext_iff, mul_getAt, one_getAt, comp_id]
  mul_left_inv a := by rw [ext_iff, mul_getAt, inv_getAt, getInv_comp_getAt, one_getAt]

def fromPerm (π : Perm (Fin n)) : ArrayPerm n where
  toArray := Array.ofFn π
  invArray := Array.ofFn π.symm
  sizeTo := Array.size_ofFn _
  sizeInv := Array.size_ofFn _
  left_inv' i := by simp_rw [Array.getElem_ofFn, Fin.eta, symm_apply_apply]

@[simp]
theorem fromPerm_toArray (π : Perm (Fin n)) : (fromPerm π).toArray = Array.ofFn π := rfl
@[simp]
theorem fromPerm_invArray (π : Perm (Fin n)) : (fromPerm π).invArray = Array.ofFn π.symm := rfl
@[simp]
theorem fromPerm_getAt (π : Perm (Fin n)) : (fromPerm π).getAt = π := funext fun _ => by
  simp_rw [getAt_def, fromPerm_toArray, Array.getElem_ofFn]
@[simp]
theorem fromPerm_getInv (π : Perm (Fin n)) : (fromPerm π).getInv = π.symm := funext fun _ => by
  simp_rw [getInv_def, fromPerm_invArray, Array.getElem_ofFn]

theorem fromPerm_coe (a : ArrayPerm n) : fromPerm a = a := by
  rw [ext_iff, fromPerm_getAt, EquivLike.coe_coe, coeFn_eq_getAt]

theorem coe_fromPerm (π : Perm (Fin n)) : fromPerm π = π := by
  rw [DFunLike.ext'_iff, EquivLike.coe_coe, coeFn_eq_getAt, fromPerm_getAt]

def mulEquivPerm : ArrayPerm n ≃* Perm (Fin n) where
  toFun := EquivLike.toEquiv
  invFun := fromPerm
  left_inv := fromPerm_coe
  right_inv := coe_fromPerm
  map_mul' := coe_mul

@[simp]
theorem coe_one : ((1 : ArrayPerm n) : Perm (Fin n)) = 1 := mulEquivPerm.map_one

@[simp]
theorem coe_inv (a : ArrayPerm n) : ((a⁻¹ : ArrayPerm n) : Perm (Fin n)) = (a : Perm (Fin n))⁻¹ :=
  mulEquivPerm.map_inv _

@[simp]
theorem fromPerm_one : fromPerm 1 = (1 : ArrayPerm n) := mulEquivPerm.symm.map_one

@[simp]
theorem fromPerm_mul (π ρ : Perm (Fin n)) : fromPerm (π * ρ) = fromPerm π * fromPerm ρ :=
  mulEquivPerm.symm.map_mul _ _

@[simp]
theorem fromPerm_inv (π : Perm (Fin n)) : fromPerm (π⁻¹) = (fromPerm π)⁻¹ :=
  mulEquivPerm.symm.map_inv _

def swap (a : ArrayPerm n) (i j : Fin n) : ArrayPerm n where
  toArray := a.toArray.swap (i.cast a.sizeTo.symm) (j.cast a.sizeTo.symm)
  invArray := a.invArray.swap ((a.getAt i).cast a.sizeInv.symm) ((a.getAt j).cast a.sizeInv.symm)
  sizeTo := (Array.size_swap _ _ _).trans a.sizeTo
  sizeInv := (Array.size_swap _ _ _).trans a.sizeInv
  left_inv' k := by
    simp_rw [a.toArray.get_swap _ _ _ a.coe_lt_toArray_size,
    a.invArray.get_swap _ _ _ a.coe_lt_invArray_size, Fin.getElem_fin, coe_cast, ← getInv_def,
    ← getAt_def, val_eq_val, ← apply_ite (a.getAt), getInv_getAt,
    a.getAt_bijective.injective.eq_iff]
    rcases eq_or_ne k i with rfl | hki
    · simp_rw [if_true, ite_eq_right_iff, imp_self]
    · simp_rw [hki, if_false]
      rcases eq_or_ne k j with rfl | hkj
      · simp_rw [if_true]
      · simp_rw [if_neg hkj, if_neg hki]

@[simp]
theorem swap_toArray (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).toArray =
a.toArray.swap (i.cast a.sizeTo.symm) (j.cast a.sizeTo.symm) := rfl
@[simp]
theorem swap_invArray (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).invArray =
a.invArray.swap ((a.getAt i).cast a.sizeInv.symm) ((a.getAt j).cast a.sizeInv.symm) := rfl

theorem swap_eq_mul_fromPerm_swap (a : ArrayPerm n) (i j : Fin n) :
    a.swap i j = a * fromPerm (Equiv.swap i j) := by
  ext : 2
  simp_rw [mul_getAt, fromPerm_getAt, comp_apply, swap_apply_def, apply_ite (a.getAt),
  getAt_def, swap_toArray, a.toArray.get_swap _ _ _ a.coe_lt_toArray_size, Fin.getElem_fin,
  coe_cast, val_eq_val]

theorem one_swap (i j : Fin n) : (1 : ArrayPerm n).swap i j = fromPerm (Equiv.swap i j) := by
  rw [swap_eq_mul_fromPerm_swap, one_mul]

theorem swap_eq_mul_one_swap (a : ArrayPerm n) (i j : Fin n) :
    a.swap i j = a * (1 : ArrayPerm n).swap i j := by
  rw [swap_eq_mul_fromPerm_swap, one_swap]

theorem swap_getAt (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getAt =
    a.getAt ∘ Equiv.swap i j := by
  rw [swap_eq_mul_fromPerm_swap, mul_getAt, fromPerm_getAt]

@[simp]
theorem swap_getAt_apply_left (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getAt i =
    a.getAt j := by
  rw [swap_getAt, comp_apply, swap_apply_left]

@[simp]
theorem swap_getAt_apply_right (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getAt j =
    a.getAt i := by
  rw [swap_getAt, comp_apply, swap_apply_right]

theorem swap_getAt_apply_of_ne_of_ne (a : ArrayPerm n) (i j : Fin n) {k} :
  k ≠ i → k ≠ j → (a.swap i j).getAt k = a.getAt k := by
  rw [swap_getAt, comp_apply, a.getAt_bijective.injective.eq_iff]
  exact swap_apply_of_ne_of_ne

theorem swap_getInv (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getInv =
    Equiv.swap i j ∘ a.getInv := by
  rw [swap_eq_mul_fromPerm_swap, mul_getInv, fromPerm_getInv, symm_swap]

@[simp]
theorem swap_getInv_apply_left (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getInv (a.getAt i) =
    j := by
  rw [swap_getInv, comp_apply, getInv_getAt, swap_apply_left]

@[simp]
theorem swap_getInv_apply_right (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getInv (a.getAt j) =
    i := by
  rw [swap_getInv, comp_apply, getInv_getAt, swap_apply_right]

theorem swap_getInv_apply_of_ne_of_ne (a : ArrayPerm n) (i j : Fin n) {k} :
  k ≠ a.getAt i → k ≠ a.getAt j → (a.swap i j).getInv k = a.getInv k := by
  simp_rw [swap_getInv, comp_apply, ← a.getInv_apply_ne]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (a : ArrayPerm n) (i : Fin n) : a.swap i i = a := by
  ext : 1
  rw [swap_getAt, Equiv.swap_self, coe_refl, comp_id]

@[simp]
theorem swap_swap (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).swap i j = a := by
  ext : 1
  simp_rw [swap_getAt, comp.assoc, ← Equiv.coe_trans, Equiv.swap_swap, coe_refl, comp_id]

def swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : ArrayPerm n :=
bs.foldl (fun a => uncurry a.swap) a

@[simp]
theorem swaps_empty (a : ArrayPerm n) : a.swaps [] = a := rfl

@[simp]
theorem swaps_singleton (a : ArrayPerm n) (i j : Fin n) : a.swaps [(i, j)] = a.swap i j := rfl

@[simp]
theorem swaps_singleton' (a : ArrayPerm n) (b : Fin n × Fin n) : a.swaps [b] = a.swap b.1 b.2 := rfl

@[simp]
theorem swaps_cons (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (i j : Fin n) :
  a.swaps ((i, j) :: bs) = (a.swap i j).swaps bs := rfl

theorem swaps_cons' (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (b : Fin n × Fin n) :
  a.swaps (b :: bs) = (a.swap b.1 b.2).swaps bs := rfl

theorem swaps_append (a : ArrayPerm n) (bs cs : List (Fin n × Fin n)) :
  a.swaps (bs ++ cs) = (a.swaps bs).swaps cs := by simp_rw [swaps, List.foldl_append]

theorem swaps_concat (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (i j : Fin n) :
  a.swaps (bs.concat (i, j)) = (a.swaps bs).swap i j := by
  rw [List.concat_eq_append, swaps_append, swaps_singleton]

theorem swaps_reverse (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs).swaps (bs.reverse) = a := by
  induction' bs with b bs IH generalizing a
  · rfl
  · rw [swaps_cons, reverse_cons', swaps_concat, IH, swap_swap]

theorem swaps_eq_mul_fromPerm_foldl_swap (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    a.swaps bs = a * fromPerm (bs.foldl (fun π b => π * Equiv.swap b.1 b.2) 1) := by
  induction' bs using list_reverse_induction with b bs IH generalizing a
  · simp_rw [swaps_empty, foldl_nil, fromPerm_one, mul_one]
  · simp_rw [swaps_append, swaps_singleton', (a.swaps b).swap_eq_mul_fromPerm_swap, IH, mul_assoc,
    foldl_append, foldl_cons, foldl_nil, fromPerm_mul]

theorem one_swaps (bs : List (Fin n × Fin n)) :
    (1 : ArrayPerm n).swaps bs = fromPerm (bs.foldl (fun π b => π * Equiv.swap b.1 b.2) 1) := by
  rw [swaps_eq_mul_fromPerm_foldl_swap, one_mul]

theorem swaps_eq_mul_one_swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    a.swaps bs = a * (1 : ArrayPerm n).swaps bs := by
  rw [swaps_eq_mul_fromPerm_foldl_swap, one_swaps]




def condFlipBit (bs : List Bool) (hbs : bs.length = n) : List (Fin n × Fin n) := _

end ArrayPerm
