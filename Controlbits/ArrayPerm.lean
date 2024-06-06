import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.Indexes

set_option autoImplicit false

namespace Fin

@[simp] theorem cast_comp {n m k : ℕ} (h : n = m) (h' : m = k) :
    cast h' ∘ cast h = cast (Eq.trans h h') := rfl

theorem mk_eq_iff_val_eq {n : ℕ} {a : Fin n} {k : ℕ} {hk : k < n} :
    ⟨k, hk⟩ = a ↔ k = (a : Nat) := ext_iff

theorem fst_lt_snd_lt_of_mem_map_val {n : ℕ} (bs : List (Fin n × Fin n)) (b : ℕ × ℕ)
    (hb : b ∈ bs.map fun b => (b.1.val, b.2.val)) : b.1 < n ∧ b.2 < n := by
  rw [List.mem_map] at hb
  rcases hb with ⟨⟨_, _⟩, ⟨_, rfl⟩⟩
  exact ⟨Fin.isLt _, Fin.isLt _⟩

end Fin

namespace Equiv

open List Function

variable {α : Type*} [DecidableEq α]

theorem swap_coe {n : ℕ} {i j k : Fin n} : swap i j k = swap (i : ℕ) (j : ℕ) (k : ℕ) := by
  simp_rw [swap_apply_def, apply_ite (Fin.val), Fin.val_eq_val]

theorem swap_prop (p : α → Prop) {i j k : α} (hk : p k) (hi : p i) (hj : p j) :
    p (swap i j k) := by
  simp_rw [swap_apply_def, apply_ite p, hi, hj, hk, ite_self]

def swaps (bs : List (α × α)) : Perm α := (bs.map fun b => Equiv.swap b.1 b.2).prod

@[simp]
theorem swaps_nil : swaps ([] : List (α × α)) = 1 := rfl

@[simp]
theorem swaps_cons (b : α × α) (bs : List (α × α)) : swaps (b :: bs) = swap b.1 b.2 * swaps bs :=
  prod_cons

theorem swaps_coe {n : ℕ} {bs : List (Fin n × Fin n)} {k : Fin n} :
    swaps bs k = swaps (bs.map fun b => (b.1.val, b.2.val)) k := by
  induction' bs with b bs IH
  · rfl
  · simp_rw [map_cons, swaps_cons, Perm.coe_mul, comp_apply, swap_coe, IH]

theorem swaps_prop (p : α → Prop) [DecidablePred p] {k : α} (bs : List (α × α))
    (hb : ∀ b ∈ bs, p b.1 ∧ p b.2) (hk : p k) : p (swaps bs k) := by
  induction' bs with b bs IH
  · exact hk
  · simp_rw [mem_cons, forall_eq_or_imp] at hb
    rw [swaps_cons]
    exact swap_prop p (IH (hb.2)) hb.1.1 hb.1.2

theorem swaps_singleton (b : α × α) : swaps [b] = swap b.1 b.2 := rfl

@[simp]
theorem swaps_append (bs₁ bs₂: List (α × α)) :
    swaps (bs₁ ++ bs₂) = swaps bs₁ * swaps bs₂ := by
  unfold swaps
  rw [map_append, prod_append]

theorem swaps_mul (bs₁ bs₂ : List (α × α)) :
    swaps bs₁ * swaps bs₂ = swaps (bs₁ ++ bs₂) := (swaps_append _ _).symm

theorem swaps_concat (b : α × α) (bs : List (α × α)) :
    swaps (bs.concat b) = swaps bs * swap b.1 b.2 := by
  rw [concat_eq_append, swaps_append, swaps_singleton]

theorem swaps_reverse (bs : List (α × α)) :
    swaps (reverse bs) = (swaps bs)⁻¹ := by
  unfold swaps
  simp_rw [map_reverse, prod_reverse_noncomm, map_map, comp_def, swap_inv]

theorem swaps_inverse (bs : List (α × α)) :
    (swaps bs)⁻¹ = swaps (reverse bs) := (swaps_reverse _).symm

@[simp]
theorem swaps_reverse_mul_swaps (bs : List (α × α)) :
    swaps (reverse bs) * swaps bs = 1 := by rw [swaps_reverse, mul_left_inv]

@[simp]
theorem swaps_mul_swaps_reverse (bs : List (α × α)) :
    swaps bs * swaps (reverse bs) = 1 := by rw [swaps_reverse, mul_right_inv]

@[simp]
theorem swaps_reverse_apply_swaps_apply (bs : List (α × α)) (a : α):
    swaps (reverse bs) (swaps bs a) = a := by rw [swaps_reverse, Perm.inv_apply_self]

@[simp]
theorem swaps_reverse_apply_swaps_reverse (bs : List (α × α)) (a : α):
    swaps bs (swaps (reverse bs) a) = a := by rw [swaps_reverse, Perm.apply_inv_self]

@[simp]
theorem symm_swaps (bs : List (α × α)) :
    (swaps bs).symm = swaps (reverse bs) := swaps_inverse _

theorem swaps_self_pair (a : α) : swaps [(a, a)] = 1 := by
  rw [swaps_cons, swap_self, swaps_nil, Perm.one_def, Perm.mul_refl]

@[simp]
theorem swaps_self_pairs (as : List α) : swaps (as.zip as) = 1 := by
  induction' as with a as IH
  · rfl
  · rw [zip_cons_cons, swaps_cons, swap_self, Perm.refl_mul, IH]

@[simp]
theorem swaps_comm (bs : List (α × α)) :
    swaps (bs.map Prod.swap) = swaps bs := by
  induction' bs with b bs IH
  · rfl
  · rw [map_cons, swaps_cons, swaps_cons, Prod.fst_swap, Prod.snd_swap, swap_comm, IH]

theorem swaps_mul_eq_mul_swaps (bs : List (α × α)) (π : Perm α) :
    swaps bs * π = π * swaps (bs.map fun b => (π⁻¹ b.1, π⁻¹ b.2)) := by
  induction' bs with b bs IH generalizing π
  · rfl
  · rw [swaps_cons, mul_assoc, IH, ← mul_assoc, swap_mul_eq_mul_swap,
    map_cons, swaps_cons, mul_assoc]

theorem mul_swaps_eq_swaps_mul (bs : List (α × α)) (π : Perm α) :
    π * swaps bs = swaps (bs.map fun b => (π b.1, π b.2)) * π := by
  simp_rw [swaps_mul_eq_mul_swaps, map_map, comp_def, Perm.inv_apply_self,
  Prod.mk.eta, map_id']

theorem swaps_apply_apply (bs : List (α × α)) (π : Perm α) :
    swaps (bs.map fun b => (π b.1, π b.2)) = π * swaps bs * π⁻¹ := by
  rw [mul_swaps_eq_swaps_mul, mul_inv_cancel_right]

end Equiv

namespace Array

open Equiv Function List

variable {α : Type*}

@[simp]
theorem swap_congr (a a' : Array α) {i j : Fin a.size} {i' j' : Fin a'.size}
    (ha : a = a') (hi : (i : ℕ) = i') (hj : (j : ℕ) = j') : a.swap i j = a'.swap i' j' := by
  refine' ext _ _ _ (fun k  hk hk' => _)
  · simp_rw [size_swap, ha]
  · simp_rw [get_swap', getElem_fin, ha, hi, hj]

@[simp]
theorem swap_self (a : Array α) {i : Fin a.size} : a.swap i i = a := by
  refine' ext _ _ (a.size_swap i i) (fun j  _ hj => _)
  simp_rw [a.get_swap i i j hj, getElem_fin]
  rcases eq_or_ne j i with rfl | hji
  · simp_rw [if_true]
  · simp_rw [hji, if_false]

theorem get_swap_eq_get_apply_swap (a : Array α) {i j : Fin a.size} (k : ℕ) (h : k < a.size)
    (h' : k < (a.swap i j).size := (a.size_swap _ _).symm.trans_gt h)
    (h'' : Equiv.swap i.val j.val k < a.size := swap_prop (fun t => t < a.size) h i.isLt j.isLt) :
    (a.swap i j)[k] = a[Equiv.swap i.val j.val k] := by
  simp_rw [get_swap', swap_apply_def]
  split_ifs <;> rfl

theorem get_swap_eq_get_apply_swap' (a : Array α) {i j : Fin a.size} (k : ℕ)
    (h : k < (a.swap i j).size) (h' : k < a.size := (a.size_swap _ _).trans_gt h)
    (h'' : Equiv.swap i.val j.val k < a.size := swap_prop (fun t => t < a.size) h' i.isLt j.isLt) :
    (a.swap i j)[k] = a[Equiv.swap i.val j.val k] :=
  a.get_swap_eq_get_apply_swap _ h'

theorem get_swap_fin (a : Array α) {i j k : Fin a.size}
    (h' : k < (a.swap i j).size := (a.size_swap _ _).symm.trans_gt k.isLt)
    (h'' : Equiv.swap i.val j.val k.val < a.size :=
    swap_prop (fun t => t < a.size) k.isLt i.isLt j.isLt) :
    (a.swap i j)[k] = a[Equiv.swap i.val j.val k] := by
  simp_rw [Fin.getElem_fin, a.get_swap_eq_get_apply_swap']

def swaps (a : Array α) (bs : List (Fin a.size × Fin a.size)) : Array α :=
  match bs with
  | [] => a
  | (b :: bs) => (a.swap b.1 b.2).swaps
    (bs.map (fun b => (b.1.cast (a.size_swap _ _).symm, b.2.cast (a.size_swap _ _).symm)))
    termination_by bs.length

@[simp]
theorem swaps_nil (a : Array α) : a.swaps [] = a := rfl

@[simp]
theorem swaps_cons (a : Array α) (b : Fin a.size × Fin a.size)
    (bs : List (Fin a.size × Fin a.size)) : a.swaps (b :: bs) = (a.swap b.1 b.2).swaps
    (bs.map (fun b => (b.1.cast (a.size_swap _ _).symm, b.2.cast (a.size_swap _ _).symm))) := rfl

theorem swaps_singleton (a : Array α) (b : Fin a.size × Fin a.size) :
  a.swaps [b] = a.swap b.1 b.2 := rfl

@[simp]
theorem size_swaps (a : Array α) (bs : List (Fin a.size × Fin a.size)) :
    (a.swaps bs).size = a.size :=
  match bs with
  | [] => rfl
  | (b :: bs) => by rw [swaps_cons, size_swaps, size_swap]
  termination_by bs.length

theorem swaps_append (a : Array α) (bs₁ bs₂ : List (Fin a.size × Fin a.size)) :
    a.swaps (bs₁ ++ bs₂) = (a.swaps bs₁).swaps
    (bs₂.map (fun b => (b.1.cast (a.size_swaps _).symm, b.2.cast (a.size_swaps _).symm))) :=
  match bs₁ with
  | [] => by simp_rw [List.nil_append, swaps_nil, Fin.cast_eq_self, Prod.mk.eta, map_id']
  | (b₁ :: bs₁) => by
    rw [cons_append, swaps_cons, map_append]
    refine' ((a.swap b₁.1 b₁.2).swaps_append _ _).trans _
    rw [map_map]
    rfl
  termination_by bs₁.length

@[simp]
theorem swaps_concat (a : Array α) (b : Fin a.size × Fin a.size)
    (bs : List (Fin a.size × Fin a.size)) : a.swaps (bs.concat b) =
    (a.swaps bs).swap (b.1.cast (a.size_swaps _).symm) (b.2.cast (a.size_swaps _).symm) := by
  simp only [concat_eq_append, swaps_append, map_cons, map_nil, swaps_cons, swaps_nil]

theorem get_swaps_eq_get_apply_swaps (a : Array α) {bs : List (Fin a.size × Fin a.size)}
    (k : ℕ) (h : k < a.size)
    (h' : k < (a.swaps bs).size := (a.size_swaps _).symm.trans_gt h)
    (h'' : Equiv.swaps (bs.map fun b => (b.1.val, b.2.val)) k < a.size :=
    swaps_prop (fun k => k < a.size) _ (Fin.fst_lt_snd_lt_of_mem_map_val _) h) :
    (a.swaps bs)[k] = a[Equiv.swaps (bs.map fun b => (Fin.val b.1, Fin.val b.2)) k] := by
  induction' bs using list_reverse_induction with bs b IH generalizing k
  · rfl
  · simp_rw [← concat_eq_append, swaps_concat, map_concat, Equiv.swaps_concat,
    (a.swaps bs).get_swap_eq_get_apply_swap', Fin.coe_cast, Perm.coe_mul, comp_apply,
    IH _ (swap_prop (fun t => t < a.size) h (Fin.isLt _) (Fin.isLt _))]

theorem get_swaps_eq_get_apply_swaps' (a : Array α) {bs : List (Fin a.size × Fin a.size)}
    (k : ℕ)
    (h : k < (a.swaps bs).size) (h' : k < a.size := ((size_swaps _ _).trans_gt h))
    (h'' : Equiv.swaps (bs.map fun b => (b.1.val, b.2.val)) k < a.size :=
    swaps_prop (fun k => k < a.size) _ (Fin.fst_lt_snd_lt_of_mem_map_val _) h') :
    (a.swaps bs)[k] = a[Equiv.swaps (bs.map fun b => (Fin.val b.1, Fin.val b.2)) k] :=
 get_swaps_eq_get_apply_swaps _ _ h'

end Array

structure ArrayPerm (n : ℕ) where
  toArray : Array (Fin n)
  invArray : Array (Fin n)
  sizeTo : toArray.size = n := by rfl
  sizeInv : invArray.size = n := by rfl
  left_inv' : ∀ i : Fin n, invArray[toArray[i.val].val] = i := by decide

namespace ArrayPerm

open Function Fin Equiv List Array

variable {n m : ℕ}

instance : Repr (ArrayPerm n) where
  reprPrec a _ := "ArramPerm " ++ repr n ++ " : " ++ repr a.toArray

instance : ToString (ArrayPerm n) where
  toString a := "ArramPerm " ++ toString n ++ " : " ++ toString a.toArray

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

@[simp]
theorem mk_getAt {a b : Array (Fin n)} {sa sb hab} :
  getAt ⟨a, b, sa, sb, hab⟩ = fun i => a[i] := rfl

theorem getAt_def (a : ArrayPerm n) {i : Fin n} :
  a.getAt i = a.toArray[(i : ℕ)]'a.coe_lt_toArray_size := rfl

theorem toArray_get (a : ArrayPerm n) {i : ℕ} (h : i < a.toArray.size) :
  a.toArray[i] = a.getAt ⟨i, lt_of_lt_toArray_size h⟩ := rfl

theorem getAt_eq_iff_toArray_eq {a b : ArrayPerm n} :
    a.getAt = b.getAt ↔ a.toArray = b.toArray :=
  ⟨fun h => Array.ext _ _ (a.sizeTo.trans b.sizeTo.symm)
  (fun _ _ _ => congrFun h ⟨_, a.sizeTo.trans_gt (by assumption)⟩),
  fun h => funext (fun i => by unfold getAt; simp_rw [h])⟩

def getInv (a : ArrayPerm n) : Fin n → Fin n :=
  fun i => have := a.sizeInv ; a.invArray[(i : ℕ)]

@[simp]
theorem mk_getInv {a b : Array (Fin n)} {sa sb hab} :
  getInv ⟨a, b, sa, sb, hab⟩ = fun i => b[i] := rfl

theorem getInv_def (a : ArrayPerm n) {i : Fin n} :
  a.getInv i = a.invArray[(i : ℕ)]'a.coe_lt_invArray_size := rfl

theorem invArray_get (a : ArrayPerm n) {i : ℕ} (h : i < a.invArray.size) :
  a.invArray[i] = a.getInv ⟨i, lt_of_lt_invArray_size h⟩ := rfl

theorem getInv_eq_iff_invArray_eq {a b : ArrayPerm n} :
    a.getInv = b.getInv ↔ a.invArray = b.invArray :=
  ⟨fun h => Array.ext _ _ (a.sizeInv.trans b.sizeInv.symm)
  (fun _ _ _ => congrFun h ⟨_, a.sizeInv.trans_gt (by assumption)⟩),
    fun h => funext (fun i => by unfold getInv; simp_rw [h])⟩

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

def cast (h : n = m) (a : ArrayPerm n) : ArrayPerm m where
  toArray := (a.toArray.map <| Fin.cast h)
  invArray := a.invArray.map <| Fin.cast h
  sizeTo := (a.toArray.size_map _).trans <| a.sizeTo.trans h
  sizeInv := (a.invArray.size_map _).trans <| a.sizeInv.trans h
  left_inv'  i := by
    simp only [getElem_map, coe_cast, invArray_get_toArray_get, cast_mk, Fin.eta]

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

protected def mk' (toArray : Array (Fin n)) (invArray : Array (Fin n))
  (sizeTo : toArray.size = n := by rfl) (sizeInv : invArray.size = n := by rfl)
  (right_inv' : ∀ i : Fin n, toArray[(invArray[(i : ℕ)] : ℕ)] = i := by decide) : ArrayPerm n :=
  {toArray, invArray, sizeTo, sizeInv,
    left_inv' := by
      let A : ArrayPerm n := ⟨invArray, toArray, sizeInv, sizeTo, right_inv'⟩
      exact fun _ => A.toArray_get_invArray_get (A.coe_lt_invArray_size)}

@[simp]
theorem mk'_getAt {a b : Array (Fin n)} {sa sb hab} :
  (ArrayPerm.mk' a b sa sb hab).getAt = fun i => a[i] := rfl

@[simp]
theorem mk'_getInv {a b : Array (Fin n)} {sa sb hab} :
  (ArrayPerm.mk' a b sa sb hab).getInv = fun i => b[i] := rfl

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

theorem getInv_eq_iff_invArray_eq_getAt_eq (a b : ArrayPerm n) :
    a.getInv = b.getInv ↔ a.getAt = b.getAt :=
  ⟨fun h => a.getInv_leftInverse.eq_rightInverse (h ▸ b.getInv_rightInverse),
  fun h => a.getAt_leftInverse.eq_rightInverse (h ▸ b.getAt_rightInverse)⟩

theorem invArray_eq_iff_toArray_eq (a b : ArrayPerm n) :
    a.invArray = b.invArray ↔ a.toArray = b.toArray := by
  rw [← getInv_eq_iff_invArray_eq, getInv_eq_iff_invArray_eq_getAt_eq, getAt_eq_iff_toArray_eq]

theorem ext'_iff (a b : ArrayPerm n) : a = b ↔ a.toArray = b.toArray := by
  trans (a.toArray = b.toArray ∧ a.invArray = b.invArray)
  · rcases a ; rcases b ; simp_rw [mk.injEq]
  · rw [invArray_eq_iff_toArray_eq, and_self]

theorem ext' {a b : ArrayPerm n} (h : a.toArray = b.toArray) : a = b := by rwa [ext'_iff]

theorem ext_iff (a b : ArrayPerm n) : a = b ↔ a.getAt = b.getAt := by
rw [getAt_eq_iff_toArray_eq, ext'_iff]

@[ext]
theorem ext {a b : ArrayPerm n} : a.getAt = b.getAt → a = b := (ext_iff a b).mpr

instance : Mul (ArrayPerm n) := ⟨fun a b =>
  ⟨b.toArray.map a.getAt,
    a.invArray.map b.getInv,
    (b.toArray.size_map _).trans b.sizeTo,
    (a.invArray.size_map _).trans a.sizeInv, fun h => by
      simp_rw [Array.getElem_map, invArray_get_getAt, getInv_toArray_get]⟩⟩

theorem mul_toArray (a b : ArrayPerm n) : (a * b).toArray = b.toArray.map a.getAt := rfl
theorem mul_invArray (a b : ArrayPerm n) : (a * b).invArray = a.invArray.map b.getInv := rfl

@[simp]
theorem mul_getAt (a b : ArrayPerm n) : (a * b).getAt = a.getAt ∘ b.getAt :=
  funext fun _ => Array.getElem_map _ _ _ _

@[simp]
theorem mul_getInv (a b : ArrayPerm n) : (a * b).getInv = b.getInv ∘ a.getInv :=
  funext fun _ => Array.getElem_map _ _ _ _

@[simps! apply_apply apply_symm_apply]
def mulEquivPerm : ArrayPerm n ≃* Perm (Fin n) where
  toFun a := ⟨a.getAt, a.getInv, a.getInv_getAt, a.getAt_getInv⟩
  invFun π := ⟨ofFn π, ofFn π.symm, size_ofFn _, size_ofFn _, fun _ => by
    simp_rw [getElem_ofFn, Fin.eta, symm_apply_apply]⟩
  left_inv a := ext <| by simp only [coe_fn_mk, coe_fn_symm_mk, mk_getAt, Fin.getElem_fin,
    getElem_ofFn, Fin.eta]
  right_inv π := Equiv.ext <| by simp only [mk_getAt, Fin.getElem_fin, getElem_ofFn, Fin.eta,
    mk_getInv, coe_fn_mk, implies_true]
  map_mul' a b := Equiv.ext <| by simp only [mul_getAt, mul_getInv, coe_fn_mk, comp_apply,
    Perm.coe_mul, implies_true]

@[simp]
theorem mulEquivPerm_symm_apply_getAt (π : Equiv.Perm (Fin n)) :
  (mulEquivPerm.symm π).getAt = π := funext fun _ => Array.getElem_ofFn _ _ _

@[simp]
theorem mulEquivPerm_symm_apply_getInv (π : Equiv.Perm (Fin n)) :
  (mulEquivPerm.symm π).getInv = π⁻¹ := funext fun _ => Array.getElem_ofFn _ _ _

instance One : One (ArrayPerm n) :=
⟨enum n, enum n, size_enum _, size_enum _, fun h => by simp only [Fin.getElem_fin, getElem_enum]⟩

theorem one_toArray : (1 : ArrayPerm n).toArray = enum n := rfl
theorem one_invArray : (1 : ArrayPerm n).invArray = enum n := rfl

@[simp]
theorem one_getAt : (1 : ArrayPerm n).getAt = id := funext fun _ => getElem_enum _ _
@[simp]
theorem one_getInv : (1 : ArrayPerm n).getInv = id := funext fun _ => getElem_enum _ _

instance : Inv (ArrayPerm n) :=
⟨fun a => ⟨a.invArray, a.toArray, a.sizeInv, a.sizeTo, a.getAt_getInv⟩⟩

theorem inv_toArray (a : ArrayPerm n) : a⁻¹.toArray = a.invArray := rfl
theorem inv_invArray (a : ArrayPerm n) : a⁻¹.invArray = a.toArray := rfl

@[simp]
theorem inv_getAt (a : ArrayPerm n) : a⁻¹.getAt = a.getInv := rfl
@[simp]
theorem inv_getInv (a : ArrayPerm n) : a⁻¹.getInv = a.getAt := rfl

instance : Group (ArrayPerm n) where
  mul_assoc f g h := by simp_rw [ext_iff, mul_getAt, comp.assoc]
  one_mul a := by rw [ext_iff, mul_getAt, one_getAt, id_comp]
  mul_one a := by rw [ext_iff, mul_getAt, one_getAt, comp_id]
  mul_left_inv a := by rw [ext_iff, mul_getAt, inv_getAt, getInv_comp_getAt, one_getAt]

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

theorem swap_toArray (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).toArray =
a.toArray.swap (i.cast a.sizeTo.symm) (j.cast a.sizeTo.symm) := rfl

theorem swap_invArray (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).invArray =
a.invArray.swap ((a.getAt i).cast a.sizeInv.symm) ((a.getAt j).cast a.sizeInv.symm) := rfl

theorem swap_getAt (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j).getAt = a.getAt ∘ Equiv.swap i j := by
  ext k : 1
  simp_rw [comp_apply, Equiv.swap_apply_def, apply_ite (a.getAt), Fin.ext_iff (a := k)]
  exact a.toArray.get_swap _ _ _ ((sizeTo _).symm.trans_gt k.isLt)

theorem swap_getInv (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getInv =
    a.getInv ∘ Equiv.swap (a.getAt i) (a.getAt j) := by
  ext k : 1
  simp_rw [getInv_apply_eq, swap_getAt, comp_apply, ← mulEquivPerm_apply_apply,
  ← mulEquivPerm_apply_symm_apply, ← Perm.mul_apply, mul_swap_eq_swap_mul (mulEquivPerm a).symm,
  symm_apply_apply, swap_mul_self_mul, Perm.mul_symm, Perm.coe_one, id_eq]

@[simp]
theorem one_swap_getAt (i j : Fin n) : (swap 1 i j).getAt = Equiv.swap i j := by
  rw [swap_getAt, one_getAt, id_comp]

@[simp]
theorem one_swap_getInv (i j : Fin n) : (swap 1 i j).getInv = Equiv.swap i j := by
  ext : 1
  simp_rw [swap_getInv, one_getAt, id_eq, one_getInv, id_comp]

@[simp]
theorem one_swap_mul_self (i j : Fin n) : swap 1 i j * swap 1 i j = 1 := by
  ext : 2
  rw [mul_getAt, one_swap_getAt, comp_apply, swap_apply_self, one_getAt, id_eq]

@[simp]
theorem one_swap_inverse (i j : Fin n) : (swap 1 i j)⁻¹ = swap 1 i j := by
  ext : 1
  rw [inv_getAt, one_swap_getInv, one_swap_getAt]

@[simp]
theorem swap_getAt_apply (a : ArrayPerm n) (i j k : Fin n) :
    (a.swap i j).getAt k = a.getAt (Equiv.swap i j k) := by rw [swap_getAt, comp_apply]

theorem swap_eq_mul_one_swap (a : ArrayPerm n) (i j : Fin n) : a.swap i j = a * swap 1 i j := by
  ext : 2
  simp only [swap_getAt_apply, mul_getAt, one_swap_getAt, comp_apply]

theorem mulEquivPerm_swap (a : ArrayPerm n) (i j : Fin n) :
    mulEquivPerm (swap a i j) = mulEquivPerm a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, mulEquivPerm_apply_apply, swap_getAt_apply]

@[simp]
theorem mulEquivPerm_one_swap (i j : Fin n) :
    mulEquivPerm (swap 1 i j) = Equiv.swap i j := by simp_rw [mulEquivPerm_swap, map_one, one_mul]

theorem swap_eq_one_swap_mul (a : ArrayPerm n) (i j : Fin n) :
    a.swap i j = swap 1 (a.getAt i) (a.getAt j) * a := by
  apply mulEquivPerm.injective
  simp_rw [map_mul, mulEquivPerm_one_swap, mulEquivPerm_swap,
  mul_swap_eq_swap_mul, mulEquivPerm_apply_apply]

theorem swap_getAt' (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j).getAt = Equiv.swap (a.getAt i) (a.getAt j) ∘ a.getAt := by
  rw [swap_eq_one_swap_mul, mul_getAt, one_swap_getAt]

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

theorem swap_inv_eq_one_swap_mul (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j)⁻¹ = swap 1 i j * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j)⁻¹ = a⁻¹ * swap 1 (a.getAt i) (a.getAt j) := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

theorem swap_getInv' (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getInv =
    Equiv.swap i j ∘ a.getInv := by
  rw [swap_eq_mul_one_swap, mul_getInv, one_swap_getInv]

@[simp]
theorem swap_getInv_apply' (a : ArrayPerm n) (i j k : Fin n) :
    (a.swap i j).getInv k = Equiv.swap i j (a.getInv k) := by
  rw [swap_getInv', comp_apply]

@[simp]
theorem swap_getInv_apply (a : ArrayPerm n) (i j k : Fin n) :
    (a.swap i j).getInv k = a.getInv (Equiv.swap (a.getAt i) (a.getAt j) k) := by
  rw [swap_getInv, comp_apply]

@[simp]
theorem swap_getInv_apply_left (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j).getInv (a.getAt i) = j := by
  rw [swap_getInv_apply, swap_apply_left, getInv_getAt]

@[simp]
theorem swap_getInv_apply_right (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).getInv (a.getAt j) =
    i := by
  rw [swap_getInv_apply, swap_apply_right, getInv_getAt]

theorem swap_getInv_apply_of_ne_of_ne (a : ArrayPerm n) (i j : Fin n) {k} :
  k ≠ a.getAt i → k ≠ a.getAt j → (a.swap i j).getInv k = a.getInv k := by
  rw [swap_getInv_apply, a.getInv_leftInverse.injective.eq_iff]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (a : ArrayPerm n) (i : Fin n) : a.swap i i = a := by
  ext : 1
  rw [swap_getAt, Equiv.swap_self, coe_refl, comp_id]

@[simp]
theorem swap_swap (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).swap i j = a := by
  ext : 1
  simp_rw [swap_getAt, comp.assoc, ← Equiv.coe_trans, Equiv.swap_swap, coe_refl, comp_id]

def swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : ArrayPerm n where
  toArray := a.toArray.swaps (bs.map (fun b => (b.1.cast a.sizeTo.symm, b.2.cast a.sizeTo.symm)))
  invArray := a.invArray.swaps (bs.reverse.map fun b => ((a.getAt b.1).cast a.sizeInv.symm,
    (a.getAt b.2).cast a.sizeInv.symm))
  sizeTo := (a.toArray.size_swaps _).trans a.sizeTo
  sizeInv := (a.invArray.size_swaps _).trans a.sizeInv
  left_inv' i := by
    simp_rw [a.toArray.get_swaps_eq_get_apply_swaps', a.invArray.get_swaps_eq_get_apply_swaps',
    toArray_get, invArray_get, map_map, comp_def, coe_cast,
    getInv_apply_eq, mk_eq_iff_val_eq, ← swaps_coe, Fin.eta, ← mulEquivPerm_apply_apply,
    ← Perm.mul_apply, mul_swaps_eq_swaps_mul, Perm.mul_apply, swaps_coe, map_map, comp_def,
    map_reverse, Equiv.swaps_reverse, Perm.inv_apply_self]

theorem swaps_toArray (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs).toArray =
  a.toArray.swaps (bs.map (fun b => (b.1.cast a.sizeTo.symm, b.2.cast a.sizeTo.symm))) := rfl

theorem swaps_invArray (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : (a.swaps bs).invArray =
    a.invArray.swaps (bs.reverse.map fun b => ((a.getAt b.1).cast a.sizeInv.symm,
    (a.getAt b.2).cast a.sizeInv.symm)) := rfl

@[simp]
theorem swaps_getAt (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs).getAt = a.getAt ∘ Equiv.swaps bs :=
  funext fun i => (a.toArray.get_swaps_eq_get_apply_swaps' _ _).trans <|
    (a.toArray_get _).trans (congrArg _ <| Fin.ext <|
    by simp_rw [swaps_coe, map_map, comp_def, coe_cast])

@[simp]
theorem swaps_getAt_apply (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (k : Fin n) :
    (a.swaps bs).getAt k = a.getAt (Equiv.swaps bs k) := by rw [swaps_getAt, comp_apply]

theorem swaps_eq_mul_one_swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    a.swaps bs = a * swaps 1 bs := ArrayPerm.ext <| by
  simp only [swaps_getAt, mul_getAt, one_getAt, id_comp]

@[simp]
theorem mulEquivPerm_swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    mulEquivPerm (swaps a bs) = mulEquivPerm a * Equiv.swaps bs := Equiv.ext fun _ => by
  simp only [mulEquivPerm_apply_apply, swaps_getAt_apply, Perm.mul_apply]

@[simp]
theorem mulEquivPerm_one_swaps (bs : List (Fin n × Fin n))  :
    mulEquivPerm (swaps 1 bs) = Equiv.swaps bs := by simp_rw [mulEquivPerm_swaps, map_one, one_mul]

theorem swaps_eq_one_swaps_mul (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : a.swaps bs =
    swaps 1 (bs.map fun b => (a.getAt b.1, a.getAt b.2)) * a := mulEquivPerm.injective <| by
  simp only [mulEquivPerm_swaps, mul_swaps_eq_swaps_mul,
  mulEquivPerm_apply_apply, map_mul, map_one, one_mul]

theorem one_swaps_inverse (bs : List (Fin n × Fin n)) : (swaps 1 bs)⁻¹ =
    swaps 1 bs.reverse := mulEquivPerm.injective <| by
  simp only [map_inv, mulEquivPerm_swaps, map_one, one_mul, swaps_inverse]

theorem swaps_inv_eq_one_swaps_mul (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs)⁻¹ = swaps 1 bs.reverse * a⁻¹ := by
  rw [swaps_eq_mul_one_swaps, mul_inv_rev, one_swaps_inverse]

theorem swaps_inv_eq_mul_one_swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs)⁻¹ = a⁻¹ * swaps 1 (bs.reverse.map fun b => (a.getAt b.1, a.getAt b.2)) := by
  rw [swaps_eq_one_swaps_mul, mul_inv_rev, mul_right_inj, one_swaps_inverse, map_reverse]

theorem swaps_getInv (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : (a.swaps bs).getInv =
    a.getInv ∘ Equiv.swaps (bs.reverse.map fun b => (a.getAt b.1, a.getAt b.2)) := by
  simp_rw [← inv_getAt, a.swaps_inv_eq_mul_one_swaps, mul_getAt, inv_getAt,
  swaps_getAt, one_getAt, id_comp]

@[simp]
theorem one_swaps_getAt (bs : List (Fin n × Fin n)) : (swaps 1 bs).getAt = Equiv.swaps bs := by
  simp only [swaps_getAt, one_getAt, id_comp]

@[simp]
theorem one_swaps_getInv (bs : List (Fin n × Fin n)) :
    (swaps 1 bs).getInv = Equiv.swaps bs.reverse := funext fun _ => by
  simp only [getInv_apply_eq, swaps_getAt_apply, swaps_reverse_apply_swaps_reverse, one_getAt,
    id_eq]

theorem swaps_getAt' (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs).getAt = Equiv.swaps (bs.map fun b => (a.getAt b.1, a.getAt b.2)) ∘ a.getAt := by
  rw [swaps_eq_one_swaps_mul, mul_getAt, one_swaps_getAt]

theorem swaps_getInv' (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs).getInv = Equiv.swaps bs.reverse ∘ a.getInv := by
  rw [swaps_eq_mul_one_swaps, mul_getInv, one_swaps_getInv]

theorem one_swaps_reverse (bs : List (Fin n × Fin n)) : swaps 1 bs.reverse =
    (swaps 1 bs)⁻¹ := (one_swaps_inverse _).symm

@[simp]
theorem one_swaps_mul_one_swaps_reverse (bs : List (Fin n × Fin n)) :
    swaps 1 bs * swaps 1 bs.reverse = 1 := by rw [one_swaps_reverse, mul_right_inv]

@[simp]
theorem one_swaps_reverse_mul_one_swaps (bs : List (Fin n × Fin n)) :
    swaps 1 bs.reverse * swaps 1 bs = 1 := by rw [one_swaps_reverse, mul_left_inv]

theorem swaps_swaps_reverse (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs).swaps bs.reverse = a := by
  rw [swaps_eq_mul_one_swaps, swaps_eq_mul_one_swaps, mul_assoc,
  one_swaps_mul_one_swaps_reverse, mul_one]

theorem swaps_reverse_swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs.reverse).swaps bs = a := by
  rw [swaps_eq_mul_one_swaps, swaps_eq_mul_one_swaps, mul_assoc,
  one_swaps_reverse_mul_one_swaps, mul_one]

@[simp]
theorem swaps_nil (a : ArrayPerm n) : a.swaps [] = a := rfl

@[simp]
theorem swaps_cons (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (b : Fin n × Fin n) :
    a.swaps (b :: bs) = (a.swap b.1 b.2).swaps bs := by
  ext : 1
  simp_rw [swaps_getAt, swap_getAt, Equiv.swaps_cons, Perm.coe_mul, comp.assoc]

theorem swaps_eq_foldl (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    a.swaps bs = bs.foldl (fun a b => a.swap b.1 b.2) a := by
  induction' bs with b bs IH generalizing a
  · rfl
  · rw [swaps_cons, foldl_cons, IH]

theorem swaps_singleton (a : ArrayPerm n) (b : Fin n × Fin n) : a.swaps [b] = a.swap b.1 b.2 := rfl

@[simp]
theorem swaps_append (a : ArrayPerm n) (bs cs : List (Fin n × Fin n)) :
    a.swaps (bs ++ cs) = (a.swaps bs).swaps cs := by
  simp_rw [swaps_eq_foldl, foldl_append]

theorem swaps_swaps (a : ArrayPerm n) (bs cs : List (Fin n × Fin n)) :
    (a.swaps bs).swaps cs = a.swaps (bs ++ cs) := (a.swaps_append _ _).symm

theorem swaps_concat (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (b : Fin n × Fin n) :
  a.swaps (bs.concat b) = (a.swaps bs).swap b.1 b.2 := by
  simp_rw [concat_eq_append, swaps_append, swaps_singleton]


def condFlipBit (bs : Array (Fin 2)) : List (Fin ((bs.size)*2) × Fin ((bs.size)*2)) :=
(Fin.list (bs.size)).map fun k => (finProdFinEquiv (k, 0), finProdFinEquiv (k, bs.get k))

def blahj (bs : Array (Fin 2)) : ArrayPerm ((bs.size)*2) := swaps 1 <|
  (Fin.list (bs.size)).map fun k => (finProdFinEquiv (k, 0), finProdFinEquiv (k, bs.get k))

#eval (blahj #[0, 1, 0, 1]).swap (0 : Fin 8) (2 : Fin 8)

end ArrayPerm
