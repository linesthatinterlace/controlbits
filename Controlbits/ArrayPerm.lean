import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.Indexes
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.Interval.Finset.Fin
import Controlbits.Bool

set_option autoImplicit false

namespace List

variable {α β : Type*}

theorem list_reverse_induction' (p : List α → Prop) (base : p [])
    (ind : ∀ (l : List α) (e : α), p l → p (l.concat e)) : (∀ (l : List α), p l) :=
  list_reverse_induction p base (by simp_rw [← concat_eq_append] ; exact ind)

theorem mem_concat {a b : α} {l : List α} : a ∈ l ++ [b] ↔ a ∈ l ∨ a = b := by
  rw [mem_append, mem_singleton]

theorem mem_concat' {a b : α} {l : List α} : a ∈ l.concat b ↔ a ∈ l ∨ a = b := by
  rw [concat_eq_append, mem_concat]

theorem map_concat' (f : α → β) (a : α) (l : List α) :
    map f (l ++ [a]) = (map f l) ++ [f a] := by
  induction l <;> [rfl; simp only [cons_append, map_cons, map_append, map_nil]]

end List

namespace Prod

/-- Composing a `Prod.map` with another `Prod.map` onto a third function is equal to
a single `Prod.map` of composed functions composed onto the third function.
-/
theorem map_comp_map_left {α β γ δ ε ζ κ: Type*} (f : α → β) (f' : γ → δ) (g : β → ε) (g' : δ → ζ)
    (h : κ → α × γ) : Prod.map g g' ∘ Prod.map f f' ∘ h = Prod.map (g ∘ f) (g' ∘ f') ∘ h :=
  rfl

end Prod

namespace Fin

theorem lt_iff_extendDomain_equivSubtype_lt {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) :
    i < n ↔ (π.extendDomain equivSubtype) i < n := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [hi, true_iff]
    rw [π.extendDomain_apply_subtype equivSubtype hi,
    equivSubtype_symm_apply, equivSubtype_apply]
    exact Fin.isLt _
  · simp_rw [π.extendDomain_apply_not_subtype equivSubtype (hi.not_lt)]

open Prod

@[simp] theorem cast_comp {n m k : ℕ} (h : n = m) (h' : m = k) :
    cast h' ∘ cast h = cast (Eq.trans h h') := rfl

theorem mk_eq_iff_val_eq {n : ℕ} {a : Fin n} {k : ℕ} {hk : k < n} :
    ⟨k, hk⟩ = a ↔ k = (a : Nat) := ext_iff

theorem fst_lt_snd_lt_of_mem_map_val {n : ℕ} (bs : List (Fin n × Fin n)) (b : ℕ × ℕ)
    (hb : b ∈ bs.map (Prod.map val val)) : b.1 < n ∧ b.2 < n := by
  rw [List.mem_map] at hb
  rcases hb with ⟨⟨_, _⟩, ⟨_, rfl⟩⟩
  exact ⟨Fin.isLt _, Fin.isLt _⟩

theorem forall₂_iff {n : ℕ} {p : (i : ℕ) → i < n → i < n → Prop} :
  (∀ i h h₂, p i h h₂) ↔ ∀ (i : Fin n), p i i.isLt i.isLt :=
  ⟨fun H _ => H _ _ _, fun H i h _ => H ⟨i, h⟩⟩

@[simp]
theorem val_comp_cast {n m : ℕ} (h : n = m) : val ∘ cast h = val := rfl

end Fin

namespace Equiv

open List Function Fin Prod

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem coe_swap {n : ℕ} {i j k : Fin n} : swap (i : ℕ) (j : ℕ) (k : ℕ) = swap i j k :=
  val_injective.swap_apply _ _ _

theorem swap_smul {R : Type*} [Group R] [MulAction R α] {i j k : α} {r : R} :
    swap (r • i) (r • j) (r • k) = r • swap i j k :=
  (MulAction.injective r).swap_apply _ _ _

theorem swap_prop (p : α → Prop) {i j k : α} (hk : p k) (hi : p i) (hj : p j) :
    p (swap i j k) := by
  simp_rw [swap_apply_def, apply_ite p, hi, hj, hk, ite_self]

theorem uncurry_swap : uncurry swap = fun (x : α × α) => swap x.1 x.2 := rfl

@[simp]
theorem uncurry_swap_apply (x : α × α) : uncurry swap x = swap x.1 x.2 := rfl

end Equiv

namespace Array

open Equiv Function List Fin

variable {α β γ : Type*}

theorem mem_iff_getElem {as : Array α} {a : α} :
    a ∈ as ↔ ∃ (i : ℕ), ∃ (hi : i < as.size), as[i] = a := by
  rw [mem_def, List.mem_iff_getElem]
  exact Iff.rfl

@[simp]
theorem getElem_mem {as : Array α} {i : ℕ} (hi : i < as.size) :
    as[i] ∈ as := mem_iff_getElem.mpr ⟨i, hi, rfl⟩

theorem mem_iff_get {as : Array α} {a : α} :
    a ∈ as ↔ ∃ (i : Fin (as.size)), as.get i = a := by
  simp_rw [get_eq_getElem, mem_iff_getElem, Fin.exists_iff]

@[simp]
theorem getD_eq_get_lt (a : Array α) (x : α) (i : ℕ) (h : i < a.size) : a[i]?.getD x = a[i] := by
  rw [a.getElem?_lt h, Option.getD_some]

@[simp]
theorem getD_eq_get_ge (a : Array α) (x : α) (i : ℕ) (h : a.size ≤ i) : a[i]?.getD x = x := by
  rw [a.getElem?_ge h, Option.getD_none]

theorem getD_eq_get (a : Array α) (x : α) (i : ℕ) :
    a[i]?.getD x = if h : i < a.size then a[i] else x := by
  split_ifs with h
  · rw [a.getD_eq_get_lt x i h]
  · rw [a.getD_eq_get_ge x i (le_of_not_lt h)]

@[simp]
theorem ofFn_get (a : Array α) : Array.ofFn a.get = a :=
  ext _ _ (size_ofFn _) (fun _ _ _ => getElem_ofFn _ _ _)

@[simp]
theorem get_ofFn {n : ℕ} (f : Fin n → α) :
    (ofFn f).get = f ∘ (Fin.cast (size_ofFn _)) := funext <| fun _ => by
  rw [get_eq_getElem, getElem_ofFn, comp_apply]
  exact congrArg _ (Fin.ext rfl)

@[simps]
def equivSigmaTuple : Array α ≃ Σ n, Fin n → α where
  toFun a := ⟨a.size, a.get⟩
  invFun f := ofFn f.2
  left_inv := ofFn_get
  right_inv := fun _ => Fin.sigma_eq_of_eq_comp_cast _ (get_ofFn _)

@[simp]
theorem range_zero : range 0 = #[] := rfl

@[simp]
theorem range_succ {n : ℕ} : range (n + 1) = (range n).push n := rfl

@[simp]
theorem getElem_range {i n : ℕ} (h : i < (range n).size) : (range n)[i] = i := by
  induction' n with n IH
  · simp_rw [size_range, Nat.not_lt_zero] at h
  · simp_rw [range_succ, Array.get_push, size_range]
    simp_rw [size_range] at IH
    rw [size_range, Nat.lt_succ_iff, le_iff_eq_or_lt] at h
    rcases h with rfl | h
    · simp_rw [lt_irrefl, dite_false]
    · simp_rw [h, dite_true]
      exact IH h

theorem mem_range_iff {i n : ℕ} : i ∈ range n ↔ i < n := by
  simp_rw [Array.mem_iff_getElem, getElem_range, size_range, exists_prop, exists_eq_right]

theorem getElem_range_lt {i n : ℕ} {h : i < (range n).size} : (range n)[i] < n := by
  simp_rw [← mem_range_iff, getElem_mem]

theorem getElem_append {i : ℕ} {as bs : Array α} (h : i < (as ++ bs).size)
    (h' : ¬ (i < as.size) → i - as.size < bs.size :=
    fun hi => Nat.sub_lt_left_of_lt_add (le_of_not_lt hi) (h.trans_eq (size_append as bs))) :
    (as ++ bs)[i] = if hi : i < as.size then as[i] else bs[i - as.size] := by
  split_ifs with hi
  · exact Array.get_append_left hi
  · exact Array.get_append_right (le_of_not_lt hi)

theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith bs f).size) : i < as.size := by
  rw [Array.size_eq_length_data] at h ⊢
  rw [Array.zipWith_eq_zipWith_data] at h
  exact List.lt_length_left_of_zipWith h

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith bs f).size) : i < bs.size := by
  rw [Array.size_eq_length_data] at h ⊢
  rw [Array.zipWith_eq_zipWith_data] at h
  exact List.lt_length_right_of_zipWith h

theorem lt_length_left_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < as.size := lt_length_left_of_zipWith h

theorem lt_length_right_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < bs.size := lt_length_right_of_zipWith h

@[simp]
theorem getElem_zipWith {as : Array α} {bs : Array β} {f : α → β → γ} {i : ℕ}
    (h : i < (as.zipWith bs f).size) : (as.zipWith bs f)[i] =
    f (as[i]'(lt_length_left_of_zipWith h)) (bs[i]'(lt_length_right_of_zipWith h)) := by
  simp_rw [getElem_eq_data_getElem, Array.zipWith_eq_zipWith_data, List.getElem_zipWith]

@[simp]
theorem getElem_zip {as : Array α} {bs : Array β} {i : ℕ}
    (h : i < (as.zip bs).size) : (as.zip bs)[i] =
    (as[i]'(lt_length_left_of_zip h), bs[i]'(lt_length_right_of_zip h)) := by
  simp_rw [getElem_eq_data_getElem, Array.zip_eq_zip_data, List.getElem_zip]

@[simp]
theorem size_attachWith {as : Array α} {P : α → Prop} {H : ∀ a, a ∈ as → P a} :
    (as.attachWith _ H).size = as.size := by
  unfold attachWith List.attachWith
  simp_rw [size_eq_length_data, List.length_pmap]

@[simp]
theorem getElem_attachWith {as : Array α} {P : α → Prop} {H : ∀ a, a ∈ as → P a} {i : ℕ}
    (h : i < (as.attachWith _ H).size) :
    haveI := size_attachWith (H := H); (as.attachWith _ H)[i] = ⟨as[i], H _ (getElem_mem _)⟩ := by
  unfold attachWith List.attachWith
  simp_rw [Array.getElem_eq_data_getElem, List.getElem_pmap]

@[simp]
theorem size_attach {as : Array α} : as.attach.size = as.size := size_attachWith

@[simp]
theorem getElem_attach {as : Array α} {i : ℕ} (h : i < as.attach.size) :
    haveI := size_attach (as := as); (as.attach)[i] = ⟨as[i], (getElem_mem _)⟩ := getElem_attachWith _

@[simp]
theorem size_swapN {as : Array α} {i j : Nat} (hi : i < as.size) (hj : j < as.size):
    (as.swapN i j hi hj).size = as.size := as.size_swap _ _

theorem getElem_swapN {as : Array α} {i j : Nat} (hi : i < as.size) (hj : j < as.size)
    (k : ℕ) (hk : k < (as.swapN i j hi hj).size) :
    (as.swapN i j hi hj)[k] =
    if k = i then as[j] else if k = j then as[i] else as[k]'(hk.trans_eq <| as.size_swapN _ _) :=
  as.get_swap' _ _ _ _

theorem swap!_eq_swapN {as : Array α} {i j : ℕ}(hi : i < as.size)
    (hj : j < as.size) :
    as.swap! i j = as.swapN i j := by
  unfold swap!
  unfold swapN
  simp_rw [hi, hj, dite_true]

theorem swap!_eq_swap {as : Array α} {i j : ℕ}(hi : i < as.size)
    (hj : j < as.size) : as.swap ⟨i, hi⟩ ⟨j, hj⟩ = as.swapN i j := rfl

theorem getElem_swap!_of_ge_left {as : Array α} {i j k : ℕ} (h : as.size ≤ i)
    (hk : k < (as.swap! i j).size) :
    (as.swap! i j)[k] = as[k]'(hk.trans_eq <| as.size_swap! _ _) := by
  unfold swap!
  simp_rw [h.not_lt, dite_false]

theorem getElem_swap!_of_ge_right {as : Array α} {i j k : ℕ} (h : as.size ≤ j)
    (hk : k < (as.swap! i j).size) :
    (as.swap! i j)[k] = as[k]'(hk.trans_eq <| as.size_swap! _ _) := by
  unfold swap!
  simp_rw [h.not_lt, dite_false, dite_eq_ite, ite_self]

@[simp]
theorem getElem_swap!_left {as : Array α} {i j : ℕ} (hj : j < as.size)
    (hi : i < (as.swap! i j).size) :
    (as.swap! i j)[i] = as[j] := by
  simp_rw [size_swap!] at hi
  unfold swap!
  simp_rw [hi, hj, dite_true]
  exact get_swap_left _

@[simp]
theorem getElem_swap!_right {as : Array α} {i j : ℕ} (hi : i < as.size)
    (hj : j < (as.swap! i j).size) :
    (as.swap! i j)[j] = as[i] := by
  simp_rw [size_swap!] at hj
  unfold swap!
  simp_rw [hi, hj, dite_true]
  exact get_swap_right _

theorem getElem_swap!_of_ne_ne {as : Array α} {i j k : ℕ} (hi : k ≠ i) (hj : k ≠ j)
    (hk : k < (as.swap! i j).size) :
    (as.swap! i j)[k] = as[k]'(hk.trans_eq <| as.size_swap! _ _) := by
  simp_rw [size_swap!] at hk
  unfold swap!
  split_ifs <;> try {rfl}
  exact Array.get_swap_of_ne _ _ hi hj

theorem getElem_swap! {as : Array α} {i j k : ℕ} (hk : k < (as.swap! i j).size) :
    (as.swap! i j)[k] =
    if h : k = i ∧ j < as.size then as[j]'h.2 else if h₂ : k = j ∧ i < as.size then as[i]'h₂.2
    else as[k]'(hk.trans_eq <| as.size_swap! _ _) := by
  rcases eq_or_ne k i with rfl | hi
  · simp_rw [true_and]
    rcases lt_or_le j as.size with hj | hj
    · simp_rw [hj, dite_true, getElem_swap!_left hj]
    · simp_rw [hj.not_lt, dite_false, getElem_swap!_of_ge_right hj]
      split_ifs <;> rfl
  · rcases eq_or_ne k j with rfl | hj
    · simp_rw [hi, false_and, dite_false, true_and]
      rcases lt_or_le i as.size with hi | hi
      · simp_rw [hi, dite_true, getElem_swap!_right hi]
      · simp_rw [hi.not_lt, dite_false, getElem_swap!_of_ge_left hi]
    · simp_rw [hi, hj, false_and, dite_false, getElem_swap!_of_ne_ne hi hj]

theorem getElem_swapN_eq_getElem_swap_apply {as : Array α} {i j : Nat} (hi : i < as.size)
    (hj : j < as.size)
    (k : ℕ) (hk : k < (as.swapN i j hi hj).size) :
    (as.swapN i j hi hj)[k] =
    as[Equiv.swap i j k]'(swap_prop (· < as.size) (hk.trans_eq <| as.size_swapN _ _) hi hj) := by
  simp_rw [getElem_swapN, swap_apply_def]
  split_ifs <;> rfl

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

@[simp] theorem size_uncurry_swap (a : Array α) (x : Fin a.size × Fin a.size) :
    (uncurry a.swap x).size = a.size := size_swap _ _ _

@[simp] theorem uncurry_swap_apply (a : Array α) (x : Fin a.size × Fin a.size) :
    uncurry a.swap x = a.swap x.1 x.2 := rfl

@[simp]
theorem uncurry_swap_congr (a a' : Array α) {x : Fin a.size × Fin a.size}
    {y : Fin a'.size × Fin a'.size} : a = a' → x.1.val = y.1.val → x.2.val = y.2.val →
    uncurry a.swap x = uncurry a'.swap y := swap_congr _ _

@[simp]
theorem uncurry_swap_self (a : Array α) {i : Fin a.size} :
    uncurry a.swap (i, i) = a := swap_self _

theorem get_uncurry_swap_eq_get_apply_uncurry_swap (a : Array α) {x : Fin a.size × Fin a.size}
    (k : ℕ) (h : k < a.size)
    (h' : k < (uncurry a.swap x).size := (a.size_uncurry_swap _).symm.trans_gt h)
    (h'' : uncurry Equiv.swap (x.map val val) k < a.size :=
    swap_prop (fun t => t < a.size) h x.1.isLt x.2.isLt) :
    (uncurry a.swap x)[k] = a[uncurry Equiv.swap (x.map val val) k] :=
  get_swap_eq_get_apply_swap _ _ h

theorem get_uncurry_swap_eq_get_apply_uncurry_swap' (a : Array α) {x : Fin a.size × Fin a.size}
    (k : ℕ) (h : k < (uncurry a.swap x).size)
    (h' : k < a.size := (a.size_uncurry_swap _).trans_gt h)
    (h'' : uncurry Equiv.swap (x.map val val) k < a.size :=
    swap_prop (fun t => t < a.size) h' x.1.isLt x.2.isLt) :
    (uncurry a.swap x)[k] = a[uncurry Equiv.swap (x.map val val) k] :=
  a.get_uncurry_swap_eq_get_apply_uncurry_swap _ h'

end Array

/--
An `ArrayPerm n` is a permutation on `Fin n` represented by two arrays, which we can
think of as an array of values and a corresponding area of indexes which are inverse to
one another. (One can flip the interpretation of indexes and values, and this is essentially
the inversion operation.)
It is designed to be a performant version of `Equiv.Perm`.
-/
structure ArrayPerm (n : ℕ) where
  /--
  Gives the `ArrayPerm` as an array of values. Index `i` is mapped to the value at position `i`
  in `toArray`.
  -/
  protected toArray : Array ℕ
  /--
  Gives the `ArrayPerm` as an array of indexes. Value `v` is mapped to the index at position `v`
  in `invArray`.
  -/
  protected invArray : Array ℕ
  size_toArray : toArray.size = n := by rfl
  size_invArray : invArray.size = n := by rfl
  protected getElem_toArray_lt' :
    ∀ {i : ℕ} (hi : i < n), toArray[i] < n := by decide
  protected getElem_invArray_lt' :
  ∀ {i : ℕ} (hi : i < n), invArray[i] < n := by decide
  protected getElem_invArray_getElem_toArray' : ∀ {i : ℕ} (hi : i < n),
      haveI := getElem_toArray_lt' hi;
      invArray[toArray[i]] = i := by decide

namespace ArrayPerm

open Function Fin Equiv List Array

variable {n m : ℕ}

instance : Repr (ArrayPerm n) where
  reprPrec a _ := "ArrayPerm " ++ " : " ++ repr a.toArray

instance : ToString (ArrayPerm n) where
  toString a := "ArrayPerm " ++ " : " ++ toString a.toArray


/-
theorem size_toArray (a : ArrayPerm n) : a.toArray.size = n := a.size_toArray'


theorem lt_of_lt_size_toArray (a : ArrayPerm n) {i : ℕ}
    (hi : i < a.toArray.size := by get_elem_tactic) : i < n :=

theorem lt_of_lt_size_invArray (a : ArrayPerm n) {i : ℕ}
    (hi : i < a.invArray.size := by get_elem_tactic) : i < n :=
-/

/-



theorem lt_size_toArray_of_lt_size_invArray (a : ArrayPerm n) {i : ℕ}
    (hi : i < a.invArray.size := by get_elem_tactic) : i < a.toArray.size :=
  hi.trans_eq <| a.size_invArray.trans a.size_toArray.symm

theorem lt_size_invArray_of_lt_size_toArray (a : ArrayPerm n) {i : ℕ}
    (hi : i < a.toArray.size := by get_elem_tactic) : i < a.invArray.size :=
  hi.trans_eq <| a.size_toArray.trans a.size_invArray.symm

-/

theorem size_toArray_eq_size_toArray (a b : ArrayPerm n) :
    a.toArray.size = b.toArray.size := a.size_toArray.trans b.size_toArray.symm

theorem size_invArray_eq_size_invArray (a b : ArrayPerm n) :
    a.invArray.size = b.invArray.size := a.size_invArray.trans b.size_invArray.symm

theorem size_invArray_eq_size_toArray (a b : ArrayPerm n) :
    a.invArray.size = b.toArray.size := a.size_invArray.trans b.size_toArray.symm

theorem getElem_toArray_lt (a : ArrayPerm n) {i : ℕ} (hi : i < a.toArray.size) :
    a.toArray[i] < n :=
  a.getElem_toArray_lt' <| hi.trans_eq a.size_toArray

theorem getElem_invArray_lt (a : ArrayPerm n) {i : ℕ} (hi : i < a.invArray.size) :
    a.invArray[i] < n :=
  a.getElem_invArray_lt' <| hi.trans_eq a.size_invArray

theorem lt_size_toArray_of_lt_size_toArray (a b : ArrayPerm n) {i : ℕ}
    (hi : i < a.toArray.size) : i < b.toArray.size :=
  hi.trans_eq (a.size_toArray_eq_size_toArray b)

theorem lt_size_invArray_of_lt_size_toArray (a b : ArrayPerm n) {i : ℕ}
    (hi : i < a.toArray.size) : i < b.invArray.size :=
  hi.trans_eq (b.size_invArray_eq_size_toArray a).symm

theorem lt_size_toArray_of_lt_size_invArray (a b : ArrayPerm n) {i : ℕ}
    (hi : i < a.invArray.size) : i < b.toArray.size :=
  hi.trans_eq (a.size_invArray_eq_size_toArray b)

theorem lt_size_invArray_of_lt_size_invArray (a b : ArrayPerm n) {i : ℕ}
    (hi : i < a.invArray.size) : i < b.invArray.size :=
  hi.trans_eq (a.size_invArray_eq_size_invArray b)

theorem lt_size_toArray_of_lt (a : ArrayPerm n) {i : ℕ} (hi : i < n) : i < a.toArray.size :=
  hi.trans_eq a.size_toArray.symm

theorem lt_size_invArray_of_lt (a : ArrayPerm n) {i : ℕ} (hi : i < n) : i < a.invArray.size :=
  hi.trans_eq a.size_invArray.symm

@[simp]
theorem getElem_toArray_lt_size_invArray (a b : ArrayPerm n) {i : ℕ} (hi : i < a.toArray.size) :
    a.toArray[i] < b.invArray.size := (a.getElem_toArray_lt _).trans_eq b.size_invArray.symm

@[simp]
theorem getElem_invArray_lt_size_toArray (a b : ArrayPerm n) {i : ℕ} (hi : i < a.invArray.size) :
    a.invArray[i] < b.toArray.size := (a.getElem_invArray_lt _).trans_eq b.size_toArray.symm

@[simp]
theorem getElem_toArray_lt_size_toArray (a b : ArrayPerm n) {i : ℕ} (hi : i < a.toArray.size) :
    a.toArray[i] < b.toArray.size :=
  a.lt_size_toArray_of_lt_size_invArray _ (a.getElem_toArray_lt_size_invArray _ _)

@[simp]
theorem getElem_invArray_lt_size_invArray (a b : ArrayPerm n) {i : ℕ} (hi : i < a.invArray.size) :
    a.invArray[i] < b.invArray.size :=
  a.lt_size_invArray_of_lt_size_toArray _ (a.getElem_invArray_lt_size_toArray _ _)

@[simp]
theorem getElem_invArray_getElem_toArray (a : ArrayPerm n) {i : ℕ}
    (hi : i < a.toArray.size) : a.invArray[a.toArray[i]] = i :=
  a.getElem_invArray_getElem_toArray' (hi.trans_eq a.size_toArray)

@[simp]
theorem getElem_toArray_getElem_invArray (a : ArrayPerm n) {i : ℕ}
    (hi : i < a.invArray.size) : a.toArray[a.invArray[i]] = i := by
  have H : Injective (fun (i : Fin (a.invArray.size)) =>
      Fin.mk a.invArray[i.1] <| a.getElem_invArray_lt_size_toArray a _) :=
    Surjective.injective_of_fintype (finCongr (a.size_invArray_eq_size_toArray a)) (fun i => by
    simp_rw [Fin.ext_iff, Fin.exists_iff]
    exact ⟨a.toArray[i.1], a.getElem_toArray_lt_size_invArray a _,
      a.getElem_invArray_getElem_toArray _⟩)
  unfold Injective at H
  simp_rw [Fin.forall_iff, Fin.ext_iff] at H
  apply H
  · apply a.getElem_invArray_getElem_toArray
  · apply a.getElem_toArray_lt_size_invArray
  · assumption

@[simp]
theorem getElem?_invArray_getElem_toArray (a : ArrayPerm n) {i : ℕ}
    (hi : i < a.toArray.size := by get_elem_tactic) : a.invArray[a.toArray[i]]? = some i :=
  (a.invArray.getElem?_eq_getElem _ (a.getElem_toArray_lt_size_invArray _ _)).trans
    (congrArg _ <| a.getElem_invArray_getElem_toArray _)

@[simp]
theorem getElem?_toArray_getElem_invArray (a : ArrayPerm n) {i : ℕ}
    (hi : i < a.invArray.size := by get_elem_tactic) : a.toArray[a.invArray[i]]? = some i :=
  (a.toArray.getElem?_eq_getElem _ (a.getElem_invArray_lt_size_toArray _ _)).trans
    (congrArg _ <| a.getElem_toArray_getElem_invArray _)

theorem toArray_injective (a : ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ}
    (hj : j < n) (hij : haveI:= a.size_toArray ; a.toArray[i] = a.toArray[j]) : i = j := by
  have H := congrArg (a.invArray[·]?) hij
  simp only [getElem?_invArray_getElem_toArray, Option.some.injEq] at H
  assumption

theorem invArray_injective (a : ArrayPerm n) {i j : ℕ} (hi : i < n)
    (hj : j < n) (hij : haveI:= a.size_invArray ; a.invArray[i] = a.invArray[j]) : i = j := by
  have H := congrArg (a.toArray[·]?) hij
  simp only [getElem?_toArray_getElem_invArray, Option.some.injEq] at H
  assumption

theorem invArray_surjective (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), haveI:= a.size_invArray ; a.invArray[j] = i :=
  haveI:= a.size_toArray ;
  ⟨a.toArray[i], a.getElem_toArray_lt _, a.getElem_invArray_getElem_toArray _⟩

theorem toArray_surjective (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), haveI:= a.size_toArray ; a.toArray[j] = i :=
  haveI:= a.size_invArray;
  ⟨a.invArray[i], a.getElem_invArray_lt _, a.getElem_toArray_getElem_invArray _⟩

theorem mem_toArray_iff (a : ArrayPerm n) {i : ℕ} : i ∈ a.toArray ↔ i < n := by
  simp_rw [Array.mem_iff_getElem, a.size_toArray]
  refine ⟨?_, a.toArray_surjective⟩
  rintro ⟨j, hj, rfl⟩
  apply a.getElem_toArray_lt

theorem mem_invArray_iff (a : ArrayPerm n) {i : ℕ} : i ∈ a.invArray ↔ i < n := by
  simp_rw [Array.mem_iff_getElem, a.size_invArray]
  refine ⟨?_, a.invArray_surjective⟩
  rintro ⟨j, hj, rfl⟩
  apply a.getElem_invArray_lt

theorem mem_invArray (a : ArrayPerm n) (i : ℕ) (hi : i < n) : i ∈ a.invArray := by
  rwa [mem_invArray_iff]

theorem mem_toArray (a : ArrayPerm n) (i : ℕ) (hi : i < n) : i ∈ a.toArray := by
  rwa [mem_toArray_iff]

theorem lt_of_mem_invArray (a : ArrayPerm n) (i : ℕ) (hi : i ∈ a.invArray) : i < n := by
  rwa [mem_invArray_iff] at hi

theorem lt_of_mem_toArray (a : ArrayPerm n) (i : ℕ) (hi : i ∈ a.toArray) : i < n := by
  rwa [mem_toArray_iff] at hi


/--
We can make an `ArrayPerm` using the right-inverse hypothesis instead of the left-inverse
hypothesis, and we called this `ArrayPerm.mk'`.
-/
protected def mk' (toArray : Array ℕ) (invArray : Array ℕ)
  (size_toArray' : toArray.size = n := by rfl)
  (size_invArray' : invArray.size = n := by rfl)
  (getElem_toArray_lt' :
    ∀ {i : ℕ} (hi : i < n), toArray[i] < n := by decide)
  (getElem_invArray_lt' :
  ∀ {i : ℕ} (hi : i < n), invArray[i] < n := by decide)
  (getElem_toArray_getElem_invArray' : ∀ {i : ℕ} (hi : i < n),
      haveI := getElem_invArray_lt' hi;
      toArray[invArray[i]] = i := by decide): ArrayPerm n where
  toArray := toArray
  invArray := invArray
  size_toArray := size_toArray'
  size_invArray := size_invArray'
  getElem_toArray_lt' := getElem_toArray_lt'
  getElem_invArray_lt' := getElem_invArray_lt'
  getElem_invArray_getElem_toArray' := fun _ =>
    letI A : ArrayPerm n :=
      ⟨invArray, toArray, size_invArray', size_toArray',
      getElem_invArray_lt', getElem_toArray_lt', getElem_toArray_getElem_invArray'⟩
    A.getElem_toArray_getElem_invArray _

@[simp]
theorem mk'_toArray (tA) (iA) (stA) (siA) (gEtAlt) (gEiAlt) (gEtAgEiA) :
    (ArrayPerm.mk' (n := n) tA iA stA siA gEtAlt gEiAlt gEtAgEiA).toArray = tA := rfl

@[simp]
theorem mk'_invArray (tA) (iA) (stA) (siA) (gEtAlt) (gEiAlt) (gEtAgEiA) :
    (ArrayPerm.mk' (n := n) tA iA stA siA gEtAlt gEiAlt gEtAgEiA).invArray = iA := rfl

theorem invArray_eq_iff_toArray_eq (a b : ArrayPerm n) :
    a.invArray = b.invArray ↔ a.toArray = b.toArray := by
  refine ⟨fun h => Array.ext _ _ ?_ (fun i hi₁ hi₂ => ?_),
    fun h => Array.ext _ _ ?_ (fun i hi₁ hi₂ => ?_)⟩
  · rw [a.size_toArray, b.size_toArray]
  · apply a.invArray_injective
    · simp_rw [getElem_invArray_getElem_toArray, h, getElem_invArray_getElem_toArray]
    · apply a.getElem_toArray_lt
    · apply b.getElem_toArray_lt
  · rw [a.size_invArray, b.size_invArray]
  · apply a.toArray_injective
    · simp_rw [getElem_toArray_getElem_invArray, h, getElem_toArray_getElem_invArray]
    · apply a.getElem_invArray_lt
    · apply b.getElem_invArray_lt

theorem eq_iff_toArray_eq (a b : ArrayPerm n) : a = b ↔ a.toArray = b.toArray := by
  trans (a.toArray = b.toArray ∧ a.invArray = b.invArray)
  · rcases a ; rcases b ; simp_rw [mk.injEq]
  · rw [invArray_eq_iff_toArray_eq, and_self]

theorem eq_iff_getElem_toArray_eq (a b : ArrayPerm n):
  a = b ↔ ∀ (i : ℕ) (hi₁ : i < a.toArray.size) (hi₂ : i < b.toArray.size),
  a.toArray[i] = b.toArray[i] := ⟨fun h _ _ _ => h ▸ rfl, fun h => by
    rw [eq_iff_toArray_eq]
    exact Array.ext _ _ (by rw [a.size_toArray, b.size_toArray]) h⟩

theorem eq_of_getElem_toArray_eq (a b : ArrayPerm n)
  (h : ∀ (i : ℕ) (hi₁ : i < a.toArray.size) (hi₂ : i < b.toArray.size),
    a.toArray[i] = b.toArray[i]) : a = b := (a.eq_iff_getElem_toArray_eq b).mpr h

instance : One (ArrayPerm n) where
  one := {
    toArray := range n
    invArray := range n
    size_toArray := size_range
    size_invArray := size_range
    getElem_toArray_lt' := fun _ => getElem_range_lt
    getElem_invArray_lt' := fun _ => getElem_range_lt
    getElem_invArray_getElem_toArray' := fun _ => by simp_rw [Array.getElem_range]}

theorem one_toArray : (1 : ArrayPerm n).toArray = Array.range n := rfl
theorem one_invArray : (1 : ArrayPerm n).invArray = Array.range n := rfl

@[simp]
theorem getElem_one_toArray {i : ℕ} (hi : i < (1 : ArrayPerm n).toArray.size) :
  (1 : ArrayPerm n).toArray[i] = i := getElem_range _
@[simp]
theorem getElem_one_invArray {i : ℕ} (hi : i < (1 : ArrayPerm n).invArray.size) :
  (1 : ArrayPerm n).invArray[i] = i := getElem_range _

instance : Inv (ArrayPerm n) where
  inv a := (ArrayPerm.mk' a.invArray a.toArray
  a.size_invArray a.size_toArray
  a.getElem_invArray_lt' a.getElem_toArray_lt'
  a.getElem_invArray_getElem_toArray')

@[simp]
theorem inv_toArray (a : ArrayPerm n) : a⁻¹.toArray = a.invArray := rfl
@[simp]
theorem inv_invArray (a : ArrayPerm n) : a⁻¹.invArray = a.toArray := rfl

instance : Mul (ArrayPerm n) where
  mul a b := {
    toArray := b.toArray.map fun i => a.toArray[i]?.getD 0
    invArray := a.invArray.map fun i => b.invArray[i]?.getD 0
    size_toArray := by rw [size_map, size_toArray]
    size_invArray := by rw [size_map, size_invArray]
    getElem_toArray_lt' := fun _ => by simp only [Array.getElem_map, size_toArray,
      getElem_toArray_lt, getD_eq_get_lt]
    getElem_invArray_lt' := fun _ => by simp only [Array.getElem_map, size_invArray,
      getElem_invArray_lt, getD_eq_get_lt]
    getElem_invArray_getElem_toArray' := fun _ => by simp only [Array.getElem_map, size_toArray,
      getElem_toArray_lt, getD_eq_get_lt, getElem_invArray_getElem_toArray, size_invArray]}

theorem mul_toArray (a b : ArrayPerm n) : (a * b).toArray =
    b.toArray.map fun i => a.toArray[i]?.getD 0 := rfl
theorem mul_invArray (a b : ArrayPerm n) : (a * b).invArray =
    a.invArray.map fun i => b.invArray[i]?.getD 0 := rfl

theorem getElem_mul_toArray (a b : ArrayPerm n) {i : ℕ} (hi : i < (a * b).toArray.size) :
    (a * b).toArray[i] = a.toArray[b.toArray[i]'(lt_size_toArray_of_lt_size_toArray _ _ hi)] := by
  simp only [mul_toArray, Array.getElem_map, size_toArray, getElem_toArray_lt, getD_eq_get_lt]

theorem getElem_mul_invArray (a b : ArrayPerm n) {i : ℕ} (hi : i < (a * b).invArray.size) :
    (a * b).invArray[i] =
    b.invArray[a.invArray[i]'(lt_size_invArray_of_lt_size_invArray _ _ hi)] := by
  simp only [mul_invArray, Array.getElem_map, size_invArray, getElem_invArray_lt, getD_eq_get_lt]

instance : Group (ArrayPerm n) where
  mul_assoc a b c := (a * b * c).eq_of_getElem_toArray_eq (a * (b * c)) fun _ _ _ => by
    simp_rw [getElem_mul_toArray]
  one_mul a := (1 * a).eq_of_getElem_toArray_eq a fun _ _ _ => by
    simp_rw [getElem_mul_toArray, getElem_one_toArray]
  mul_one a := (a * 1).eq_of_getElem_toArray_eq a fun _ _ _ => by
    simp_rw [getElem_mul_toArray, getElem_one_toArray]
  mul_left_inv a := (a⁻¹ * a).eq_of_getElem_toArray_eq 1 fun _ _ _ => by
    simp_rw [getElem_mul_toArray, inv_toArray, getElem_one_toArray,
    getElem_invArray_getElem_toArray]

instance : SMul (ArrayPerm n) ℕ where
  smul a i := if h : i < n then haveI := a.size_toArray; a.toArray[i] else i

theorem smul_nat_def (a : ArrayPerm n) (i : ℕ) :
    a • i = if h : i < n then haveI := a.size_toArray; a.toArray[i] else i := rfl

theorem smul_of_lt (a : ArrayPerm n) {i : ℕ} (h : i < n) :
    haveI := a.size_toArray ; a • i = a.toArray[i] := dif_pos h

theorem smul_of_ge (a : ArrayPerm n) {i : ℕ} (h : n ≤ i) :
    a • i = i := dif_neg (not_lt_of_le h)

instance : FaithfulSMul (ArrayPerm n) ℕ where
  eq_of_smul_eq_smul := by
    simp_rw [eq_iff_getElem_toArray_eq, smul_nat_def]
    rintro a b h i hi₁ hi₂
    have h := h i
    simp_rw [a.size_toArray] at hi₁
    simp_rw [b.size_toArray] at hi₂
    simp_rw [hi₁, dite_true] at h
    exact h

theorem ext' {a b : ArrayPerm n} (h : ∀ i : ℕ, a • i = b • i) : a = b :=
  FaithfulSMul.eq_of_smul_eq_smul h

theorem ext_iff' (a b : ArrayPerm n) : a = b ↔ ∀ i : ℕ, a • i = b • i :=
  ⟨fun h _ => h ▸ rfl, ext'⟩

theorem lt_iff_smul_lt (a : ArrayPerm n) {i : ℕ} : i < n ↔ a • i < n := by
  rcases lt_or_le i n with h | h
  · simp_rw [h, true_iff, a.smul_of_lt h]
    apply a.getElem_toArray_lt
  · simp_rw [h.not_lt, false_iff, a.smul_of_ge h]
    exact h.not_lt

theorem le_iff_le_smul (a : ArrayPerm n) {i : ℕ} : n ≤ i ↔ n ≤ a • i := by
  simp_rw [← not_lt]
  exact a.lt_iff_smul_lt.not

@[ext]
theorem ext {a b : ArrayPerm n} (h : ∀ i < n, a • i = b • i) : a = b := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := ℕ)
  intros i
  rcases lt_or_le i n with hi | hi
  · exact h i hi
  · simp_rw [smul_of_ge _ hi]

theorem ext_iff (a b : ArrayPerm n) : a = b ↔ ∀ i < n, a • i = b • i :=
  ⟨fun h _ _ => h ▸ rfl, ext⟩

theorem smul_right_inj (a : ArrayPerm n) {i j : ℕ} : a • i = a • j ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rcases lt_or_le i n with hi | hi
  · have hj := hi
    rw [a.lt_iff_smul_lt, h, ← lt_iff_smul_lt] at hj
    refine a.toArray_injective hi hj ?_
    rwa [a.smul_of_lt hi, a.smul_of_lt hj] at h
  · have hj := hi
    rw [a.le_iff_le_smul, h, ← le_iff_le_smul] at hj
    rwa [a.smul_of_ge hi, a.smul_of_ge hj] at h

instance : MulAction (ArrayPerm n) ℕ where
  one_smul k := (k.lt_or_ge n).by_cases
    (fun h => by simp_rw [smul_of_lt _ h, getElem_one_toArray])
    (fun h => smul_of_ge _ h)
  mul_smul _ _ k := (k.lt_or_ge n).by_cases
    (fun h => by simp_rw [smul_of_lt _ h, getElem_mul_toArray,
    smul_of_lt _ (getElem_toArray_lt _ _)])
      (fun h => by simp_rw [smul_of_ge _ h])

instance : SMul (ArrayPerm n) (Fin n) where
  smul a i := ⟨a • i.val, a.lt_iff_smul_lt.mp i.isLt⟩

@[simp]
theorem coe_smul (a : ArrayPerm n) {i : Fin n} : (a • i : Fin n) = a • (i : ℕ) := rfl

instance : FaithfulSMul (ArrayPerm n) (Fin n) where
  eq_of_smul_eq_smul := by
    simp_rw [Fin.forall_iff, Fin.ext_iff, coe_smul]
    exact ext

instance : MulAction (ArrayPerm n) (Fin n) where
  one_smul _ := Fin.ext <| by rw [coe_smul, one_smul]
  mul_smul _ _ _ := Fin.ext <| by simp_rw [coe_smul, mul_smul]

theorem smul_nat_eq_dite_smul_fin (a : ArrayPerm n) (i : ℕ) :
    a • i = if h : i < n then ↑(a • (Fin.mk i h)) else i := by
  simp_rw [coe_smul, dite_eq_ite]
  symm
  simp_rw [ite_eq_left_iff, not_lt]
  exact fun h => (a.smul_of_ge h).symm

@[simp]
theorem smul_mk (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    ↑(a • (⟨i, hi⟩ : Fin n)) = a • i := by rw [coe_smul]

@[simps!]
def ofPerm (f : Perm ℕ) (hf : ∀ i, i < n ↔ f i < n) : ArrayPerm n where
  toArray := (Array.range n).map f
  invArray := (Array.range n).map ⇑f⁻¹
  getElem_toArray_lt' := fun {i} => by
    simp only [size_map, size_range, hf i, Array.getElem_map, Array.getElem_range, imp_self]
  getElem_invArray_lt' := fun {i} => by
    simp only [size_map, size_range, Array.getElem_map, Array.getElem_range,
    hf (f⁻¹ i), Perm.apply_inv_self, imp_self]
  size_toArray := by simp only [size_map, size_range]
  size_invArray := by simp only [size_map, size_range]
  getElem_invArray_getElem_toArray' := by
    simp only [size_map, size_range, Array.getElem_map, Array.getElem_range,
    Perm.inv_apply_self, implies_true]

@[simp]
theorem getElem_ofPerm_toArray {f : Perm ℕ} {hf : ∀ i, i < n ↔ f i < n} {i : ℕ}
    {hi : i < (ofPerm f hf).toArray.size} : (ofPerm f hf).toArray[i] = f i := by
  simp_rw [ofPerm_toArray, Array.getElem_map, Array.getElem_range]

@[simp]
theorem getElem_ofPerm_invArray {f : Perm ℕ} {hf : ∀ i, i < n ↔ f i < n} {i : ℕ}
    {hi : i < (ofPerm f hf).invArray.size} : (ofPerm f hf).invArray[i] = f⁻¹ i := by
  simp_rw [ofPerm_invArray, Array.getElem_map, Array.getElem_range]

@[simps!]
def natPerm : ArrayPerm n →* Perm ℕ where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  map_mul' a b := Equiv.ext fun _ => by
    simp only [mul_smul, mul_inv_rev, coe_fn_mk, Perm.coe_mul, comp_apply]
  map_one' := Equiv.ext fun _ => by
    simp only [one_smul, inv_one, coe_fn_mk, Perm.coe_one, id_eq]

theorem lt_iff_natPerm_lt (a : ArrayPerm n) (i : ℕ) : i < n ↔ natPerm a i < n := a.lt_iff_smul_lt

theorem natPerm_apply_apply_of_lt (a : ArrayPerm n) {i : ℕ} (h : i < n) :
    haveI := a.size_toArray; natPerm a i = a.toArray[i] := a.smul_of_lt h

theorem natPerm_apply_apply_of_ge (a : ArrayPerm n) {i : ℕ} (h : n ≤ i) : natPerm a i = i :=
  a.smul_of_ge h

theorem natPerm_apply_symm_apply_of_lt (a : ArrayPerm n) {i : ℕ} (h : i < n) :
    haveI := a.size_invArray; (natPerm a)⁻¹ i = a.invArray[i] := by
  simp_rw [← MonoidHom.map_inv, natPerm_apply_apply_of_lt _ h, inv_toArray]

theorem natPerm_apply_symm_apply_of_ge (a : ArrayPerm n) {i : ℕ} (h : n ≤ i) :
    (natPerm a)⁻¹ i = i := by rw [← MonoidHom.map_inv, natPerm_apply_apply_of_ge _ h]

theorem natPerm_inj {a b : ArrayPerm n} : natPerm a = natPerm b ↔ a = b := by
  simp_rw [Equiv.ext_iff, ext_iff']
  exact Iff.rfl

theorem natPerm_injective : Function.Injective (natPerm (n := n)) := fun _ _ => natPerm_inj.mp

theorem natPerm_ofPerm (f : Perm ℕ) (hf : ∀ i, i < n ↔ f i < n) (i : ℕ) :
    natPerm (ofPerm f hf) i = if i < n then f i else i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [natPerm_apply_apply_of_lt _ hi, getElem_ofPerm_toArray, hi, if_true]
  · simp_rw [natPerm_apply_apply_of_ge _ hi, hi.not_lt, if_false]

theorem ofPerm_natPerm (a : ArrayPerm n) :
    ofPerm (natPerm a) (a.lt_iff_natPerm_lt) = a := by
  ext i hi
  simp_rw [smul_of_lt _ hi, getElem_ofPerm_toArray, a.natPerm_apply_apply_of_lt hi]

theorem natPerm_range : MonoidHom.range (natPerm (n := n)) = {e : Perm ℕ | ∀ i ≥ n, i = e i} := by
  simp_rw [Set.ext_iff, MonoidHom.coe_range, Set.mem_range, ge_iff_le, Set.mem_setOf_eq]
  intros e
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨a, rfl⟩ i hi
    exact (a.natPerm_apply_apply_of_ge hi).symm
  · have H : ∀ i, i < n ↔ e i < n := fun i => by
      simp_rw [← not_le, not_iff_not]
      exact ⟨fun hi => (h _ hi) ▸ hi, fun hi => by rwa [e.injective (h _ hi)]⟩
    use ofPerm e H
    simp_rw [Equiv.ext_iff, natPerm_ofPerm e H, ite_eq_left_iff, not_lt]
    exact h

/--
`ArrayPerm n` is equivalent to `Perm (Fin n)`, and this equivalence respects the
multiplication (and, indeed, the scalar action on `Fin n`).
-/
def mulEquivPerm : ArrayPerm n ≃* Perm (Fin n) where
  toFun a := (Fin.equivSubtype.symm).permCongr ((natPerm a).subtypePerm a.lt_iff_natPerm_lt)
  invFun π := ofPerm (π.extendDomain Fin.equivSubtype) (lt_iff_extendDomain_equivSubtype_lt _)
  left_inv a := ext fun i h => by
    simp_rw [smul_of_lt _ h, getElem_ofPerm_toArray,
    Perm.extendDomain_apply_subtype _ equivSubtype h, permCongr_apply,
    equivSubtype_symm_apply, symm_symm, equivSubtype_apply, Perm.subtypePerm_apply,
    a.natPerm_apply_apply_of_lt h]
  right_inv π := Equiv.ext fun i => Fin.ext <| by
    simp only [permCongr_apply, symm_symm, equivSubtype_apply, Perm.subtypePerm_apply,
      natPerm_apply_apply_of_lt _ i.isLt, getElem_ofPerm_toArray,
      π.extendDomain_apply_subtype equivSubtype i.isLt, equivSubtype_symm_apply]
  map_mul' a b := Equiv.ext fun _ => by simp only [map_mul, permCongr_apply, symm_symm,
    equivSubtype_apply, Perm.subtypePerm_apply, Perm.coe_mul, comp_apply, equivSubtype_symm_apply]


@[simp]
theorem mulEquivPerm_apply_apply (a : ArrayPerm n) (i : Fin n) :
    (mulEquivPerm a) i = a • i := Fin.ext <| by
  unfold mulEquivPerm
  simp only [MulEquiv.coe_mk, coe_fn_mk, permCongr_apply, symm_symm, equivSubtype_apply,
    Perm.subtypePerm_apply, natPerm_apply_apply, equivSubtype_symm_apply, coe_smul]

@[simp]
theorem mulEquivPerm_inv_apply (a : ArrayPerm n) (i : Fin n) :
    (mulEquivPerm a)⁻¹ i = a⁻¹ • i := by
  simp_rw [← map_inv, mulEquivPerm_apply_apply]

theorem mulEquivPerm_symm_apply_toArray (π : Perm (Fin n)) :
    (mulEquivPerm.symm π).toArray = Array.ofFn (val ∘ π) := by
  unfold mulEquivPerm
  simp only [MulEquiv.symm_mk, MulEquiv.coe_mk, coe_fn_symm_mk, ofPerm_toArray]
  refine Array.ext _ _ (by simp only [size_map, size_range, size_ofFn]) ?_
  simp only [size_map, size_range, size_ofFn, Array.getElem_map, Array.getElem_range,
    Array.getElem_ofFn, comp_apply]
  intros i hi _
  simp only [Perm.extendDomain_apply_subtype _ equivSubtype hi,
    equivSubtype_symm_apply, equivSubtype_apply]

theorem mulEquivPerm_symm_apply_invArray (π : Perm (Fin n)) :
    (mulEquivPerm.symm π).invArray = Array.ofFn (val ∘ ⇑π⁻¹) := by
  rw [← inv_toArray, ← map_inv, mulEquivPerm_symm_apply_toArray]

theorem mulEquivPerm_symm_apply_getElem_toArray (π : Perm (Fin n)) {i : ℕ}
    {hi : i < (mulEquivPerm.symm π).toArray.size} :
    (mulEquivPerm.symm π).toArray[i] = π ⟨i, hi.trans_eq (size_toArray _)⟩ := by
  simp_rw [mulEquivPerm_symm_apply_toArray, Array.getElem_ofFn, comp_apply]

theorem mulEquivPerm_symm_apply_getElem_invArray (π : Perm (Fin n)) {i : ℕ}
    {hi : i < (mulEquivPerm.symm π).invArray.size} :
    (mulEquivPerm.symm π).invArray[i] = π⁻¹ ⟨i, hi.trans_eq (size_invArray _)⟩ := by
  simp_rw [mulEquivPerm_symm_apply_invArray, Array.getElem_ofFn, comp_apply]

@[simp]
theorem mulEquivPerm_smul (a : ArrayPerm n) (i : Fin n) :
  (mulEquivPerm a) • i = a • i := rfl

@[simp]
theorem mulEquivPerm_symm_smul (π : Perm (Fin n)) (i : Fin n) :
    (mulEquivPerm.symm π) • i = π • i := Fin.ext <| by
  simp_rw [coe_smul, Perm.smul_def, smul_nat_def,
  mulEquivPerm_symm_apply_getElem_toArray, i.isLt, dite_true]

@[simp]
theorem mulEquivPerm_symm_smul_nat (π : Perm (Fin n)) (i : ℕ) :
    (mulEquivPerm.symm π) • i = if h : i < n then ↑(π • (⟨i, h⟩ : Fin n)) else i := by
  simp_rw [smul_nat_eq_dite_smul_fin, mulEquivPerm_symm_smul]

/--
`ArrayPerm.cast` re-interprets an `ArrayPerm n` as an `ArrayPerm m`, where `n = m`.
-/
def cast (h : n = m) (a : ArrayPerm n) : ArrayPerm m where
  toArray := a.toArray
  invArray := a.invArray
  getElem_toArray_lt' := h ▸ a.getElem_toArray_lt'
  getElem_invArray_lt' := h ▸ a.getElem_invArray_lt'
  size_toArray := h ▸ a.size_toArray
  size_invArray := h ▸ a.size_invArray
  getElem_invArray_getElem_toArray' := fun _ => a.getElem_invArray_getElem_toArray _

@[simp]
theorem cast_toArray (h : n = m) (a : ArrayPerm n) :
    (a.cast h).toArray = a.toArray := rfl

@[simp]
theorem cast_invArray (h : n = m) (a : ArrayPerm n) :
    (a.cast h).invArray = a.invArray := rfl

@[simp]
theorem cast_smul (h : n = m) (a : ArrayPerm n) (i : ℕ) :
    (a.cast h) • i = a • i := by simp only [smul_nat_def, cast_toArray, h]

@[simp]
theorem cast_inv (h : n = m) (a : ArrayPerm n) :
    (a.cast h)⁻¹ = a⁻¹.cast h := rfl

@[simp]
theorem cast_mul (h : n = m) (a b : ArrayPerm n) : (a * b).cast h = a.cast h * b.cast h := rfl

/--
When `n = m`, `ArrayPerm n` is multiplicatively equivalent to `ArrayPerm m`.
-/

def arrayPermCongr (h : n = m) : ArrayPerm n ≃* ArrayPerm m where
  toFun := cast h
  invFun := cast h.symm
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem getElem_toArray_append_range_sub (a : ArrayPerm n) {i : ℕ}
    {h : i < (a.toArray ++ Array.map (fun x => x + n) (Array.range (m - n))).size} :
    haveI := a.size_toArray
    (a.toArray ++ (Array.range (m - n)).map ((· + n)))[i] = a • i := by
  rcases lt_or_le i n with hi | hi
  · rw [Array.get_append_left (hi.trans_eq a.size_toArray.symm), a.smul_of_lt hi]
  · simp_rw [Array.get_append_right (hi.trans_eq' a.size_toArray), size_toArray,
    Array.getElem_map, Array.getElem_range, Nat.sub_add_cancel hi, a.smul_of_ge hi]

theorem getElem_invArray_append_range_sub (a : ArrayPerm n) {i : ℕ}
    {h : i < (a.invArray ++ Array.map (fun x => x + n) (Array.range (m - n))).size} :
    haveI := a.size_invArray
    (a.invArray ++ (Array.range (m - n)).map ((· + n)))[i] = a⁻¹ • i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [Array.get_append_left (hi.trans_eq a.size_invArray.symm),
    (a⁻¹).smul_of_lt hi, inv_toArray]
  · simp_rw [Array.get_append_right (hi.trans_eq' a.size_invArray), size_invArray,
    Array.getElem_map, Array.getElem_range, Nat.sub_add_cancel hi, (a⁻¹).smul_of_ge hi]

/--
`ArrayPerm.castLE` re-interprets an `ArrayPerm n` as an `ArrayPerm m`, where `n ≤ m`.
-/
def castLE (h : n ≤ m) (a : ArrayPerm n) : ArrayPerm m where
  toArray := a.toArray ++ (Array.range (m - n)).map ((· + n))
  invArray := a.invArray ++ (Array.range (m - n)).map ((· + n))
  size_toArray := by
    simp only [size_append, a.size_toArray, size_map, size_range, h, Nat.add_sub_cancel']
  size_invArray := by
    simp only [size_append, a.size_invArray, size_map, size_range, h, Nat.add_sub_cancel']
  getElem_toArray_lt' := fun _ => by
    rw [getElem_toArray_append_range_sub, smul_nat_def]
    split_ifs with hin
    · exact (a.getElem_toArray_lt _).trans_le h
    · assumption
  getElem_invArray_lt' := fun _ => by
    rw [getElem_invArray_append_range_sub, smul_nat_def]
    split_ifs with hin
    · exact (a.getElem_invArray_lt _).trans_le h
    · assumption
  getElem_invArray_getElem_toArray' := fun {i} hi => by
    simp_rw [getElem_toArray_append_range_sub, getElem_invArray_append_range_sub, inv_smul_smul]

theorem castLE_toArray (a : ArrayPerm n) {h : n ≤ m} :
    (a.castLE h).toArray = a.toArray ++ (Array.range (m - n)).map ((· + n)) := rfl

theorem castLE_invArray (a : ArrayPerm n) {h : n ≤ m} :
    (a.castLE h).invArray = a.invArray ++ (Array.range (m - n)).map ((· + n)) := rfl

theorem getElem_castLE_toArray (a : ArrayPerm n) {h : n ≤ m} {i : ℕ}
    {hi : i < (a.castLE h).toArray.size} :
    (a.castLE h).toArray[i] = a • i := a.getElem_toArray_append_range_sub

theorem getElem_castLE_invArray (a : ArrayPerm n) {h : n ≤ m} {i : ℕ}
    {hi : i < (a.castLE h).invArray.size} :
    (a.castLE h).invArray[i] = a⁻¹ • i := a.getElem_invArray_append_range_sub

@[simp]
theorem castLE_smul (a : ArrayPerm n) {i : ℕ} {h : n ≤ m} :
    (a.castLE h) • i = a • i := by
  simp only [smul_nat_def, getElem_castLE_toArray, dite_eq_ite, ite_eq_left_iff, not_lt]
  intro hi
  simp_rw [(h.trans hi).not_lt, dite_false]

@[simp]
theorem castLE_inv (a : ArrayPerm n) {h : n ≤ m} :
    (a.castLE h)⁻¹ = a⁻¹.castLE h := rfl

theorem castLE_mul (a b : ArrayPerm n) (h : n ≤ m) :
    (a * b).castLE h = a.castLE h * b.castLE h := by
  ext i
  simp only [mul_smul, castLE_smul]

theorem castLE_inj {a b : ArrayPerm n} {h : n ≤ m} : castLE h a = castLE h b ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [ext_iff, castLE_smul]
  exact fun H _ hi => H _ (hi.trans_le h)

theorem castLE_injective (h : n ≤ m) : Function.Injective (castLE h) := fun _ _ => castLE_inj.mp

@[simp]
theorem castLE_one {h : n ≤ m} : ((1 : ArrayPerm n).castLE h) = 1 := by
  ext i : 1
  simp_rw [castLE_smul, one_smul]

def arrayPermMonoidHom (h : n ≤ m) : ArrayPerm n →* ArrayPerm m where
  toFun := castLE h
  map_mul' a b := a.castLE_mul b h
  map_one' := castLE_one

theorem arrayPermMonoidHom_injective {h : n ≤ m} :
  (⇑(arrayPermMonoidHom h)).Injective := castLE_injective h

theorem castLE_of_eq (h : n = m) (h' : n ≤ m := h.le) (a : ArrayPerm n) :
    a.castLE h' = a.cast h := by
  ext i : 1
  simp_rw [castLE_smul, cast_smul]

variable {α : Type*}

def onIndices (a : ArrayPerm n) (b : Array α) (hb : b.size = n) : Array α :=
    (Array.range n).attach.map
    (fun i => b[a • i.1]'((a.lt_iff_smul_lt.mp (mem_range_iff.mp i.2)).trans_eq hb.symm))

theorem size_onIndices (a : ArrayPerm n) {b : Array α} {hb : b.size = n} :
    size (a.onIndices b hb) = n := by
  unfold onIndices
  simp_rw [size_map, size_attach, size_range]

theorem getElem_onIndices (a : ArrayPerm n) (b : Array α) (hb : b.size = n) {i : ℕ}
    {hi : i < (a.onIndices b hb).size} :
    haveI := (a.lt_iff_smul_lt.mp (hi.trans_eq a.size_onIndices)).trans_eq hb.symm
    (a.onIndices b hb)[i] = b[a • i] := by
  unfold onIndices
  simp only [Array.getElem_map, Array.getElem_attach, Array.getElem_range]

def CycleMinAux (a : ArrayPerm n) : ℕ → ArrayPerm n × {a : Array ℕ // a.size = n}
  | 0 => ⟨1, range n, size_range⟩
  | 1 =>
    ⟨a, (Array.range n).zipWith a.toArray min, by
    rw [Array.size_zipWith, size_range, a.size_toArray, min_self]⟩
  | (i+2) =>
    have ⟨ρ, b, hb⟩ := a.CycleMinAux (i + 1);
    have ρ' := ρ ^ 2
    ⟨ρ', b.zipWith (ρ'.onIndices b hb) min,
    by simp_rw [Array.size_zipWith, hb, size_onIndices, min_self]⟩

def CycleMin (a : ArrayPerm n) (i : ℕ) : Array ℕ := (a.CycleMinAux i).2.1

@[simp]
theorem size_cycleMin (a : ArrayPerm n) (i : ℕ) : (a.CycleMin i).size = n := (a.CycleMinAux i).2.2

theorem cycleMinAux_succ_fst (a : ArrayPerm n) (i : ℕ) :
    (a.CycleMinAux (i + 1)).1 = a ^ (2 ^ i) := by
  induction' i with i IH
  · rw [pow_zero, pow_one]
    rfl
  · rw [pow_succ, pow_mul]
    exact IH ▸ rfl

theorem cycleMin_zero (a : ArrayPerm n) : a.CycleMin 0 = Array.range n := rfl

theorem cycleMin_one (a : ArrayPerm n) :
  a.CycleMin 1 = (Array.range n).zipWith a.toArray min := rfl

theorem cycleMin_succ_succ (a : ArrayPerm n) (i : ℕ) :
    (a.CycleMin (i + 2)) =
    (a.CycleMin (i + 1)).zipWith ((a ^ (2 ^ (i + 1))).onIndices
    (a.CycleMin (i + 1)) (a.size_cycleMin (i + 1))) min := by
  rw [← cycleMinAux_succ_fst]
  rfl

theorem getElem_cycleMin_zero (a : ArrayPerm n) (x : ℕ) (h : x < (a.CycleMin 0).size) :
    (a.CycleMin 0)[x] = x := by
  simp_rw [cycleMin_zero, Array.getElem_range]

@[simp]
lemma getElem_CycleMin_succ (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin (i + 1)).size) :
  haveI := a.size_cycleMin (i + 1)
  haveI := a.size_cycleMin i
  haveI := (a ^ 2^i).lt_iff_smul_lt (i := x)
  (a.CycleMin (i + 1))[x] = min (a.CycleMin i)[x] (a.CycleMin i)[(a ^ 2^i) • x] := by
  cases' i with i
  · simp_rw [zero_add, cycleMin_one, cycleMin_zero, Array.getElem_zipWith,
    Array.getElem_range, pow_zero, pow_one, a.smul_of_lt (h.trans_eq <| a.size_cycleMin 1)]
  · simp_rw [cycleMin_succ_succ, Array.getElem_zipWith, getElem_onIndices]

lemma cycleMin_le (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin i).size) :
    ∀ k < 2^i, (a.CycleMin i)[x] ≤ (a ^ k) • x := by
  induction' i with i IH generalizing x
  · simp_rw [pow_zero, Nat.lt_one_iff, getElem_cycleMin_zero, forall_eq, pow_zero, one_smul, le_rfl]
  · simp_rw [pow_succ', Nat.two_mul, getElem_CycleMin_succ, min_le_iff]
    intro k hk'
    rcases lt_or_le k (2^i) with hk | hk
    · exact Or.inl (IH _ _ _ hk)
    · rw [← Nat.sub_lt_iff_lt_add hk] at hk'
      convert Or.inr (IH _ _ _ hk') using 2
      rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hk]

lemma le_fastCycleMin (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin i).size) :
    ∀ z, (∀ k < 2^i, z ≤ (a ^ k) • x) → z ≤ (a.CycleMin i)[x] := by
  induction' i with i IH generalizing x
  · simp_rw [pow_zero, Nat.lt_one_iff, forall_eq, pow_zero, one_smul, getElem_cycleMin_zero,
    imp_self, implies_true]
  · simp_rw [getElem_CycleMin_succ, le_min_iff]
    intros z hz
    refine' ⟨_, _⟩
    · exact IH _ _ _ (fun _ hk => hz _ (hk.trans
        (Nat.pow_lt_pow_of_lt Nat.one_lt_two (Nat.lt_succ_self _))))
    · rw [pow_succ', Nat.two_mul] at hz
      refine' IH _ _ _ (fun _ hk => _)
      simp_rw [← mul_smul, ← pow_add]
      exact hz _ (Nat.add_lt_add_right hk _)

lemma exists_lt_fastCycleMin_eq_pow_apply (a : ArrayPerm n) (x : ℕ) (i : ℕ)
    (h : x < (a.CycleMin i).size) :
    ∃ k < 2^i, (a.CycleMin i)[x] = (a ^ k) • x := by
  induction' i with i IH generalizing x
  · simp_rw [getElem_cycleMin_zero]
    exact ⟨0, Nat.two_pow_pos _, pow_zero a ▸ (one_smul _ x).symm⟩
  · simp only [size_cycleMin] at IH h ⊢
    rcases (IH _ h) with ⟨k, hk, hπk⟩
    rcases (IH _ ((a ^ (2 ^ i)).lt_iff_smul_lt.mp h)) with ⟨k', hk', hπk'⟩
    simp_rw [getElem_CycleMin_succ, hπk, hπk', ← mul_smul, ← pow_add,
    pow_succ', Nat.two_mul]
    rcases lt_or_le ((a ^ k) • x) ((a ^ (k' + 2 ^ i)) • x) with hkk' | hkk'
    · rw [min_eq_left hkk'.le]
      exact ⟨k, hk.trans (Nat.lt_add_of_pos_right (Nat.two_pow_pos _)), rfl⟩
    · rw [min_eq_right hkk']
      exact ⟨k' + 2^i, Nat.add_lt_add_right hk' _, rfl⟩

/--
For `a` an `ArrayPerm n`, `a.swap hi hj` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : ArrayPerm n) {i j : ℕ} (hi : i < n) (hj : j < n) : ArrayPerm n where
  toArray := a.toArray.swapN i j (a.lt_size_toArray_of_lt hi) (a.lt_size_toArray_of_lt hj)
  invArray := a.invArray.map (fun k => Equiv.swap i j k)
  size_toArray := (Array.size_swap _ _ _).trans a.size_toArray
  size_invArray := (Array.size_map _ _).trans a.size_invArray
  getElem_toArray_lt' := fun _ => by
    simp_rw [a.toArray.getElem_swapN_eq_getElem_swap_apply, getElem_toArray_lt]
  getElem_invArray_lt' := fun _ => by
    simp_rw [Array.getElem_map]
    exact swap_prop (· < n) (a.getElem_invArray_lt _) hi hj
  getElem_invArray_getElem_toArray' := fun _ => by
    simp_rw [a.toArray.getElem_swapN_eq_getElem_swap_apply, Array.getElem_map,
    getElem_invArray_getElem_toArray, swap_apply_self]

variable (i j k : ℕ) (hi : i < n) (hj : j < n)

theorem swap_toArray (a : ArrayPerm n) : (a.swap hi hj).toArray =
a.toArray.swap ⟨i, hi.trans_eq a.size_toArray.symm⟩
    ⟨j, hj.trans_eq a.size_toArray.symm⟩ := rfl

theorem swap_invArray (a : ArrayPerm n)  : (a.swap hi hj).invArray =
a.invArray.map (fun k => Equiv.swap i j k) := rfl

theorem swap_smul (a : ArrayPerm n) : (a.swap hi hj) • k = a • (Equiv.swap i j k) := by
  rcases lt_or_ge k n with hk | hk
  · unfold swap
    simp_rw [smul_of_lt _ (swap_prop (· < n) hk hi hj), smul_of_lt _ hk,
    a.toArray.getElem_swapN_eq_getElem_swap_apply]
  · simp_rw [Equiv.swap_apply_of_ne_of_ne (hk.trans_lt' hi).ne' (hk.trans_lt' hj).ne',
      smul_of_ge _ hk]

theorem swap_inv_smul (a : ArrayPerm n) : (a.swap hi hj)⁻¹ • k =
    a⁻¹ • (Equiv.swap (a • i) (a • j) k) := by
  simp_rw [inv_smul_eq_iff, swap_smul, ← Equiv.swap_smul, smul_inv_smul, swap_apply_self]

@[simp]
theorem one_swap_smul : (swap 1 hi hj) • k = Equiv.swap i j k := by
  rw [swap_smul, one_smul]

theorem one_swap_inv_smul : (swap 1 hi hj)⁻¹ • k = Equiv.swap i j k := by
  simp_rw [swap_inv_smul, one_smul, inv_one, one_smul]

@[simp]
theorem one_swap_mul_self : swap 1 hi hj * swap 1 hi hj = 1 := by
  ext : 1
  simp_rw [mul_smul, one_swap_smul, swap_apply_self, one_smul]

@[simp]
theorem one_swap_inverse : (swap 1 hi hj)⁻¹ = swap 1 hi hj := by
  ext : 1
  rw [one_swap_smul, one_swap_inv_smul]

theorem swap_eq_mul_one_swap (a : ArrayPerm n) : a.swap hi hj = a * swap 1 hi hj := by
  ext : 1
  simp only [swap_smul, mul_smul, one_swap_smul, one_smul]

theorem natPerm_swap (a : ArrayPerm n) :
    natPerm (swap a hi hj) = natPerm a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, natPerm_apply_apply, swap_smul]

@[simp]
theorem natPerm_one_swap  :
    natPerm (swap 1 hi hj) = Equiv.swap i j := by simp_rw [natPerm_swap, map_one, one_mul]

theorem swap_eq_one_swap_mul (a : ArrayPerm n) (hi' : a • i < n := a.lt_iff_smul_lt.mp hi)
    (hj' : a • j < n := a.lt_iff_smul_lt.mp hj) :
    a.swap hi hj = swap 1 hi' hj' * a := by
  ext : 1
  simp_rw [mul_smul, one_swap_smul, swap_smul, Equiv.swap_smul]

theorem swap_smul' (a : ArrayPerm n) :
    (a.swap hi hj) • k = Equiv.swap (a • i) (a • j) (a • k) := by
  rw [swap_eq_one_swap_mul, mul_smul, one_swap_smul]

theorem swap_smul_left (a : ArrayPerm n) :
    (a.swap hi hj) • i = a • j := by rw [swap_smul, swap_apply_left]

theorem swap_smul_right (a : ArrayPerm n) :
  (a.swap hi hj) • j = a • i := by rw [swap_smul, swap_apply_right]

theorem swap_smul_of_ne_of_ne (a : ArrayPerm n) {k} :
  k ≠ i → k ≠ j → (a.swap hi hj) • k = a • k := by
  rw [swap_smul, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

theorem swap_inv_eq_one_swap_mul (a : ArrayPerm n) :
    (a.swap hi hj)⁻¹ = swap 1 hi hj * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (a : ArrayPerm n) (hi' : a • i < n := a.lt_iff_smul_lt.mp hi)
    (hj' : a • j < n := a.lt_iff_smul_lt.mp hj) :
    (a.swap hi hj)⁻¹ = a⁻¹ * swap 1 hi' hj' := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

theorem swap_inv_smul' (a : ArrayPerm n) :
  (a.swap hi hj)⁻¹ • k = Equiv.swap i j (a⁻¹ • k) := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, mul_smul, one_swap_inv_smul]

theorem swap_inv_smul_left (a : ArrayPerm n) :
    (a.swap hi hj)⁻¹ • (a • i) = j := by
  rw [swap_inv_smul, swap_apply_left, inv_smul_smul]

theorem swap_inbv_smul_right (a : ArrayPerm n) :
    (a.swap hi hj)⁻¹ • (a • j) = i := by
  rw [swap_inv_smul, swap_apply_right, inv_smul_smul]

theorem swap_inv_smul_of_ne_of_ne (a : ArrayPerm n) {k} :
  k ≠ a • i → k ≠ a • j → (a.swap hi hj)⁻¹ • k = a⁻¹ • k := by
  rw [swap_inv_smul, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (a : ArrayPerm n) (hi' : i < n) : a.swap hi hi' = a := by
  ext : 1
  rw [swap_smul, Equiv.swap_self, Equiv.refl_apply]

@[simp]
theorem swap_swap (a : ArrayPerm n) (hi' : i < n) (hj' : j < n) :
    (a.swap hi hj).swap hi' hj' = a := by
  ext : 1
  simp_rw [swap_smul, swap_apply_self]

end ArrayPerm

/-
section FlipPairs

open ArrayPerm Equiv List

def flipPairs (m : ℕ) (i : Fin (m + 1)) :=
    (List.finRange (2^m)).map fun k => (mergeBitRes i false k, mergeBitRes i true k)

variable {m : ℕ} {i : Fin (m + 1)}

lemma mem_flipPairs (k : BV m) : (mergeBitRes i false k, mergeBitRes i true k) ∈
    flipPairs m i := List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩

lemma eq_mbr_of_mem_flipPairs {b} (hb : b ∈ flipPairs m i) : b =
  (mergeBitRes i false (getRes i b.1), mergeBitRes i true (getRes i b.1)) := by
  simp_rw [flipPairs, mem_map, mem_finRange, true_and, Prod.ext_iff, mergeBitRes_eq_iff] at hb
  rcases hb with ⟨k, ⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  simp_rw [Prod.ext_iff, eq_mergeBitRes_iff, h₁, h₃, h₂, h₄, true_and]

lemma mem_flipPairs_iff {b} : b ∈ flipPairs m i ↔
    b.1 = mergeBitRes i false (getRes i b.1) ∧
    b.2 = mergeBitRes i true (getRes i b.1) :=
  ⟨ fun hb => Prod.ext_iff.mp (eq_mbr_of_mem_flipPairs hb),
    fun ⟨h₁, h₂⟩ => by rw [← Prod.eta b, h₁, h₂] ; exact mem_flipPairs _⟩

lemma flipPairs_length : (flipPairs m i).length = 2^m :=
  (List.length_map _ _).trans (List.length_finRange _)

lemma flipPairs_get (t : Fin (flipPairs m i).length) :
  (flipPairs m i).get t = (mergeBitRes i false (t.cast flipPairs_length),
  mergeBitRes i true (t.cast flipPairs_length)) := by
  unfold flipPairs
  simp_rw [List.get_map, List.get_finRange, Prod.ext_iff, mergeBitRes_inj_iff, Fin.ext_iff,
    Fin.coe_cast, true_and]

lemma flipPairs_nodup : (flipPairs m i).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro t t'
  simp_rw [flipPairs_get, Prod.ext_iff, mergeBitRes_inj_iff, Fin.ext_iff, Fin.coe_cast, true_and,
  and_imp, imp_self, implies_true]

lemma ne_ne_ne_ne_of_mem_flipPairs_mem_flipPairs {b b'} (hb : b ∈ flipPairs m i)
    (hb' : b' ∈ flipPairs m i) (hbb' : b ≠ b') :
  b.1 ≠ b'.1 ∧ b.1 ≠ b'.2 ∧ b.2 ≠ b'.1 ∧ b.2 ≠ b'.2 := by
  simp_rw [mem_flipPairs_iff] at hb hb'
  simp_rw [Prod.ext_iff.not, not_and_or] at hbb'
  rw [hb.1, hb.2, hb'.1, hb'.2] at hbb' ⊢
  simp_rw [(mergeBitRes_inj_iff i).not, not_and_or, not_true_eq_false, not_false_eq_true,
  true_or, false_or, true_and, and_self]
  exact fun h => by simp_rw [h, not_true, or_false] at hbb'

lemma mergeBitRes_true_ne_fst_of_mem_flipPairs {b} (hb : b ∈ flipPairs m i) {k} :
    mergeBitRes i true k ≠ b.1 := by
  simp_rw [mem_flipPairs_iff] at hb
  rw [hb.1, mergeBitRes_ne_inj_iff]
  exact Or.inl (Bool.false_ne_true.symm)

lemma mergeBitRes_not_bit_get_val_ne_snd_of_mem_flipPairs {b} (hb : b ∈ flipPairs m i) {k} :
    mergeBitRes i false k ≠ b.2 := by
  simp_rw [mem_flipPairs_iff] at hb
  simp_rw [hb.2, mergeBitRes_ne_inj_iff]
  exact Or.inl Bool.false_ne_true

lemma swaps_flipPairs_apply_mergeBitRes_false {k : BV m} :
    swaps (flipPairs m i) (mergeBitRes i false k) = mergeBitRes i true k :=
  (swaps_apply_eq_swap_of_nodup_of_norep (flipPairs m i) flipPairs_nodup
    ne_ne_ne_ne_of_mem_flipPairs_mem_flipPairs _ (mem_flipPairs k)).1

lemma swaps_flipPairs_apply_mergeBitRes_true {k : BV m} :
    swaps (flipPairs m i) (mergeBitRes i true k) = mergeBitRes i false k :=
  (swaps_apply_eq_swap_of_nodup_of_norep (flipPairs m i) flipPairs_nodup
    ne_ne_ne_ne_of_mem_flipPairs_mem_flipPairs _ (mem_flipPairs k)).2

lemma swaps_flipPairs_eq_flipBit_get :
  swaps (flipPairs m i) = flipBit i := by
  ext q : 1
  rcases mergeBitRes_surj i q with ⟨b, p, rfl⟩
  simp_rw [flipBit_mergeBitRes]
  cases b
  · rw [swaps_flipPairs_apply_mergeBitRes_false, Bool.not_false]
  · rw [swaps_flipPairs_apply_mergeBitRes_true, Bool.not_true]

abbrev ArrayPerm.flipBit (i : Fin (m + 1)) := swaps 1 (flipPairs m i)

lemma flipPairs_swaps_apply (q : BV (m + 1)) :
    ArrayPerm.flipBit i • q = flipBit i q := by
  simp_rw [one_swaps_smul, swaps_flipPairs_eq_flipBit_get]

lemma mulEquivPerm_swaps_flipPairs :
    ArrayPerm.mulEquivPerm (ArrayPerm.flipBit i) = _root_.flipBit i := by
  ext : 1
  simp_rw [mulEquivPerm_apply_apply, flipPairs_swaps_apply]

end FlipPairs

section CondPairs

open ArrayPerm Equiv List

def condPairs (m : ℕ) (i : Fin (m + 1)) (bs : Array Bool) (hbs : bs.size = 2^m) :=
    (List.finRange (2^m)).map fun k => (mergeBitRes i false k, mergeBitRes i bs[k.val] k)

variable {m : ℕ} {i : Fin (m + 1)} {bs : Array Bool} {hbs : bs.size = 2^m}

lemma mem_condPairs (k : BV m) : (mergeBitRes i false k, mergeBitRes i bs[k.val] k) ∈
    condPairs m i bs hbs := List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩

lemma eq_mbr_of_mem_condPairs {b} (hb : b ∈ condPairs m i bs hbs) : b =
  (mergeBitRes i false (getRes i b.1), mergeBitRes i bs[(getRes i b.1).val] (getRes i b.1)) := by
  simp_rw [condPairs, mem_map, mem_finRange, true_and, Prod.ext_iff, mergeBitRes_eq_iff] at hb
  rcases hb with ⟨k, ⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
  simp_rw [Prod.ext_iff, eq_mergeBitRes_iff, h₁, h₃, h₂, h₄, true_and]

lemma mem_condPairs_iff {b} : b ∈ condPairs m i bs hbs ↔
    b.1 = mergeBitRes i false (getRes i b.1) ∧
    b.2 = mergeBitRes i bs[(getRes i b.1).val] (getRes i b.1) :=
  ⟨ fun hb => Prod.ext_iff.mp (eq_mbr_of_mem_condPairs hb),
    fun ⟨h₁, h₂⟩ => by rw [← Prod.eta b, h₁, h₂] ; exact mem_condPairs _⟩

lemma condPairs_length : (condPairs m i bs hbs).length = 2^m :=
  (List.length_map _ _).trans (List.length_finRange _)

lemma condPairs_get (t : Fin (condPairs m i bs hbs).length) :
  (condPairs m i bs hbs).get t = (mergeBitRes i false (t.cast condPairs_length),
  mergeBitRes i bs[(t.cast condPairs_length).val] (t.cast condPairs_length)) := by
  unfold condPairs
  simp_rw [List.get_map, List.get_finRange, Prod.ext_iff, mergeBitRes_inj_iff, Fin.ext_iff,
    Fin.coe_cast, true_and]

lemma condPairs_nodup : (condPairs m i bs hbs).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro t t'
  simp_rw [condPairs_get, Prod.ext_iff, mergeBitRes_inj_iff, Fin.ext_iff, Fin.coe_cast, true_and,
  and_imp, imp_self, implies_true]

lemma ne_ne_ne_ne_of_mem_condPairs_mem_condPairs {b b'} (hb : b ∈ condPairs m i bs hbs)
    (hb' : b' ∈ condPairs m i bs hbs) (hbb' : b ≠ b') :
  b.1 ≠ b'.1 ∧ b.1 ≠ b'.2 ∧ b.2 ≠ b'.1 ∧ b.2 ≠ b'.2 := by
  simp_rw [mem_condPairs_iff] at hb hb'
  simp_rw [Prod.ext_iff.not, not_and_or] at hbb'
  rw [hb.1, hb.2, hb'.1, hb'.2] at hbb' ⊢
  simp_rw [(mergeBitRes_inj_iff i).not, true_and, not_and_or]
  have h : ¬getRes i b.1 = getRes i b'.1 := fun h => by simp_rw [h, not_true, or_false] at hbb'
  exact ⟨h, Or.inr h, Or.inr h, Or.inr h⟩

lemma mergeBitRes_true_ne_fst_of_mem_condPairs {b} (hb : b ∈ condPairs m i bs hbs) {k} :
    mergeBitRes i true k ≠ b.1 := by
  simp_rw [mem_condPairs_iff] at hb
  rw [hb.1, mergeBitRes_ne_inj_iff]
  exact Or.inl (Bool.false_ne_true.symm)

lemma mergeBitRes_not_bit_get_val_ne_snd_of_mem_condPairs {b} (hb : b ∈ condPairs m i bs hbs) {k} :
    mergeBitRes i (!bs[k.val]) k ≠ b.2 := by
  simp_rw [mem_condPairs_iff] at hb
  rw [hb.2, mergeBitRes_ne_inj_iff]
  exact or_not_of_imp (fun h => h ▸ Bool.not_ne_self _)

lemma mergeBitRes_true_ne_snd_of_mem_condPairs_of_bit_get_val_false {k} (h : bs[k.val] = false) {b}
    (hb : b ∈ condPairs m i bs hbs) : mergeBitRes i true k ≠ b.2 := by
  rw [← Bool.not_false, ←h]
  exact mergeBitRes_not_bit_get_val_ne_snd_of_mem_condPairs hb

lemma swaps_condPairs_apply_mergeBitRes_false {k : BV m} :
    swaps (condPairs m i bs hbs) (mergeBitRes i false k) = mergeBitRes i bs[k.val] k :=
  (swaps_apply_eq_swap_of_nodup_of_norep (condPairs m i bs hbs) condPairs_nodup
    ne_ne_ne_ne_of_mem_condPairs_mem_condPairs _ (mem_condPairs k)).1

lemma swaps_condPairs_apply_mergeBitRes_bit_get_val {k : BV m} :
    swaps (condPairs m i bs hbs) (mergeBitRes i bs[k.val] k) = mergeBitRes i false k :=
  (swaps_apply_eq_swap_of_nodup_of_norep (condPairs m i bs hbs) condPairs_nodup
    ne_ne_ne_ne_of_mem_condPairs_mem_condPairs _ (mem_condPairs k)).2

lemma swaps_condPairs_apply_mergeBitRes_true {k : BV m} :
    swaps (condPairs m i bs hbs) (mergeBitRes i true k) = mergeBitRes i (!bs[k.val]) k := by
  rcases h : bs[k.val] with (_ | _)
  · exact swaps_apply_of_ne _ _ (fun b hb =>
      ⟨mergeBitRes_true_ne_fst_of_mem_condPairs hb,
      mergeBitRes_true_ne_snd_of_mem_condPairs_of_bit_get_val_false h hb⟩)
  · rw [←h, swaps_condPairs_apply_mergeBitRes_bit_get_val, h, Bool.not_true]

lemma swaps_condPairs_eq_condFlipBit_get :
  swaps (condPairs m i bs hbs) = condFlipBit i fun k => bs[k.val] := by
  ext q : 1
  rcases mergeBitRes_surj i q with ⟨b, p, rfl⟩
  simp_rw [condFlipBit_mergeBitRes]
  cases b
  · rw [swaps_condPairs_apply_mergeBitRes_false, Bool.xor_false]
  · rw [swaps_condPairs_apply_mergeBitRes_true, Bool.xor_true]

lemma condPairs_swaps_apply (q : BV (m + 1)) :
    swaps 1 (condPairs m i bs hbs) • q = condFlipBit i (fun k => bs[k.val]) q := by
  simp_rw [one_swaps_smul, swaps_condPairs_eq_condFlipBit_get]

lemma mulEquivPerm_swaps_condPairs :  ArrayPerm.mulEquivPerm (swaps 1 (condPairs m i bs hbs)) =
    condFlipBit i (fun k => bs[k.val]) := by
  ext : 1
  simp_rw [mulEquivPerm_apply_apply, condPairs_swaps_apply]

end CondPairs

/-


def condPairs' (m : ℕ) (i : Fin (m + 1)) (bs : Array Bool) (hbs : bs.size = 2^m) :
    List (BV (m + 1) × BV (m + 1)) :=
  match m with
  | 0 => [(0, bif bs[0] then 1 else 0)]
  | m + 1 => _



lemma condPairs_base (i : Fin 1) (bs : Array Bool) (hbs : bs.size = 1) :
    condPairs 0 i bs hbs = [((0 : BV 1), bif bs[0] then 1 else 0)] := by
  simp_rw [condPairs, Nat.pow_zero, Fin.fin_one_eq_zero, Bool.cond_eq_ite, Fin.list_succ,
    Fin.list_zero, List.map_cons, List.map_nil, mergeBitRes_base, if_false, Fin.coe_fin_one]

  ·
def condFlipBit' (m : ℕ) (i : Fin (m + 1)) (bs : Array Bool) (hbs : bs.size = 2^m) :=
    swaps 1 <| (Fin.list (2^m)).map fun k =>
    (mergeBitRes i false k, mergeBitRes i (bs.get (k.cast hbs.symm)) k)
-/
/-
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (condFlipBit (1 : Fin 3) (#[false, true, false, true].get ∘ Fin.cast rfl))
#eval [0, 1, 2, 3, 4, 5, 6, 7].map (mulEquivPerm (condFlipBit' 3 1 (#[false, true, false, true]) rfl))

-/-/
