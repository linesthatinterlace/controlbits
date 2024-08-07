import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.Indexes
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.GroupAction.Period
import Batteries.Data.Array.Lemmas

set_option autoImplicit false

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
    Set.InjOn (fun k => a ^ k • x) (Finset.range ((MulAction.period a x))) := by
  intro i hi j hj ha
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj ha
  by_contra hij'
  wlog hij : i < j with H
  · exact (H a ha.symm hj hi (Ne.symm hij') ((Ne.symm hij').lt_of_le (le_of_not_lt hij)))
  · rw [← inv_smul_eq_iff, ← mul_smul, ← inv_pow_sub _ hij.le, inv_pow, inv_smul_eq_iff] at ha
    exact (lt_irrefl (period a x)) ((MulAction.period_le_of_fixed (Nat.sub_pos_of_lt hij)
      ha.symm).trans_lt ((Nat.sub_le _ _).trans_lt hj))

end MulAction

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


namespace Equiv

open List Function Fin Prod

variable {α : Type*} [DecidableEq α]

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

namespace Perm

variable {α β : Type*} {p : α → Prop} [DecidablePred p] {a : α} {f : Equiv.Perm α}

theorem ofSubtype_apply (f : Equiv.Perm (Subtype p)) :
  (ofSubtype f) a = if ha : p a then (f ⟨a, ha⟩ : α) else a := by
  split_ifs with ha
  · exact Equiv.Perm.ofSubtype_apply_of_mem _ _
  · exact Equiv.Perm.ofSubtype_apply_of_not_mem _ ha

theorem ofSubtype_subtypePerm_apply (h : ∀ (x : α), p x ↔ p (f x)) :
    ofSubtype (f.subtypePerm h) a = if p a then f a else a := by
  simp_rw [ofSubtype_apply, subtypePerm_apply, dite_eq_ite]

theorem subtype_extendDomain_equivSubtype_iff_subtype (e : Equiv.Perm β) (f : β ≃ Subtype p) :
    p ((e.extendDomain f) a) ↔ p a := by
  by_cases ha : p a
  · simp_rw [ha, iff_true, extendDomain_apply_subtype _ _ ha, Subtype.prop]
  · simp_rw [ha, extendDomain_apply_not_subtype _ _ ha, ha]

end Perm

end Equiv

namespace Fin

theorem extendDomain_equivSubtype_lt_iff_lt {n : ℕ} (π : Equiv.Perm (Fin n)) (i : ℕ) :
    (π.extendDomain equivSubtype) i < n ↔ i < n :=
  Equiv.Perm.subtype_extendDomain_equivSubtype_iff_subtype π equivSubtype

open Prod

@[simp] theorem cast_comp {n m k : ℕ} (h : n = m) (h' : m = k) :
    cast h' ∘ cast h = cast (Eq.trans h h') := rfl

theorem mk_eq_iff_val_eq {n : ℕ} {a : Fin n} {k : ℕ} {hk : k < n} :
    ⟨k, hk⟩ = a ↔ k = (a : Nat) := by rw [Fin.ext_iff]

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

namespace Array

open Equiv Function List Fin

variable {α β γ : Type*}

theorem ext_iff (a : Array α) (b : Array α) : a = b ↔
    (a.size = b.size) ∧ (∀ (i : ℕ) (hi₁ : i < a.size) (hi₂ : i < b.size), a[i] = b[i]) :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ _ => rfl⟩, fun h => Array.ext _ _ h.1 h.2⟩

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
/--
`Array α` is equivalent to the sigma-type of tuples over `α`.
-/
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
theorem getElem_zipWithIndex {as : Array α} {i : ℕ}
    (h : i < (as.zipWithIndex).size) :
    (as.zipWithIndex)[i] = (as[i]'(h.trans_eq as.size_zipWithIndex), i) := by
  unfold zipWithIndex
  simp_rw [Array.getElem_mapIdx]

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

theorem size_nil : (#[] : Array α).size = 0 := rfl

theorem getElem_shrink_loop {as : Array α} {n x : ℕ} (h : x < (shrink.loop n as).size) :
    (shrink.loop n as)[x] = as[x]'
    (h.trans_le ((as.size_shrink_loop n).trans_le (Nat.sub_le _ _))) := by
  induction' n with n IH generalizing as
  · rfl
  · exact (IH _).trans (as.getElem_pop x _)

@[simp]
theorem getElem_shrink {as : Array α} {n x : ℕ} (h : x < (as.shrink n).size) :
    (as.shrink n)[x] = as[x]'(h.trans_le ((as.size_shrink n).trans_le (min_le_left _ _))) :=
  getElem_shrink_loop _

@[simp]
theorem shrink_size_self {as : Array α} :
    as.shrink as.size = as := by
  simp_rw [Array.ext_iff, size_shrink, min_self, getElem_shrink, implies_true, and_self]

@[simp]
theorem size_unzip_fst {as : Array (α × β)} : (unzip as).1.size = as.size := by
  refine Array.foldl_induction (fun k (abs : Array α × Array β) => abs.1.size = k) size_nil ?_
  simp_rw [size_push, add_left_inj, imp_self, implies_true]

@[simp]
theorem size_unzip_snd {as : Array (α × β)} : (unzip as).2.size = as.size := by
  refine Array.foldl_induction (fun k (abs : Array α × Array β) => abs.2.size = k) size_nil ?_
  simp_rw [size_push, add_left_inj, imp_self, implies_true]

@[simp]
theorem getElem_unzip_fst {as : Array (α × β)} {x : ℕ} (h : x < (unzip as).1.size) :
    (unzip as).1[x] = (as[x]'(h.trans_eq size_unzip_fst)).1 := by
  refine (Array.foldl_induction (fun (k : ℕ) (abs : Array α × Array β) =>
    ∀ (hk : k ≤ as.size) x (h : x < k) (hk' : abs.1.size = k), abs.1[x] = (as[x]'(h.trans_le hk)).1)
    ?_ ?_) le_rfl x (h.trans_eq size_unzip_fst) size_unzip_fst
  · simp_rw [size_nil, Nat.not_lt_zero, forall_false, implies_true]
  · simp_rw [get_eq_getElem, size_push, add_left_inj, Nat.add_one_le_iff, is_le', is_lt,
    forall_true_left, get_push, Nat.lt_succ_iff, le_iff_lt_or_eq, Prod.forall]
    rintro _ _ _ h _ (hi | rfl) ha
    · simp_rw [ha, hi, dite_true]
      exact h _ hi ha
    · simp_rw [ha, lt_irrefl, dite_false]

@[simp]
theorem getElem_unzip_snd {as : Array (α × β)} {x : ℕ} (h : x < (unzip as).2.size) :
    (unzip as).2[x] = (as[x]'(h.trans_eq size_unzip_snd)).2 := by
  refine (Array.foldl_induction (fun (k : ℕ) (abs : Array α × Array β) =>
    ∀ (hk : k ≤ as.size) x (h : x < k) (hk' : abs.2.size = k), abs.2[x] = (as[x]'(h.trans_le hk)).2)
    ?_ ?_) le_rfl x (h.trans_eq size_unzip_snd) size_unzip_snd
  · simp_rw [size_nil, Nat.not_lt_zero, forall_false, implies_true]
  · simp_rw [get_eq_getElem, size_push, add_left_inj, Nat.add_one_le_iff, is_le', is_lt,
    forall_true_left, get_push, Nat.lt_succ_iff, le_iff_lt_or_eq, Prod.forall]
    rintro _ _ _ h _ (hi | rfl) ha
    · simp_rw [ha, hi, dite_true]
      exact h _ hi ha
    · simp_rw [ha, lt_irrefl, dite_false]

theorem zip_unzip {as : Array (α × β)} : zip as.unzip.fst as.unzip.snd = as := by
  simp_rw [Array.ext_iff, size_zip, size_unzip_fst, size_unzip_snd, min_self,
  getElem_zip, getElem_unzip_fst, getElem_unzip_snd, implies_true, and_self]

theorem unzip_zip {as : Array α} {bs : Array β} :
  (zip as bs).unzip = (as.shrink (min as.size bs.size), bs.shrink (min as.size bs.size)) := by
  simp_rw [Prod.ext_iff, Array.ext_iff, size_unzip_fst, size_unzip_snd, size_zip, size_shrink,
  min_comm _ bs.size, min_left_comm _ bs.size, min_self,
  min_comm _ as.size, min_left_comm _ as.size, min_self,
  getElem_unzip_fst, getElem_unzip_snd, getElem_zip, getElem_shrink, implies_true, and_self]

theorem unzip_zip_of_le {as : Array α} {bs : Array β} (h : as.size ≤ bs.size) :
  (zip as bs).unzip = (as, bs.shrink as.size) := by
  simp_rw [unzip_zip, min_eq_left h, shrink_size_self]

theorem unzip_zip_of_ge {as : Array α} {bs : Array β} (h : bs.size ≤ as.size) :
  (zip as bs).unzip = (as.shrink bs.size, bs) := by
  simp_rw [unzip_zip, min_eq_right h, shrink_size_self]

theorem unzip_zip_of_eq {as : Array α} {bs : Array β} (h : as.size = bs.size) :
  (zip as bs).unzip = (as, bs) := by
  simp_rw [unzip_zip_of_le h.le, h, shrink_size_self]

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

theorem getElem_swap!_eq_getElem_swap_apply {as : Array α} {i j k : ℕ} (hi : i < as.size)
    (hj : j < as.size) (hk : k < (as.swap! i j).size) :
    (as.swap! i j)[k] =
    as[Equiv.swap i j k]'(swap_prop (· < as.size) (hk.trans_eq <| as.size_swap! _ _) hi hj) := by
  simp_rw [getElem_swap!, hi, hj, and_true, swap_apply_def]
  split_ifs <;> rfl

@[simp]
theorem getElem_swap!_of_eq {as : Array α} {i k : ℕ} (hk : k < (as.swap! i i).size) :
    (as.swap! i i)[k] = as[k]'(hk.trans_eq <| as.size_swap! _ _) := by
  simp_rw [getElem_swap!]
  split_ifs with h
  · simp_rw [h.1]
  · rfl

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
  refine ext _ _ ?_ (fun k  hk hk' => ?_)
  · simp_rw [size_swap, ha]
  · simp_rw [get_swap', getElem_fin, ha, hi, hj]

@[simp]
theorem swap_self (a : Array α) {i : Fin a.size} : a.swap i i = a := by
  refine ext _ _ (a.size_swap i i) (fun j  _ hj => ?_)
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

theorem size_uncurry_swap (a : Array α) (x : Fin a.size × Fin a.size) :
    (uncurry a.swap x).size = a.size := size_swap _ _ _

theorem uncurry_swap_apply (a : Array α) (x : Fin a.size × Fin a.size) :
    uncurry a.swap x = a.swap x.1 x.2 := rfl

theorem uncurry_swap_congr (a a' : Array α) {x : Fin a.size × Fin a.size}
    {y : Fin a'.size × Fin a'.size} : a = a' → x.1.val = y.1.val → x.2.val = y.2.val →
    uncurry a.swap x = uncurry a'.swap y := swap_congr _ _

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
  protected size_toArray' : toArray.size = n := by rfl
  protected size_invArray' : invArray.size = n := by rfl
  protected getElem_toArray_lt' :
    ∀ {i : ℕ} (hi : i < n), toArray[i]'(hi.trans_eq size_toArray'.symm) < n := by decide
  protected getElem_invArray_lt' :
  ∀ {i : ℕ} (hi : i < n), invArray[i]'(hi.trans_eq size_invArray'.symm) < n := by decide
  protected left_inv' : ∀ {i : ℕ} (hi : i < n),
      invArray[toArray[i]'(hi.trans_eq size_toArray'.symm)]'
      ((getElem_toArray_lt' hi).trans_eq size_invArray'.symm) = i :=
    by decide

namespace ArrayPerm

open Function Fin Equiv List Array

variable {n : ℕ}

instance : Repr (ArrayPerm n) where
  reprPrec a _ := "ArrayPerm" ++ " : " ++ repr a.toArray

instance : ToString (ArrayPerm n) where
  toString a := "ArrayPerm" ++ " : " ++ toString a.toArray

@[simp]
lemma size_toArray (a : ArrayPerm n) : a.toArray.size = n := a.size_toArray'

@[simp]
lemma size_invArray (a : ArrayPerm n) : a.invArray.size = n := a.size_invArray'

instance : GetElem (ArrayPerm n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.toArray[i]'(h.trans_eq a.size_toArray.symm)

@[simp]
theorem getElem_lt {a : ArrayPerm n} {i : ℕ} {hi : i < n} : a[i] < n :=
  a.getElem_toArray_lt' hi

@[simp]
theorem getElem_toArray {a : ArrayPerm n} {i : ℕ} {hi : i < a.toArray.size} :
  a.toArray[i] = a[i]'(hi.trans_eq a.size_toArray) := rfl

@[simp]
theorem getElem_mk (a a' : Array ℕ) {sta sia getl geil geiageta} {i : ℕ} (hi : i < n) :
  (ArrayPerm.mk a a' sta sia getl geil geiageta)[i] = a[i]'(hi.trans_eq sta.symm) := rfl

instance : Inv (ArrayPerm n) where
  inv a := {
    toArray := a.invArray
    invArray := a.toArray
    size_toArray' := a.size_invArray
    size_invArray' := a.size_toArray
    getElem_toArray_lt' := a.getElem_invArray_lt'
    getElem_invArray_lt' := a.getElem_toArray_lt'
    left_inv' := fun hi => by
      rw [getElem_toArray]
      have H : Injective (fun (i : Fin n) => Fin.mk
      (a.invArray[i.1]'(i.isLt.trans_eq a.size_invArray.symm)) (a.getElem_invArray_lt' i.isLt)) :=
        Surjective.injective_of_fintype (Equiv.refl _)
        (fun i => ⟨⟨a[i.1], getElem_lt⟩, Fin.ext <| a.left_inv' i.isLt⟩)
      unfold Injective at H
      simp_rw [Fin.forall_iff, Fin.ext_iff] at H
      exact H _ getElem_lt _ hi (a.left_inv' <| a.getElem_invArray_lt' hi)}


@[simp]
theorem getElem_inv_getElem (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    a⁻¹[a[i]]'getElem_lt = i := a.left_inv' hi

@[simp]
theorem getElem_getElem_inv (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
  a[a⁻¹[i]]'getElem_lt = i := (a⁻¹).left_inv' hi

@[simp]
theorem getElem_invArray {a : ArrayPerm n} {i : ℕ} {hi : i < a.invArray.size} :
  a.invArray[i] = a⁻¹[i]'(hi.trans_eq a.size_invArray) := rfl

@[simp]
theorem getElem_inv_mk (a a' : Array ℕ) {sta sia getl geil geiageta} {i : ℕ} (hi : i < n) :
  (ArrayPerm.mk a a' sta sia getl geil geiageta)⁻¹[i] = a'[i]'(hi.trans_eq sia.symm) := rfl

theorem getElem_injective (a : ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n)
    (hij : a[i] = a[j]) : i = j := (a.getElem_inv_getElem hi).symm.trans
    (by simp_rw [hij, a.getElem_inv_getElem])

theorem getElem_inj (a : ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff (a : ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i :=
  ⟨a⁻¹[i], getElem_lt, a.getElem_getElem_inv _⟩

theorem eq_getElem_inv_iff (a: ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by
  rw [← (a⁻¹).getElem_inj (getElem_lt) hj, getElem_inv_getElem]

theorem getElem_inv_eq_iff (a: ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by
  rw [← a.getElem_inj (getElem_lt) hj, getElem_getElem_inv]

theorem ne_getElem_inv_iff (a: ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := (a.eq_getElem_inv_iff _ _).ne

theorem getElem_inv_ne_iff (a: ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := (a.getElem_inv_eq_iff _ _).ne

theorem toArray_eq_iff_forall_getElem_eq (a b : ArrayPerm n) :
    a.toArray = b.toArray ↔ ∀ i (hi : i < n), a[i] = b[i] := by
  simp_rw [ext_iff, a.size_toArray, b.size_toArray, getElem_toArray, true_and]
  exact ⟨fun h _ hi => h _ hi hi, fun h => fun _ _ => h _⟩

theorem invArray_eq_iff_forall_getElem_eq (a b : ArrayPerm n) :
    a.invArray = b.invArray ↔ ∀ i (hi : i < n), a⁻¹[i] = b⁻¹[i] :=
  toArray_eq_iff_forall_getElem_eq a⁻¹ b⁻¹

@[ext]
theorem ext {a b : ArrayPerm n} (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.toArray = b.toArray ∧ a.invArray = b.invArray by
    · rcases a ; rcases b ; simp_rw [mk.injEq]
      exact h
  simp_rw [toArray_eq_iff_forall_getElem_eq, h,
    invArray_eq_iff_forall_getElem_eq, implies_true, true_and]
  refine fun _ _ => a.getElem_injective getElem_lt getElem_lt ?_
  simp_rw [getElem_getElem_inv, h, getElem_getElem_inv]

instance : SMul (ArrayPerm n) ℕ where
  smul a i := if h : i < n then a[i]'h else i

theorem smul_nat_def (a : ArrayPerm n) (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i := rfl

theorem smul_of_lt {a : ArrayPerm n} {i : ℕ} (h : i < n) : a • i = a[i] := dif_pos h

theorem smul_of_ge {a : ArrayPerm n} {i : ℕ} (h : n ≤ i) : a • i = i := dif_neg (not_lt_of_le h)

@[simp]
theorem smul_getElem {a b : ArrayPerm n} {i : ℕ} (h : i < n) : a • b[i] = a[b[i]] := smul_of_lt _

theorem smul_lt_iff_lt (a : ArrayPerm n) {i : ℕ} : a • i < n ↔ i < n := by
  rcases lt_or_le i n with h | h
  · simp_rw [h, iff_true, smul_of_lt h]
    apply a.getElem_lt
  · simp_rw [h.not_lt, iff_false, smul_of_ge h]
    exact h.not_lt

theorem smul_lt_of_lt (a : ArrayPerm n) {i : ℕ} (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

instance : FaithfulSMul (ArrayPerm n) ℕ where
  eq_of_smul_eq_smul := fun h => ArrayPerm.ext <| fun i hi => by
    specialize h i
    simp_rw [smul_of_lt hi] at h
    exact h

theorem eq_iff_smul_eq_smul {a b : ArrayPerm n} : a = b ↔ ∀ i : ℕ, a • i = b • i :=
  ⟨fun h _ => h ▸ rfl, eq_of_smul_eq_smul⟩

theorem eq_of_smul_eq_smul_lt {a b : ArrayPerm n} (h : ∀ i < n, a • i = b • i) : a = b := by
  apply eq_of_smul_eq_smul (α := ℕ)
  intros i
  rcases lt_or_le i n with hi | hi
  · exact h i hi
  · simp_rw [smul_of_ge hi]

theorem eq_iff_smul_eq_smul_lt {a b : ArrayPerm n} : a = b ↔ ∀ i < n, a • i = b • i :=
  ⟨fun h _ _ => h ▸ rfl, eq_of_smul_eq_smul_lt⟩

theorem smul_right_inj (a : ArrayPerm n) {i j : ℕ} : a • i = a • j ↔ i = j := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  by_cases hi : i < n
  · have hj := hi
    rw [← a.smul_lt_iff_lt, h, smul_lt_iff_lt] at hj
    refine a.getElem_injective hi hj ?_
    rwa [smul_of_lt hi, smul_of_lt hj] at h
  · rw [smul_of_ge (le_of_not_lt hi)] at h
    rw [h, a.smul_lt_iff_lt] at hi
    rwa [smul_of_ge (le_of_not_lt hi)] at h

instance : One (ArrayPerm n) where
  one := {
    toArray := range n
    invArray := range n
    size_toArray' := size_range
    size_invArray' := size_range
    getElem_toArray_lt' := fun _ => getElem_range_lt
    getElem_invArray_lt' := fun _ => getElem_range_lt
    left_inv' := fun _ => by simp_rw [Array.getElem_range]}

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : ArrayPerm n)[i] = i := getElem_range _

set_option profiler true

instance : Mul (ArrayPerm n) where
  mul a b := {
    toArray := b.toArray.map (a • ·)
    invArray := a.invArray.map (b⁻¹ • ·)
    size_toArray' := by rw [size_map, size_toArray]
    size_invArray' := by rw [size_map, size_invArray]
    getElem_toArray_lt' := fun hi => by
      simp_rw [Array.getElem_map, getElem_toArray, smul_getElem, getElem_lt]
    getElem_invArray_lt' := fun hi => by
      simp_rw [Array.getElem_map, getElem_invArray, smul_getElem, getElem_lt]
    left_inv' := fun hi => by
      simp_rw [Array.getElem_map, getElem_toArray, getElem_invArray,
      smul_getElem, getElem_inv_getElem]}

@[simp]
theorem getElem_mul (a b : ArrayPerm n) {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]]'getElem_lt := by
  refine (Array.getElem_map _ _ _ _).trans ?_
  simp_rw [getElem_toArray, smul_of_lt getElem_lt]

instance : Group (ArrayPerm n) where
  mul_assoc a b c := ext <| fun _ hi => by
    simp_rw [getElem_mul]
  one_mul a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one]
  mul_one a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one]
  mul_left_inv a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one, getElem_inv_getElem]

@[simp]
theorem getElem_pow_add (a : ArrayPerm n) {i x y : ℕ} (hi : i < n) :
    (a^(x + y))[i] = (a^x)[(a^y)[i]]'getElem_lt := by
  simp_rw [pow_add, getElem_mul]

theorem getElem_pow_eq_getElem_pow_of_ge (a : ArrayPerm n) {i x y : ℕ} (hxy : x ≤ y) (hi : i < n) :
    (a^y)[i] = (a^x)[i] ↔ (a^(y - x))[i] = i := by
  rcases Nat.exists_eq_add_of_le hxy with ⟨k, rfl⟩
  simp_rw [getElem_pow_add, add_tsub_cancel_left, getElem_inj]

theorem getElem_pow_eq_getElem_pow_of_le (a : ArrayPerm n) {i x y : ℕ} (hxy : x ≤ y)
    (hi : i < n) : (a^x)[i] = (a^y)[i] ↔ (a^(y - x))[i] = i := by
  simp_rw [← getElem_pow_eq_getElem_pow_of_ge _ hxy, eq_comm]

instance : MulAction (ArrayPerm n) ℕ where
  one_smul k := by simp_rw [smul_nat_def, getElem_one, dite_eq_ite, ite_self]
  mul_smul _ _ i := by
    rcases lt_or_le i n with hi | hi
    · simp_rw [smul_of_lt hi, getElem_mul, smul_of_lt getElem_lt]
    · simp_rw [smul_of_ge hi]

theorem smul_eq_iff_eq_one (a : ArrayPerm n) : (∀ i < n, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul_lt, one_smul]

theorem smul_eq_iff_eq_one' (a : ArrayPerm n) : (∀ i : ℕ, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul, one_smul]

theorem smul_eq_id_iff_eq_one (a : ArrayPerm n) : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [← one_smul_eq_id (ArrayPerm n), funext_iff, one_smul, smul_eq_iff_eq_one']

instance : SMul (ArrayPerm n) (Fin n) where
  smul a i := ⟨a • i.val, a.smul_lt_iff_lt.mpr i.isLt⟩

@[simp]
theorem coe_smul (a : ArrayPerm n) {i : Fin n} : (a • i : Fin n) = a • (i : ℕ) := rfl

instance : FaithfulSMul (ArrayPerm n) (Fin n) where
  eq_of_smul_eq_smul := fun {_ _} => by
    simp_rw [eq_iff_smul_eq_smul_lt, Fin.forall_iff, Fin.ext_iff, coe_smul, imp_self]

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


/--
`ofPerm` maps a member of `Perm ℕ` which maps the subtype `< n` to itself to the corresponding
`ArrayPerm n`.
-/
def ofPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) : ArrayPerm n where
  toArray := (Array.range n).map f
  invArray := (Array.range n).map ⇑f⁻¹
  getElem_toArray_lt' := fun {i} => by
    simp_rw [Array.getElem_map, Array.getElem_range, hf, imp_self]
  getElem_invArray_lt' := fun {i} => by
    simp_rw [Array.getElem_map, Array.getElem_range,
    (hf (f⁻¹ i)).symm, Perm.apply_inv_self, imp_self]
  size_toArray' := by simp only [size_map, size_range]
  size_invArray' := by simp only [size_map, size_range]
  left_inv' := by
    simp only [size_map, size_range, Array.getElem_map, Array.getElem_range,
    Perm.inv_apply_self, implies_true]

@[simp]
theorem getElem_ofPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {i : ℕ}
    {hi : i < n} : (ofPerm f hf)[i] = f i := by
  unfold ofPerm
  simp_rw [getElem_mk, Array.getElem_map, Array.getElem_range]

@[simp]
theorem getElem_inv_ofPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {i : ℕ} {hi : i < n} :
    (ofPerm f hf)⁻¹[i] = f⁻¹ i := by
  unfold ofPerm
  simp_rw [getElem_inv_mk, Array.getElem_map, Array.getElem_range]

@[simp]
theorem inv_ofPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} :
    (ofPerm f hf)⁻¹ =
    ofPerm f⁻¹ (fun x => (hf (f⁻¹ x)).symm.trans (Perm.apply_inv_self _ _ ▸ Iff.rfl)) := rfl

@[simp]
theorem mul_ofPerm {f g : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {hg : ∀ i, g i < n ↔ i < n} :
    (ofPerm f hf) * (ofPerm g hg) =
    ofPerm (f * g) (fun x => (hf (g x)).trans (hg x)) := by
  simp only [ArrayPerm.ext_iff, getElem_mul, getElem_ofPerm, Perm.mul_apply, implies_true]

@[simp]
theorem smul_ofPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {k : ℕ} :
    (ofPerm f hf) • k = if k < n then f k else k := by
  simp_rw [smul_nat_def, getElem_ofPerm, dite_eq_ite]

/--
`natPerm` is the injective monoid homomorphism from `ArrayPerm n` to `Perm ℕ`.
-/
@[simps!]
def natPerm : ArrayPerm n →* Perm ℕ where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  map_mul' a b := Equiv.ext fun _ => by
    simp only [mul_smul, mul_inv_rev, coe_fn_mk, Perm.coe_mul, comp_apply]
  map_one' := Equiv.ext fun _ => by
    simp only [one_smul, inv_one, coe_fn_mk, Perm.coe_one, id_eq]

theorem natPerm_lt_iff_lt (a : ArrayPerm n) {i : ℕ} : natPerm a i < n ↔ i < n := a.smul_lt_iff_lt

theorem natPerm_apply_apply_of_lt (a : ArrayPerm n) {i : ℕ} (h : i < n) :
    natPerm a i = a[i] := a.smul_of_lt h

theorem natPerm_apply_apply_of_ge (a : ArrayPerm n) {i : ℕ} (h : n ≤ i) : natPerm a i = i :=
  a.smul_of_ge h

theorem natPerm_apply_symm_apply_of_lt (a : ArrayPerm n) {i : ℕ} (h : i < n) :
    (natPerm a)⁻¹ i = a⁻¹[i] := by
  simp_rw [← MonoidHom.map_inv, natPerm_apply_apply_of_lt _ h]

theorem natPerm_apply_symm_apply_of_ge (a : ArrayPerm n) {i : ℕ} (h : n ≤ i) :
    (natPerm a)⁻¹ i = i := by rw [← MonoidHom.map_inv, natPerm_apply_apply_of_ge _ h]

theorem natPerm_inj {a b : ArrayPerm n} : natPerm a = natPerm b ↔ a = b := by
  simp_rw [Equiv.ext_iff, eq_iff_smul_eq_smul]
  exact Iff.rfl

theorem natPerm_injective : Function.Injective (natPerm (n := n)) := fun _ _ => natPerm_inj.mp

theorem natPerm_ofPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) (i : ℕ) :
    natPerm (ofPerm f hf) i = if i < n then f i else i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [natPerm_apply_apply_of_lt _ hi, getElem_ofPerm, hi, if_true]
  · simp_rw [natPerm_apply_apply_of_ge _ hi, hi.not_lt, if_false]

theorem ofPerm_natPerm (a : ArrayPerm n) :
    ofPerm (natPerm a) (fun _ => a.natPerm_lt_iff_lt) = a := by
  ext i hi
  simp_rw [getElem_ofPerm, a.natPerm_apply_apply_of_lt hi]

theorem apply_eq_of_ge_iff_exists_natPerm_apply (e : Perm ℕ) :
    (∀ i ≥ n, e i = i) ↔ ∃ a : ArrayPerm n, natPerm a = e := by
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

open Equiv.Perm in
/--
`ArrayPerm n` is equivalent to `Perm (Fin n)`, and this equivalence respects the
multiplication (and, indeed, the scalar action on `Fin n`).
-/
def mulEquivPerm : ArrayPerm n ≃* Perm (Fin n) where
  toFun a := equivSubtype.symm.permCongr ((natPerm a).subtypePerm
    (fun _ => a.natPerm_lt_iff_lt.symm))
  invFun π := ofPerm (π.extendDomain equivSubtype)
    (fun _ => subtype_extendDomain_equivSubtype_iff_subtype π equivSubtype)
  left_inv a := ext fun i h => by
    simp_rw [getElem_ofPerm,
    Perm.extendDomain_apply_subtype _ equivSubtype h, permCongr_apply,
    equivSubtype_symm_apply, symm_symm, equivSubtype_apply, Perm.subtypePerm_apply,
    a.natPerm_apply_apply_of_lt h]
  right_inv π := Equiv.ext fun i => Fin.ext <| by
    simp only [permCongr_apply, symm_symm, equivSubtype_apply, Perm.subtypePerm_apply,
      natPerm_apply_apply_of_lt _ i.isLt, getElem_ofPerm,
      π.extendDomain_apply_subtype equivSubtype i.isLt, equivSubtype_symm_apply]
  map_mul' a b := Equiv.ext fun _ => by simp only [map_mul, permCongr_apply, symm_symm,
    equivSubtype_apply, Perm.subtypePerm_apply, Perm.coe_mul, comp_apply, equivSubtype_symm_apply]

@[simp]
theorem mulEquivPerm_apply_apply_val (a : ArrayPerm n) (i : Fin n):
    (mulEquivPerm a i : ℕ) = a • i := by
  unfold mulEquivPerm
  simp only [MulEquiv.coe_mk, coe_fn_mk, permCongr_apply, symm_symm, equivSubtype_apply,
    Perm.subtypePerm_apply, natPerm_apply_apply, equivSubtype_symm_apply]

theorem mulEquivPerm_apply_apply_val_eq_natPerm_apply (a : ArrayPerm n) (i : Fin n):
    (mulEquivPerm a i : ℕ) = natPerm a • i := a.mulEquivPerm_apply_apply_val i

@[simp]
theorem mulEquivPerm_inv_apply_val (a : ArrayPerm n) (i : Fin n) :
    ((mulEquivPerm a)⁻¹ i : ℕ) = a⁻¹ • i := by
  simp_rw [← map_inv, mulEquivPerm_apply_apply_val]

theorem mulEquivPerm_symm_apply_getElem (π : Perm (Fin n)) {i : ℕ} {hi : i < n} :
    (mulEquivPerm.symm π)[i] = π ⟨i, hi⟩ := by
  unfold mulEquivPerm
  simp_rw [MulEquiv.symm_mk, MulEquiv.coe_mk, coe_fn_symm_mk, getElem_ofPerm,
    Perm.extendDomain_apply_subtype _ equivSubtype hi, equivSubtype_symm_apply, equivSubtype_apply]

theorem mulEquivPerm_symm_apply_getElem_inv (π : Perm (Fin n)) {i : ℕ} {hi : i < n} :
    (mulEquivPerm.symm π)⁻¹[i] = π⁻¹ ⟨i, hi⟩ := by
  rw [← map_inv, mulEquivPerm_symm_apply_getElem]

@[simp]
theorem mulEquivPerm_symm_smul_nat (π : Perm (Fin n)) (i : ℕ) :
    (mulEquivPerm.symm π) • i = if h : i < n then ↑(π • Fin.mk i h) else i := by
  simp_rw [smul_nat_def, Perm.smul_def, mulEquivPerm_symm_apply_getElem]

@[simp]
theorem mulEquivPerm_symm_smul (π : Perm (Fin n)) (i : Fin n) :
    (mulEquivPerm.symm π) • i = π • i := Fin.ext <| by
  simp_rw [coe_smul, mulEquivPerm_symm_smul_nat, Perm.smul_def, i.isLt, dite_true]

instance : Fintype (ArrayPerm n) := Fintype.ofEquiv (Perm (Fin n)) mulEquivPerm.symm.toEquiv

instance : Inhabited (ArrayPerm n) := Equiv.inhabited mulEquivPerm.toEquiv

instance : Unique (ArrayPerm 0) := Equiv.unique mulEquivPerm.toEquiv

instance : Unique (ArrayPerm 1) := Equiv.unique mulEquivPerm.toEquiv

instance : DecidableEq (ArrayPerm n) := Equiv.decidableEq mulEquivPerm.toEquiv

lemma isOfFinOrder (a : ArrayPerm n) : IsOfFinOrder a := isOfFinOrder_of_finite _

lemma orderOf_pos (a : ArrayPerm n) : 0 < orderOf a := by
  rw [orderOf_pos_iff]
  exact a.isOfFinOrder

theorem period_pos (a : ArrayPerm n) {i : ℕ} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_eq_one_iff (a : ArrayPerm n) {i : ℕ} :
    MulAction.period a i = 1 ↔ (hi : i < n) → a[i] = i := by
  simp_rw [MulAction.period_eq_one_iff]
  rcases lt_or_le i n with hi | hi
  · simp_rw [hi, forall_true_left, smul_of_lt hi]
  · simp_rw [hi.not_lt, forall_false, iff_true, smul_of_ge hi]

theorem period_eq_one_of_zero (a : ArrayPerm 0) {i : ℕ} : MulAction.period a i = 1 := by
  simp_rw [period_eq_one_iff, not_lt_zero', forall_false]

theorem period_eq_one_of_one (a : ArrayPerm 1) {i : ℕ} : MulAction.period a i = 1 := by
  simp_rw [period_eq_one_iff, Nat.lt_one_iff]
  intro hi
  simp_rw [hi, ← Nat.lt_one_iff, getElem_lt]

theorem period_eq_one_of_ge (a : ArrayPerm n) {i : ℕ} (hi : n ≤ i) : MulAction.period a i = 1 := by
  simp_rw [period_eq_one_iff, hi.not_lt, forall_false]

theorem period_le_card_of_getElem_pow_mem (a : ArrayPerm n) {i : ℕ} (hi : i < n)
  (s : Finset ℕ) (hia : ∀ k < s.card + 1, (a ^ k)[i] ∈ s) : MulAction.period a i ≤ s.card := by
  simp_rw [← smul_of_lt hi] at hia
  exact MulAction.period_le_card_of_smul_pow_mem _ _ hia

theorem period_le_of_lt (a : ArrayPerm n) {i : ℕ} (hi : i < n) : MulAction.period a i ≤ n := by
  refine (MulAction.period_le_card_of_smul_pow_mem a (Finset.range n) ?_).trans_eq
    (Finset.card_range _)
  simp_rw [Finset.card_range, Finset.mem_range, smul_lt_iff_lt, hi, implies_true]

theorem period_le_of_ne_zero [NeZero n] (a : ArrayPerm n) {i : ℕ} : MulAction.period a i ≤ n := by
  rcases lt_or_le i n with hi | hi
  · exact a.period_le_of_lt hi
  · rw [a.period_eq_one_of_ge hi]
    exact NeZero.pos n

theorem exists_pos_le_pow_smul_eq_of_ge_of_ne_zero [NeZero n] (a : ArrayPerm n) {i : ℕ}
    (hi : n ≤ i) : ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k) • i = i :=
  ⟨1, Nat.zero_lt_one, NeZero.pos n, smul_of_ge hi⟩

theorem exists_pos_le_pow_smul_eq_of_lt (a : ArrayPerm n) {i : ℕ}
    (hi : i < n) : ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k) • i = i :=
  ⟨MulAction.period a i, a.period_pos, a.period_le_of_lt hi, MulAction.pow_period_smul a i⟩

theorem exists_pos_le_pow_smul_eq_of_ne_zero [NeZero n] (a : ArrayPerm n) {i : ℕ} :
    ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k) • i = i :=
  ⟨MulAction.period a i, a.period_pos, a.period_le_of_ne_zero, MulAction.pow_period_smul a i⟩

theorem exists_pos_le_pow_getElem_eq (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k)[i] = i := by
  simp_rw [← smul_of_lt hi, a.exists_pos_le_pow_smul_eq_of_lt hi]

variable {α : Type*}

def onIndices (a : ArrayPerm n) (b : Array α) (hb : b.size = n) : Array α :=
    (Array.range n).attach.map
    (fun i => b[a • i.1]'((a.smul_lt_iff_lt.mpr (mem_range_iff.mp i.2)).trans_eq hb.symm))

theorem size_onIndices (a : ArrayPerm n) {b : Array α} {hb : b.size = n} :
    size (a.onIndices b hb) = n := by
  unfold onIndices
  simp_rw [size_map, size_attach, size_range]

@[simp]
theorem getElem_onIndices (a : ArrayPerm n) (b : Array α) (hb : b.size = n) {i : ℕ}
    {hi : i < (a.onIndices b hb).size} :
    haveI := (a.smul_lt_iff_lt.mpr (hi.trans_eq a.size_onIndices)).trans_eq hb.symm
    (a.onIndices b hb)[i] = b[a • i] := by
  unfold onIndices
  simp only [Array.getElem_map, Array.getElem_attach, Array.getElem_range]

@[simp]
theorem onIndices_range (a : ArrayPerm n) :
    a.onIndices (Array.range n) size_range = a.toArray := by
  refine Array.ext _ _ (by rw [size_onIndices, a.size_toArray]) (fun _ _ h => ?_)
  simp_rw [getElem_onIndices, Array.getElem_range, smul_of_lt (h.trans_eq a.size_toArray),
    getElem_toArray]

def cycleOf (a : ArrayPerm n) (x : ℕ) : Finset ℕ :=
  if h : x < n then (Finset.range n).image (fun k => (a ^ k)[x]) else {x}

theorem cycleOf_eq_map_smul_range_period (a : ArrayPerm n) (x : ℕ) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k) • x) := by
  unfold cycleOf
  rcases lt_or_le x n with hx | hx
  · simp_rw [hx, dite_true, Finset.ext_iff, Finset.mem_image, Finset.mem_range, ← smul_of_lt hx]
    refine fun _ => ⟨fun ⟨k, h⟩ => ⟨k % MulAction.period a x, (Nat.mod_lt _ a.period_pos),
      by simp_rw [MulAction.pow_mod_period_smul, h]⟩, fun ⟨_, hlt, h⟩ =>
      ⟨_, (hlt.trans_le <| a.period_le_of_lt hx), h⟩⟩
  · simp_rw [hx.not_lt, dite_false, smul_of_ge hx, Finset.ext_iff,
    Finset.mem_singleton, Finset.mem_image, Finset.mem_range, exists_and_right]
    exact fun _ => ⟨fun h => ⟨⟨0, a.period_pos⟩, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩

theorem card_cycleOf (a : ArrayPerm n) (x : ℕ) : (a.cycleOf x).card = MulAction.period a x := by
  refine Eq.trans ?_ (Finset.card_range (MulAction.period a x))
  rw [cycleOf_eq_map_smul_range_period, Finset.card_image_iff]
  exact MulAction.smul_injOn_range_period a

theorem mem_cycleOf_iff_exists_pow_lt_period (a : ArrayPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i < MulAction.period a x, (a ^ i) • x = y := by
  rw [cycleOf_eq_map_smul_range_period]
  simp_rw [Finset.mem_image, Finset.mem_range]

theorem mem_cycleOf_iff_exists_pow (a : ArrayPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i) • x = y := by
  rw [cycleOf_eq_map_smul_range_period]
  simp_rw [Finset.mem_image, Finset.mem_range]
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩,
    fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_pos, ?_⟩⟩
  simp_rw [MulAction.pow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_zpow (a : ArrayPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow]
  refine ⟨fun ⟨_, h⟩ => ⟨_, (zpow_natCast a _).symm ▸ h⟩,
    fun ⟨k, h⟩ => ⟨(k % MulAction.period a x).toNat, ?_⟩⟩
  simp_rw [← zpow_natCast, Int.toNat_of_nonneg
    (Int.emod_nonneg _ ((Nat.cast_ne_zero (R := ℤ)).mpr (a.period_pos (i := x)).ne')),
    MulAction.zpow_mod_period_smul, h]

theorem self_mem_cycleOf (a : ArrayPerm n) (x : ℕ) : x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow]
  exact ⟨0, by simp only [pow_zero, one_smul]⟩

theorem smul_mem_cycleOf (a : ArrayPerm n) (x : ℕ) : (a • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow]
  exact ⟨1, by simp only [pow_one]⟩

theorem smul_pow_mem_cycleOf (a : ArrayPerm n) (x k : ℕ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow]
  exact ⟨k, rfl⟩

theorem smul_zpow_mem_cycleOf (a : ArrayPerm n) (x : ℕ) (k : ℤ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow]
  exact ⟨k, rfl⟩

def CycleMinAux (a : ArrayPerm n) : ℕ → ArrayPerm n × {a : Array ℕ // a.size = n}
  | 0 => ⟨1, range n, size_range⟩
  | 1 =>
    ⟨a, (Array.range n).zipWith a.toArray min, by
    rw [Array.size_zipWith, size_range, a.size_toArray, min_self]⟩
  | (i+2) =>
    have ⟨ρ, b, hb⟩ := a.CycleMinAux (i + 1);
    ⟨ρ ^ 2, b.zipWith ((ρ ^ 2).onIndices b hb) min,
    by simp_rw [Array.size_zipWith, hb, size_onIndices, min_self]⟩

def CycleMin (a : ArrayPerm n) (i : ℕ) : Array ℕ := (a.CycleMinAux i).2.1

@[simp]
theorem size_cycleMin (a : ArrayPerm n) (i : ℕ) : (a.CycleMin i).size = n :=
  Subtype.prop (p := fun (a : Array ℕ) => a.size = n) _

theorem cycleMinAux_succ_fst (a : ArrayPerm n) (i : ℕ) :
    (a.CycleMinAux (i + 1)).1 = a ^ (2 ^ i) := by
  induction' i with i IH
  · rw [pow_zero, pow_one]
    rfl
  · rw [pow_succ, pow_mul]
    exact IH ▸ rfl

theorem cycleMin_zero (a : ArrayPerm n) : a.CycleMin 0 = Array.range n := rfl

theorem cycleMin_succ (a : ArrayPerm n) (i : ℕ) :
    (a.CycleMin (i + 1)) =
    (a.CycleMin i).zipWith ((a ^ (2 ^ i)).onIndices (a.CycleMin i) (a.size_cycleMin i)) min := by
  rcases i with (_ | i)
  · simp_rw [cycleMin_zero, onIndices_range, pow_zero, pow_one]
    rfl
  · rw [← cycleMinAux_succ_fst]
    rfl

theorem getElem_cycleMin_zero (a : ArrayPerm n) (x : ℕ) (h : x < (a.CycleMin 0).size) :
    (a.CycleMin 0)[x] = x := by
  simp_rw [cycleMin_zero, Array.getElem_range]

@[simp]
lemma getElem_CycleMin_succ (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin (i + 1)).size) :
  haveI := a.size_cycleMin (i + 1)
  haveI := a.size_cycleMin i
  haveI := (a ^ 2^i).smul_lt_iff_lt (i := x)
  (a.CycleMin (i + 1))[x] = min (a.CycleMin i)[x] (a.CycleMin i)[(a ^ 2^i) • x] := by
  simp_rw [cycleMin_succ, Array.getElem_zipWith, getElem_onIndices]

lemma cycleMin_le_pow_lt_smul (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin i).size) :
    ∀ k < 2^i, (a.CycleMin i)[x] ≤ (a ^ k) • x := by
  induction' i with i IH generalizing x
  · simp_rw [pow_zero, Nat.lt_one_iff, getElem_cycleMin_zero, forall_eq, pow_zero, one_smul, le_rfl]
  · simp_rw [pow_succ', Nat.two_mul, getElem_CycleMin_succ, min_le_iff]
    intro k hk'
    by_cases hk : k < 2^i
    · exact Or.inl (IH _ _ _ hk)
    · rw [← Nat.sub_lt_iff_lt_add (le_of_not_lt hk)] at hk'
      convert Or.inr (IH _ _ _ hk') using 2
      rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (le_of_not_lt hk)]

lemma cycleMin_le_pow_smul_of_period_le_two_pow {i : ℕ}
    (a : ArrayPerm n) (x : ℕ) (hn : MulAction.period a x ≤ 2^i) (h : x < (a.CycleMin i).size) :
    ∀ k, (a.CycleMin i)[x] ≤ (a ^ k) • x := fun k => by
  have H := a.smul_pow_mem_cycleOf x k
  simp_rw [mem_cycleOf_iff_exists_pow_lt_period] at H
  rcases H with ⟨_, hk₁, hk₂⟩
  exact (a.cycleMin_le_pow_lt_smul x i _ _ (hk₁.trans_le hn)).trans_eq hk₂

lemma cycleMin_le_zpow_smul_of_period_le_two_pow {i : ℕ}
    (a : ArrayPerm n) (x : ℕ) (hn : MulAction.period a x ≤ 2^i) (h : x < (a.CycleMin i).size) :
    ∀ k : ℤ, (a.CycleMin i)[x] ≤ (a ^ k) • x := fun k => by
  have H := a.smul_zpow_mem_cycleOf x k
  simp_rw [mem_cycleOf_iff_exists_pow_lt_period] at H
  rcases H with ⟨_, hk₁, hk₂⟩
  exact (a.cycleMin_le_pow_lt_smul x i _ _ (hk₁.trans_le hn)).trans_eq hk₂

lemma cycleMin_le_pow_smul_of_le_two_pow {i : ℕ} (hn : n ≤ 2^i)
    (a : ArrayPerm n) (x : ℕ) (h : x < (a.CycleMin i).size) :
    ∀ k, (a.CycleMin i)[x] ≤ (a ^ k) • x :=
  a.cycleMin_le_pow_smul_of_period_le_two_pow x
    ((a.period_le_of_lt (h.trans_eq <| a.size_cycleMin i)).trans hn) _

lemma cycleMin_le_zpow_smul_of_le_two_pow {i : ℕ} (hn : n ≤ 2^i)
    (a : ArrayPerm n) (x : ℕ) (h : x < (a.CycleMin i).size) :
    ∀ k : ℤ, (a.CycleMin i)[x] ≤ (a ^ k) • x :=
  a.cycleMin_le_zpow_smul_of_period_le_two_pow x
    ((a.period_le_of_lt (h.trans_eq <| a.size_cycleMin i)).trans hn) _

lemma cycleMin_le_self (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin i).size) :
    (a.CycleMin i)[x] ≤ x := (a.cycleMin_le_pow_lt_smul x i h 0 (Nat.two_pow_pos _)).trans_eq
      (by simp_rw [pow_zero, one_smul])

lemma le_cycleMin (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin i).size) :
    ∀ z, (∀ k < 2^i, z ≤ (a ^ k) • x) → z ≤ (a.CycleMin i)[x] := by
  induction' i with i IH generalizing x
  · simp_rw [pow_zero, Nat.lt_one_iff, forall_eq, pow_zero, one_smul, getElem_cycleMin_zero,
    imp_self, implies_true]
  · simp_rw [getElem_CycleMin_succ, le_min_iff]
    intros z hz
    refine ⟨?_, ?_⟩
    · exact IH _ _ _ (fun _ hk => hz _ (hk.trans
        (Nat.pow_lt_pow_of_lt Nat.one_lt_two (Nat.lt_succ_self _))))
    · rw [pow_succ', Nat.two_mul] at hz
      refine IH _ _ _ (fun _ hk => ?_)
      simp_rw [← mul_smul, ← pow_add]
      exact hz _ (Nat.add_lt_add_right hk _)

lemma exists_lt_cycleMin_eq_pow_apply (a : ArrayPerm n) (x : ℕ) (i : ℕ)
    (h : x < (a.CycleMin i).size) :
    ∃ k < 2^i, (a.CycleMin i)[x] = (a ^ k) • x := by
  induction' i with i IH generalizing x
  · simp_rw [getElem_cycleMin_zero]
    exact ⟨0, Nat.two_pow_pos _, pow_zero a ▸ (one_smul _ x).symm⟩
  · simp only [size_cycleMin] at IH h ⊢
    rcases (IH _ h) with ⟨k, hk, hπk⟩
    rcases (IH _ ((a ^ (2 ^ i)).smul_lt_iff_lt.mpr h)) with ⟨k', hk', hπk'⟩
    simp_rw [getElem_CycleMin_succ, hπk, hπk', ← mul_smul, ← pow_add,
    pow_succ', Nat.two_mul]
    rcases lt_or_le ((a ^ k) • x) ((a ^ (k' + 2 ^ i)) • x) with hkk' | hkk'
    · rw [min_eq_left hkk'.le]
      exact ⟨k, hk.trans (Nat.lt_add_of_pos_right (Nat.two_pow_pos _)), rfl⟩
    · rw [min_eq_right hkk']
      exact ⟨k' + 2^i, Nat.add_lt_add_right hk' _, rfl⟩

section Cast

variable {m : ℕ}

/--
`ArrayPerm.cast` re-interprets an `ArrayPerm n` as an `ArrayPerm m`, where `n = m`.
-/
def cast (h : n = m) (a : ArrayPerm n) : ArrayPerm m where
  toArray := a.toArray
  invArray := a.invArray
  getElem_toArray_lt' := fun _ => getElem_toArray.trans_lt <| getElem_lt.trans_eq h
  getElem_invArray_lt' := fun _ => getElem_invArray.trans_lt <| getElem_lt.trans_eq h
  size_toArray' := h ▸ a.size_toArray
  size_invArray' := h ▸ a.size_invArray
  left_inv' :=
    fun hi => a.getElem_inv_getElem (hi.trans_eq h.symm)

@[simp]
theorem getElem_cast (h : n = m) (a : ArrayPerm n) {i : ℕ} (hi : i < m):
    (a.cast h)[i] = a[i] := rfl

@[simp]
theorem getElem_inv_cast (h : n = m) (a : ArrayPerm n) {i : ℕ} (hi : i < m):
    (a.cast h)⁻¹[i] = a⁻¹[i] := rfl

@[simp]
theorem cast_smul (h : n = m) (a : ArrayPerm n) (i : ℕ) :
    (a.cast h) • i = a • i := by simp only [smul_nat_def, getElem_cast, h]

@[simp]
theorem cast_inv (h : n = m) (a : ArrayPerm n) :
    (a.cast h)⁻¹ = a⁻¹.cast h := rfl

@[simp]
theorem cast_mul (h : n = m) (a b : ArrayPerm n) :
    (a * b).cast h = a.cast h * b.cast h := ext <| fun _ hi => by
  simp only [smul_of_lt hi, getElem_mul, getElem_cast]

/--
When `n = m`, `ArrayPerm n` is multiplicatively equivalent to `ArrayPerm m`.
-/

def arrayPermCongr (h : n = m) : ArrayPerm n ≃* ArrayPerm m where
  toFun := cast h
  invFun := cast h.symm
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' := cast_mul h

theorem getElem_toArray_append_range_sub (a : ArrayPerm n) {i : ℕ}
    {h : i < (a.toArray ++ Array.map (fun x => x + n) (Array.range (m - n))).size} :
    haveI := a.size_toArray
    (a.toArray ++ (Array.range (m - n)).map ((· + n)))[i] = a • i := by
  rcases lt_or_le i n with hi | hi
  · rw [Array.get_append_left (hi.trans_eq a.size_toArray.symm), a.smul_of_lt hi, getElem_toArray]
  · simp_rw [Array.get_append_right (hi.trans_eq' a.size_toArray), size_toArray,
    Array.getElem_map, Array.getElem_range, Nat.sub_add_cancel hi, a.smul_of_ge hi]

theorem getElem_invArray_append_range_sub (a : ArrayPerm n) {i : ℕ}
    {h : i < (a.invArray ++ Array.map (fun x => x + n) (Array.range (m - n))).size} :
    haveI := a.size_invArray
    (a.invArray ++ (Array.range (m - n)).map ((· + n)))[i] = a⁻¹ • i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [Array.get_append_left (hi.trans_eq a.size_invArray.symm),
    (a⁻¹).smul_of_lt hi, getElem_invArray]
  · simp_rw [Array.get_append_right (hi.trans_eq' a.size_invArray), size_invArray,
    Array.getElem_map, Array.getElem_range, Nat.sub_add_cancel hi, (a⁻¹).smul_of_ge hi]

/--
`ArrayPerm.castLE` re-interprets an `ArrayPerm n` as an `ArrayPerm m`, where `n ≤ m`.
-/
def castLE (h : n ≤ m) (a : ArrayPerm n) : ArrayPerm m where
  toArray := a.toArray ++ (Array.range (m - n)).map ((· + n))
  invArray := a.invArray ++ (Array.range (m - n)).map ((· + n))
  size_toArray' := by
    simp only [size_append, a.size_toArray, size_map, size_range, h, Nat.add_sub_cancel']
  size_invArray' := by
    simp only [size_append, a.size_invArray, size_map, size_range, h, Nat.add_sub_cancel']
  getElem_toArray_lt' := fun _ => by
    rw [getElem_toArray_append_range_sub, smul_nat_def]
    split_ifs with hin
    · exact getElem_lt.trans_le h
    · assumption
  getElem_invArray_lt' := fun _ => by
    rw [getElem_invArray_append_range_sub, smul_nat_def]
    split_ifs with hin
    · exact getElem_lt.trans_le h
    · assumption
  left_inv' := fun {i} hi => by
    simp_rw [getElem_toArray_append_range_sub, getElem_invArray_append_range_sub, inv_smul_smul]

theorem getElem_castLE (a : ArrayPerm n) (h : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castLE h)[i] = if hi : i < n then a[i] else i := a.getElem_toArray_append_range_sub

theorem getElem_inv_castLE (a : ArrayPerm n) (h : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castLE h)⁻¹[i] = if hi : i < n then a⁻¹[i] else i := a.getElem_invArray_append_range_sub

@[simp]
theorem castLE_smul (a : ArrayPerm n) {i : ℕ} {h : n ≤ m} :
    (a.castLE h) • i = a • i := by
  simp_rw [smul_nat_def, a.getElem_castLE h, dite_eq_ite, ite_eq_left_iff]
  intro hi
  simp_rw [(h.trans (le_of_not_lt hi)).not_lt, dite_false]

@[simp]
theorem castLE_inv (a : ArrayPerm n) {h : n ≤ m} :
    (a.castLE h)⁻¹ = a⁻¹.castLE h := rfl

theorem castLE_mul (a b : ArrayPerm n) (h : n ≤ m) :
    (a * b).castLE h = a.castLE h * b.castLE h := by
  ext i
  simp only [getElem_castLE, getElem_mul, mul_smul]
  rcases lt_or_le i n with hi | hi
  · simp only [hi, dite_true, getElem_lt]
  · simp only [hi.not_lt, dite_false]

theorem castLE_inj {a b : ArrayPerm n} {h : n ≤ m} : castLE h a = castLE h b ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [ArrayPerm.ext_iff, getElem_castLE]
  refine fun H _ hi => ?_
  specialize H _ (hi.trans_le h)
  simp_rw [hi, dite_true] at H
  exact H

theorem castLE_injective (h : n ≤ m) : Function.Injective (castLE h) := fun _ _ => castLE_inj.mp

@[simp]
theorem castLE_one {h : n ≤ m} : ((1 : ArrayPerm n).castLE h) = 1 := by
  ext i hi : 1
  simp_rw [getElem_castLE, getElem_one, dite_eq_ite, ite_self]

def arrayPermMonoidHom (h : n ≤ m) : ArrayPerm n →* ArrayPerm m where
  toFun := castLE h
  map_mul' a b := a.castLE_mul b h
  map_one' := castLE_one

theorem arrayPermMonoidHom_injective {h : n ≤ m} :
  (⇑(arrayPermMonoidHom h)).Injective := castLE_injective h

theorem castLE_of_eq (h : n = m) (h' : n ≤ m := h.le) (a : ArrayPerm n) :
    a.castLE h' = a.cast h := by
  ext i hi : 1
  simp_rw [getElem_castLE, getElem_cast, hi.trans_eq h.symm, dite_true]

end Cast

/--
For `a` an `ArrayPerm n`, `a.swap hi hj` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : ArrayPerm n) {i j : ℕ} (hi : i < n) (hj : j < n) : ArrayPerm n where
  toArray := a.toArray.swap! i j
  invArray := a.invArray.map (fun k => Equiv.swap i j k)
  size_toArray' := (Array.size_swap! _ _ _).trans a.size_toArray
  size_invArray' := (Array.size_map _ _).trans a.size_invArray
  getElem_toArray_lt' := fun _ => by
    simp_rw [a.toArray.getElem_swap!_eq_getElem_swap_apply
      (hi.trans_eq a.size_toArray.symm) (hj.trans_eq a.size_toArray.symm), getElem_toArray,
      a.getElem_lt]
  getElem_invArray_lt' := fun _ => by
    simp_rw [Array.getElem_map, getElem_invArray]
    exact swap_prop (· < n) getElem_lt hi hj
  left_inv' := fun _ => by
    simp_rw [a.toArray.getElem_swap!_eq_getElem_swap_apply
      (hi.trans_eq a.size_toArray.symm) (hj.trans_eq a.size_toArray.symm), Array.getElem_map,
      getElem_toArray, getElem_invArray, getElem_inv_getElem, swap_apply_self]

variable (i j k : ℕ) (hi : i < n) (hj : j < n)

@[simp]
theorem getElem_swap (a : ArrayPerm n) (hk : k < n) :
    (a.swap hi hj)[k] = a[Equiv.swap i j k]'(swap_prop (· < n) hk hi hj) :=
  a.toArray.getElem_swap!_eq_getElem_swap_apply
    (hi.trans_eq a.size_toArray.symm) (hj.trans_eq a.size_toArray.symm) _

@[simp]
theorem getElem_inv_swap (a : ArrayPerm n) (hk : k < n) :
    (a.swap hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.invArray.getElem_map _ _ _

theorem swap_smul_eq_smul_swap (a : ArrayPerm n) : (a.swap hi hj) • k = a • (Equiv.swap i j k) := by
  rcases lt_or_ge k n with hk | hk
  · simp_rw [smul_of_lt (swap_prop (· < n) hk hi hj), smul_of_lt hk, getElem_swap]
  · simp_rw [Equiv.swap_apply_of_ne_of_ne (hk.trans_lt' hi).ne' (hk.trans_lt' hj).ne',
      smul_of_ge hk]

theorem swap_inv_eq_swap_apply_inv_smul (a : ArrayPerm n) :
  (a.swap hi hj)⁻¹ • k = Equiv.swap i j (a⁻¹ • k) := by
  simp_rw [inv_smul_eq_iff, swap_smul_eq_smul_swap,
  ← swap_smul, smul_inv_smul, swap_apply_self]

theorem swap_smul_eq_swap_apply_smul (a : ArrayPerm n) :
    (a.swap hi hj) • k = Equiv.swap (a • i) (a • j) (a • k) := by
  rw [swap_smul, swap_smul_eq_smul_swap]

theorem swap_inv_smul_eq_inv_smul_swap (a : ArrayPerm n) : (a.swap hi hj)⁻¹ • k =
    a⁻¹ • (Equiv.swap (a • i) (a • j) k) := by
  simp_rw [swap_inv_eq_swap_apply_inv_smul, ← Equiv.swap_smul, inv_smul_smul]

theorem swap_smul_left (a : ArrayPerm n) :
    (a.swap hi hj) • i = a • j := by rw [swap_smul_eq_smul_swap, swap_apply_left]

theorem swap_smul_right (a : ArrayPerm n) :
  (a.swap hi hj) • j = a • i := by rw [swap_smul_eq_smul_swap, swap_apply_right]

theorem swap_smul_of_ne_of_ne (a : ArrayPerm n) {k} :
  k ≠ i → k ≠ j → (a.swap hi hj) • k = a • k := by
  rw [swap_smul_eq_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

theorem swap_inv_smul_left (a : ArrayPerm n) :
    (a.swap hi hj)⁻¹ • (a • i) = j := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_left, inv_smul_smul]

theorem swap_inv_smul_right (a : ArrayPerm n) :
    (a.swap hi hj)⁻¹ • (a • j) = i := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_right, inv_smul_smul]

theorem swap_inv_smul_of_ne_of_ne (a : ArrayPerm n) {k} :
  k ≠ a • i → k ≠ a • j → (a.swap hi hj)⁻¹ • k = a⁻¹ • k := by
  rw [swap_inv_smul_eq_inv_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (a : ArrayPerm n) (hi' : i < n) : a.swap hi hi' = a := by
  ext : 1
  simp_rw [getElem_swap, Equiv.swap_self, Equiv.refl_apply]

@[simp]
theorem swap_swap (a : ArrayPerm n) (hi' : i < n) (hj' : j < n) :
    (a.swap hi hj).swap hi' hj' = a := by
  ext : 1
  simp_rw [getElem_swap, swap_apply_self]

theorem getElem_one_swap (hk : k < n) : (swap 1 hi hj)[k] = Equiv.swap i j k := by
  rw [getElem_swap, getElem_one]

theorem getElem_inv_one_swap (hk : k < n) : (swap 1 hi hj)⁻¹[k] = Equiv.swap i j k := by
  simp_rw [getElem_inv_swap, inv_one, getElem_one]

theorem one_swap_smul : (swap 1 hi hj) • k = Equiv.swap i j k := by
  rw [swap_smul_eq_smul_swap, one_smul]

theorem one_swap_inv_smul : (swap 1 hi hj)⁻¹ • k = Equiv.swap i j k := by
  simp_rw [swap_inv_smul_eq_inv_smul_swap, one_smul, inv_one, one_smul]

theorem one_swap_mul_self : swap 1 hi hj * swap 1 hi hj = 1 := by
  ext : 1
  simp_rw [getElem_mul, getElem_one_swap, swap_apply_self, getElem_one]

theorem one_swap_inverse : (swap 1 hi hj)⁻¹ = swap 1 hi hj := by
  ext : 1
  rw [getElem_one_swap, getElem_inv_one_swap]

theorem swap_eq_mul_one_swap (a : ArrayPerm n) : a.swap hi hj = a * swap 1 hi hj := by
  ext : 1
  simp only [getElem_swap, getElem_mul, getElem_one]

theorem swap_eq_one_swap_mul (a : ArrayPerm n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    a.swap hi hj = swap 1 hi' hj' * a := by
  rw [eq_iff_smul_eq_smul]
  simp_rw [mul_smul, one_swap_smul, swap_smul_eq_smul_swap, swap_smul, implies_true]

theorem swap_inv_eq_one_swap_mul (a : ArrayPerm n) :
    (a.swap hi hj)⁻¹ = swap 1 hi hj * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (a : ArrayPerm n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    (a.swap hi hj)⁻¹ = a⁻¹ * swap 1 hi' hj' := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

theorem natPerm_swap (a : ArrayPerm n) :
    natPerm (swap a hi hj) = natPerm a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, natPerm_apply_apply, swap_smul_eq_smul_swap]

@[simp]
theorem natPerm_one_swap  :
    natPerm (swap 1 hi hj) = Equiv.swap i j := by simp_rw [natPerm_swap, map_one, one_mul]

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
