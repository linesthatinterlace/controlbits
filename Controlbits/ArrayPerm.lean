import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.Indexes
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.GroupAction.Period
import Batteries.Data.Array.Lemmas

set_option autoImplicit false

section GetElem

variable {coll : Type*} {idx : Type*} {elem : outParam (Type*)}
  {valid : outParam (coll → idx → Prop)}

@[simp]
theorem getElem_ite [GetElem coll idx elem valid] {P : Prop} [Decidable P] {c : coll} {i j : idx}
    (h : valid c (if P then i else j)) :
  c[if P then i else j] = if hP : P then
    c[i]'(by simp_rw [hP, ite_true] at h ; exact h) else
    c[j]'(by simp_rw [hP, ite_false] at h ; exact h) :=
  if hP : P then by simp_rw [hP, ite_true, dite_true] else by simp_rw [hP, ite_false, dite_false]

@[simp]
theorem getElem_dite [GetElem coll idx elem valid] {P : Prop} [Decidable P]
    {c : coll} {i : P → idx} {j : ¬P → idx}
    (h : valid c (if hP : P then i hP else j hP)) :
  c[if hP : P then i hP else j hP] = if hP : P then
    c[i hP]'(by simp_rw [hP, dite_true] at h ; exact h) else
    c[j hP]'(by simp_rw [hP, dite_false] at h ; exact h) :=
  if hP : P then by simp_rw [hP, dite_true] else by simp_rw [hP, dite_false]

end GetElem

namespace Nat

theorem log2_one : log2 1 = 0 := by
  unfold log2
  exact if_neg (not_succ_le_self _)

theorem log2_mul_two {k : ℕ} [NeZero k] : log2 (2 * k) = log2 k + 1 := by
  nth_rewrite 1 [log2]
  simp_rw [le_mul_iff_one_le_right (zero_lt_two), Nat.mul_div_cancel_left _ (zero_lt_two),
  NeZero.one_le, if_true]

theorem log2_two_mul {k : ℕ} [NeZero k] : log2 (k * 2) = log2 k + 1 := by
  nth_rewrite 1 [log2]
  simp_rw [le_mul_iff_one_le_left (zero_lt_two), Nat.mul_div_cancel _ (zero_lt_two),
  NeZero.one_le, if_true]

theorem log2_two_pow {k : ℕ} : log2 (2^k) = k := by
  induction' k with _ IH
  · exact log2_one
  · rw [pow_succ, log2_two_mul, IH]

end Nat

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

@[simp]
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
theorem getD_of_lt (a : Array α) (x : α) (i : ℕ) (h : i < a.size) : a[i]?.getD x = a[i] := by
  rw [a.getElem?_lt h, Option.getD_some]

@[simp]
theorem getD_of_ge (a : Array α) (x : α) (i : ℕ) (h : a.size ≤ i) : a[i]?.getD x = x := by
  rw [a.getElem?_ge h, Option.getD_none]

theorem getElem?_eq_some (a : Array α) (x : α) (i : ℕ) :
    a[i]? = some x ↔ ∃ (h : i < a.size), a[i] = x := by
  refine ⟨fun h => ?_, fun ⟨H, h⟩ => ?_⟩
  · have H : i < a.size := by
      simp_rw [← not_le]
      intro hc
      simp_rw [getElem?_ge _ hc] at h
    simp_rw [Array.getElem?_eq_getElem _ _ H, Option.some.injEq] at h
    exact ⟨H, h⟩
  · simp_rw [Array.getElem?_eq_getElem _ _ H, Option.some.injEq, h]

theorem getD_eq_iff (a : Array α) (x d : α) (i : ℕ) :
    a[i]?.getD d = x ↔ (∃ (h : i < a.size), a[i] = x) ∨ (a.size ≤ i ∧ d = x) := by
  simp_rw [← Array.getD_eq_get?, Array.getD, dite_eq_iff, get_eq_getElem, exists_prop, not_lt]

theorem getD_eq_iff_of_ne {d x : α} (hdx : d ≠ x) (a : Array α) (i : ℕ) :
    a[i]?.getD d = x ↔ ∃ (h : i < a.size), a[i] = x := by
  simp_rw [getD_eq_iff, hdx, and_false, or_false]

theorem getD_false_eq_true_iff_getElem_eq_true {a : Array Bool} {i : ℕ} :
    a[i]?.getD false = true ↔ ∃ (h : i < a.size), a[i] = true :=
  getD_eq_iff_of_ne Bool.false_ne_true _ _

theorem getD_true_eq_true_iff_getElem_eq_false {a : Array Bool} {i : ℕ} :
    a[i]?.getD true = false ↔ ∃ (h : i < a.size), a[i] = false :=
  getD_eq_iff_of_ne Bool.false_ne_true.symm _ _

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
  rw [Array.data_zipWith] at h
  exact List.lt_length_left_of_zipWith h

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith bs f).size) : i < bs.size := by
  rw [Array.size_eq_length_data] at h ⊢
  rw [Array.data_zipWith] at h
  exact List.lt_length_right_of_zipWith h

theorem lt_length_left_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < as.size := lt_length_left_of_zipWith h

theorem lt_length_right_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < bs.size := lt_length_right_of_zipWith h

@[simp]
theorem getElem_zipWith {as : Array α} {bs : Array β} {f : α → β → γ} {i : ℕ}
    (h : i < (as.zipWith bs f).size) : (as.zipWith bs f)[i] =
    f (as[i]'(lt_length_left_of_zipWith h)) (bs[i]'(lt_length_right_of_zipWith h)) := by
  simp_rw [getElem_eq_data_getElem, Array.data_zipWith, List.getElem_zipWith]

@[simp]
theorem getElem_zip {as : Array α} {bs : Array β} {i : ℕ}
    (h : i < (as.zip bs).size) : (as.zip bs)[i] =
    (as[i]'(lt_length_left_of_zip h), bs[i]'(lt_length_right_of_zip h)) := by
  simp_rw [getElem_eq_data_getElem, Array.data_zip, List.getElem_zip]

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


theorem foldr_induction'
    {as : Array α} (motive : Fin (as.size + 1) → β → Prop) {init : β}
    (h0 : motive (Fin.last _) init) {f : α → β → β}
    (hf : ∀ (i : Fin as.size) b, motive i.succ b → motive i.castSucc (f as[(i : ℕ)] b)) :
    motive 0 (as.foldr f init) := by
  refine foldr_induction (motive ·) (by convert Fin.natCast_eq_last _ ▸ h0) (?_)
  simp_rw [Nat.cast_add, Fin.coe_eq_castSucc, Nat.cast_one, Fin.coeSucc_eq_succ]
  exact hf

theorem foldl_induction'
    {as : Array α} (motive : Fin (as.size + 1) → β → Prop) {init : β}
    (h0 : motive 0 init) {f : β → α → β}
    (hf : ∀ (i : Fin as.size) b, motive i.castSucc b → motive i.succ (f b as[(i : ℕ)])) :
    motive (Fin.last _) (as.foldl f init) := by
  refine natCast_eq_last _ ▸ foldl_induction (motive ·) h0 ?_
  simp_rw [Nat.cast_add, Nat.cast_one, coe_eq_castSucc, coeSucc_eq_succ]
  exact hf

theorem foldl_empty {init : β} {f : β → α → β} : foldl f init #[] = init := rfl

theorem foldr_empty {init : β} {f : α → β → β} : foldr f init #[] = init := rfl

def popOff (as : Array α) (n : ℕ) [NeZero n] : Array α :=
  (·.2.2) <| as.foldl (init := (true, (0 : Fin n), Array.empty)) fun (b, n, r) a =>
    ((n == -1).xor b, n + 1, if b then r.push a else r)


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
  in `fwdArray`.
  -/
  protected fwdArray : Array ℕ
  /--
  Gives the `ArrayPerm` as an array of indexes. Value `v` is mapped to the index at position `v`
  in `bwdArray`.
  -/
  protected bwdArray : Array ℕ
  protected size_fwdArray' : fwdArray.size = n := by rfl
  protected size_bwdArray' : bwdArray.size = n := by rfl
  protected getElem_fwdArray_lt' :
    ∀ {i : ℕ} (hi : i < n), fwdArray[i]'(hi.trans_eq size_fwdArray'.symm) < n := by decide
  protected getElem_bwdArray_lt' :
  ∀ {i : ℕ} (hi : i < n), bwdArray[i]'(hi.trans_eq size_bwdArray'.symm) < n := by decide
  protected left_inv' : ∀ {i : ℕ} (hi : i < n),
      bwdArray[fwdArray[i]'(hi.trans_eq size_fwdArray'.symm)]'
      ((getElem_fwdArray_lt' hi).trans_eq size_bwdArray'.symm) = i :=
    by decide

namespace ArrayPerm

open Function Fin Equiv List Array

variable {n : ℕ}

instance : Repr (ArrayPerm n) where
  reprPrec a _ := repr (a.fwdArray, a.bwdArray)

instance : ToString (ArrayPerm n) where
  toString a := toString (a.fwdArray, a.bwdArray)

@[simp]
lemma size_fwdArray (a : ArrayPerm n) : a.fwdArray.size = n := a.size_fwdArray'

@[simp]
lemma size_bwdArray (a : ArrayPerm n) : a.bwdArray.size = n := a.size_bwdArray'

instance : GetElem (ArrayPerm n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.fwdArray[i]'(h.trans_eq a.size_fwdArray.symm)

@[simp]
theorem getElem_lt {a : ArrayPerm n} {i : ℕ} {hi : i < n} : a[i] < n :=
  a.getElem_fwdArray_lt' hi

@[simp]
theorem getElem_fwdArray {a : ArrayPerm n} {i : ℕ} {hi : i < a.fwdArray.size} :
  a.fwdArray[i] = a[i]'(hi.trans_eq a.size_fwdArray) := rfl

@[simp]
theorem getElem_mk (a a' : Array ℕ) {sta sia getl geil geiageta} {i : ℕ} (hi : i < n) :
  (ArrayPerm.mk a a' sta sia getl geil geiageta)[i] = a[i]'(hi.trans_eq sta.symm) := rfl

theorem lt_of_mem_fwdArray {a : ArrayPerm n} {x : ℕ} : x ∈ a.fwdArray → x < n := by
  simp_rw [Array.mem_iff_getElem, getElem_fwdArray]
  rintro ⟨_, _, rfl⟩
  exact getElem_lt

def ofArray (a : Array ℕ) (hx : ∀ {x} (hx : x < a.size), a[x] < a.size := by decide)
  (ha : a.data.Nodup := by decide) : ArrayPerm (a.size) where
  fwdArray := a
  bwdArray := a.mapIdx (fun i _ => a.data.indexOf i.1)
  size_fwdArray' := rfl
  size_bwdArray' := by simp_rw [size_mapIdx]
  getElem_fwdArray_lt' := hx
  getElem_bwdArray_lt' := fun {i} hi => by
    have H : Surjective (fun (i : Fin (a.size)) => Fin.mk a[i.1] (hx i.2)) :=
      Injective.surjective_of_fintype (Equiv.refl (Fin (a.size))) fun _ _ => by
      simp_rw [Fin.mk.injEq, Fin.ext_iff, getElem_eq_data_getElem, ha.getElem_inj_iff, imp_self]
    simp_rw [Surjective, Fin.ext_iff, Fin.forall_iff] at H
    rcases H _ hi with ⟨_, rfl⟩
    simp_rw [Array.getElem_mapIdx, indexOf_lt_length]
    exact List.getElem_mem _ _ _
  left_inv' := fun _ => by
    simp_rw [Array.getElem_mapIdx, Array.getElem_eq_data_getElem, List.indexOf_getElem ha]

@[simp]
theorem getElem_ofArray {a : Array ℕ} {hx : ∀ {x} (hx : x < a.size), a[x] < a.size}
    {ha : a.data.Nodup} {i : ℕ} (hi : i < a.size) : (ofArray a hx ha)[i] = a[i] := rfl

def finFwdArray (a : ArrayPerm n) : Array (Fin n) :=
  a.fwdArray.attach.map fun x => ⟨x.1, lt_of_mem_fwdArray x.2⟩

theorem finFwdArray_eq_fwdArray_attach_map_mk {a : ArrayPerm n} :
  a.finFwdArray = a.fwdArray.attach.map (fun x => ⟨x.1, lt_of_mem_fwdArray x.2⟩) := rfl

@[simp]
theorem size_finFwdArray {a : ArrayPerm n} : a.finFwdArray.size = n :=
  (Array.size_map _ _).trans <| Array.size_attach.trans a.size_fwdArray

@[simp]
theorem getElem_finFwdArray {a : ArrayPerm n} {x : ℕ} (hx : x < a.finFwdArray.size) :
    a.finFwdArray[x] = ⟨a[x]'(hx.trans_eq a.size_finFwdArray), getElem_lt⟩ := by
  simp_rw [finFwdArray_eq_fwdArray_attach_map_mk, Array.getElem_map, Array.getElem_attach,
    getElem_fwdArray]

theorem fwdArray_eq_finFwdArray_map_val {a : ArrayPerm n} :
    a.fwdArray = a.finFwdArray.map Fin.val := by
  simp_rw [Array.ext_iff, size_map, size_finFwdArray, size_fwdArray, Array.getElem_map,
    getElem_finFwdArray, getElem_fwdArray, implies_true, and_self]

instance : Inv (ArrayPerm n) where
  inv a := {
    fwdArray := a.bwdArray
    bwdArray := a.fwdArray
    size_fwdArray' := a.size_bwdArray
    size_bwdArray' := a.size_fwdArray
    getElem_fwdArray_lt' := a.getElem_bwdArray_lt'
    getElem_bwdArray_lt' := a.getElem_fwdArray_lt'
    left_inv' := fun hi => by
      rw [getElem_fwdArray]
      have H : Injective (fun (i : Fin n) => Fin.mk
      (a.bwdArray[i.1]'(i.isLt.trans_eq a.size_bwdArray.symm)) (a.getElem_bwdArray_lt' i.isLt)) :=
        Surjective.injective_of_fintype (Equiv.refl _)
        (fun i => ⟨⟨a[i.1], getElem_lt⟩, Fin.ext <| a.left_inv' i.isLt⟩)
      unfold Injective at H
      simp_rw [Fin.forall_iff, Fin.ext_iff] at H
      exact H _ getElem_lt _ hi (a.left_inv' <| a.getElem_bwdArray_lt' hi)}

@[simp]
theorem getElem_inv_getElem (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    a⁻¹[a[i]]'getElem_lt = i := a.left_inv' hi

@[simp]
theorem getElem_getElem_inv (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
  a[a⁻¹[i]]'getElem_lt = i := (a⁻¹).left_inv' hi

@[simp]
theorem getElem_bwdArray {a : ArrayPerm n} {i : ℕ} {hi : i < a.bwdArray.size} :
  a.bwdArray[i] = a⁻¹[i]'(hi.trans_eq a.size_bwdArray) := rfl

@[simp]
theorem getElem_inv_ofArray {a : Array ℕ} {hx : ∀ {x} (hx : x < a.size), a[x] < a.size}
    {ha : a.data.Nodup} {i : ℕ} (hi : i < a.size) : (ofArray a hx ha)⁻¹[i] = a.data.indexOf i :=
  Array.getElem_mapIdx _ _ _ _

@[simp]
theorem getElem_inv_mk (a a' : Array ℕ) {sta sia getl geil geiageta} {i : ℕ} (hi : i < n) :
  (ArrayPerm.mk a a' sta sia getl geil geiageta)⁻¹[i] = a'[i]'(hi.trans_eq sia.symm) := rfl

theorem lt_of_mem_bwdArray {a : ArrayPerm n} {x : ℕ} : x ∈ a.bwdArray → x < n := by
  simp_rw [Array.mem_iff_getElem, getElem_bwdArray]
  rintro ⟨_, _, rfl⟩
  exact getElem_lt

def finBwdArray (a : ArrayPerm n) : Array (Fin n) :=
  a.bwdArray.attach.map fun x => ⟨x.1, lt_of_mem_bwdArray x.2⟩

theorem finBwdArray_eq_bwdArray_attach_map_mk {a : ArrayPerm n} :
  a.finBwdArray = a.bwdArray.attach.map (fun x => ⟨x.1, lt_of_mem_bwdArray x.2⟩) := rfl

@[simp]
theorem size_finBwdArray {a : ArrayPerm n} : a.finBwdArray.size = n :=
  (Array.size_map _ _).trans <| Array.size_attach.trans a.size_bwdArray

@[simp]
theorem getElem_finBwdArray {a : ArrayPerm n} {x : ℕ} (hx : x < a.finBwdArray.size) :
    a.finBwdArray[x] = ⟨a⁻¹[x]'(hx.trans_eq a.size_finBwdArray), getElem_lt⟩ := by
  simp_rw [finBwdArray_eq_bwdArray_attach_map_mk, Array.getElem_map, Array.getElem_attach,
    getElem_bwdArray]

theorem bwdArray_eq_finBwdArray_map_val {a : ArrayPerm n} :
    a.bwdArray = a.finBwdArray.map Fin.val := by
  simp_rw [Array.ext_iff, size_map, size_finBwdArray, size_bwdArray, Array.getElem_map,
    getElem_finBwdArray, getElem_bwdArray, implies_true, and_self]

theorem mem_bwdArray_of_lt {a : ArrayPerm n} {x : ℕ} (hx : x < n) : x ∈ a.bwdArray := by
  simp_rw [Array.mem_iff_getElem, getElem_bwdArray, size_bwdArray]
  exact ⟨a[x], getElem_lt, a.getElem_inv_getElem _⟩

theorem mem_fwdArray_of_lt {a : ArrayPerm n} {x : ℕ} (hx : x < n) : x ∈ a.fwdArray := by
  simp_rw [Array.mem_iff_getElem, getElem_fwdArray, size_fwdArray]
  exact ⟨a⁻¹[x], getElem_lt, a.getElem_getElem_inv _⟩

@[simp]
theorem mem_fwdArray_iff_lt {a : ArrayPerm n} {x : ℕ} : x ∈ a.fwdArray ↔ x < n :=
  ⟨lt_of_mem_fwdArray, mem_fwdArray_of_lt⟩

@[simp]
theorem mem_bwdArray_iff_lt {a : ArrayPerm n} {x : ℕ} : x ∈ a.bwdArray ↔ x < n :=
  ⟨lt_of_mem_bwdArray, mem_bwdArray_of_lt⟩

theorem mem_finFwdArray {a : ArrayPerm n} {x : Fin n} : x ∈ a.finFwdArray := by
  simp_rw [Array.mem_iff_getElem, getElem_finFwdArray, size_finFwdArray,
  Fin.ext_iff]
  exact ⟨a⁻¹[x.1], getElem_lt, a.getElem_getElem_inv _⟩

theorem mem_finBwdArray {a : ArrayPerm n} {x : Fin n} : x ∈ a.finBwdArray := by
  simp_rw [Array.mem_iff_getElem, getElem_finBwdArray, size_finBwdArray,
  Fin.ext_iff]
  exact ⟨a[x.1], getElem_lt, a.getElem_inv_getElem _⟩

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

theorem self_eq_getElem_inv_iff (a: ArrayPerm n) {i : ℕ} {hi : i < n} : i = a⁻¹[i] ↔ a[i] = i := by
  rw [← (a⁻¹).getElem_inj (getElem_lt) hi, getElem_inv_getElem]

theorem getElem_inv_eq_iff (a: ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by
  rw [← a.getElem_inj (getElem_lt) hj, getElem_getElem_inv]

theorem getElem_inv_eq_self_iff (a : ArrayPerm n) {i : ℕ} {hi : i < n} :
    a⁻¹[i] = i ↔ i = a[i] := by
  rw [← a.getElem_inj (getElem_lt) hi, getElem_getElem_inv]

theorem ne_getElem_inv_iff (a: ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := (a.eq_getElem_inv_iff _ _).ne

theorem self_ne_getElem_inv_iff (a: ArrayPerm n) {i : ℕ} {hi : i < n} :
    i ≠ a⁻¹[i] ↔ a[i] ≠ i := (a.eq_getElem_inv_iff _ _).ne

theorem getElem_inv_ne_iff (a: ArrayPerm n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := (a.getElem_inv_eq_iff _ _).ne

theorem getElem_inv_ne_self_iff (a: ArrayPerm n) {i : ℕ} {hi : i < n}:
    a⁻¹[i] ≠ i ↔ i ≠ a[i] := (a.getElem_inv_eq_iff _ _).ne

theorem fwdArray_eq_iff_forall_getElem_eq (a b : ArrayPerm n) :
    a.fwdArray = b.fwdArray ↔ ∀ i (hi : i < n), a[i] = b[i] := by
  simp_rw [ext_iff, a.size_fwdArray, b.size_fwdArray, getElem_fwdArray, true_and]
  exact ⟨fun h _ hi => h _ hi hi, fun h => fun _ _ => h _⟩

theorem bwdArray_eq_iff_forall_getElem_eq (a b : ArrayPerm n) :
    a.bwdArray = b.bwdArray ↔ ∀ i (hi : i < n), a⁻¹[i] = b⁻¹[i] :=
  fwdArray_eq_iff_forall_getElem_eq a⁻¹ b⁻¹

@[ext]
theorem ext {a b : ArrayPerm n} (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.fwdArray = b.fwdArray ∧ a.bwdArray = b.bwdArray by
    · rcases a ; rcases b ; simp_rw [mk.injEq]
      exact h
  simp_rw [fwdArray_eq_iff_forall_getElem_eq, h,
    bwdArray_eq_iff_forall_getElem_eq, implies_true, true_and]
  refine fun _ _ => a.getElem_injective getElem_lt getElem_lt ?_
  simp_rw [getElem_getElem_inv, h, getElem_getElem_inv]

instance : SMul (ArrayPerm n) (Fin n) where
  smul a i := ⟨a[i.1], getElem_lt⟩

@[simp]
theorem val_smul (a : ArrayPerm n) {i : Fin n} : (a • i : Fin n) = a[i.1] := rfl

@[simp]
theorem smul_mk (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    (a • (⟨i, hi⟩ : Fin n)) = ⟨a[i], getElem_lt⟩ := Fin.ext a.val_smul

theorem getElem_eq_val_smul_mk (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    a[i] = ↑(a • Fin.mk i hi) := by rw [smul_mk]

instance : FaithfulSMul (ArrayPerm n) (Fin n) where
  eq_of_smul_eq_smul := by
    simp_rw [ArrayPerm.ext_iff, Fin.ext_iff, Fin.forall_iff, val_smul, imp_self, implies_true]

theorem eq_iff_smul_eq_smul {a b : ArrayPerm n} : a = b ↔ ∀ i : Fin n, a • i = b • i :=
  ⟨fun h _ => h ▸ rfl, eq_of_smul_eq_smul⟩

theorem smul_right_inj (a : ArrayPerm n) {i j : Fin n} : a • i = a • j ↔ i = j := by
  simp_rw [Fin.ext_iff, val_smul, getElem_inj]

instance : One (ArrayPerm n) where
  one := {
    fwdArray := range n
    bwdArray := range n
    size_fwdArray' := size_range
    size_bwdArray' := size_range
    getElem_fwdArray_lt' := fun _ => getElem_range_lt
    getElem_bwdArray_lt' := fun _ => getElem_range_lt
    left_inv' := fun _ => by simp_rw [Array.getElem_range]}

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : ArrayPerm n)[i] = i := getElem_range _

instance : Mul (ArrayPerm n) where
  mul a b := {
    fwdArray := b.finFwdArray.map (fun (i : Fin n) => a[(i : ℕ)])
    bwdArray := a.finBwdArray.map (fun (i : Fin n) => b⁻¹[(i : ℕ)])
    size_fwdArray' := by rw [size_map, size_finFwdArray]
    size_bwdArray' := by rw [size_map, size_finBwdArray]
    getElem_fwdArray_lt' := fun hi => by
      simp_rw [Array.getElem_map, getElem_finFwdArray, getElem_lt]
    getElem_bwdArray_lt' := fun hi => by
      simp_rw [Array.getElem_map, getElem_finBwdArray, getElem_lt]
    left_inv' := fun hi => by
      simp_rw [Array.getElem_map, getElem_finFwdArray, getElem_finBwdArray, getElem_inv_getElem]}

@[simp]
theorem getElem_mul (a b : ArrayPerm n) {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]]'getElem_lt := by
  refine (Array.getElem_map _ _ _ _).trans ?_
  simp_rw [getElem_finFwdArray]

instance : Group (ArrayPerm n) where
  mul_assoc a b c := ext <| fun _ hi => by
    simp_rw [getElem_mul]
  one_mul a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one]
  mul_one a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one]
  inv_mul_cancel a := ext <| fun _ hi => by
    simp_rw [getElem_mul, getElem_one, getElem_inv_getElem]

@[simp]
theorem getElem_pow_add (a : ArrayPerm n) {i x y : ℕ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [pow_add, getElem_mul]

@[simp]
theorem getElem_zpow_add (a : ArrayPerm n) {i : ℕ} {x y : ℤ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [zpow_add, getElem_mul]

instance : MulAction (ArrayPerm n) (Fin n) where
  one_smul _ := Fin.ext <| by simp_rw [val_smul, getElem_one]
  mul_smul _ _ _ := Fin.ext <| by simp_rw [val_smul, getElem_mul]

open Equiv.Perm in
/--
`ArrayPerm n` is equivalent to `Perm (Fin n)`, and this equivalence respects the
multiplication (and, indeed, the scalar action on `Fin n`).
-/
@[simps! apply_apply_val apply_symm_apply_val]
def finPerm (n : ℕ) : ArrayPerm n ≃* Perm (Fin n) where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  invFun π := ⟨Array.ofFn (val ∘ π), Array.ofFn (val ∘ π.symm), size_ofFn _, size_ofFn _,
  fun _ => (Array.getElem_ofFn _ _ _).trans_lt (is_lt _),
  fun _ => (Array.getElem_ofFn _ _ _).trans_lt (is_lt _),
  fun _ => by simp_rw [Array.getElem_ofFn, comp_apply, Fin.eta, symm_apply_apply]⟩
  left_inv a := ArrayPerm.ext <| fun _ _ => by simp_rw [coe_fn_mk, coe_fn_symm_mk, getElem_mk,
    Array.getElem_ofFn, comp_apply, val_smul]
  right_inv π := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [coe_fn_mk, val_smul, getElem_mk,
    Array.getElem_ofFn, Fin.eta, comp_apply]
  map_mul' a b := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [mul_inv_rev, Perm.coe_mul,
    comp_apply, coe_fn_mk, val_smul, getElem_mul]

@[simp]
theorem finPerm_symm_apply_getElem (π : Perm (Fin n)) {i : ℕ} {hi : i < n} :
    ((finPerm n).symm π)[i] = π ⟨i, hi⟩ := by
  unfold finPerm
  simp_rw [MulEquiv.symm_mk, MulEquiv.coe_mk, coe_fn_symm_mk, getElem_mk, Array.getElem_ofFn,
    comp_apply]

@[simp]
theorem finPerm_symm_apply_getElem_inv (π : Perm (Fin n)) {i : ℕ} {hi : i < n} :
    ((finPerm n).symm π)⁻¹[i] = π⁻¹ ⟨i, hi⟩ := by
  rw [← map_inv, finPerm_symm_apply_getElem]

instance : Fintype (ArrayPerm n) := Fintype.ofEquiv (Perm (Fin n)) (finPerm n).symm.toEquiv

instance : Inhabited (ArrayPerm n) := Equiv.inhabited (finPerm n).toEquiv

@[simp]
theorem default_eq : (default : ArrayPerm n) = 1 := map_one ((finPerm n).symm)

instance : Unique (ArrayPerm 0) := Equiv.unique (finPerm 0).toEquiv

instance : Unique (ArrayPerm 1) := Equiv.unique (finPerm 1).toEquiv

instance : DecidableEq (ArrayPerm n) := Equiv.decidableEq (finPerm n).toEquiv

lemma isOfFinOrder (a : ArrayPerm n) : IsOfFinOrder a := isOfFinOrder_of_finite _

lemma orderOf_pos (a : ArrayPerm n) : 0 < orderOf a := by
  rw [orderOf_pos_iff]
  exact a.isOfFinOrder

instance : SMul (ArrayPerm n) ℕ where
  smul a i := if h : i < n then a[i]'h else i

theorem smul_nat_eq_dite (a : ArrayPerm n) (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i := rfl

theorem smul_of_lt {a : ArrayPerm n} {i : ℕ} (h : i < n) : a • i = a[i] := dif_pos h

theorem smul_of_ge {a : ArrayPerm n} {i : ℕ} (h : n ≤ i) : a • i = i := dif_neg (not_lt_of_le h)

theorem getElem_eq_smul {a : ArrayPerm n} {i : ℕ} (h : i < n) : a[i] = a • i := (dif_pos _).symm

theorem smul_val (a : ArrayPerm n) {i : Fin n} :
    a • i.1 = ((a • i) : Fin n) := smul_of_lt _

@[simp]
theorem smul_getElem {a b : ArrayPerm n} {i : ℕ} (h : i < n) : a • b[i] = a[b[i]] := smul_of_lt _

theorem smul_eq_iff {a : ArrayPerm n} {i j : ℕ} :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by
  rw [smul_nat_eq_dite, dite_eq_iff', not_lt]

theorem eq_smul_iff {a : ArrayPerm n} {i j : ℕ} :
    i = a • j ↔ (∀ (hj : j < n), i = a[j]) ∧ (n ≤ j → i = j) := by
  simp_rw [eq_comm (a := i), smul_eq_iff]

theorem smul_eq_self_iff {a : ArrayPerm n} {i : ℕ} :
  a • i = i ↔ ∀ (hi : i < n), a[i] = i := dite_eq_right_iff

theorem self_eq_smul_iff {a : ArrayPerm n} {i : ℕ} :
    i = a • i ↔ ∀ (hi : i < n), i = a[i] := by
  simp_rw [eq_comm (a := i), smul_eq_self_iff]

instance : MulAction (ArrayPerm n) ℕ where
  one_smul k := (lt_or_le k n).by_cases
    (fun hk => smul_of_lt hk ▸ getElem_one _) (fun hk => smul_of_ge hk)
  mul_smul _ _ k := (lt_or_le k n).by_cases
    (fun hk => by simp_rw [smul_of_lt hk, getElem_mul, smul_of_lt getElem_lt])
    (fun hk => by simp_rw [smul_of_ge hk])

theorem smul_eq_smul_same_iff {a b : ArrayPerm n} {i : ℕ} :
  a • i = b • i ↔ ∀ (hi : i < n), a[i] = b[i] := by
  simp_rw [← inv_smul_eq_iff, ← mul_smul, smul_eq_self_iff, getElem_mul,
  forall_congr' fun h => b.getElem_inv_eq_iff getElem_lt h]

theorem eq_iff_smul_eq_smul_lt {a b : ArrayPerm n} : a = b ↔ ∀ i < n, a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, ArrayPerm.ext_iff]
  refine forall_congr' fun i => ?_
  rw [Classical.imp_iff_left_iff]
  exact (lt_or_le i n).imp id fun h => by simp_rw [h.not_lt, forall_false]

instance : FaithfulSMul (ArrayPerm n) ℕ where
  eq_of_smul_eq_smul := by
    simp_rw [eq_iff_smul_eq_smul_lt]
    exact fun h _ _ => h _

theorem smul_nat_right_inj (a : ArrayPerm n) {i j : ℕ} : a • i = a • j ↔ i = j := by
  simp_rw [← inv_smul_eq_iff, inv_smul_smul]

@[simp]
theorem smul_lt_iff_lt (a : ArrayPerm n) {i : ℕ} : a • i < n ↔ i < n := by
  rcases lt_or_le i n with h | h
  · simp_rw [h, iff_true, smul_of_lt h, getElem_lt]
  · simp_rw [h.not_lt, iff_false, not_lt, smul_of_ge h, h]

theorem smul_lt_of_lt {a : ArrayPerm n} {i : ℕ} (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

theorem lt_of_smul_lt {a : ArrayPerm n} {i : ℕ} (h : a • i < n) : i < n := a.smul_lt_iff_lt.mp h

theorem smul_eq_iff_eq_one (a : ArrayPerm n) : (∀ i < n, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul_lt, one_smul]

theorem smul_eq_id_iff_eq_one (a : ArrayPerm n) : ((a • ·) : Fin n → Fin n) = id ↔ a = 1 := by
  simp_rw [← one_smul_eq_id (ArrayPerm n), funext_iff, eq_iff_smul_eq_smul]

theorem smul_nat_eq_iff_eq_one (a : ArrayPerm n) : (∀ i : ℕ, a • i = i) ↔ a = 1 := by
  simp_rw [← smul_eq_iff_eq_one, smul_nat_eq_dite, dite_eq_right_iff]
  exact forall₂_congr (fun a ha => ⟨fun h _ => h, fun h => h _⟩)

theorem smul_nat_eq_id_iff_eq_one (a : ArrayPerm n) : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [funext_iff, id_eq, smul_nat_eq_iff_eq_one]

theorem fixedBy_of_ge {a : ArrayPerm n} {i : ℕ} (h : n ≤ i) :
    i ∈ MulAction.fixedBy ℕ a := by
  rw [MulAction.mem_fixedBy]
  exact smul_of_ge h

theorem Ici_subset_fixedBy {a : ArrayPerm n} :
    Set.Ici n ⊆ MulAction.fixedBy ℕ a := fun _ => fixedBy_of_ge

theorem Ici_subset_fixedPoints :
    Set.Ici n ⊆ MulAction.fixedPoints (ArrayPerm n) ℕ := fun _ hx _ => smul_of_ge hx

open Pointwise in
theorem Iic_mem_set_fixedBy {a : ArrayPerm n} :
    Set.Iio n ∈ MulAction.fixedBy (Set ℕ) a := Set.ext <| fun _ => by
  rw [← inv_inv a]
  simp_rw [Set.mem_inv_smul_set_iff, Set.mem_Iio, smul_lt_iff_lt]

theorem fixedBy_image_val_subset {a : ArrayPerm n} :
    (MulAction.fixedBy (Fin n) a).image (Fin.val) ⊆ MulAction.fixedBy ℕ a := fun _ => by
  simp_rw [Set.mem_image, MulAction.mem_fixedBy, forall_exists_index, and_imp,
  Fin.forall_iff, Fin.ext_iff, smul_mk]
  rintro _ h ha rfl
  exact (smul_of_lt h).trans ha

theorem period_eq_one_of_ge {a : ArrayPerm n} {i : ℕ} (hi : n ≤ i) : MulAction.period a i = 1 := by
  simp_rw [MulAction.period_eq_one_iff, smul_of_ge hi]

theorem period_eq_one_iff (a : ArrayPerm n) {i : ℕ} :
    MulAction.period a i = 1 ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [MulAction.period_eq_one_iff]
  rcases lt_or_le i n with hi | hi
  · simp_rw [hi, forall_true_left, smul_of_lt hi]
  · simp_rw [hi.not_lt, forall_false, iff_true, smul_of_ge hi]

@[simp]
theorem getElem_pow_period {a : ArrayPerm n} {i : ℕ} {hi : i < n} :
    (a ^ MulAction.period a i)[i] = i := by
  rw [← smul_of_lt hi, MulAction.pow_period_smul]

theorem getElem_pow_mod_period {a : ArrayPerm n} {i : ℕ} {hi : i < n} (k : ℕ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt hi, MulAction.pow_mod_period_smul]

theorem getElem_zpow_mod_period {a : ArrayPerm n} {i : ℕ} {hi : i < n} (k : ℤ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt hi, MulAction.zpow_mod_period_smul]

theorem period_nat_pos (a : ArrayPerm n) {i : ℕ} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_pos (a : ArrayPerm n) {i : Fin n} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_fin {a : ArrayPerm n} {i : Fin n} :
    MulAction.period a i = MulAction.period a (i : ℕ) := by
  rw [le_antisymm_iff]
  refine ⟨MulAction.period_le_of_fixed (period_nat_pos _) (Fin.ext ?_),
    MulAction.period_le_of_fixed (period_pos _) ?_⟩
  · simp_rw [val_smul, getElem_pow_period]
  · simp_rw [smul_val, MulAction.pow_period_smul]

@[simp]
theorem period_mk {a : ArrayPerm n} {i : ℕ} {hi : i < n} :
    MulAction.period a (Fin.mk i hi) = MulAction.period a i := period_fin

theorem period_eq_one_of_zero (a : ArrayPerm 0) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_eq_one_of_one (a : ArrayPerm 1) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_le_card_of_getElem_pow_mem (a : ArrayPerm n) {i : ℕ} (hi : i < n)
  (s : Finset ℕ) : (∀ k < s.card + 1, (a ^ k)[i] ∈ s) → MulAction.period a i ≤ s.card := by
  simp_rw [← smul_of_lt hi]
  exact MulAction.period_le_card_of_smul_pow_mem _ _

theorem getElem_injOn_range_period (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    Set.InjOn (fun k => (a ^ k)[i]) (Finset.range (MulAction.period a i)) := by
  simp_rw [← smul_of_lt hi]
  exact MulAction.smul_injOn_range_period _

theorem period_le_of_lt (a : ArrayPerm n) {i : ℕ} (hi : i < n) : MulAction.period a i ≤ n := by
  refine (period_le_card_of_getElem_pow_mem a hi (Finset.range n) ?_).trans_eq
    (Finset.card_range _)
  simp_rw [Finset.card_range, Finset.mem_range, getElem_lt, implies_true]

theorem period_le_of_ne_zero [NeZero n] (a : ArrayPerm n) {i : ℕ} : MulAction.period a i ≤ n := by
  rcases lt_or_le i n with hi | hi
  · exact a.period_le_of_lt hi
  · rw [a.period_eq_one_of_ge hi]
    exact NeZero.pos n

theorem exists_pos_le_pow_getElem_eq (a : ArrayPerm n) {i : ℕ} (hi : i < n) :
    ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k)[i] = i :=
  ⟨MulAction.period a i, a.period_nat_pos, a.period_le_of_lt hi, getElem_pow_period⟩

/--
`ofPerm` maps a member of `Perm ℕ` which maps the subtype `< n` to itself to the corresponding
`ArrayPerm n`.
-/
def ofPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) : ArrayPerm n where
  fwdArray := (Array.range n).map f
  bwdArray := (Array.range n).map ⇑f⁻¹
  getElem_fwdArray_lt' := fun {i} => by
    simp_rw [Array.getElem_map, Array.getElem_range, hf, imp_self]
  getElem_bwdArray_lt' := fun {i} => by
    simp_rw [Array.getElem_map, Array.getElem_range,
    (hf (f⁻¹ i)).symm, Perm.apply_inv_self, imp_self]
  size_fwdArray' := by simp only [size_map, size_range]
  size_bwdArray' := by simp only [size_map, size_range]
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

/--
`natPerm` is the injective monoid homomorphism from `ArrayPerm n` to `Perm ℕ`.
-/

def natPerm (n : ℕ) : ArrayPerm n →* Perm ℕ :=
  (Perm.extendDomainHom equivSubtype).comp (finPerm n : ArrayPerm _ →* Equiv.Perm (Fin n))

@[simp]
theorem natPerm_apply_apply (a : ArrayPerm n) {i : ℕ} : natPerm n a i = a • i := by
  unfold natPerm
  simp_rw [MonoidHom.comp_apply, MonoidHom.coe_coe, Perm.extendDomainHom_apply]
  rcases lt_or_le i n with hi | hi
  · simp_rw [Perm.extendDomain_apply_subtype _ equivSubtype hi, smul_of_lt hi,
      equivSubtype_symm_apply, equivSubtype_apply, finPerm_apply_apply_val]
  · simp_rw [Perm.extendDomain_apply_not_subtype _ equivSubtype hi.not_lt, smul_of_ge hi]

@[simp]
theorem natPerm_apply_symm_apply (a : ArrayPerm n) {i : ℕ} : (natPerm n a).symm i = a⁻¹ • i := by
  rw [← Perm.inv_def, ← map_inv, natPerm_apply_apply]

@[simp]
theorem natPerm_lt_iff_lt (a : ArrayPerm n) {i : ℕ} : natPerm n a i < n ↔ i < n := by
  rw [natPerm_apply_apply, smul_lt_iff_lt]

theorem natPerm_apply_apply_of_lt (a : ArrayPerm n) {i : ℕ} (h : i < n) :
    natPerm n a i = a[i] := by rw [natPerm_apply_apply, smul_of_lt h]

theorem natPerm_apply_apply_of_ge (a : ArrayPerm n) {i : ℕ} (h : n ≤ i) : natPerm n a i = i := by
  rw [natPerm_apply_apply, smul_of_ge h]

theorem natPerm_apply_symm_apply_of_lt (a : ArrayPerm n) {i : ℕ} (h : i < n) :
    (natPerm n a)⁻¹ i = a⁻¹[i] := by
  simp_rw [← MonoidHom.map_inv, natPerm_apply_apply_of_lt _ h]

theorem natPerm_apply_symm_apply_of_ge (a : ArrayPerm n) {i : ℕ} (h : n ≤ i) :
    (natPerm n a)⁻¹ i = i := by rw [← MonoidHom.map_inv, natPerm_apply_apply_of_ge _ h]

theorem natPerm_injective : Function.Injective (natPerm n) :=
  (Equiv.Perm.extendDomainHom_injective equivSubtype).comp (finPerm n).injective

theorem natPerm_inj {a b : ArrayPerm n} : natPerm n a = natPerm n b ↔ a = b :=
  natPerm_injective.eq_iff

theorem natPerm_ofPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) (i : ℕ) :
    natPerm n (ofPerm f hf) i = if i < n then f i else i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [natPerm_apply_apply_of_lt _ hi, getElem_ofPerm, hi, if_true]
  · simp_rw [natPerm_apply_apply_of_ge _ hi, hi.not_lt, if_false]

theorem ofPerm_natPerm (a : ArrayPerm n) :
    ofPerm (natPerm n a) (fun _ => a.natPerm_lt_iff_lt) = a := by
  ext i hi
  simp_rw [getElem_ofPerm, a.natPerm_apply_apply_of_lt hi]

theorem apply_eq_of_ge_iff_exists_natPerm_apply (e : Perm ℕ) :
    (∀ i ≥ n, e i = i) ↔ ∃ a : ArrayPerm n, natPerm n a = e := by
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

variable {α : Type*}

def onIndices (a : ArrayPerm n) (as : Array α) (has : n ≤ as.size) : Array α :=
    as.mapIdx (fun i _ => if hi : i < n then as[a[i.1]]'(getElem_lt.trans_le has) else as[i.1])

@[simp]
theorem size_onIndices {a : ArrayPerm n} {as : Array α} {has : n ≤ as.size} :
    size (a.onIndices as has) = as.size := size_mapIdx _ _

@[simp]
theorem getElem_onIndices {a : ArrayPerm n} {as : Array α} {has : n ≤ as.size} {i : ℕ}
    {hi : i < (a.onIndices as has).size} :
    (a.onIndices as has)[i] =
    if h : i < n then as[a[i]]'(getElem_lt.trans_le has) else as[i]'(hi.trans_eq size_onIndices) :=
  Array.getElem_mapIdx _ _ _ _

theorem getElem_onIndices_getElem_inv {a : ArrayPerm n} {as : Array α} {has : n ≤ as.size}
    {i : ℕ} {hi : i < n} : (a.onIndices as has)[a⁻¹[i]]'
    (getElem_lt.trans_le <| has.trans_eq size_onIndices.symm) = as[i] := by
  simp_rw [getElem_onIndices, getElem_lt, dite_true, getElem_getElem_inv]

@[simp]
theorem one_onIndices {as : Array α} {has : n ≤ as.size} :
    (1 : ArrayPerm n).onIndices as has = as := by
  simp_rw [Array.ext_iff, size_onIndices, getElem_onIndices, getElem_one, dite_eq_right_iff,
    implies_true, and_self]

theorem mul_onIndices {a b : ArrayPerm n} {as : Array α} {has : n ≤ as.size} :
    (a * b).onIndices as has = b.onIndices (a.onIndices as has)
    (has.trans_eq size_onIndices.symm) := by
  simp_rw [Array.ext_iff, size_onIndices, getElem_onIndices, getElem_mul,
    getElem_lt, dite_true, true_and]
  intros i _ _
  rcases lt_or_le i n with hin | hin
  · simp_rw [hin, dite_true]
  · simp_rw [hin.not_lt, dite_false]

theorem mem_of_mem_onIndices {a : ArrayPerm n} {as : Array α} {has : n ≤ as.size} {x : α}
    (hx : x ∈ a.onIndices as has) : x ∈ as := by
  simp_rw [Array.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_onIndices, size_onIndices] at hx
  rcases hx with ⟨i, hi, hix⟩
  rcases lt_or_le i n with hin | hin
  · simp_rw [hin, dite_true] at hix
    exact ⟨a[i], getElem_lt.trans_le has, hix⟩
  · simp_rw [hin.not_lt, dite_false] at hix
    exact ⟨i, hi, hix⟩

theorem mem_onIndices_of_mem {a : ArrayPerm n} {as : Array α} {has : n ≤ as.size} {x : α}
    (hx : x ∈ as) : x ∈ a.onIndices as has := by
  simp_rw [Array.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_onIndices, size_onIndices]
  rcases hx with ⟨i, hi, hix⟩
  rcases lt_or_le i n with hin | hin
  · refine ⟨a⁻¹[i], getElem_lt.trans_le has, ?_⟩
    simp_rw [getElem_lt, dite_true, getElem_getElem_inv, hix]
  · refine ⟨i, hi, ?_⟩
    simp_rw [hin.not_lt, dite_false, hix]

theorem mem_onIndices_iff {a : ArrayPerm n} {as : Array α} {has : n ≤ as.size} {x : α} :
    x ∈ a.onIndices as has ↔ x ∈ as := ⟨mem_of_mem_onIndices, mem_onIndices_of_mem⟩

@[simp]
theorem onIndices_range (a : ArrayPerm n) :
    a.onIndices (Array.range n) size_range.ge = a.fwdArray := by
  simp_rw [Array.ext_iff, size_onIndices, size_range, size_fwdArray, getElem_onIndices,
    Array.getElem_range, getElem_fwdArray, true_and]
  exact fun _ hin => by simp_rw [hin, dite_true, implies_true]

@[simp]
theorem onIndices_enum (a : ArrayPerm n) :
    a.onIndices (Fin.enum n) (size_enum _).ge = a.finFwdArray := by
  simp_rw [Array.ext_iff, size_onIndices, size_finFwdArray, getElem_onIndices, Fin.getElem_enum,
    getElem_finFwdArray, size_enum, true_and]
  exact fun _ hin => by simp_rw [hin, dite_true, implies_true]

def cycleOf (a : ArrayPerm n) (x : ℕ) : Finset ℕ :=
  if h : x < n then (Finset.range n).image (fun k => (a ^ k)[x]) else {x}

theorem cycleOf_lt {a : ArrayPerm n} {x : ℕ} (hx : x < n) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k)[x]) := by
  unfold cycleOf
  simp_rw [dif_pos hx, Finset.ext_iff, Finset.mem_image, Finset.mem_range]
  refine fun _ => ⟨fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos,
    by simp_rw [getElem_pow_mod_period, h]⟩, fun ⟨_, hlt, h⟩ =>
    ⟨_, (hlt.trans_le <| a.period_le_of_lt hx), h⟩⟩

theorem cycleOf_ge {a : ArrayPerm n} {x : ℕ} (hx : n ≤ x) :
    a.cycleOf x = {x} := dif_neg (not_lt_of_le hx)

theorem card_cycleOf (a : ArrayPerm n) (x : ℕ) : (a.cycleOf x).card = MulAction.period a x := by
  rcases lt_or_le x n with hx | hx
  · refine Eq.trans ?_ (Finset.card_range (MulAction.period a x))
    rw [cycleOf_lt hx, Finset.card_image_iff]
    exact getElem_injOn_range_period _ _
  · rw [cycleOf_ge hx, period_eq_one_of_ge hx, Finset.card_singleton]

theorem cycleOf_eq_map_smul_range_period (a : ArrayPerm n) (x : ℕ) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k) • x) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleOf_lt hx, smul_of_lt hx]
  · simp_rw [cycleOf_ge hx, smul_of_ge hx, Finset.ext_iff, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range, exists_and_right]
    exact fun _ => ⟨fun h => h ▸ ⟨⟨0, a.period_nat_pos⟩, rfl⟩, fun h => h.2.symm⟩

theorem mem_cycleOf_iff_exists_pow_lt_period_smul (a : ArrayPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i) • x = y := by
  rw [cycleOf_eq_map_smul_range_period]
  simp_rw [Finset.mem_image, Finset.mem_range]

theorem mem_cycleOf_iff_exists_pow_smul (a : ArrayPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_lt_period_smul]
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩,
    fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos, ?_⟩⟩
  simp_rw [MulAction.pow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_zpow_smul (a : ArrayPerm n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_smul]
  refine ⟨fun ⟨_, h⟩ => ⟨_, (zpow_natCast a _).symm ▸ h⟩,
    fun ⟨k, h⟩ => ⟨(k % MulAction.period a x).toNat, ?_⟩⟩
  simp_rw [← zpow_natCast, Int.toNat_of_nonneg
    (Int.emod_nonneg _ ((Nat.cast_ne_zero (R := ℤ)).mpr (a.period_nat_pos (i := x)).ne')),
    MulAction.zpow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_getElem_pow_lt_period (a : ArrayPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_lt_period_smul, smul_of_lt hx]

theorem mem_cycleOf_iff_exists_getElem_pow (a : ArrayPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul, smul_of_lt hx]

theorem mem_cycleOf_iff_exists_getElem_zpow (a : ArrayPerm n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul, smul_of_lt hx]

theorem self_mem_cycleOf (a : ArrayPerm n) (x : ℕ) : x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨0, by simp only [pow_zero, one_smul]⟩

theorem nonempty_cycleOf {a : ArrayPerm n} {x : ℕ} : (a.cycleOf x).Nonempty :=
  ⟨_, a.self_mem_cycleOf x⟩

theorem smul_mem_cycleOf (a : ArrayPerm n) (x : ℕ) : (a • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨1, by simp only [pow_one]⟩

theorem smul_inv_mem_cycleOf (a : ArrayPerm n) (x : ℕ) : (a⁻¹ • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨-1, by simp only [zpow_neg, zpow_one]⟩

theorem smul_pow_mem_cycleOf (a : ArrayPerm n) (x k : ℕ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨k, rfl⟩

theorem smul_zpow_mem_cycleOf (a : ArrayPerm n) (x : ℕ) (k : ℤ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨k, rfl⟩

theorem getElem_mem_cycleOf (a : ArrayPerm n) {x : ℕ} (hx : x < n) : a[x] ∈ a.cycleOf x := by
  convert a.smul_mem_cycleOf x
  rw [smul_of_lt hx]

theorem getElem_inv_mem_cycleOf (a : ArrayPerm n) {x : ℕ} (hx : x < n) : a⁻¹[x] ∈ a.cycleOf x := by
  convert a.smul_inv_mem_cycleOf x
  rw [smul_of_lt hx]

theorem getElem_pow_mem_cycleOf (a : ArrayPerm n) {x : ℕ} (hx : x < n) (k : ℕ):
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_pow_mem_cycleOf x k
  rw [smul_of_lt hx]

theorem getElem_zpow_mem_cycleOf (a : ArrayPerm n) {x : ℕ} (hx : x < n) (k : ℤ) :
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_zpow_mem_cycleOf x k
  rw [smul_of_lt hx]

theorem getElem_inv_pow_mem_cycleOf (a : ArrayPerm n) {x : ℕ} (hx : x < n) (k : ℕ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  convert a.getElem_zpow_mem_cycleOf hx (-(k : ℤ))
  simp_rw [inv_pow, zpow_neg, zpow_natCast]

theorem getElem_inv_zpow_mem_cycleOf (a : ArrayPerm n) {x : ℕ} (hx : x < n) (k : ℤ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  simp only [inv_zpow']
  exact a.getElem_zpow_mem_cycleOf hx (-k)

def CycleMinArrayAux (a : ArrayPerm n) : ℕ → ArrayPerm n × {a : Array ℕ // a.size = n}
  | 0 => ⟨1, range n, size_range⟩
  | 1 =>
    ⟨a, (Array.range n).zipWith a.fwdArray min, by
    rw [Array.size_zipWith, size_range, a.size_fwdArray, min_self]⟩
  | (i+2) =>
    let ⟨ρ, b, hb⟩ := a.CycleMinArrayAux (i + 1)
    let ρ' := ρ ^ 2
    ⟨ρ', b.zipWith (ρ'.onIndices b hb.ge) min,
    by simp_rw [Array.size_zipWith, size_onIndices, min_self, hb]⟩

@[simp]
theorem cycleMinAux_zero_fst (a : ArrayPerm n) : (a.CycleMinArrayAux 0).1 = 1 := rfl

@[simp]
theorem cycleMinAux_succ_fst (a : ArrayPerm n) (i : ℕ) :
    (a.CycleMinArrayAux (i + 1)).1 = a ^ (2 ^ i) := by
  induction' i with i IH
  · rw [pow_zero, pow_one]
    rfl
  · rw [pow_succ, pow_mul]
    exact IH ▸ rfl

def CycleMinArray (a : ArrayPerm n) (i : ℕ) : Array ℕ := (a.CycleMinArrayAux i).2

@[simp]
theorem cycleMinAux_snd_val {a : ArrayPerm n} {i : ℕ} :
    (a.CycleMinArrayAux i).2 = CycleMinArray a i := rfl

@[simp]
theorem size_cycleMinArray {a : ArrayPerm n} {i : ℕ} :
    (a.CycleMinArray i).size = n := (a.CycleMinArrayAux i).2.2

theorem getElem_cycleMinArray_zero {a : ArrayPerm n} {x : ℕ} (hx : x < (a.CycleMinArray 0).size):
  (a.CycleMinArray 0)[x] = x := Array.getElem_range _

theorem getElem_cycleMinArray_succ {a : ArrayPerm n} {i x : ℕ}
    (hx : x < (a.CycleMinArray (i + 1)).size) :
    (a.CycleMinArray (i + 1))[x] = min ((a.CycleMinArray i)[x]'
    (hx.trans_eq <| size_cycleMinArray.trans size_cycleMinArray.symm))
    ((a.CycleMinArray i)[(a^2^i)[x]'(hx.trans_eq size_cycleMinArray)]'
    (getElem_lt.trans_eq size_cycleMinArray.symm)) := by
  rcases i with (_ | i) <;>
  refine (Array.getElem_zipWith _).trans ?_
  · simp_rw [Array.getElem_range, getElem_fwdArray, getElem_cycleMinArray_zero, pow_zero, pow_one]
  · simp_rw [getElem_onIndices, hx.trans_eq size_cycleMinArray, dite_true,
      cycleMinAux_snd_val, cycleMinAux_succ_fst, ← pow_mul, ← pow_succ]

@[simp]
theorem getElem_cycleMinArray_lt {a : ArrayPerm n} {i : ℕ} {x : ℕ}
    (hx : x < (a.CycleMinArray i).size) : (a.CycleMinArray i)[x] < n := by
  induction' i with i IH generalizing x
  · simp_rw [getElem_cycleMinArray_zero]
    exact hx.trans_eq size_cycleMinArray
  · simp_rw [getElem_cycleMinArray_succ, min_lt_iff, IH, true_or]

lemma getElem_cycleMinArray_le_getElem_pow_lt (a : ArrayPerm n) {i : ℕ} {x : ℕ}
    {hx : x < (a.CycleMinArray i).size} {k : ℕ} (hk : k < 2^i) :
    (a.CycleMinArray i)[x] ≤ (a ^ k)[x]'(hx.trans_eq size_cycleMinArray) := by
  induction' i with i IH generalizing x k
  · simp_rw [pow_zero, Nat.lt_one_iff] at hk
    simp_rw [getElem_cycleMinArray_zero, hk, pow_zero, getElem_one, le_rfl]
  · simp_rw [getElem_cycleMinArray_succ, min_le_iff]
    by_cases hk' : k < 2^i
    · exact Or.inl (IH hk')
    · rw [pow_succ', Nat.two_mul, ← Nat.sub_lt_iff_lt_add (le_of_not_lt hk')] at hk
      exact Or.inr ((IH hk).trans_eq <| by
        rw [getElem_pow_add, Nat.sub_add_cancel (le_of_not_lt hk')])

lemma getElem_cycleMinArray_le_getElem_pow_of_period_le_two_pow (a : ArrayPerm n) (i : ℕ) {x : ℕ}
    (hx : x < (a.CycleMinArray i).size) (hai : MulAction.period a x ≤ 2^i) :
    ∀ k, (a.CycleMinArray i)[x] ≤ (a ^ k)[x]'(hx.trans_eq size_cycleMinArray) := fun k => by
  simp_rw [size_cycleMinArray] at hx
  have H := a.getElem_pow_mem_cycleOf hx k
  rw [mem_cycleOf_iff_exists_getElem_pow_lt_period] at H
  rcases H with ⟨_, hk₁, hk₂⟩
  exact (a.getElem_cycleMinArray_le_getElem_pow_lt (hk₁.trans_le hai)).trans_eq hk₂

lemma getElem_cycleMinArray_le_getElem_zpow_of_period_le_two_pow (a : ArrayPerm n) (i : ℕ) {x : ℕ}
      (hx : x < (a.CycleMinArray i).size) (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, (a.CycleMinArray i)[x] ≤ (a ^ k)[x]'(hx.trans_eq size_cycleMinArray) := fun k => by
  simp_rw [size_cycleMinArray] at hx
  have H := a.getElem_zpow_mem_cycleOf hx k
  rw [mem_cycleOf_iff_exists_getElem_pow_lt_period] at H
  rcases H with ⟨_, hk₁, hk₂⟩
  exact (a.getElem_cycleMinArray_le_getElem_pow_lt (hk₁.trans_le hai)).trans_eq hk₂

lemma getElem_cycleMinArray_le_self (a : ArrayPerm n) (i : ℕ) {x : ℕ}
      (hx : x < (a.CycleMinArray i).size) : (a.CycleMinArray i)[x] ≤ x :=
  (a.getElem_cycleMinArray_le_getElem_pow_lt (Nat.two_pow_pos _)).trans_eq
      (by simp_rw [pow_zero, getElem_one])

lemma exists_lt_getElem_cycleMin_eq_getElem_pow (a : ArrayPerm n) (i : ℕ) {x : ℕ}
      (hx : x < (a.CycleMinArray i).size) :
    ∃ k < 2^i, (a.CycleMinArray i)[x] = (a ^ k)[x]'(hx.trans_eq size_cycleMinArray) := by
  induction' i with i IH generalizing x
  · simp_rw [getElem_cycleMinArray_zero]
    exact ⟨0, Nat.two_pow_pos _, pow_zero a ▸ (getElem_one _).symm⟩
  · have hx' := hx.trans_eq size_cycleMinArray
    simp_rw [size_cycleMinArray] at IH
    rcases IH hx' with ⟨k, hk, hπk⟩
    rcases (IH (x := (a ^ (2 ^ i))[x]) getElem_lt) with ⟨k', hk', hπk'⟩
    simp_rw [getElem_cycleMinArray_succ, hπk, hπk', getElem_pow_add,
    pow_succ', Nat.two_mul]
    rcases lt_or_le ((a ^ k)[x]) ((a ^ (k' + 2 ^ i))[x]) with hkk' | hkk'
    · rw [min_eq_left hkk'.le]
      exact ⟨k, hk.trans (Nat.lt_add_of_pos_right (Nat.two_pow_pos _)), rfl⟩
    · rw [min_eq_right hkk']
      exact ⟨k' + 2^i, Nat.add_lt_add_right hk' _, rfl⟩

lemma getElem_cycleMinArray_eq_min'_cycleOf (a : ArrayPerm n) (i : ℕ) {x : ℕ}
      (hx : x < (a.CycleMinArray i).size) (hai : MulAction.period a x ≤ 2^i) :
      (a.CycleMinArray i)[x] = (a.cycleOf x).min' nonempty_cycleOf := by
  simp_rw [size_cycleMinArray] at hx
  refine le_antisymm (Finset.le_min' _ _ _ ?_) (Finset.min'_le _ _ ?_) <;>
  simp_rw [mem_cycleOf_iff_exists_getElem_pow _ hx]
  · simp_rw [forall_exists_index, forall_apply_eq_imp_iff]
    exact getElem_cycleMinArray_le_getElem_pow_of_period_le_two_pow _ _ _ hai
  · rcases a.exists_lt_getElem_cycleMin_eq_getElem_pow i (x := x) (by assumption) with ⟨k, _, hk⟩
    exact ⟨_, hk.symm⟩

def CycleMin (a : ArrayPerm n) (i : ℕ) (x : ℕ) : ℕ := (a.CycleMinArray i)[x]?.getD x

theorem getElem_cycleMinArray (a : ArrayPerm n) (i : ℕ) {x : ℕ}
    (hx : x < (a.CycleMinArray i).size) : (a.CycleMinArray i)[x] = a.CycleMin i x :=
  (getD_of_lt _ _ _ _).symm

theorem cycleMin_of_lt {a : ArrayPerm n} {i x : ℕ} (hx : x < n) :
    a.CycleMin i x = (a.CycleMinArray i)[x]'(hx.trans_eq size_cycleMinArray.symm) :=
  getD_of_lt _ _ _ _

theorem cycleMin_of_getElem {a b : ArrayPerm n} {i x : ℕ} (hx : x < n) :
    a.CycleMin i (b[x]) = (a.CycleMinArray i)[b[x]]'(getElem_lt.trans_eq size_cycleMinArray.symm) :=
  getD_of_lt _ _ _ _

theorem cycleMin_of_ge {a : ArrayPerm n} {i x : ℕ} (hx : n ≤ x) :
    a.CycleMin i x = x := getD_of_ge _ _ _ (size_cycleMinArray.trans_le hx)

@[simp]
theorem cycleMin_zero {a : ArrayPerm n} {x : ℕ} :
  a.CycleMin 0 x = x := if hx : x < n then
    (cycleMin_of_lt hx).trans <| Array.getElem_range _ else cycleMin_of_ge (le_of_not_lt hx)

@[simp]
theorem cycleMin_succ {a : ArrayPerm n} {i x : ℕ} :
    a.CycleMin (i + 1) x = min (a.CycleMin i x) (a.CycleMin i (a^2^i • x)) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [smul_of_lt hx, cycleMin_of_lt hx, cycleMin_of_getElem, getElem_cycleMinArray_succ]
  · simp_rw [smul_of_ge hx, cycleMin_of_ge hx, min_self]

@[simp]
theorem cycleMin_lt_iff_lt {a : ArrayPerm n} {i : ℕ} {x : ℕ} :
    a.CycleMin i x < n ↔ x < n := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, hx, getElem_cycleMinArray_lt]
  · simp_rw [cycleMin_of_ge hx]

lemma cycleMin_le_smul_pow_lt_two_pow (a : ArrayPerm n) {i : ℕ} (x : ℕ) {k : ℕ} (hk : k < 2^i) :
    a.CycleMin i x ≤ (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinArray_le_getElem_pow_lt _ hk
  · simp_rw [cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_pow_smul_of_period_le_two_pow (a : ArrayPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) : ∀ k, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinArray_le_getElem_pow_of_period_le_two_pow _ _ _ hai _
  · simp_rw [cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_zpow_smul_of_period_le_two_pow  (a : ArrayPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, smul_of_lt hx]
    exact getElem_cycleMinArray_le_getElem_zpow_of_period_le_two_pow _ _ _ hai _
  · simp_rw [cycleMin_of_ge hx, smul_of_ge hx, le_rfl]

lemma cycleMin_le_self (a : ArrayPerm n) (i : ℕ) {x : ℕ} :
    a.CycleMin i x ≤ x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx]
    exact getElem_cycleMinArray_le_self _ _ _
  · simp_rw [cycleMin_of_ge hx, le_rfl]

lemma exists_lt_cycleMin_eq_smul_pow (a : ArrayPerm n) (i : ℕ) {x : ℕ} :
    ∃ k < 2^i, a.CycleMin i x = (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx, smul_of_lt hx]
    exact exists_lt_getElem_cycleMin_eq_getElem_pow _ _ _
  · simp_rw [cycleMin_of_ge hx, smul_of_ge hx]
    exact ⟨0, Nat.two_pow_pos _, trivial⟩

lemma cycleMin_eq_min'_cycleOf (a : ArrayPerm n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    a.CycleMin i x = (a.cycleOf x).min' nonempty_cycleOf := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_of_lt hx]
    exact getElem_cycleMinArray_eq_min'_cycleOf _ _ _ hai
  · simp_rw [cycleMin_of_ge hx, cycleOf_ge hx]
    exact rfl

section Cast

variable {m : ℕ}

/--
`ArrayPerm.cast` re-interprets an `ArrayPerm n` as an `ArrayPerm m`, where `n = m`.
-/
def cast (h : n = m) (a : ArrayPerm n) : ArrayPerm m where
  fwdArray := a.fwdArray
  bwdArray := a.bwdArray
  getElem_fwdArray_lt' := fun _ => getElem_fwdArray.trans_lt <| getElem_lt.trans_eq h
  getElem_bwdArray_lt' := fun _ => getElem_bwdArray.trans_lt <| getElem_lt.trans_eq h
  size_fwdArray' := h ▸ a.size_fwdArray
  size_bwdArray' := h ▸ a.size_bwdArray
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
    (a.cast h) • i = a • i := by simp only [smul_nat_eq_dite, getElem_cast, h]

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

theorem getElem_fwdArray_append_range_sub (a : ArrayPerm n) {i : ℕ}
    {h : i < (a.fwdArray ++ Array.map (fun x => x + n) (Array.range (m - n))).size} :
    haveI := a.size_fwdArray
    (a.fwdArray ++ (Array.range (m - n)).map ((· + n)))[i] = a • i := by
  rcases lt_or_le i n with hi | hi
  · rw [Array.get_append_left (hi.trans_eq a.size_fwdArray.symm), a.smul_of_lt hi, getElem_fwdArray]
  · simp_rw [Array.get_append_right (hi.trans_eq' a.size_fwdArray), size_fwdArray,
    Array.getElem_map, Array.getElem_range, Nat.sub_add_cancel hi, a.smul_of_ge hi]

theorem getElem_bwdArray_append_range_sub (a : ArrayPerm n) {i : ℕ}
    {h : i < (a.bwdArray ++ Array.map (fun x => x + n) (Array.range (m - n))).size} :
    haveI := a.size_bwdArray
    (a.bwdArray ++ (Array.range (m - n)).map ((· + n)))[i] = a⁻¹ • i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [Array.get_append_left (hi.trans_eq a.size_bwdArray.symm),
    (a⁻¹).smul_of_lt hi, getElem_bwdArray]
  · simp_rw [Array.get_append_right (hi.trans_eq' a.size_bwdArray), size_bwdArray,
    Array.getElem_map, Array.getElem_range, Nat.sub_add_cancel hi, (a⁻¹).smul_of_ge hi]

/--
`ArrayPerm.castLE` re-interprets an `ArrayPerm n` as an `ArrayPerm m`, where `n ≤ m`.
-/
def castLE (h : n ≤ m) (a : ArrayPerm n) : ArrayPerm m where
  fwdArray := a.fwdArray ++ (Array.range (m - n)).map ((· + n))
  bwdArray := a.bwdArray ++ (Array.range (m - n)).map ((· + n))
  size_fwdArray' := by
    simp only [size_append, a.size_fwdArray, size_map, size_range, h, Nat.add_sub_cancel']
  size_bwdArray' := by
    simp only [size_append, a.size_bwdArray, size_map, size_range, h, Nat.add_sub_cancel']
  getElem_fwdArray_lt' := fun _ => by
    rw [getElem_fwdArray_append_range_sub, smul_nat_eq_dite]
    split_ifs with hin
    · exact getElem_lt.trans_le h
    · assumption
  getElem_bwdArray_lt' := fun _ => by
    rw [getElem_bwdArray_append_range_sub, smul_nat_eq_dite]
    split_ifs with hin
    · exact getElem_lt.trans_le h
    · assumption
  left_inv' := fun {i} hi => by
    simp_rw [getElem_fwdArray_append_range_sub, getElem_bwdArray_append_range_sub, inv_smul_smul]

@[simp]
theorem getElem_castLE (a : ArrayPerm n) (h : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castLE h)[i] = if hi : i < n then a[i] else i := a.getElem_fwdArray_append_range_sub

@[simp]
theorem getElem_inv_castLE (a : ArrayPerm n) (h : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castLE h)⁻¹[i] = if hi : i < n then a⁻¹[i] else i := a.getElem_bwdArray_append_range_sub

theorem getElem_castLE_of_lt (a : ArrayPerm n) (h : n ≤ m) {i : ℕ} (hi : i < n) :
    (a.castLE h)[i] = a[i] := by simp_rw [getElem_castLE, hi, dite_true]

@[simp]
theorem castLE_smul (a : ArrayPerm n) {i : ℕ} {h : n ≤ m} :
    (a.castLE h) • i = a • i := by
  simp_rw [smul_nat_eq_dite, a.getElem_castLE h, dite_eq_ite, ite_eq_left_iff]
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
  fwdArray := a.fwdArray.swap! i j
  bwdArray := a.bwdArray.map (fun k => Equiv.swap i j k)
  size_fwdArray' := (Array.size_swap! _ _ _).trans a.size_fwdArray
  size_bwdArray' := (Array.size_map _ _).trans a.size_bwdArray
  getElem_fwdArray_lt' := fun _ => by
    simp_rw [a.fwdArray.getElem_swap!_eq_getElem_swap_apply
      (hi.trans_eq a.size_fwdArray.symm) (hj.trans_eq a.size_fwdArray.symm), getElem_fwdArray,
      a.getElem_lt]
  getElem_bwdArray_lt' := fun _ => by
    simp_rw [Array.getElem_map, getElem_bwdArray]
    exact swap_prop (· < n) getElem_lt hi hj
  left_inv' := fun _ => by
    simp_rw [a.fwdArray.getElem_swap!_eq_getElem_swap_apply
      (hi.trans_eq a.size_fwdArray.symm) (hj.trans_eq a.size_fwdArray.symm), Array.getElem_map,
      getElem_fwdArray, getElem_bwdArray, getElem_inv_getElem, swap_apply_self]

variable (i j k : ℕ) (hi : i < n) (hj : j < n)

@[simp]
theorem getElem_swap (a : ArrayPerm n) (hk : k < n) :
    (a.swap hi hj)[k] = a[Equiv.swap i j k]'(swap_prop (· < n) hk hi hj) :=
  a.fwdArray.getElem_swap!_eq_getElem_swap_apply
    (hi.trans_eq a.size_fwdArray.symm) (hj.trans_eq a.size_fwdArray.symm) _

@[simp]
theorem getElem_inv_swap (a : ArrayPerm n) (hk : k < n) :
    (a.swap hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.bwdArray.getElem_map _ _ _

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
  rw [eq_iff_smul_eq_smul_lt]
  simp_rw [mul_smul, one_swap_smul, swap_smul_eq_smul_swap, swap_smul, implies_true]

theorem swap_inv_eq_one_swap_mul (a : ArrayPerm n) :
    (a.swap hi hj)⁻¹ = swap 1 hi hj * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (a : ArrayPerm n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    (a.swap hi hj)⁻¹ = a⁻¹ * swap 1 hi' hj' := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

theorem natPerm_swap (a : ArrayPerm n) :
    natPerm n (swap a hi hj) = natPerm n a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, natPerm_apply_apply, swap_smul_eq_smul_swap]

@[simp]
theorem natPerm_one_swap  :
    natPerm n (swap 1 hi hj) = Equiv.swap i j := by simp_rw [natPerm_swap, map_one, one_mul]

end ArrayPerm
