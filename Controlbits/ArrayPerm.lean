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

/-- `swaps bs` is the permutation that swaps each pair along the list of pairs bs. -/
def swaps (bs : List (α × α)) : Perm α := (bs.map <| uncurry Equiv.swap).prod

@[simp]
theorem swaps_nil : swaps ([] : List (α × α)) = 1 := rfl

@[simp]
theorem swaps_cons (b : α × α) (bs : List (α × α)) : swaps (b :: bs) = uncurry swap b * swaps bs :=
  prod_cons

theorem _root_.Function.Injective.swaps_map_comp_apply {bs : List (α × α)} {k : α} {f : α → β}
    (hf : Function.Injective f) (g : α × α → α × α) :
    swaps (bs.map ((map f f) ∘ g)) (f k) = f (swaps (bs.map g) k) := by
  induction' bs with b bs IH
  · rfl
  · simp_rw [map_cons, swaps_cons, Perm.mul_apply, IH, comp_apply, uncurry_swap,
    map_fst, map_snd, hf.swap_apply]

theorem _root_.Function.Injective.swaps_map_apply {bs : List (α × α)} {k : α} {f : α → β}
    (hf : Function.Injective f) : swaps (bs.map (map f f)) (f k) = f (swaps bs k) := by
  convert bs.map_id ▸ (hf.swaps_map_comp_apply id)

theorem swaps_coe {n : ℕ} {bs : List (Fin n × Fin n)} {k : Fin n} :
    swaps (bs.map (Prod.map val val)) k.val = swaps bs k :=
  val_injective.swaps_map_apply

theorem swaps_smul {R : Type*} [Group R] [MulAction R α] {bs : List (α × α)} {k : α} {r : R} :
    swaps (bs.map (r • ·)) (r • k) = r • swaps bs k :=
  (MulAction.injective r).swaps_map_apply

theorem swaps_prop (p : α → Prop) {k : α} (bs : List (α × α))
    (hb : ∀ b ∈ bs, p b.1 ∧ p b.2) (hk : p k) : p (swaps bs k) := by
  induction' bs with b bs IH
  · exact hk
  · simp_rw [mem_cons, forall_eq_or_imp] at hb
    rw [swaps_cons]
    exact swap_prop p (IH (hb.2)) hb.1.1 hb.1.2

theorem swaps_singleton (b : α × α) : swaps [b] = uncurry swap b := rfl

@[simp]
theorem swaps_append (bs₁ bs₂: List (α × α)) :
    swaps (bs₁ ++ bs₂) = swaps bs₁ * swaps bs₂ := by
  unfold swaps
  rw [map_append, prod_append]

theorem swaps_mul (bs₁ bs₂ : List (α × α)) :
    swaps bs₁ * swaps bs₂ = swaps (bs₁ ++ bs₂) := (swaps_append _ _).symm

theorem swaps_concat (b : α × α) (bs : List (α × α)) :
    swaps (bs ++ [b]) = swaps bs * uncurry swap b := by rw [swaps_append, swaps_singleton]

theorem swaps_concat' (b : α × α) (bs : List (α × α)) :
    swaps (bs.concat b) = swaps bs * uncurry swap b := by
  rw [concat_eq_append, swaps_concat]

theorem swaps_reverse (bs : List (α × α)) :
    swaps (reverse bs) = (swaps bs)⁻¹ := by
  unfold swaps
  simp_rw [map_reverse, prod_reverse_noncomm, List.map_map, comp_def, uncurry_swap, swap_inv]

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
  rw [swaps_cons, uncurry_swap_apply, swap_self, swaps_nil, Perm.one_def, Perm.mul_refl]

@[simp]
theorem swaps_self_pairs (as : List α) : swaps (as.zip as) = 1 := by
  induction' as with a as IH
  · rfl
  · rw [zip_cons_cons, swaps_cons, uncurry_swap_apply, swap_self, Perm.refl_mul, IH]

@[simp]
theorem swaps_comm (bs : List (α × α)) :
    swaps (bs.map Prod.swap) = swaps bs := by
  induction' bs with b bs IH
  · rfl
  · simp_rw [map_cons, swaps_cons, uncurry_swap, fst_swap, snd_swap, swap_comm, IH]

theorem swaps_mul_eq_mul_swaps (bs : List (α × α)) (π : Perm α) :
    swaps bs * π = π * swaps (bs.map (Prod.map (π⁻¹ : Perm α) (π⁻¹ : Perm α))) := by
  induction' bs with b bs IH generalizing π
  · rfl
  · simp_rw [map_cons, swaps_cons, mul_assoc, IH, ← mul_assoc, uncurry_swap_apply,
    swap_mul_eq_mul_swap, mul_assoc, map_fst, map_snd]

theorem mul_swaps_eq_swaps_mul (bs : List (α × α)) (π : Perm α) :
    π * swaps bs = swaps (bs.map (Prod.map π π)) * π := by
  simp_rw [swaps_mul_eq_mul_swaps, List.map_map, Prod.map_comp_map, Perm.inv_def,
    symm_comp_self, Prod.map_id, List.map_id]

theorem mul_swaps_mul (bs : List (α × α)) (π : Perm α) :
    swaps (bs.map (Prod.map π π)) = π * swaps bs * π⁻¹ := by
  rw [mul_swaps_eq_swaps_mul, mul_inv_cancel_right]

theorem swaps_nil_apply (a : α) : Equiv.swaps [] a = a := rfl

@[simp]
theorem swaps_concat_apply_left (bs : List (α × α)) (b : α × α) :
    swaps (bs ++ [b]) b.1 = swaps bs b.2 := by
  rw [swaps_concat, Perm.mul_apply, uncurry_swap_apply, swap_apply_left]

@[simp]
theorem swaps_concat_apply_right (bs : List (α × α)) (b : α × α) :
    swaps (bs ++ [b]) b.2 = swaps bs b.1 := by
  rw [swaps_concat, Perm.mul_apply, uncurry_swap_apply, swap_apply_right]

theorem swaps_concat_apply_of_ne_of_ne (bs : List (α × α)) {b : α × α} {a : α}
    (ha₁ : a ≠ b.1) (ha₂ : a ≠ b.2) : swaps (bs ++ [b]) a = swaps bs a := by
  rw [swaps_concat, Perm.mul_apply, uncurry_swap_apply, swap_apply_of_ne_of_ne ha₁ ha₂]

theorem swaps_concat_apply_left' (bs : List (α × α)) (b : α × α) :
    swaps (bs.concat b) b.1 = swaps bs b.2 := by
  rw [concat_eq_append, swaps_concat_apply_left]

theorem swaps_concat_apply_right' (bs : List (α × α)) (b : α × α) :
    swaps (bs.concat b) b.2 = swaps bs b.1 := by
  rw [concat_eq_append, swaps_concat_apply_right]

theorem swaps_concat_apply_of_ne_of_ne' (bs : List (α × α)) {b : α × α} {a : α}
    (ha₁ : a ≠ b.1) (ha₂ : a ≠ b.2) : swaps (bs.concat b) a = swaps bs a := by
  rw [concat_eq_append, swaps_concat_apply_of_ne_of_ne _ ha₁ ha₂]

theorem swaps_apply_of_ne (bs : List (α × α)) (a : α)
    (hb : ∀ b, b ∈ bs → a ≠ b.1 ∧ a ≠ b.2) : Equiv.swaps bs a = a := by
  induction' bs using list_reverse_induction with bs b IH generalizing a
  · exact swaps_nil_apply a
  · simp_rw [mem_concat] at hb
    have IH := IH _ fun b h => hb b (Or.inl h)
    have hb := hb b (Or.inr rfl)
    rw [swaps_concat_apply_of_ne_of_ne bs hb.1 hb.2, IH]

theorem swaps_apply_eq_swap_of_nodup_of_norep (bs : List (α × α)) (hbn : bs.Nodup)
  (hxy : ∀ {b b'}, b ∈ bs → b' ∈ bs → b ≠ b' → b.1 ≠ b'.1 ∧ b.1 ≠ b'.2 ∧ b.2 ≠ b'.1 ∧ b.2 ≠ b'.2) :
    ∀ b ∈ bs, Equiv.swaps bs b.1 = b.2 ∧ Equiv.swaps bs b.2 = b.1 := fun b hb => by
  induction' bs using list_reverse_induction with bs b' IH
  · exact (List.not_mem_nil _ hb).elim
  · simp_rw [List.nodup_append, List.nodup_singleton, true_and, List.disjoint_singleton] at hbn
    simp_rw [mem_append, mem_singleton] at hb hxy
    simp_rw [swaps_append, swaps_singleton, Perm.mul_apply, uncurry_swap_apply]
    rcases hb with hb | rfl
    · have H := hxy (Or.inl hb) (Or.inr rfl) (ne_of_mem_of_not_mem hb hbn.2)
      convert IH hbn.1 (fun h₁ h₂ h₃ => hxy (Or.inl h₁) (Or.inl h₂) h₃) hb
      exacts [swap_apply_of_ne_of_ne H.1 H.2.1, swap_apply_of_ne_of_ne H.2.2.1 H.2.2.2]
    · have H := fun b' (hb' : b' ∈ bs) =>
        hxy (Or.inr rfl) (Or.inl hb') (ne_of_mem_of_not_mem hb' hbn.2).symm
      simp_rw [swap_apply_left, swap_apply_right]
      exact ⟨swaps_apply_of_ne bs b.2 (fun _ hb' => (H _ hb').2.2),
        swaps_apply_of_ne bs b.1 (fun _ hb' => ⟨(H _ hb').1, (H _ hb').2.1⟩)⟩

theorem swaps_apply_self_or_pairs_mem_of_nodup_of_norep (bs : List (α × α)) (hbn : bs.Nodup)
  (hxy : ∀ {b b'}, b ∈ bs → b' ∈ bs → b ≠ b' → b.1 ≠ b'.1 ∧ b.1 ≠ b'.2 ∧ b.2 ≠ b'.1 ∧ b.2 ≠ b'.2) :
    ∀ a : α, swaps bs a = a ∨ (a, swaps bs a) ∈ bs ∨ (swaps bs a, a) ∈ bs := fun a => by
  by_cases h : ∀ b, b ∈ bs → a ≠ b.1 ∧ a ≠ b.2
  · exact Or.inl (swaps_apply_of_ne bs a h)
  · refine' Or.inr _
    push_neg at h
    rcases h with ⟨b, hb, hba⟩
    have H := swaps_apply_eq_swap_of_nodup_of_norep bs hbn hxy b hb
    rcases eq_or_ne a b.1 with rfl | ha
    · rw [H.1]
      exact Or.inl hb
    · rw [hba ha, H.2]
      exact Or.inr hb

theorem swaps_apply_rdropWhile (bs : List (α × α)) (a : α) :
    Equiv.swaps bs a = Equiv.swaps
    (bs.rdropWhile (fun b => !decide (a = b.1) && !decide (a = b.2))) a := by
  induction' bs using list_reverse_induction with bs b IH generalizing a
  · rfl
  · rcases eq_or_ne a b.1 with rfl | h₁
    · rw [bs.rdropWhile_concat_neg _ _
        (by simp_rw [decide_True, Bool.not_true, Bool.false_and, not_false_eq_true])]
    · rcases eq_or_ne a b.2 with rfl | h₂
      · rw [bs.rdropWhile_concat_neg _ _
        (by simp_rw [decide_True, Bool.not_true, Bool.and_false, not_false_eq_true])]
      · rw [swaps_concat_apply_of_ne_of_ne _ h₁ h₂, IH,
        bs.rdropWhile_concat_pos _ _
        (by simp_rw [h₁, h₂, decide_False, Bool.not_false, Bool.and_self])]

theorem swaps_apply_filter_eq (bs : List (α × α)) :
    Equiv.swaps bs = Equiv.swaps
    (bs.filter (fun b => !decide (b.1 = b.2))) := by
  induction' bs using list_reverse_induction with bs b IH
  · rfl
  · simp_rw [filter_append, filter_singleton, swaps_append,
    Bool.apply_cond swaps, swaps_singleton, swaps_nil,
    Bool.cond_not, uncurry_swap_apply]
    rcases eq_or_ne b.1 b.2 with h | h
    · simp_rw [h, decide_True, cond_true, mul_one, IH, swap_self, Perm.mul_refl]
    · simp_rw [h, decide_False, cond_false, IH]

def swapsChain (bs : List (α × α)) : α → List (α × α) :=
  bs.reverseRecOn (fun _ => []) (fun _ b sc a =>
  if a = b.1 then sc b.2 ++ [b] else if a = b.2 then sc b.1 ++ [b] else sc a)

@[simp]
lemma swapsChain_nil (a : α) : swapsChain [] a = [] := by
  unfold swapsChain
  simp_rw [reverseRecOn_nil]

lemma swapsChain_concat (bs : List (α × α)) (b : α × α) (a : α) :
    swapsChain (bs ++ [b]) a = if a = b.1 then swapsChain bs b.2 ++ [b]
    else if a = b.2 then swapsChain bs b.1 ++ [b]
    else swapsChain bs a := by
  unfold swapsChain
  simp_rw [reverseRecOn_concat]

@[simp]
lemma swapsChain_concat_left (bs : List (α × α)) (b : α × α) :
    swapsChain (bs ++ [b]) b.1 = swapsChain bs b.2 ++ [b] := by
  simp_rw [swapsChain_concat, if_true]

@[simp]
lemma swapsChain_concat_right (bs : List (α × α)) (b : α × α) :
    swapsChain (bs ++ [b]) b.2 = swapsChain bs b.1 ++ [b] := by
  simp_rw [swapsChain_concat, if_true]
  rcases eq_or_ne b.2 b.1 with h | h
  · simp_rw [h, if_true]
  · simp_rw [h, if_false]

lemma swapsChain_concat_of_ne_of_ne (bs : List (α × α)) {b : α × α} {a : α}
  (h₁ : a ≠ b.1) (h₂ : a ≠ b.2) :
    swapsChain (bs ++ [b]) a = swapsChain bs a := by
  simp_rw [swapsChain_concat, h₁, h₂, if_false]

theorem swaps_swapsChain (bs : List (α × α)) (a : α) :
    swaps bs a = swaps (swapsChain bs a) a := by
  induction' bs using list_reverse_induction with bs b IH generalizing a
  · simp_rw [swapsChain_nil]
  · rcases eq_or_ne a b.1 with rfl | h₁
    · simp_rw [swapsChain_concat_left, swaps_concat_apply_left, IH]
    · rcases eq_or_ne a b.2 with rfl | h₂
      · simp_rw [swapsChain_concat_right, swaps_concat_apply_right, IH]
      · simp_rw [swapsChain_concat_of_ne_of_ne _ h₁ h₂, swaps_concat_apply_of_ne_of_ne _ h₁ h₂, IH]

theorem swapsChain_swapsChain (bs : List (α × α)) (a : α) :
    swapsChain (swapsChain bs a) a = swapsChain bs a := by
  induction' bs using list_reverse_induction with bs b IH generalizing a
  · simp_rw [swapsChain_nil]
  · rcases eq_or_ne a b.1 with rfl | h₁
    · simp_rw [swapsChain_concat_left, IH]
    · rcases eq_or_ne a b.2 with rfl | h₂
      · simp_rw [swapsChain_concat_right, IH]
      · simp_rw [swapsChain_concat_of_ne_of_ne _ h₁ h₂, IH]

theorem swapsChain_length (bs : List (α × α)) (a : α) : (swapsChain bs a).length ≤ bs.length := by
  induction' bs using list_reverse_induction with bs b IH generalizing a
  · simp_rw [swapsChain_nil, length_nil, le_refl]
  · rcases eq_or_ne a b.1 with rfl | h₁
    · simp_rw [swapsChain_concat_left, length_append, length_singleton,
      Nat.add_le_add_iff_right, IH]
    · rcases eq_or_ne a b.2 with rfl | h₂
      · simp_rw [swapsChain_concat_right, length_append, length_singleton,
        Nat.add_le_add_iff_right, IH]
      · simp_rw [swapsChain_concat_of_ne_of_ne _ h₁ h₂, length_append, length_singleton]
        exact (IH a).trans (Nat.le_succ _)

end Equiv

namespace Array

open Equiv Function List Fin

variable {α β γ : Type*}

theorem mem_iff_getElem {as : Array α} {a : α} :
    a ∈ as ↔ ∃ (i : ℕ), ∃ (hi : i < as.size), as[i] = a := by
  rw [mem_def, List.mem_iff_getElem]
  exact Iff.rfl

@[simp]
theorem getElem_mem {as : Array α} {i : ℕ} {hi : i < as.size} :
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

theorem getElem_range_lt {i n : ℕ} (h : i < (range n).size) : (range n)[i] < n := by
  simp_rw [← mem_range_iff, getElem_mem]

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
    haveI := size_attachWith (H := H); (as.attachWith _ H)[i] = ⟨as[i], H _ getElem_mem⟩ := by
  unfold attachWith List.attachWith
  simp_rw [Array.getElem_eq_data_getElem, List.getElem_pmap]

@[simp]
theorem size_attach {as : Array α} : as.attach.size = as.size := size_attachWith

@[simp]
theorem getElem_attach {as : Array α} {i : ℕ} (h : i < as.attach.size) :
    haveI := size_attach (as := as); (as.attach)[i] = ⟨as[i], getElem_mem⟩ := getElem_attachWith _

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

/--
Swaps pairs of entries in an array a given by a list bs.
-/
@[semireducible]
def swaps (a : Array α) : List (Fin a.size × Fin a.size) → Array α
  | [] => a
  | b :: bs => (uncurry a.swap b).swaps
    (bs.map (Prod.map (Fin.cast (a.size_swap _ _).symm) (Fin.cast (a.size_swap _ _).symm)))
  termination_by bs => bs.length

@[simp]
theorem swaps_nil (a : Array α) : a.swaps [] = a := rfl

@[simp]
theorem swaps_cons (a : Array α) (b : Fin a.size × Fin a.size)
    (bs : List (Fin a.size × Fin a.size)) : a.swaps (b :: bs) = (uncurry a.swap b).swaps
    (bs.map (Prod.map (Fin.cast (a.size_swap _ _).symm) (Fin.cast (a.size_swap _ _).symm))) :=
  rfl

theorem swaps_singleton (a : Array α) (b : Fin a.size × Fin a.size) :
  a.swaps [b] = uncurry a.swap b := by simp_rw [swaps_cons, map_nil, swaps_nil]

@[simp]
theorem size_swaps (a : Array α) (bs : List (Fin a.size × Fin a.size)) :
    (a.swaps bs).size = a.size :=
  match bs with
  | [] => by rw[swaps_nil]
  | (b :: bs) => by rw [swaps_cons, size_swaps, size_uncurry_swap]
  termination_by bs.length

theorem swaps_append (a : Array α) (bs₁ bs₂ : List (Fin a.size × Fin a.size)) :
    a.swaps (bs₁ ++ bs₂) = (a.swaps bs₁).swaps
    (bs₂.map (Prod.map (Fin.cast (a.size_swaps _).symm) (Fin.cast (a.size_swaps _).symm))) :=
  match bs₁ with
  | [] => by simp_rw [List.nil_append, swaps_nil, Fin.cast_refl, Prod.map_id, map_id]
  | (b₁ :: bs₁) => by
    rw [cons_append, swaps_cons, map_append]
    refine' ((uncurry a.swap b₁).swaps_append _ _).trans _
    simp_rw [map_map, Prod.map_comp_map, Fin.cast_comp, swaps_cons]
  termination_by bs₁.length

theorem swaps_concat (a : Array α) (b : Fin a.size × Fin a.size)
    (bs : List (Fin a.size × Fin a.size)) : a.swaps (bs ++ [b]) =
    (uncurry (a.swaps bs).swap) (Prod.map (Fin.cast (a.size_swaps _).symm)
    (Fin.cast (a.size_swaps _).symm) b) := by
  simp_rw [swaps_append, map_cons, map_nil, swaps_singleton]

theorem swaps_concat' (a : Array α) (b : Fin a.size × Fin a.size)
    (bs : List (Fin a.size × Fin a.size)) : a.swaps (bs.concat b) =
    (uncurry (a.swaps bs).swap) (Prod.map (Fin.cast (a.size_swaps _).symm)
    (Fin.cast (a.size_swaps _).symm) b) := by
  simp_rw [concat_eq_append, swaps_concat]


theorem get_swaps_eq_get_apply_swaps (a : Array α) {bs : List (Fin a.size × Fin a.size)}
    (k : ℕ) (h : k < a.size)
    (h' : k < (a.swaps bs).size := (a.size_swaps _).symm.trans_gt h)
    (h'' : Equiv.swaps (bs.map (Prod.map val val)) k < a.size :=
    swaps_prop (fun k => k < a.size) _ (Fin.fst_lt_snd_lt_of_mem_map_val _) h) :
    (a.swaps bs)[k] = a[Equiv.swaps (bs.map (Prod.map val val)) k] := by
  induction' bs using list_reverse_induction with bs b IH generalizing k
  · simp_rw [swaps_nil, map_nil, Equiv.swaps_nil, Perm.one_apply]
  · specialize IH _ (swap_prop
      (fun t => t < a.size) h b.1.isLt b.2.isLt)
    simp_rw [swaps_concat, map_concat', Equiv.swaps_concat,
    uncurry_swap_apply, Equiv.uncurry_swap_apply, Prod.map_fst, Prod.map_snd,
    (a.swaps bs).get_swap_eq_get_apply_swap', Perm.mul_apply, coe_cast, IH]

theorem get_swaps_eq_get_apply_swaps' (a : Array α) {bs : List (Fin a.size × Fin a.size)}
    (k : ℕ)
    (h : k < (a.swaps bs).size) (h' : k < a.size := ((size_swaps _ _).trans_gt h))
    (h'' : Equiv.swaps (bs.map (Prod.map val val)) k < a.size :=
    swaps_prop (fun k => k < a.size) _ (Fin.fst_lt_snd_lt_of_mem_map_val _) h') :
    (a.swaps bs)[k] = a[Equiv.swaps (bs.map (Prod.map val val)) k] :=
 get_swaps_eq_get_apply_swaps _ _ h'

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
  protected getElem_toArray_lt' :
    ∀ {i : ℕ} (hi : i < toArray.size), toArray[i] < n := by decide
  protected getElem_invArray_lt' :
  ∀ {i : ℕ} (hi : i < invArray.size), invArray[i] < n := by decide
  protected size_toArray' : toArray.size = n := by rfl
  protected size_invArray' : invArray.size = n := by rfl
  protected getElem_invArray_getElem_toArray' : ∀ {i : ℕ} (hi : i < toArray.size),
      haveI := getElem_toArray_lt' hi;
      invArray[toArray[i]] = i := by decide

/-
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
  protected toArray : Array (Fin n)
  /--
  Gives the `ArrayPerm` as an array of indexes. Value `v` is mapped to the index at position `v`
  in `invArray`.
  -/
  protected invArray : Array (Fin n)
  protected sizeTo' : toArray.size = n := by rfl
  protected sizeInv' : invArray.size = n := by rfl
  protected left_inv' : ∀ i : Fin n, invArray[toArray[i.val].val] = i := by decide
-/

namespace ArrayPerm

open Function Fin Equiv List Array

variable {n m : ℕ}

instance : Repr (ArrayPerm n) where
  reprPrec a _ := "ArrayPerm " ++ " : " ++ repr a.toArray

instance : ToString (ArrayPerm n) where
  toString a := "ArrayPerm " ++ " : " ++ toString a.toArray

@[simp]
theorem size_toArray (a : ArrayPerm n) : a.toArray.size = n := a.size_toArray'

@[simp]
theorem size_invArray (a : ArrayPerm n) : a.invArray.size = n := a.size_invArray'

theorem size_invArray_eq_size_toArray (a : ArrayPerm n) :
    a.invArray.size = a.toArray.size := a.size_invArray.trans a.size_toArray.symm

theorem getElem_toArray_lt (a : ArrayPerm n) {i : ℕ} {hi : i < a.toArray.size} :
    a.toArray[i] < n := a.getElem_toArray_lt' _
theorem getElem_invArray_lt (a : ArrayPerm n) {i : ℕ} {hi : i < a.invArray.size} :
    a.invArray[i] < n := a.getElem_invArray_lt' _

theorem getElem_toArray_lt_size_invArray (a : ArrayPerm n) {i : ℕ} {hi : i < a.toArray.size} :
    a.toArray[i] < a.invArray.size := a.getElem_toArray_lt.trans_eq a.size_invArray.symm
theorem getElem_invArray_lt_size_toArray (a : ArrayPerm n) {i : ℕ} {hi : i < a.invArray.size} :
    a.invArray[i] < a.toArray.size := a.getElem_invArray_lt.trans_eq a.size_toArray.symm

@[simp]
theorem getElem_invArray_getElem_toArray (a : ArrayPerm n) {i : ℕ} (hi : i < a.toArray.size) :
    haveI := a.getElem_toArray_lt_size_invArray
    a.invArray[a.toArray[i]] = i := a.getElem_invArray_getElem_toArray' _

@[simp]
theorem getElem_toArray_getElem_invArray (a : ArrayPerm n) {i : ℕ} (hi : i < a.invArray.size) :
    haveI := a.getElem_invArray_lt_size_toArray
    a.toArray[a.invArray[i]] = i := by
  have H : LeftInverse
    (fun (i : Fin n) => ⟨a.invArray[(i : ℕ)], a.getElem_invArray_lt⟩)
    (fun (i : Fin n) => ⟨a.toArray[(i : ℕ)], a.getElem_toArray_lt⟩) :=
    fun _ => Fin.ext <| a.getElem_invArray_getElem_toArray _
  apply (Fin.mk_eq_mk (h := a.getElem_toArray_lt) (h' := hi.trans_eq a.size_invArray)).mp
  apply H.surjective.injective_of_fintype (Equiv.refl _)
  simp_rw [getElem_invArray_getElem_toArray]

theorem toArray_injective (a : ArrayPerm n) {i j : ℕ} (hi : i < a.toArray.size)
    (hj : j < a.toArray.size) (hij : a.toArray[i] = a.toArray[j]) : i = j := by
  rw [← a.getElem_invArray_getElem_toArray hi, ← a.getElem_invArray_getElem_toArray hj]
  simp_rw [hij]

theorem invArray_injective (a : ArrayPerm n) {i j : ℕ} (hi : i < a.invArray.size)
    (hj : j < a.invArray.size) (hij : a.invArray[i] = a.invArray[j]) : i = j := by
  rw [← a.getElem_toArray_getElem_invArray hi, ← a.getElem_toArray_getElem_invArray hj]
  simp_rw [hij]

theorem invArray_surjective (a : ArrayPerm n) {i : ℕ} (hi : i < a.toArray.size) :
    ∃ (j : ℕ) (hj : j < a.invArray.size), a.invArray[j] = i :=
  ⟨a.toArray[i], a.getElem_toArray_lt_size_invArray, a.getElem_invArray_getElem_toArray hi⟩

theorem toArray_surjective (a : ArrayPerm n) {i : ℕ} (hi : i < a.invArray.size) :
    ∃ (j : ℕ) (hj : j < a.toArray.size), a.toArray[j] = i :=
  ⟨a.invArray[i], a.getElem_invArray_lt_size_toArray, a.getElem_toArray_getElem_invArray hi⟩

theorem mem_toArray_iff (a : ArrayPerm n) {i : ℕ} : i ∈ a.toArray ↔ i < n := by
  simp_rw [Array.mem_iff_getElem]
  refine ⟨?_, fun h => a.toArray_surjective (h.trans_eq a.size_invArray.symm)⟩
  rintro ⟨j, hj, rfl⟩
  exact a.getElem_toArray_lt

theorem mem_invArray_iff (a : ArrayPerm n) {i : ℕ} : i ∈ a.invArray ↔ i < n := by
  simp_rw [Array.mem_iff_getElem]
  refine ⟨?_, fun h => a.invArray_surjective (h.trans_eq a.size_toArray.symm)⟩
  rintro ⟨j, hj, rfl⟩
  exact a.getElem_invArray_lt

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
  (getElem_toArray_lt' :
    ∀ {i : ℕ} (hi : i < toArray.size), toArray[i] < n := by decide)
  (getElem_invArray_lt' :
  ∀ {i : ℕ} (hi : i < invArray.size), invArray[i] < n := by decide)
  (size_toArray' : toArray.size = n := by rfl)
  (size_invArray' : invArray.size = n := by rfl)
  (getElem_toArray_getElem_invArray' : ∀ {i : ℕ} (hi : i < invArray.size),
      haveI := getElem_invArray_lt' hi;
      toArray[invArray[i]] = i := by decide): ArrayPerm n :=
  {toArray, invArray, getElem_toArray_lt', getElem_invArray_lt', size_toArray', size_invArray',
    getElem_invArray_getElem_toArray' :=
      haveI A : ArrayPerm n := ⟨invArray, toArray, getElem_invArray_lt',
      getElem_toArray_lt', size_invArray', size_toArray', getElem_toArray_getElem_invArray'⟩;
      A.getElem_toArray_getElem_invArray}

theorem invArray_eq_iff_toArray_eq (a b : ArrayPerm n) :
    a.invArray = b.invArray ↔ a.toArray = b.toArray := by
  refine ⟨fun h => Array.ext _ _ ?_ (fun i hi₁ hi₂ => ?_),
    fun h => Array.ext _ _ ?_ (fun i hi₁ hi₂ => ?_)⟩
  · rw [a.size_toArray]
    exact b.size_toArray.symm
  · refine a.invArray_injective (a.getElem_toArray_lt_size_invArray)
      (h ▸ b.getElem_toArray_lt_size_invArray) ?_
    simp_rw [getElem_invArray_getElem_toArray, h, getElem_invArray_getElem_toArray]
  · rw [a.size_invArray]
    exact b.size_invArray.symm
  · refine a.toArray_injective (a.getElem_invArray_lt_size_toArray)
      (h ▸ b.getElem_invArray_lt_size_toArray) ?_
    simp_rw [getElem_toArray_getElem_invArray, h, getElem_toArray_getElem_invArray]

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

@[simps!]
instance One : One (ArrayPerm n) :=
⟨range n, range n, getElem_range_lt, getElem_range_lt, size_range, size_range,
  by simp_rw [Array.getElem_range, implies_true]⟩

theorem getElem_one_toArray {i : ℕ} {hi : i < (1 : ArrayPerm n).toArray.size}  :
  (1 : ArrayPerm n).toArray[i] = i := getElem_range _
theorem getElem_one_invArray {i : ℕ} {hi : i < (1 : ArrayPerm n).invArray.size}  :
  (1 : ArrayPerm n).invArray[i] = i := getElem_range _

@[simps!]
instance : Inv (ArrayPerm n) :=
⟨fun a => ArrayPerm.mk' a.invArray a.toArray
  a.getElem_invArray_lt' a.getElem_toArray_lt'
  a.size_invArray a.size_toArray
  a.getElem_invArray_getElem_toArray'⟩

theorem getElem_inv_toArray (a : ArrayPerm n) {i : ℕ} {hi : i < a⁻¹.toArray.size} :
    a⁻¹.toArray[i] = a.invArray[i] := rfl
theorem getElem_inv_invArray (a : ArrayPerm n) {i : ℕ} {hi : i < a⁻¹.invArray.size} :
    a⁻¹.invArray[i] = a.toArray[i] := rfl

@[simps!]
instance : Mul (ArrayPerm n) := ⟨fun a b =>
  ⟨(b.toArray.attachWith _ b.lt_of_mem_toArray).map
    fun i => a.toArray[i.1]'(i.2.trans_eq a.size_toArray.symm),
    (a.invArray.attachWith _ a.lt_of_mem_invArray).map
    fun i => b.invArray[i.1]'(i.2.trans_eq b.size_invArray.symm),
    by simp_rw [Array.getElem_map, getElem_attachWith, getElem_toArray_lt, implies_true],
    by simp_rw [Array.getElem_map, getElem_attachWith, getElem_invArray_lt, implies_true],
    by rw [size_map, size_attachWith, size_toArray],
    by rw [size_map, size_attachWith, size_invArray],
    by simp only [Array.getElem_map, getElem_attachWith,
      getElem_invArray_getElem_toArray, implies_true]⟩⟩

theorem getElem_mul_toArray (a b : ArrayPerm n) {i : ℕ} {hi : i < (a * b).toArray.size} :
    haveI := b.size_toArray; haveI := (a * b).size_toArray;
    (a * b).toArray[i] = a.toArray[b.toArray[i]]'
    (b.getElem_toArray_lt.trans_eq a.size_toArray.symm) := by
  simp_rw [instMul_mul_toArray, Array.getElem_map, Array.getElem_attachWith]

theorem getElem_mul_invArray (a b : ArrayPerm n) {i : ℕ} {hi : i < (a * b).invArray.size} :
    haveI := a.size_invArray; haveI := (a * b).size_invArray;
    (a * b).invArray[i] = b.invArray[a.invArray[i]]'
    (a.getElem_invArray_lt.trans_eq b.size_invArray.symm) := by
  simp_rw [instMul_mul_invArray, Array.getElem_map, Array.getElem_attachWith]

instance : Group (ArrayPerm n) where
  mul_assoc a b c := (a * b * c).eq_of_getElem_toArray_eq (a * (b * c)) fun _ _ _ => by
    simp_rw [getElem_mul_toArray]
  one_mul a := (1 * a).eq_of_getElem_toArray_eq a fun _ _ _ => by
    simp_rw [getElem_mul_toArray, getElem_one_toArray]
  mul_one a := (a * 1).eq_of_getElem_toArray_eq a fun _ _ _ => by
    simp_rw [getElem_mul_toArray, getElem_one_toArray]
  mul_left_inv a := (a⁻¹ * a).eq_of_getElem_toArray_eq 1 fun _ _ _ => by
    simp_rw [getElem_mul_toArray, getElem_inv_toArray, getElem_one_toArray,
    getElem_invArray_getElem_toArray]

@[simps!]
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
    simp_rw [size_toArray] at hi₁ hi₂
    simp_rw [hi₁, dite_true] at h
    exact h

theorem ext' {a b : ArrayPerm n} (h : ∀ i : ℕ, a • i = b • i) : a = b :=
  FaithfulSMul.eq_of_smul_eq_smul h

theorem ext_iff' (a b : ArrayPerm n) : a = b ↔ ∀ i : ℕ, a • i = b • i :=
  ⟨fun h _ => h ▸ rfl, ext'⟩

theorem lt_iff_smul_lt (a : ArrayPerm n) {i : ℕ} : i < n ↔ a • i < n := by
  rcases lt_or_le i n with h | h
  · simp_rw [h, true_iff, a.smul_of_lt h]
    exact a.getElem_toArray_lt
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
    refine a.toArray_injective (hi.trans_eq a.size_toArray.symm)
      (hj.trans_eq a.size_toArray.symm) ?_
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
    smul_of_lt _ (getElem_toArray_lt _)])
      (fun h => by simp_rw [smul_of_ge _ h])

@[simps!]
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

/-
theorem toArray_eq_smul_mk (a : ArrayPerm n) {i : ℕ} (h : i < a.toArray.size) :
  a.toArray[i] = a • ⟨i, a.size_toArray.trans_gt h⟩ := rfl

theorem invArray_eq_smul_mk (a : ArrayPerm n) {i : ℕ} (h : i < a.invArray.size) :
  a.invArray[i] = a⁻¹ • ⟨i, a.sizeInv.trans_gt h⟩ := rfl
-/

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
  size_toArray' := by simp only [size_map, size_range]
  size_invArray' := by simp only [size_map, size_range]
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
  rw [← MonoidHom.map_inv, natPerm_apply_apply_of_lt _ h, getElem_inv_toArray]

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
    (mulEquivPerm a) i = a.toArray[(i : ℕ)] := by
  unfold mulEquivPerm
  simp only [MulEquiv.coe_mk, coe_fn_mk, permCongr_apply, symm_symm, equivSubtype_apply,
    Perm.subtypePerm_apply, equivSubtype_symm_apply, a.natPerm_apply_apply_of_lt i.isLt]

@[simp]
theorem mulEquivPerm_inv_apply (a : ArrayPerm n) (i : Fin n) :
    (mulEquivPerm a)⁻¹ i = a.invArray[(i : ℕ)] := by
  rw [← map_inv, mulEquivPerm_apply_apply, getElem_inv_toArray]

@[simp]
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

@[simp]
theorem mulEquivPerm_symm_apply_invArray (π : Perm (Fin n)) :
    (mulEquivPerm.symm π).invArray = Array.ofFn (val ∘ ⇑π⁻¹) := by
  rw [← instInv_inv_toArray, ← map_inv, mulEquivPerm_symm_apply_toArray]

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
  rw [instSMulFin_smul_val, Perm.smul_def, mulEquivPerm_symm_apply_getElem_toArray]

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
  size_toArray' := h ▸ a.size_toArray'
  size_invArray' := h ▸ a.size_invArray'
  getElem_invArray_getElem_toArray' := a.getElem_invArray_getElem_toArray'

@[simp]
theorem cast_toArray (h : n = m) (a : ArrayPerm n) :
    (a.cast h).toArray = a.toArray := rfl

@[simp]
theorem cast_invArray (h : n = m) (a : ArrayPerm n) :
    (a.cast h).invArray = a.invArray := rfl

@[simp]
theorem cast_smul (h : n = m) (a : ArrayPerm n) (i : ℕ) :
    (a.cast h) • i = a • i := by simp only [instSMulNat_smul, cast_toArray, h]

@[simp]
theorem cast_inv (h : n = m) (a : ArrayPerm n) :
    (a.cast h)⁻¹ = a⁻¹.cast h := rfl

/--
When `n = m`, `ArrayPerm n` is multiplicatively equivalent to `ArrayPerm m`.
-/

def arrayPermCongr (h : n = m) : ArrayPerm n ≃* ArrayPerm m where
  toFun := cast h
  invFun := cast h.symm
  left_inv a := ext fun _ _ => by simp only [cast_smul]
  right_inv a := ext fun _ _ => by simp only [cast_smul]
  map_mul' a b := ext fun _ _ => by simp only [mul_smul, cast_smul]

/--
`ArrayPerm.castLE` re-interprets an `ArrayPerm n` as an `ArrayPerm m`, where `n ≤ m`.
-/
def castLE (h : n ≤ m) (a : ArrayPerm n) : ArrayPerm m where
  toArray := a.toArray.map (Fin.castLE h) ++
      ((Fin.enum (m - n)).map (Fin.cast (Nat.sub_add_cancel h) ∘ (Fin.addNat · n)))
  invArray := a.invArray.map (Fin.castLE h) ++
      ((Fin.enum (m - n)).map (Fin.cast (Nat.sub_add_cancel h) ∘ (Fin.addNat · n)))
  sizeTo' := by simp only [size_append, size_map, a.sizeTo, size_enum, Nat.add_sub_cancel' h]
  sizeInv' := by simp only [size_append, size_map, a.sizeInv, size_enum, Nat.add_sub_cancel' h]
  left_inv'  i := by
    rcases lt_or_le i.val a.toArray.size with hi | hi
    · simp_rw [Array.get_append_left (hi.trans_eq (size_map _ _).symm), Array.getElem_map,
      coe_castLE, Array.get_append_left (((size_map _ _).trans a.sizeInv).symm.trans_gt (is_lt _)),
        Array.getElem_map, ← Fin.coe_castLT _ (hi.trans_eq a.sizeTo), invArray_get_toArray_get,
        Fin.ext_iff, coe_castLE, coe_castLT]
    · simp_rw [Array.get_append_right ((size_map _ a.toArray).trans_le hi), Array.getElem_map,
        Fin.getElem_enum, comp_apply, addNat_mk, size_map, cast_mk, ← a.sizeTo,
        Nat.sub_add_cancel hi,
        Array.get_append_right ((((size_map _ _).trans a.sizeInv).trans
        a.sizeTo.symm).trans_le hi), size_map, Array.getElem_map, Fin.getElem_enum, comp_apply,
        addNat_mk, cast_mk, a.sizeInv, ← a.sizeTo, Nat.sub_add_cancel hi]

theorem castLE_toArray (a : ArrayPerm n) {h : n ≤ m} :
    (a.castLE h).toArray = a.toArray.map (Fin.castLE h) ++
      ((Fin.enum (m - n)).map (Fin.cast (Nat.sub_add_cancel h) ∘ (Fin.addNat · n))) := rfl

theorem castLE_invArray (a : ArrayPerm n) {h : n ≤ m} :
    (a.castLE h).invArray = a.invArray.map (Fin.castLE h) ++
      ((Fin.enum (m - n)).map (Fin.cast (Nat.sub_add_cancel h) ∘ (Fin.addNat · n))) := rfl

@[simp]
theorem castLE_smul_of_lt (a : ArrayPerm n) {i : Fin m} (hi : i < n) {h : n ≤ m} :
    (a.castLE h) • i = (a • (i.castLT hi)).castLE h := by
  simp_rw [smul_fin_def, castLE_toArray,
      Array.get_append_left (hi.trans_eq ((size_map _ _).trans a.sizeTo).symm),
      Array.getElem_map, coe_castLT]

@[simp]
theorem castLE_smul_of_ge (a : ArrayPerm n) {i : Fin m} (hi : n ≤ i) {h : n ≤ m} :
    (a.castLE h) • i = i := by
  simp_rw [smul_fin_def, castLE_toArray,
    Array.get_append_right (((size_map _ _).trans a.sizeTo).trans_le hi),
    size_map, Array.getElem_map, Fin.getElem_enum, comp_apply, addNat_mk, cast_mk, a.sizeTo,
    Nat.sub_add_cancel hi]

theorem castLE_smul (a : ArrayPerm n) {i : Fin m} {h : n ≤ m} :
    (a.castLE h) • i = if hi : i < n then (a • (i.castLT hi)).castLE h else i := by
  split_ifs with hi
  · exact a.castLE_smul_of_lt hi
  · exact a.castLE_smul_of_ge (le_of_not_lt hi)

theorem coe_castLE_smul (a : ArrayPerm n) {i : Fin m} {h : n ≤ m} :
    ((a.castLE h) • i).val = if i < n then a • i.val else i := by
  simp_rw [castLE_smul, apply_dite (Fin.val), coe_castLE, coe_smul, coe_castLT, dite_eq_ite]

@[simp]
theorem castLE_inv (a : ArrayPerm n) {h : n ≤ m} :
    (a.castLE h)⁻¹ = a⁻¹.castLE h := rfl

theorem castLE_mul {a b : ArrayPerm n} {h : n ≤ m} :
    (a * b).castLE h = a.castLE h * b.castLE h := by
  ext i
  simp only [mul_smul, coe_castLE_smul]
  rcases lt_or_le i.1 n with hi | hi
  · simp only [hi, if_true, ← lt_iff_smul_lt]
  · simp only [hi.not_lt, if_false]

theorem castLE_inj {a b : ArrayPerm n} {h : n ≤ m} : castLE h a = castLE h b ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [ext_iff, Fin.ext_iff, coe_castLE_smul, coe_smul, Fin.forall_iff]
  intros H i hi
  specialize H i (hi.trans_le h)
  simp_rw [hi, if_true] at H
  exact H

theorem castLE_injective {h : n ≤ m} : Function.Injective (castLE h) := fun _ _ => castLE_inj.mp

@[simp]
theorem castLE_one {h : n ≤ m} : ((1 : ArrayPerm n).castLE h) = 1 := by
  ext i : 1
  simp_rw [castLE_smul, one_smul, dite_eq_right_iff, Fin.ext_iff, coe_castLE,
    coe_castLT, implies_true]

def arrayPermMonoidHom (h : n ≤ m) : ArrayPerm n →* ArrayPerm m where
  toFun := castLE h
  map_mul' _ _ := castLE_mul
  map_one' := castLE_one

theorem arrayPermMonoidHom_injective {h : n ≤ m} :
  (⇑(arrayPermMonoidHom h)).Injective := castLE_injective

theorem castLE_of_eq (h : n = m) (h' : n ≤ m := h.le) (a : ArrayPerm n) :
    a.castLE h' = a.cast h := by
  ext i : 1
  simp_rw [castLE_smul, cast_smul, (i.isLt.trans_eq h.symm)]
  rfl

def CycleMinAux (a : ArrayPerm n) : ℕ → ArrayPerm n × {a : Array (Fin n) // a.size = n}
  | 0 => ⟨1, Fin.enum n, Fin.size_enum _⟩
  | 1 =>
    ⟨a, (Fin.enum n).zipWith a.toArray min, by
    rw [Array.size_zipWith, Fin.size_enum _, a.sizeTo, min_self]⟩
  | (i+2) =>
    have ⟨ρ, b, hb⟩ := a.CycleMinAux (i + 1);
    have ρ' := ρ ^ 2
    ⟨ρ', b.zipWith ((Fin.enum n).map (b[ρ' • ·])) min,
    by simp_rw [Array.size_zipWith, hb, Array.size_map, Fin.size_enum, min_self]⟩

def CycleMin (a : ArrayPerm n) (i : ℕ) : Array (Fin n) := (a.CycleMinAux i).2.1

theorem size_cycleMin (a : ArrayPerm n) (i : ℕ) : (a.CycleMin i).size = n := (a.CycleMinAux i).2.2

theorem cycleMinAux_succ_fst (a : ArrayPerm n) (i : ℕ) :
    (a.CycleMinAux (i + 1)).1 = a ^ (2 ^ i) := by
  induction' i with i IH
  · rw [pow_zero, pow_one]
    rfl
  · rw [pow_succ, pow_mul]
    exact IH ▸ rfl

theorem cycleMin_zero (a : ArrayPerm n) : a.CycleMin 0 = Fin.enum n := rfl


theorem cycleMin_one (a : ArrayPerm n) :
  a.CycleMin 1 = (Fin.enum n).zipWith a.toArray min := rfl

theorem cycleMin_succ_succ (a : ArrayPerm n) (i : ℕ) :
    haveI := a.size_cycleMin (i + 1)
    (a.CycleMin (i + 2)) = (a.CycleMin (i + 1)).zipWith ((Fin.enum n).map
      ((a.CycleMin (i + 1))[a ^ (2 ^ (i + 1)) • ·])) min := by
  rw [← cycleMinAux_succ_fst]
  rfl

theorem getElem_cycleMin_zero (a : ArrayPerm n) (x : ℕ) (h : x < (a.CycleMin 0).size) :
    (a.CycleMin 0)[x] = x := by
  simp_rw [cycleMin_zero, Fin.getElem_enum]

@[simp]
lemma getElem_CycleMin_succ (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin (i + 1)).size) :
  haveI := a.size_cycleMin (i + 1)
  haveI := a.size_cycleMin i
  haveI := (a ^ 2^i).lt_iff_smul_lt (i := x)
  (a.CycleMin (i + 1))[x] = min (a.CycleMin i)[x] (a.CycleMin i)[(a ^ 2^i) • x] := by
  cases' i with i
  · simp_rw [zero_add, cycleMin_one, cycleMin_zero, Array.getElem_zipWith,
    Fin.getElem_enum, pow_zero, pow_one, a.smul_of_lt (h.trans_eq <| a.size_cycleMin 1)]
  · simp_rw [cycleMin_succ_succ, Array.getElem_zipWith, Array.getElem_map, Fin.getElem_enum,
    (a ^ 2 ^ (i + 1)).smul_nat_eq_smul_fin_of_lt (h.trans_eq <| a.size_cycleMin _), getElem_fin]

lemma cycleMin_le (a : ArrayPerm n) (x : ℕ) (i : ℕ) (h : x < (a.CycleMin i).size):
    ∀ k < 2^i, (a.CycleMin i)[x] ≤ (a ^ k) • x := by
  induction' i with i IH generalizing x
  · simp_rw [pow_zero, Nat.lt_one_iff, getElem_cycleMin_zero, forall_eq, pow_zero, one_smul, le_rfl]
  · simp_rw [pow_succ', Nat.two_mul, getElem_CycleMin_succ, Fin.coe_min, min_le_iff]
    intro k hk'
    rcases lt_or_le k (2^i) with hk | hk
    · exact Or.inl (IH _ _ _ hk)
    · rw [← Nat.sub_lt_iff_lt_add hk] at hk'
      convert Or.inr (IH _ _ _ hk') using 2
      rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hk]

/--
For `a` an `ArrayPerm n`, `a.swap i j` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : ArrayPerm n) (i j : Fin n) : ArrayPerm n where
  toArray := a.toArray.swap (i.cast a.sizeTo.symm) (j.cast a.sizeTo.symm)
  invArray := a.invArray.map (fun k => Equiv.swap i j k)
  sizeTo' := (Array.size_swap _ _ _).trans a.sizeTo
  sizeInv' := (Array.size_map _ _).trans a.sizeInv
  left_inv' k := by
    simp_rw [a.toArray.get_swap', getElem_fin, coe_cast, toArray_eq_smul_mk, Array.getElem_map,
      invArray_eq_smul_mk, Fin.eta, smul_ite, inv_smul_smul, ← Fin.ext_iff,
      ← Equiv.swap_apply_def, swap_apply_self]

@[simp]
theorem uncurry_swap (a : ArrayPerm n) (x : Fin n × Fin n) :
  uncurry a.swap x = a.swap x.1 x.2 := rfl

theorem swap_toArray (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).toArray =
a.toArray.swap (i.cast a.sizeTo.symm) (j.cast a.sizeTo.symm) := rfl

theorem swap_invArray (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).invArray =
a.invArray.map (fun k => Equiv.swap i j k) := rfl

theorem swap_smul (a : ArrayPerm n) (i j k : Fin n) :
    (a.swap i j) • k = a • (Equiv.swap i j k) := by
  simp_rw [Equiv.swap_apply_def, apply_ite (a • ·), Fin.ext_iff (a := k)]
  exact a.toArray.get_swap _ _ _ ((sizeTo _).symm.trans_gt k.isLt)

theorem uncurry_swap_smul (a : ArrayPerm n) (b : Fin n × Fin n) (k : Fin n) :
    (uncurry a.swap b) • k = a • (uncurry Equiv.swap b k) := swap_smul _ _ _ _

theorem swap_inv_smul (a : ArrayPerm n) (i j k : Fin n) :
    (a.swap i j)⁻¹ • k =
    a⁻¹ • (Equiv.swap (a • i) (a • j) k) := by
  simp_rw [inv_smul_eq_iff, swap_smul, ← Equiv.swap_smul, smul_inv_smul, swap_apply_self]

@[simp]
theorem one_swap_smul (i j k : Fin n) : (swap 1 i j) • k = Equiv.swap i j k := by
  rw [swap_smul, one_smul]

theorem one_swap_inv_smul (i j k : Fin n) : (swap 1 i j)⁻¹ • k = Equiv.swap i j k := by
  simp_rw [swap_inv_smul, one_smul, inv_one, one_smul]

@[simp]
theorem one_swap_mul_self (i j : Fin n) : swap 1 i j * swap 1 i j = 1 := by
  ext : 1
  simp_rw [mul_smul, one_swap_smul, swap_apply_self, one_smul]

@[simp]
theorem one_swap_inverse (i j : Fin n) : (swap 1 i j)⁻¹ = swap 1 i j := by
  ext : 1
  rw [one_swap_smul, one_swap_inv_smul]

theorem swap_eq_mul_one_swap (a : ArrayPerm n) (i j : Fin n) : a.swap i j = a * swap 1 i j := by
  ext : 1
  simp only [swap_smul, mul_smul, one_swap_smul, one_smul]

theorem mulEquivPerm_swap (a : ArrayPerm n) (i j : Fin n) :
    mulEquivPerm (swap a i j) = mulEquivPerm a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, mulEquivPerm_apply_apply, swap_smul]

@[simp]
theorem mulEquivPerm_one_swap (i j : Fin n) :
    mulEquivPerm (swap 1 i j) = Equiv.swap i j := by simp_rw [mulEquivPerm_swap, map_one, one_mul]

theorem swap_eq_one_swap_mul (a : ArrayPerm n) (i j : Fin n) :
    a.swap i j = swap 1 (a • i) (a • j) * a := by
  ext : 1
  simp_rw [mul_smul, one_swap_smul, swap_smul, Equiv.swap_smul]

theorem swap_smul' (a : ArrayPerm n) (i j k : Fin n) :
    (a.swap i j) • k = Equiv.swap (a • i) (a • j) (a • k) := by
  rw [swap_eq_one_swap_mul, mul_smul, one_swap_smul]

theorem swap_smul_left (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j) • i = a • j := by rw [swap_smul, swap_apply_left]

theorem swap_smul_right (a : ArrayPerm n) (i j : Fin n) :
  (a.swap i j) • j = a • i := by rw [swap_smul, swap_apply_right]

theorem swap_smul_of_ne_of_ne (a : ArrayPerm n) (i j : Fin n) {k} :
  k ≠ i → k ≠ j → (a.swap i j) • k = a • k := by
  rw [swap_smul, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

theorem swap_inv_eq_one_swap_mul (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j)⁻¹ = swap 1 i j * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j)⁻¹ = a⁻¹ * swap 1 (a • i) (a • j) := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

theorem swap_inv_smul' (a : ArrayPerm n) (i j k : Fin n) :
  (a.swap i j)⁻¹ • k = Equiv.swap i j (a⁻¹ • k) := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, mul_smul, one_swap_inv_smul]

theorem swap_inv_smul_left (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j)⁻¹ • (a • i) = j := by
  rw [swap_inv_smul, swap_apply_left, inv_smul_smul]

theorem swap_inbv_smul_right (a : ArrayPerm n) (i j : Fin n) :
    (a.swap i j)⁻¹ • (a • j) = i := by
  rw [swap_inv_smul, swap_apply_right, inv_smul_smul]

theorem swap_inv_smul_of_ne_of_ne (a : ArrayPerm n) (i j : Fin n) {k} :
  k ≠ a • i → k ≠ a • j → (a.swap i j)⁻¹ • k = a⁻¹ • k := by
  rw [swap_inv_smul, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (a : ArrayPerm n) (i : Fin n) : a.swap i i = a := by
  ext : 1
  rw [swap_smul, Equiv.swap_self, Equiv.refl_apply]

@[simp]
theorem swap_swap (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).swap i j = a := by
  ext : 1
  simp_rw [swap_smul, swap_apply_self]

/--
For `a` an `ArrayPerm n`, `a.swaps bs` performs the swaps given by the list `bs` in order.
-/
def swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : ArrayPerm n where
  toArray := a.toArray.swaps (bs.map <| Prod.map (Fin.cast a.sizeTo.symm) (Fin.cast a.sizeTo.symm))
  invArray := a.invArray.map (fun k => Equiv.swaps bs.reverse k)
  sizeTo' := (a.toArray.size_swaps _).trans a.sizeTo
  sizeInv' := (a.invArray.size_map _).trans a.sizeInv
  left_inv' i := by
    simp_rw [a.toArray.get_swaps_eq_get_apply_swaps', a.invArray.getElem_map,
    Fin.ext_iff, map_map, Prod.map_comp_map, val_comp_cast, swaps_coe,
    a.invArray_get_toArray_get, Equiv.swaps_reverse, Perm.inv_apply_self]

theorem swaps_toArray (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs).toArray =
  a.toArray.swaps (bs.map <| Prod.map (Fin.cast a.sizeTo.symm) (Fin.cast a.sizeTo.symm)) := rfl

theorem swaps_invArray (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : (a.swaps bs).invArray =
    a.invArray.map (fun k => Equiv.swaps bs.reverse k) := rfl

@[simp]
theorem swaps_smul (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (k : Fin n) :
    (a.swaps bs) • k = a • Equiv.swaps bs k :=
  (a.toArray.get_swaps_eq_get_apply_swaps' _ _).trans <| by
  simp_rw [map_map, Prod.map_comp_map, val_comp_cast, swaps_coe, toArray_eq_smul_mk]

theorem one_swaps_smul (bs : List (Fin n × Fin n)) (k : Fin n) :
    (swaps 1 bs) • k = Equiv.swaps bs k := by simp only [swaps_smul, one_smul]

theorem swaps_eq_mul_one_swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)):
    a.swaps bs = a * swaps 1 bs := ArrayPerm.ext fun _ => by
  simp only [swaps_smul, mul_smul, one_smul, id_comp]

@[simp]
theorem mulEquivPerm_swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    mulEquivPerm (swaps a bs) = mulEquivPerm a * Equiv.swaps bs := Equiv.ext fun _ => by
  simp only [mulEquivPerm_apply_apply, swaps_smul, Perm.mul_apply]

theorem mulEquivPerm_one_swaps (bs : List (Fin n × Fin n))  :
    mulEquivPerm (swaps 1 bs) = Equiv.swaps bs := by simp_rw [mulEquivPerm_swaps, map_one, one_mul]

theorem swaps_eq_one_swaps_mul (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : a.swaps bs =
    swaps 1 (bs.map (a • ·)) * a := by
  ext k : 1
  rw [mul_smul, one_swaps_smul, swaps_smul, Equiv.swaps_smul]

theorem one_swaps_inverse (bs : List (Fin n × Fin n)) : (swaps 1 bs)⁻¹ =
    swaps 1 bs.reverse := by
  ext : 1
  simp_rw [inv_smul_eq_iff, one_swaps_smul, swaps_reverse_apply_swaps_reverse]

theorem swaps_inv_eq_one_swaps_mul (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs)⁻¹ = swaps 1 bs.reverse * a⁻¹ := by
  rw [swaps_eq_mul_one_swaps, mul_inv_rev, one_swaps_inverse]

theorem swaps_inv_eq_mul_one_swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs)⁻¹ = a⁻¹ * swaps 1 (bs.reverse.map (a • ·)) := by
  rw [swaps_eq_one_swaps_mul, mul_inv_rev, mul_right_inj, one_swaps_inverse, map_reverse]

theorem swaps_inv_smul (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (k : Fin n) :
    (a.swaps bs)⁻¹ • k =
    a⁻¹ • Equiv.swaps (bs.reverse.map (a • ·)) k := by
  simp_rw [a.swaps_inv_eq_mul_one_swaps, mul_smul, swaps_smul, one_smul]


@[simp]
theorem one_swaps_inv_smul (bs : List (Fin n × Fin n)) (k : Fin n) :
    (swaps 1 bs)⁻¹ • k = Equiv.swaps bs.reverse k := by
  simp only [inv_smul_eq_iff, swaps_smul, swaps_reverse_apply_swaps_reverse, one_smul]

theorem swaps_smul' (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (k : Fin n) :
    (a.swaps bs) • k = Equiv.swaps (bs.map (a • ·)) (a • k) := by
  rw [swaps_eq_one_swaps_mul, mul_smul, one_swaps_smul]

theorem swaps_inv_smul' (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (k : Fin n) :
    (a.swaps bs)⁻¹ • k = Equiv.swaps bs.reverse (a⁻¹ • k) := by
  rw [swaps_eq_mul_one_swaps, mul_inv_rev, mul_smul, one_swaps_inv_smul]

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
theorem swaps_nil (a : ArrayPerm n) : a.swaps [] = a := by
  ext : 1
  simp_rw [swaps_smul, Equiv.swaps_nil, Perm.coe_one, id_eq]

@[simp]
theorem swaps_cons (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (b : Fin n × Fin n) :
    a.swaps (b :: bs) = (uncurry a.swap b).swaps bs := by
  ext : 1
  simp_rw [swaps_smul, uncurry_swap_smul, Equiv.swaps_cons, Perm.mul_apply]

theorem swaps_eq_foldl (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    a.swaps bs = bs.foldl (fun a b => uncurry a.swap b) a := by
  induction' bs with b bs IH generalizing a
  · rw [swaps_nil, foldl_nil]
  · rw [swaps_cons, foldl_cons, IH]

theorem swaps_singleton (a : ArrayPerm n) (b : Fin n × Fin n) : a.swaps [b] = uncurry a.swap b := rfl

@[simp]
theorem swaps_append (a : ArrayPerm n) (bs cs : List (Fin n × Fin n)) :
    a.swaps (bs ++ cs) = (a.swaps bs).swaps cs := by
  simp_rw [swaps_eq_foldl, foldl_append]

theorem swaps_swaps (a : ArrayPerm n) (bs cs : List (Fin n × Fin n)) :
    (a.swaps bs).swaps cs = a.swaps (bs ++ cs) := (a.swaps_append _ _).symm

theorem swaps_concat (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (b : Fin n × Fin n) :
  a.swaps (bs ++ [b]) = uncurry (a.swaps bs).swap b := by
  simp_rw [swaps_append, swaps_singleton]

theorem swaps_concat' (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (b : Fin n × Fin n) :
  a.swaps (bs.concat b) = uncurry (a.swaps bs).swap b := by
  simp_rw [concat_eq_append, swaps_concat]

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
