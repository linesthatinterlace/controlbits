import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.List.DropRight
import Mathlib.Data.List.Indexes
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.GroupTheory.GroupAction.Prod
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
    Prod_map, hf.swap_apply]

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
    swap_mul_eq_mul_swap, mul_assoc, Prod_map]

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
    let IH := IH _ fun b h => hb b (Or.inl h)
    let hb := hb b (Or.inr rfl)
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
  toArray : Array (Fin n)
  /--
  Gives the `ArrayPerm` as an array of indexes. Value `v` is mapped to the index at position `v`
  in `invArray`.
  -/
  invArray : Array (Fin n)
  sizeTo : toArray.size = n := by rfl
  sizeInv : invArray.size = n := by rfl
  left_inv' : ∀ i : Fin n, invArray[toArray[i.val].val] = i := by decide

namespace ArrayPerm

open Function Fin Equiv List Array

variable {n m : ℕ}

instance : Repr (ArrayPerm n) where
  reprPrec a _ := "ArrayPerm " ++ repr n ++ " : " ++ repr a.toArray

instance : ToString (ArrayPerm n) where
  toString a := "ArrayPerm " ++ toString n ++ " : " ++ toString a.toArray

theorem invArray_get_toArray_get (a : ArrayPerm n) (i : Fin n) :
    haveI ha := a.sizeTo ; haveI hai := a.sizeInv;
    a.invArray[a.toArray[i.val].val] = i := a.left_inv' _

theorem invArray_surjective (a : ArrayPerm n) :
    haveI ha := a.sizeInv;
    Function.Surjective (fun j : Fin n => a.invArray[j.val]) :=
  haveI hai := a.sizeTo;
  fun i => ⟨a.toArray[i.val], a.invArray_get_toArray_get _⟩

theorem toArray_injective (a : ArrayPerm n) :
    haveI ha := a.sizeTo;
    Function.Injective (fun j : Fin n => a.toArray[j.val]) :=
  haveI hai := a.sizeInv;
  fun _ _ h => by
    have H := congrArg (fun i : Fin n => a.invArray[i.val]) h
    simp_rw [invArray_get_toArray_get] at H
    exact H

theorem invArray_injective (a : ArrayPerm n) :
    haveI ha := a.sizeInv;
    Function.Injective (fun j : Fin n => a.invArray[j.val]) :=
  a.invArray_surjective.injective_of_fintype (Equiv.refl _)

theorem toArray_surjective (a : ArrayPerm n) :
    haveI ha := a.sizeTo;
    Function.Surjective (fun j : Fin n => a.toArray[j.val]) :=
  a.toArray_injective.surjective_of_fintype (Equiv.refl _)

theorem toArray_get_invArray_get (a : ArrayPerm n) (i : Fin n) :
    haveI ha := a.sizeTo ; haveI hai := a.sizeInv;
    a.toArray[a.invArray[i.val].val] = i :=
  a.invArray_injective (by simp_rw [a.left_inv'])

/--
We can make an `ArrayPerm` using the right-inverse hypothesis instead of the left-inverse
hypothesis, and we called this `ArrayPerm.mk'`.
-/
protected def mk' (toArray : Array (Fin n)) (invArray : Array (Fin n))
  (sizeTo : toArray.size = n := by rfl) (sizeInv : invArray.size = n := by rfl)
  (right_inv' : ∀ i : Fin n, toArray[(invArray[(i : ℕ)] : ℕ)] = i := by decide) : ArrayPerm n :=
  {toArray, invArray, sizeTo, sizeInv,
    left_inv' :=
      haveI A : ArrayPerm n := ⟨invArray, toArray, sizeInv, sizeTo, right_inv'⟩;
      A.toArray_get_invArray_get}

theorem invArray_eq_iff_toArray_eq (a b : ArrayPerm n) :
    a.invArray = b.invArray ↔ a.toArray = b.toArray := by
  refine' ⟨fun h => Array.ext _ _ (a.sizeTo.trans b.sizeTo.symm) _,
  fun h => Array.ext _ _ (a.sizeInv.trans b.sizeInv.symm) _⟩ <;>
  simp only [a.sizeTo, b.sizeTo, a.sizeInv, b.sizeInv, Fin.forall₂_iff] <;>
  refine' fun _ => _
  · apply a.invArray_injective
    simp_rw [a.invArray_get_toArray_get, h, b.invArray_get_toArray_get]
  · apply a.toArray_injective
    simp_rw [a.toArray_get_invArray_get, h, b.toArray_get_invArray_get]

theorem eq_iff_toArray_eq (a b : ArrayPerm n) : a = b ↔ a.toArray = b.toArray := by
  trans (a.toArray = b.toArray ∧ a.invArray = b.invArray)
  · rcases a ; rcases b ; simp_rw [mk.injEq]
  · rw [invArray_eq_iff_toArray_eq, and_self]

theorem eq_iff_toArray_get_eq (a b : ArrayPerm n) :
  haveI := a.sizeTo ; haveI := b.sizeTo ;
  a = b ↔ ∀ (i : Fin n),
  a.toArray[i.val] = b.toArray[i.val] := ⟨fun h _ => h ▸ rfl, fun h => by
    rw [eq_iff_toArray_eq]
    refine' Array.ext _ _ (a.sizeTo.trans b.sizeTo.symm) _
    simp_rw [a.sizeTo, b.sizeTo, Fin.forall₂_iff]
    exact h⟩

theorem eq_of_toArray_get_eq (a b : ArrayPerm n)
  (h : haveI := a.sizeTo ; haveI := b.sizeTo ; ∀ (i : Fin n),
  a.toArray[i.val] = b.toArray[i.val]) : a = b := (a.eq_iff_toArray_get_eq b).mpr h

instance One : One (ArrayPerm n) :=
⟨enum n, enum n, size_enum _, size_enum _, fun h => by simp only [Fin.getElem_fin, getElem_enum]⟩

theorem one_toArray : (1 : ArrayPerm n).toArray = enum n := rfl
theorem one_invArray : (1 : ArrayPerm n).invArray = enum n := rfl
theorem one_toArray_get {i : Fin n} :
  haveI h := (1 : ArrayPerm n).sizeTo ; (1 : ArrayPerm n).toArray[i.val] = i := getElem_enum _ _
theorem one_invArray_get (i : Fin n) :
  haveI h := (1 : ArrayPerm n).sizeInv ; (1 : ArrayPerm n).invArray[i.val] = i := getElem_enum _ _

instance : Inv (ArrayPerm n) :=
⟨fun a => ArrayPerm.mk' a.invArray a.toArray a.sizeInv a.sizeTo a.left_inv'⟩

theorem inv_toArray (a : ArrayPerm n) : a⁻¹.toArray = a.invArray := rfl
theorem inv_invArray (a : ArrayPerm n) : a⁻¹.invArray = a.toArray := rfl

theorem inv_toArray_get (a : ArrayPerm n) (i : Fin n) :
    haveI hai := a⁻¹.sizeTo; haveI ha := a.sizeInv;
    a⁻¹.toArray[i.val] = a.invArray[i.val] := rfl
theorem inv_invArray_get (a : ArrayPerm n) (i : Fin n) :
    haveI hai := a⁻¹.sizeInv; haveI ha := a.sizeTo;
    a⁻¹.invArray[i.val] = a.toArray[i.val] := rfl

instance : Mul (ArrayPerm n) := ⟨fun a b =>
  ⟨b.toArray.map (fun i => haveI := a.sizeTo ; a.toArray[i.val]),
    a.invArray.map (fun i => haveI := b.sizeInv ; b.invArray[i.val]),
    (b.toArray.size_map _).trans b.sizeTo,
    (a.invArray.size_map _).trans a.sizeInv, fun _ => by
    simp_rw [getElem_map, a.left_inv', b.left_inv']⟩⟩

theorem mul_toArray (a b : ArrayPerm n) :
(a * b).toArray = b.toArray.map (fun i => haveI := a.sizeTo ; a.toArray[i.val]) := rfl
theorem mul_invArray (a b : ArrayPerm n) :
(a * b).invArray = a.invArray.map (fun i => haveI := b.sizeInv ; b.invArray[i.val]) := rfl

theorem mul_toArray_get (a b : ArrayPerm n) (i : Fin n) :
    haveI ha := a.sizeTo; haveI hb := b.sizeTo; haveI hab := (a * b).sizeTo;
    (a * b).toArray[i.val] = a.toArray[b.toArray[i.val].val] := by
  simp_rw [mul_toArray, getElem_map]

theorem mul_invArray_get (a b : ArrayPerm n) (i : Fin n) :
    haveI ha := a.sizeInv; haveI hb := b.sizeInv; haveI hab := (a * b).sizeInv;
    (a * b).invArray[i.val] = b.invArray[a.invArray[i.val].val] := by
  simp_rw [mul_invArray, getElem_map]

instance : Group (ArrayPerm n) where
  mul_assoc a b c := (a * b * c).eq_of_toArray_get_eq (a * (b * c)) fun _ => by
    simp_rw [mul_toArray_get]
  one_mul a := (1 * a).eq_of_toArray_get_eq a fun _ => by
    simp_rw [mul_toArray_get, one_toArray_get]
  mul_one a := (a * 1).eq_of_toArray_get_eq a fun _ => by
    simp_rw [mul_toArray_get, one_toArray_get]
  mul_left_inv a := (a⁻¹ * a).eq_of_toArray_get_eq 1 fun _ => by
    rw [mul_toArray_get, inv_toArray_get, one_toArray_get, invArray_get_toArray_get]

instance : SMul (ArrayPerm n) (Fin n) where
  smul a i := haveI := a.sizeTo ; a.toArray[(i : ℕ)]

instance : FaithfulSMul (ArrayPerm n) (Fin n) where
  eq_of_smul_eq_smul := (eq_iff_toArray_get_eq _ _).mpr

instance : MulAction (ArrayPerm n) (Fin n) where
  one_smul _ := getElem_enum _ _
  mul_smul _ _ _ := getElem_map _ _ _ _

theorem smul_def (a : ArrayPerm n) (i : Fin n) :
    haveI := a.sizeTo ; a • i = a.toArray[i.val] := rfl

theorem mul_smul_def (a b : ArrayPerm n) (i : Fin n) :
    haveI := a.sizeTo; haveI := b.sizeTo
    (a * b) • i = a.toArray[b.toArray[i.val].val] := getElem_map _ _ _ _

theorem inv_smul_def (a : ArrayPerm n) (i : Fin n) :
    haveI := a.sizeInv ; a⁻¹ • i = a.invArray[i.val] := rfl

@[simp]
theorem mk_smul {a b : Array (Fin n)} {sa sb hab} {i : Fin n} :
  (⟨a, b, sa, sb, hab⟩ : ArrayPerm n) • i = a[i.val] := rfl

@[simp]
theorem mk_inv_smul {a b : Array (Fin n)} {sa sb hab} {i : Fin n} :
  (⟨a, b, sa, sb, hab⟩ : ArrayPerm n)⁻¹ • i = b[i.val] := rfl

theorem smul_mk (a : ArrayPerm n) {i : ℕ} (h : i < n) :
  a • ⟨i, h⟩ = a.toArray[i]'(a.sizeTo.symm.trans_gt h) := rfl

theorem inv_smul_mk (a : ArrayPerm n) {i : ℕ} (h : i < n) :
  a⁻¹ • ⟨i, h⟩ = a.invArray[i]'(a.sizeInv.symm.trans_gt h) := rfl

theorem toArray_eq_smul_mk (a : ArrayPerm n) {i : ℕ} (h : i < a.toArray.size) :
  a.toArray[i] = a • ⟨i, a.sizeTo.trans_gt h⟩ := rfl

theorem invArray_eq_smul_mk (a : ArrayPerm n) {i : ℕ} (h : i < a.invArray.size) :
  a.invArray[i] = a⁻¹ • ⟨i, a.sizeInv.trans_gt h⟩ := rfl

@[simp]
theorem toArray_coe (a : ArrayPerm n) {i : Fin n} :
  haveI := a.sizeTo ; a.toArray[i.val] = a • i := rfl

@[simp]
theorem invArray_coe (a : ArrayPerm n) {i : Fin n} :
  haveI := a.sizeInv; a.invArray[i.val] = a⁻¹ • i := rfl

@[ext]
theorem ext {a b : ArrayPerm n} (h : ∀ (i : Fin n), a • i = b • i) : a = b :=
  FaithfulSMul.eq_of_smul_eq_smul h

theorem ext_iff (a b : ArrayPerm n) : a = b ↔ ∀ (i : Fin n), a • i = b • i :=
  ⟨fun h _ => h ▸ rfl, ext⟩

/--
`ArrayPerm n` is equivalent to `Perm (Fin n)`, and this equivalence respects the
multiplication (and, indeed, the scalar action on `Fin n`).
-/
@[simps! apply_apply apply_symm_apply]
def mulEquivPerm : ArrayPerm n ≃* Perm (Fin n) where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  invFun π := ⟨ofFn π, ofFn π.symm, size_ofFn _, size_ofFn _, fun _ => by
    simp_rw [getElem_ofFn, Fin.eta, symm_apply_apply]⟩
  left_inv a := ext fun _ => by simp_rw [mk_smul, getElem_ofFn, Fin.eta, coe_fn_mk]
  right_inv π := Equiv.ext fun _ => by
    simp_rw [mk_smul, mk_inv_smul, getElem_ofFn, Fin.eta, coe_fn_mk]
  map_mul' a b := Equiv.ext fun _ => by
    simp_rw [mul_smul, mul_inv_rev, Perm.coe_mul, comp_apply, coe_fn_mk]

@[simp]
theorem mulEquivPerm_smul (a : ArrayPerm n) (i : Fin n) :
  (mulEquivPerm a) • i = a • i := rfl

theorem mulEquivPerm_inv_smul (a : ArrayPerm n) (i : Fin n) :
  (mulEquivPerm a)⁻¹ • i = a⁻¹ • i := rfl

@[simp]
theorem mulEquivPerm_symm_smul (π : Perm (Fin n)) (i : Fin n) :
  (mulEquivPerm.symm π) • i = π • i := Array.getElem_ofFn _ _ _

@[simp]
theorem mulEquivPerm_symm_inv_smul (π : Perm (Fin n)) (i : Fin n):
  (mulEquivPerm.symm π)⁻¹ • i = π⁻¹ • i := Array.getElem_ofFn _ _ _

/--
`ArrayPerm.congr` re-interprets an `ArrayPerm n` as an `ArrayPerm m`, where `n = m`.
-/
def congr (h : n = m) (a : ArrayPerm n) : ArrayPerm m where
  toArray := a.toArray.map <| Fin.cast h
  invArray := a.invArray.map <| Fin.cast h
  sizeTo := (a.toArray.size_map _).trans <| a.sizeTo.trans h
  sizeInv := (a.invArray.size_map _).trans <| a.sizeInv.trans h
  left_inv'  i := by
    simp_rw [getElem_map, coe_cast, ← Fin.coe_cast h.symm i,
    invArray_get_toArray_get, Fin.cast_trans, cast_eq_self]

theorem congr_toArray (h : n = m) (a : ArrayPerm n) :
    (a.congr h).toArray = a.toArray.map (Fin.cast h) := rfl

theorem congr_invArray (h : n = m) (a : ArrayPerm n) :
    (a.congr h).invArray = a.invArray.map (Fin.cast h) := rfl

@[simp]
theorem congr_smul (h : n = m) (a : ArrayPerm n) (i : Fin m):
    (a.congr h) • i = (a • (i.cast h.symm)).cast h := getElem_map _ _ _ _

@[simp]
theorem congr_inv (h : n = m) (a : ArrayPerm n) :
    (a.congr h)⁻¹ = a⁻¹.congr h := rfl

/--
When `n = m`, `ArrayPerm n` is multiplicatively equivalent to `ArrayPerm m`.
-/

def arrayPermCongr (h : n = m) : ArrayPerm n ≃* ArrayPerm m where
  toFun := congr h
  invFun := congr h.symm
  left_inv a := by
    ext : 1
    simp [congr_smul, conj_apply, finCongr_symm,
    finCongr_apply, Fin.cast_trans, cast_eq_self]
  right_inv a := by
    ext : 1
    simp only [congr_smul, conj_apply, finCongr_symm,
    finCongr_apply, Fin.cast_trans, cast_eq_self]
  map_mul' a b := by
    ext : 1
    simp only [congr_smul, mul_smul, Fin.cast_trans, cast_eq_self]

/--
For `a` an `ArrayPerm n`, `a.swap i j` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : ArrayPerm n) (i j : Fin n) : ArrayPerm n where
  toArray := a.toArray.swap (i.cast a.sizeTo.symm) (j.cast a.sizeTo.symm)
  invArray := a.invArray.swap ((a • i).cast a.sizeInv.symm) ((a • j).cast a.sizeInv.symm)
  sizeTo := (Array.size_swap _ _ _).trans a.sizeTo
  sizeInv := (Array.size_swap _ _ _).trans a.sizeInv
  left_inv' k := by
    simp_rw [a.toArray.get_swap', a.invArray.get_swap', Fin.getElem_fin, coe_cast, invArray_coe,
    toArray_coe, val_eq_val, ← apply_ite (a • ·), inv_smul_smul, smul_left_cancel_iff]
    rcases eq_or_ne k i with rfl | hki
    · simp_rw [if_true, ite_eq_right_iff, imp_self]
    · simp_rw [hki, if_false]
      rcases eq_or_ne k j with rfl | hkj
      · simp_rw [if_true]
      · simp_rw [if_neg hkj, if_neg hki]

@[simp]
theorem uncurry_swap (a : ArrayPerm n) (x : Fin n × Fin n) :
  uncurry a.swap x = a.swap x.1 x.2 := rfl

theorem swap_toArray (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).toArray =
a.toArray.swap (i.cast a.sizeTo.symm) (j.cast a.sizeTo.symm) := rfl

theorem swap_invArray (a : ArrayPerm n) (i j : Fin n) : (a.swap i j).invArray =
a.invArray.swap ((a • i).cast a.sizeInv.symm) ((a • j).cast a.sizeInv.symm) := rfl

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
  invArray := a.invArray.swaps (bs.reverse.map
    <| (Prod.map (Fin.cast a.sizeInv.symm) (Fin.cast a.sizeInv.symm)) ∘ (a • ·))
  sizeTo := (a.toArray.size_swaps _).trans a.sizeTo
  sizeInv := (a.invArray.size_swaps _).trans a.sizeInv
  left_inv' i := by
    simp_rw [a.toArray.get_swaps_eq_get_apply_swaps', a.invArray.get_swaps_eq_get_apply_swaps',
    toArray_eq_smul_mk, invArray_eq_smul_mk, map_map, Prod.map_comp_map_left, Prod.map_comp_map,
    val_comp_cast, ← map_map, swaps_coe, Fin.eta, swaps_smul,
    Equiv.swaps_reverse, Perm.inv_apply_self, inv_smul_smul]

theorem swaps_toArray (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    (a.swaps bs).toArray =
  a.toArray.swaps (bs.map <| Prod.map (Fin.cast a.sizeTo.symm) (Fin.cast a.sizeTo.symm)) := rfl

theorem swaps_invArray (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : (a.swaps bs).invArray =
    a.invArray.swaps (bs.reverse.map
    <| (Prod.map (Fin.cast a.sizeInv.symm) (Fin.cast a.sizeInv.symm)) ∘ (a • ·)) := rfl

@[simp]
theorem swaps_smul (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (k : Fin n) :
    (a.swaps bs) • k = a • Equiv.swaps bs k :=
  (a.toArray.get_swaps_eq_get_apply_swaps' _ _).trans <| by
  simp_rw [map_map, Prod.map_comp_map, val_comp_cast, swaps_coe, toArray_coe]

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
theorem swaps_nil (a : ArrayPerm n) : a.swaps [] = a := rfl

@[simp]
theorem swaps_cons (a : ArrayPerm n) (bs : List (Fin n × Fin n)) (b : Fin n × Fin n) :
    a.swaps (b :: bs) = (uncurry a.swap b).swaps bs := by
  ext : 1
  simp_rw [swaps_smul, uncurry_swap_smul, Equiv.swaps_cons, Perm.mul_apply]

theorem swaps_eq_foldl (a : ArrayPerm n) (bs : List (Fin n × Fin n)) :
    a.swaps bs = bs.foldl (fun a b => uncurry a.swap b) a := by
  induction' bs with b bs IH generalizing a
  · rfl
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
