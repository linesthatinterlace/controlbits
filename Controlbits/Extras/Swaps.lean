import Controlbits.ArrayPerm

namespace Equiv
open List Function Fin Prod
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

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

/--Swaps pairs of entries in an array a given by a list bs.-/
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

namespace ArrayPerm


/--
For `a` an `ArrayPerm n`, `a.swaps bs` performs the swaps given by the list `bs` in order.
-/
def swaps (a : ArrayPerm n) (bs : List (Fin n × Fin n)) : ArrayPerm n where
  toArray := a.toArray.swaps (bs.map <| Prod.map (Fin.cast a.sizeTo.symm) (Fin.cast a.sizeTo.symm))
  invArray := a.invArray.map (fun k => Equiv.swaps bs.reverse k)
  size_toArray := _
  size_invArray := _
  getElem_toArray_lt' := _
  getElem_invArray_lt' := _
  getElem_invArray_getElem_toArray' := _
  /-sizeTo' := (a.toArray.size_swaps _).trans a.sizeTo
  sizeInv' := (a.invArray.size_map _).trans a.sizeInv
  left_inv' i := by
    simp_rw [a.toArray.get_swaps_eq_get_apply_swaps', a.invArray.getElem_map,
    Fin.ext_iff, map_map, Prod.map_comp_map, val_comp_cast, swaps_coe,
    a.invArray_get_toArray_get, Equiv.swaps_reverse, Perm.inv_apply_self]-/

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
