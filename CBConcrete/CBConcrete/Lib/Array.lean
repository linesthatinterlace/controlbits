import Mathlib.Algebra.Order.Ring.Nat

namespace Array

variable {α β γ : Type*} {k i : ℕ}

theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {xs : Array α} {bs : Array β}
    (h : i < (xs.zipWith f bs).size) : i < xs.size := by
  rw [Array.size_eq_length_toList] at h ⊢
  rw [Array.toList_zipWith] at h
  exact List.lt_length_left_of_zipWith h

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {xs : Array α} {bs : Array β}
    (h : i < (xs.zipWith f bs).size) : i < bs.size := by
  rw [Array.size_eq_length_toList] at h ⊢
  rw [Array.toList_zipWith] at h
  exact List.lt_length_right_of_zipWith h

theorem lt_length_left_of_zip {i : ℕ} {xs : Array α} {bs : Array β} (h : i < (xs.zip bs).size) :
    i < xs.size := lt_length_left_of_zipWith h

theorem lt_length_right_of_zip {i : ℕ} {xs : Array α} {bs : Array β} (h : i < (xs.zip bs).size) :
    i < bs.size := lt_length_right_of_zipWith h

theorem getElem_swapIfInBounds_of_ge_left {xs : Array α} {i j k : ℕ} (h : xs.size ≤ i)
    (hk : k < (xs.swapIfInBounds i j).size) :
    (xs.swapIfInBounds i j)[k] = xs[k]'(hk.trans_eq xs.size_swapIfInBounds) := by
  unfold swapIfInBounds
  simp_rw [h.not_gt, dite_false]

theorem getElem_swapIfInBounds_of_ge_right {xs : Array α} {i j k : ℕ} (h : xs.size ≤ j)
    (hk : k < (xs.swapIfInBounds i j).size) :
    (xs.swapIfInBounds i j)[k] = xs[k]'(hk.trans_eq xs.size_swapIfInBounds) := by
  unfold swapIfInBounds
  simp_rw [h.not_gt, dite_false, dite_eq_ite, ite_self]

theorem eraseIdx_eq_take_append_drop_succ {xs : Array α} (hi : i < xs.size) :
    xs.eraseIdx i = xs.take i ++ xs.extract (i + 1) xs.size := by
  cases xs with | mk l => _
  simp_rw [List.eraseIdx_toArray, List.take_toArray, List.size_toArray, List.extract_toArray,
    List.append_toArray, mk.injEq, List.take_of_length_le List.length_drop.le,
    List.eraseIdx_eq_take_drop_succ]

theorem getElem_eraseIdx_left {xs : Array α} (hi : i < xs.size) (hki : k < i) :
    (xs.eraseIdx i)[k]'(hki.trans_le ((Nat.le_pred_of_lt hi).trans_eq
    (xs.size_eraseIdx _ _).symm)) = xs[k] := by
  simp_rw [getElem_eraseIdx, dif_pos hki]

theorem getElem_eraseIdx_right {xs : Array α} (hi : i < xs.size) (hki : i ≤ k)
    (hk : k < (xs.eraseIdx i).size) :
    (xs.eraseIdx i)[k] = xs[k + 1]'
    (Nat.succ_lt_of_lt_pred (hk.trans_eq (xs.size_eraseIdx _ _))) := by
  simp_rw [getElem_eraseIdx, dif_neg hki.not_gt]

@[simp] theorem getElem_eraseIdx_zero {xs : Array α} (has : 0 < xs.size)
    (hk : k < (xs.eraseIdx 0).size) :
    (xs.eraseIdx 0)[k] = xs[k + 1]'
    (Nat.succ_lt_of_lt_pred (hk.trans_eq (xs.size_eraseIdx _ _))) :=
  getElem_eraseIdx_right _ (zero_le _) _

@[simp, grind =]
theorem swap_same {xs : Array α} {i : Nat} {hi} : xs.swap i i hi hi = xs := by grind

@[simp, grind =]
theorem swapIfInBounds_same {xs : Array α} {i : Nat} : xs.swapIfInBounds i i = xs := by grind

def bswap (xs : Array α) (b : Bool) (i j : Nat) (hi : i < xs.size := by get_elem_tactic)
    (hj : j < xs.size := by get_elem_tactic) : Array α := bif b then xs.swap i j else xs

@[grind =>] theorem size_bswap {xs : Array α} {b : Bool} {i j : Nat} {hi hj} :
    (xs.bswap b i j hi hj).size = xs.size := by grind [bswap]

@[grind =>] theorem getElem_bswap {xs : Array α} {b : Bool} {i j : Nat} {hi hj}
    (hk : k < (xs.bswap b i j hi hj).size) :
    (xs.bswap b i j hi hj)[k] = bif b then (xs.swap i j)[k]'(by grind) else xs[k]'(by grind) := by
  grind [bswap]

@[simp]
theorem bswap_true {xs : Array α} {i j : Nat} {hi hj} :
    xs.bswap true i j hi hj = xs.swap i j hi hj := by grind

@[simp]
theorem bswap_false {xs : Array α} {i j : Nat} {hi hj} :
    xs.bswap false i j hi hj = xs := by grind

def bswapImpl (xs : Array α) (b : Bool) (i j : Nat) (hi : i < xs.size := by get_elem_tactic)
    (hj : j < xs.size := by get_elem_tactic) : Array α :=
  let v₁ := bif b then xs[j] else xs[i]
  let v₂ := bif b then xs[i] else xs[j]
  let xs' := xs.set i v₁
  xs'.set j v₂ (Nat.lt_of_lt_of_eq hj (size_set _).symm)

@[csimp] theorem bswap_eq_bswapImpl : @bswap = @bswapImpl := by
  ext <;> grind [bswap, bswapImpl]

def bswapIfInBounds (xs : Array α) (b : Bool) (i j : @& Nat) : Array α :=
  bif b then xs.swapIfInBounds i j else xs

@[grind =] theorem size_bswapIfInBounds {xs : Array α} {b : Bool} {i j : Nat} :
    (xs.bswapIfInBounds b i j).size = xs.size := by grind [bswapIfInBounds]

@[grind =] theorem getElem_bswapIfInBounds {xs : Array α} {b : Bool} {i j : Nat}
    (hk : k < (xs.bswapIfInBounds b i j).size) :
    (xs.bswapIfInBounds b i j)[k] =
    bif b then (xs.swapIfInBounds i j)[k]'(by grind) else xs[k]'(by grind) := by
  grind [bswapIfInBounds]

@[simp]
theorem bswapIfInBounds_true {xs : Array α} {i j : Nat} :
    xs.bswapIfInBounds true i j  = xs.swapIfInBounds i j := by grind

@[simp]
theorem bswapIfInBounds_false {xs : Array α} {i j : Nat} :
    xs.bswapIfInBounds false i j = xs := by grind

def bswapIfInBoundsImpl (xs : Array α) (b : Bool) (i j : @& Nat) : Array α :=
  if hi : i < xs.size then if hj : j < xs.size then xs.bswap b i j else xs else xs

@[csimp] theorem bswapIfInBounds_eq_bswapIfInBoundsImpl :
    @bswapIfInBounds = @bswapIfInBoundsImpl := by
  ext <;> grind [bswapIfInBounds, bswapIfInBoundsImpl]

theorem eq_push_pop_back_of_size_ne_zero {xs : Array α} (h : xs.size ≠ 0) :
    xs = xs.pop.push (xs.back <| Nat.pos_of_ne_zero h) := by grind

theorem back_push {v : Array α} {a : α} : (v.push a).back = a := by grind

@[elab_as_elim, induction_eliminator, grind =]
def induction {C : Array α → Sort*} (empty : C #[])
    (push : ∀ (xs : Array α) (x : α), C xs → C (xs.push x))
    (xs : Array α) : C xs :=
  match hxs : xs.size with
  | 0 => eq_empty_of_size_eq_zero hxs ▸ empty
  | n + 1 => eq_push_pop_back_of_size_ne_zero
    (hxs ▸ Nat.succ_ne_zero _) ▸ push _ _ (induction empty push xs.pop)
  termination_by xs.size

@[simp]
theorem induction_empty {C : Array α → Sort*} (empty : C #[])
    (push : ∀ (xs : Array α) (x : α), C xs → C (xs.push x)) :
  induction empty push #[] = empty := by grind

@[simp]
theorem induction_push {C : Array α → Sort*} (empty : C #[])
    (push : ∀ (xs : Array α) (x : α), C xs → C (xs.push x)) (xs : Array α) (x : α) :
    induction empty push (xs.push x) = push xs x (induction empty push xs) := by
  grind [pop_push]

@[elab_as_elim, cases_eliminator, grind =]
def cases {C : Array α → Sort*}
    (empty : C #[])
    (push : ∀ (xs : Array α) (x : α), C (xs.push x)) (v : Array α) : C v :=
  v.induction empty (fun _ _  _ => push _ _)

@[simp]
theorem cases_empty {C : Array α → Sort*} (empty : C #[])
    (push : ∀ (xs : Array α) (x : α), C (xs.push x)) :
  cases empty push #[] = empty := by grind

@[simp]
theorem cases_push {C : Array α → Sort*} (empty : C #[])
    (push : ∀ (xs : Array α) (x : α), C (xs.push x)) (xs : Array α) (x : α) :
    cases empty push (xs.push x) = push xs x := by grind [pop_push]

theorem exists_getElem_push (p : α → Prop) {c : Array α} (b : α) {k : Nat} :
    (∃ (hk : k < (c.push b).size), p (c.push b)[k]) ↔
    k = c.size ∧ p b ∨ ∃ (hk : k < c.size), p c[k] := by grind

theorem forall_getElem_push (p : α → Prop) {c : Array α} (b : α) {k : Nat} :
    (∀ (hk : k < (c.push b).size), p (c.push b)[k]) ↔
    (k = c.size → p b) ∧ ∀ (hk : k < c.size), p c[k] := by grind

end Array
