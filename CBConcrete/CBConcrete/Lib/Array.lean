import Mathlib.Algebra.Order.Ring.Nat

namespace Array

variable {α β γ : Type*} {k i : ℕ}

theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith f bs).size) : i < as.size := by
  rw [Array.size_eq_length_toList] at h ⊢
  rw [Array.toList_zipWith] at h
  exact List.lt_length_left_of_zipWith h

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith f bs).size) : i < bs.size := by
  rw [Array.size_eq_length_toList] at h ⊢
  rw [Array.toList_zipWith] at h
  exact List.lt_length_right_of_zipWith h

theorem lt_length_left_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < as.size := lt_length_left_of_zipWith h

theorem lt_length_right_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < bs.size := lt_length_right_of_zipWith h

theorem getElem_swapIfInBounds_of_ge_left {as : Array α} {i j k : ℕ} (h : as.size ≤ i)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq as.size_swapIfInBounds) := by
  unfold swapIfInBounds
  simp_rw [h.not_gt, dite_false]

theorem getElem_swapIfInBounds_of_ge_right {as : Array α} {i j k : ℕ} (h : as.size ≤ j)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq as.size_swapIfInBounds) := by
  unfold swapIfInBounds
  simp_rw [h.not_gt, dite_false, dite_eq_ite, ite_self]

@[simp]
theorem getElem_swapIfInBounds_left {as : Array α} {i j : ℕ} (hj : j < as.size)
    (hi : i < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[i] = as[j] := by
  simp_rw [size_swapIfInBounds] at hi
  unfold swapIfInBounds
  simp_rw [hi, hj, dite_true]
  exact getElem_swap_left

@[simp]
theorem getElem_swapIfInBounds_right {as : Array α} {i j : ℕ} (hi : i < as.size)
    (hj : j < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[j] = as[i] := by
  simp_rw [size_swapIfInBounds] at hj
  unfold swapIfInBounds
  simp_rw [hi, hj, dite_true]
  exact getElem_swap_right

theorem getElem_swapIfInBounds_of_ne_ne {as : Array α} {i j k : ℕ} (hi : k ≠ i) (hj : k ≠ j)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq as.size_swapIfInBounds) := by
  simp_rw [size_swapIfInBounds] at hk
  unfold swapIfInBounds
  split_ifs <;> try {rfl}
  exact Array.getElem_swap_of_ne _ hi hj

theorem getElem_swapIfInBounds {as : Array α} {i j k : ℕ} (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] =
    if h : i < as.size ∧ j < as.size then (as.swap i j)[k]'
      (hk.trans_eq ((as.size_swapIfInBounds).trans (as.size_swap).symm))
    else as[k]'(hk.trans_eq as.size_swapIfInBounds) := by
  unfold swapIfInBounds
  split
  · split <;> simp_all
  · simp_all

theorem eraseIdx_eq_take_append_drop_succ {as : Array α} (hi : i < as.size) :
    as.eraseIdx i = as.take i ++ as.extract (i + 1) as.size := by
  cases as with | mk l => _
  simp_rw [List.eraseIdx_toArray, List.take_toArray, List.size_toArray, List.extract_toArray,
    List.append_toArray, mk.injEq, List.take_of_length_le List.length_drop.le,
    List.eraseIdx_eq_take_drop_succ]

theorem getElem_eraseIdx_left {as : Array α} (hi : i < as.size) (hki : k < i) :
    (as.eraseIdx i)[k]'(hki.trans_le ((Nat.le_pred_of_lt hi).trans_eq
    (as.size_eraseIdx _ _).symm)) = as[k] := by
  simp_rw [getElem_eraseIdx, dif_pos hki]

theorem getElem_eraseIdx_right {as : Array α} (hi : i < as.size) (hki : i ≤ k)
    (hk : k < (as.eraseIdx i).size) :
    (as.eraseIdx i)[k] = as[k + 1]'
    (Nat.succ_lt_of_lt_pred (hk.trans_eq (as.size_eraseIdx _ _))) := by
  simp_rw [getElem_eraseIdx, dif_neg hki.not_gt]

@[simp] theorem getElem_eraseIdx_zero {as : Array α} (has : 0 < as.size)
    (hk : k < (as.eraseIdx 0).size) :
    (as.eraseIdx 0)[k] = as[k + 1]'
    (Nat.succ_lt_of_lt_pred (hk.trans_eq (as.size_eraseIdx _ _))) :=
  getElem_eraseIdx_right _ (zero_le _) _

end Array
