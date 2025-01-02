import Mathlib.Algebra.Order.Ring.Nat

namespace Array

variable {α β γ : Type*} {k i : ℕ}

@[simp] theorem size_flatten (ass : Array (Array α)) :
    ass.flatten.size = (List.map size ass.toList).sum := by
  rw [size_eq_length_toList, toList_flatten, List.length_flatten, List.map_map,
    Function.comp_def]

@[simp] theorem size_finRange {n : ℕ} : (Array.finRange n).size = n := size_ofFn _
@[simp] theorem getElem_finRange {n i : ℕ} {hi : i < (Array.finRange n).size} :
    (Array.finRange n)[i] = ⟨i, hi.trans_eq size_finRange⟩ := getElem_ofFn _ _ _


theorem lt_length_left_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith bs f).size) : i < as.size := by
  rw [Array.size_eq_length_toList] at h ⊢
  rw [Array.toList_zipWith] at h
  exact List.lt_length_left_of_zipWith h

theorem lt_length_right_of_zipWith {f : α → β → γ} {i : ℕ} {as : Array α} {bs : Array β}
    (h : i < (as.zipWith bs f).size) : i < bs.size := by
  rw [Array.size_eq_length_toList] at h ⊢
  rw [Array.toList_zipWith] at h
  exact List.lt_length_right_of_zipWith h

theorem lt_length_left_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < as.size := lt_length_left_of_zipWith h

theorem lt_length_right_of_zip {i : ℕ} {as : Array α} {bs : Array β} (h : i < (as.zip bs).size) :
    i < bs.size := lt_length_right_of_zipWith h

@[simp]
theorem getElem_zipWith {as : Array α} {bs : Array β} {f : α → β → γ} {i : ℕ}
    (h : i < (as.zipWith bs f).size) : (as.zipWith bs f)[i] =
    f (as[i]'(lt_length_left_of_zipWith h)) (bs[i]'(lt_length_right_of_zipWith h)) := by
  simp_rw [getElem_eq_getElem_toList, Array.toList_zipWith, List.getElem_zipWith]

@[simp]
theorem getElem_zip {as : Array α} {bs : Array β} {i : ℕ}
    (h : i < (as.zip bs).size) : (as.zip bs)[i] =
    (as[i]'(lt_length_left_of_zip h), bs[i]'(lt_length_right_of_zip h)) := by
  simp_rw [getElem_eq_getElem_toList, Array.toList_zip, List.getElem_zip]

@[simp]
theorem getElem_zipWithIndex {as : Array α} {i : ℕ}
    (h : i < (as.zipWithIndex).size) :
    (as.zipWithIndex)[i] = (as[i]'(h.trans_eq as.size_zipWithIndex), i) := by
  unfold zipWithIndex
  simp_rw [Array.getElem_mapIdx]

theorem getElem_swapIfInBounds_of_ge_left {as : Array α} {i j k : ℕ} (h : as.size ≤ i)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq <| as.size_swapIfInBounds _ _) := by
  unfold swapIfInBounds
  simp_rw [h.not_lt, dite_false]

theorem getElem_swapIfInBounds_of_ge_right {as : Array α} {i j k : ℕ} (h : as.size ≤ j)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq <| as.size_swapIfInBounds _ _) := by
  unfold swapIfInBounds
  simp_rw [h.not_lt, dite_false, dite_eq_ite, ite_self]

@[simp]
theorem getElem_swapIfInBounds_left {as : Array α} {i j : ℕ} (hj : j < as.size)
    (hi : i < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[i] = as[j] := by
  simp_rw [size_swapIfInBounds] at hi
  unfold swapIfInBounds
  simp_rw [hi, hj, dite_true]
  exact getElem_swap_left _

@[simp]
theorem getElem_swapIfInBounds_right {as : Array α} {i j : ℕ} (hi : i < as.size)
    (hj : j < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[j] = as[i] := by
  simp_rw [size_swapIfInBounds] at hj
  unfold swapIfInBounds
  simp_rw [hi, hj, dite_true]
  exact getElem_swap_right _

theorem getElem_swapIfInBounds_of_ne_ne {as : Array α} {i j k : ℕ} (hi : k ≠ i) (hj : k ≠ j)
    (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] = as[k]'(hk.trans_eq <| as.size_swapIfInBounds _ _) := by
  simp_rw [size_swapIfInBounds] at hk
  unfold swapIfInBounds
  split_ifs <;> try {rfl}
  exact Array.getElem_swap_of_ne _ _ hi hj

theorem getElem_swapIfInBounds {as : Array α} {i j k : ℕ} (hk : k < (as.swapIfInBounds i j).size) :
    (as.swapIfInBounds i j)[k] =
    if h : k = i ∧ j < as.size then as[j]'h.2 else if h₂ : k = j ∧ i < as.size then as[i]'h₂.2
    else as[k]'(hk.trans_eq <| as.size_swapIfInBounds _ _) := by
  rcases eq_or_ne k i with rfl | hi
  · simp_rw [true_and]
    rcases lt_or_le j as.size with hj | hj
    · simp_rw [hj, dite_true, getElem_swapIfInBounds_left hj]
    · simp_rw [hj.not_lt, dite_false, getElem_swapIfInBounds_of_ge_right hj]
      split_ifs <;> rfl
  · rcases eq_or_ne k j with rfl | hj
    · simp_rw [hi, false_and, dite_false, true_and]
      rcases lt_or_le i as.size with hi | hi
      · simp_rw [hi, dite_true, getElem_swapIfInBounds_right hi]
      · simp_rw [hi.not_lt, dite_false, getElem_swapIfInBounds_of_ge_left hi]
    · simp_rw [hi, hj, false_and, dite_false, getElem_swapIfInBounds_of_ne_ne hi hj]

@[simp] theorem getElem_reverse {as : Array α} (hk : k < as.reverse.size) :
    as.reverse[k] = as[as.size - 1 - k]'
    (Nat.sub_one_sub_lt_of_lt (hk.trans_eq as.size_reverse)) := by
  simp_rw [← Array.getElem_toList, Array.toList_reverse, List.getElem_reverse]

theorem eraseIdx_eq_take_append_drop_succ {as : Array α} (hi : i < as.size) :
    as.eraseIdx i = as.take i ++ as.extract (i + 1) as.size := by
  cases as with | mk l => _
  simp_rw [List.eraseIdx_toArray, List.take_toArray, size_toArray, List.extract_toArray,
    List.append_toArray, mk.injEq, List.take_of_length_le (List.length_drop _ _).le,
    List.eraseIdx_eq_take_drop_succ]

theorem getElem_eraseIdx {as : Array α} (hi : i < as.size) (hk : k < (as.eraseIdx i).size) :
    (as.eraseIdx i)[k] = if h : k < i then as[k] else as[k + 1]'
    (Nat.succ_lt_of_lt_pred (hk.trans_eq (as.size_eraseIdx _ _))) := by
  simp_rw [eraseIdx_eq_take_append_drop_succ, getElem_append, size_take,
    min_eq_left_of_lt hi, getElem_take, getElem_extract, add_comm (i + 1), ← add_assoc]
  rcases lt_or_le k i with hki | hki
  · simp_rw [dif_pos hki]
  · simp_rw [dif_neg hki.not_lt, Nat.sub_add_cancel hki]

theorem getElem_eraseIdx_left {as : Array α} (hi : i < as.size) (hki : k < i) :
    (as.eraseIdx i)[k]'(hki.trans_le ((Nat.le_pred_of_lt hi).trans_eq
    (as.size_eraseIdx _ _).symm)) = as[k] := by
  simp_rw [getElem_eraseIdx, dif_pos hki]

theorem getElem_eraseIdx_right {as : Array α} (hi : i < as.size) (hki : i ≤ k)
    (hk : k < (as.eraseIdx i).size) :
    (as.eraseIdx i)[k] = as[k + 1]'
    (Nat.succ_lt_of_lt_pred (hk.trans_eq (as.size_eraseIdx _ _))) := by
  simp_rw [getElem_eraseIdx, dif_neg hki.not_lt]

@[simp] theorem getElem_eraseIdx_zero {as : Array α} (has : 0 < as.size)
    (hk : k < (as.eraseIdx 0).size) :
    (as.eraseIdx 0)[k] = as[k + 1]'
    (Nat.succ_lt_of_lt_pred (hk.trans_eq (as.size_eraseIdx _ _))) :=
  getElem_eraseIdx_right _ (zero_le _) _

end Array
