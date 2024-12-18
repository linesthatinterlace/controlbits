import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.GroupAction.Period

universe u

namespace Nat

@[simp] theorem fold_succ_zero {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    fold (n + 1) f init = (fold n (fun i h => f (i + 1) (by omega)) (f 0 (by omega) init)) := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [fold_succ, fold_zero]
  · rw [fold_succ, IH, fold_succ]

@[simp] theorem foldRev_succ_zero {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    foldRev (n + 1) f init = f 0 (by omega)
    (foldRev n (fun i hi => f (i + 1) (by omega)) init) := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_succ, foldRev_zero]
  · rw [foldRev_succ, IH, foldRev_succ]

theorem foldRev_eq_fold_of_apply_eq_apply_pred_sub' {α : Type u} (n : Nat)
    (f g : (i : Nat) → i < n → α → α)
    (hfg : ∀ i (hi : i < n) , f i hi = g ((n - i) - 1) (by omega)) (init : α) :
    foldRev n f init = fold n g init := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_zero, fold_zero]
  · simp_rw [foldRev_succ_zero, fold_succ, hfg 0, Nat.sub_zero, Nat.add_one_sub_one]
    exact congrArg _ (IH _ _ (fun i hi => (hfg (i + 1) (Nat.succ_lt_succ hi)).trans
      (funext (fun _ => by simp_rw [Nat.add_sub_add_right]))) _)

theorem foldRev_eq_fold_of_apply_eq_apply_pred_sub {α : Type u} (n : Nat)
    (f g : (i : Nat) → i < n → α → α)
    (hfg : ∀ i j (hi : i < n) (hj : j < n), i + j = n - 1 → f i hi = g j hj) (init : α) :
    foldRev n f init = fold n g init := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_zero, fold_zero]
  · rw [foldRev_succ_zero, fold_succ, hfg 0 n (by omega) (by omega) (by omega)]
    congr
    refine IH _ _ (fun x y hx hy hxy => hfg _ _ _ _ ?_) _
    omega

theorem foldRev_eq_fold {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n → α → α) (init : α) :
    foldRev n f init = fold n (fun i (hi : i < n) => f ((n - 1) - i) (by omega)) init := by
  refine foldRev_eq_fold_of_apply_eq_apply_pred_sub _ _ _ (fun i j hi hj hij => ?_) _
  conv =>
    lhs
    congr
    rw [Nat.eq_sub_of_add_eq hij]

theorem fold_eq_foldRev {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n → α → α) (init : α) :
    fold n f init = foldRev n (fun i (hi : i < n) => f ((n - 1) - i) (by omega)) init := by
  refine (foldRev_eq_fold_of_apply_eq_apply_pred_sub _ _ _ (fun i j hi hj hij => ?_) _).symm
  conv =>
    rhs
    congr
    rw [Nat.eq_sub_of_add_eq' hij]

end Nat

namespace Equiv

variable {α : Type*} [DecidableEq α]

theorem coe_swap {n : ℕ} {i j k : Fin n} : swap (i : ℕ) (j : ℕ) (k : ℕ) = swap i j k :=
  Fin.val_injective.swap_apply _ _ _

theorem swap_smul {R : Type*} [Group R] [MulAction R α] {i j k : α} {r : R} :
    swap (r • i) (r • j) (r • k) = r • swap i j k :=
  (MulAction.injective r).swap_apply _ _ _

theorem swap_prop (p : α → Prop) {i j k : α} (hk : p k) (hi : p i) (hj : p j) :
    p (swap i j k) := by
  simp_rw [swap_apply_def, apply_ite p, hi, hj, hk, ite_self]

end Equiv

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

namespace Vector

variable {α β γ : Type*} {n m k i j : ℕ}

@[simp]
theorem getD_of_lt (a : Vector α n) (x : α) (i : ℕ) (h : i < n) : a[i]?.getD x = a[i] := by
  simp_rw [getElem?_pos a i h, Option.getD_some]

@[simp]
theorem getD_of_ge (a : Vector α n) (x : α) (i : ℕ) (h : n ≤ i) : a[i]?.getD x = x := by
  rw [getElem?_neg a i h.not_lt, Option.getD_none]

@[simp] theorem getElem_map {n i : ℕ} (hi : i < n) (f : α → β) (v : Vector α n) :
    (v.map f)[i] = f v[i] := by
  cases v ; simp_rw [map_mk, getElem_mk, Array.getElem_map]

@[simp] theorem getElem_range {n i : ℕ} (hi : i < n) : (range n)[i] = i := by
  unfold range
  simp_rw [getElem_mk, Array.getElem_range]

@[simp] theorem getElem_cast {n m i : ℕ} (hnm : n = m) (v : Vector α n) (hi : i < m)  :
  (v.cast hnm)[i] = v[i] := rfl

@[simp] theorem getElem_range_lt {n i : ℕ} (hi : i < n) : (range n)[i] < n := getElem_range _ ▸ hi

@[simp]
theorem getElem_zipWith  {n i : ℕ} (hi : i < n) {as : Vector α n} {bs : Vector β n}
    {f : α → β → γ} : (as.zipWith bs f)[i] = f (as[i]) (bs[i]) := by
  cases as ; cases bs ; simp_rw [mk_zipWith_mk, getElem_mk, Array.getElem_zipWith]

theorem getElem_swap {α : Type u_1} (a : Vector α n) (i j : ℕ) (hi : i < n)
    {hj : j < n} (k : ℕ) (hk : k < n) :
    (a.swap i j hi hj)[k] = if k = i then a[j] else if k = j then a[i] else a[k] := by
  cases a
  simp_rw [swap_mk, getElem_mk, Array.getElem_swap]

theorem getElem_swap_eq_getElem_swap_apply (as : Vector α n) (i j : ℕ) (hi : i < n)
    (hj : j < n)
    (k : ℕ) (hk : k < n) :
    (as.swap i j hi hj)[k] =
    as[Equiv.swap i j k]'(Equiv.swap_prop (· < n) hk hi hj) := by
  simp_rw [getElem_swap, Equiv.swap_apply_def]
  split_ifs <;> rfl

theorem getElem_swapIfInBounds {as : Vector α n} {i j k : ℕ} (hk : k < n) :
    (as.swapIfInBounds i j)[k] =
    if h : i < n ∧ j < n then (as.swap i j)[k] else as[k] := by
  unfold swapIfInBounds
  simp_rw [getElem_mk, Array.getElem_swapIfInBounds, Vector.size_toArray, getElem_swap,
    Vector.getElem_toArray]
  rcases eq_or_ne k i with rfl | hi
  · simp_rw [hk, true_and, and_true, ite_true]
    exact dite_congr rfl (fun _ => rfl) (fun _ => by simp_rw [dite_eq_right_iff, implies_true])
  · simp_rw [hi, false_and, dite_false, ite_false]
    rcases eq_or_ne k j with rfl | hj
    · simp_rw [ite_true, true_and, hk, and_true]
    · simp_rw [hj, false_and, dite_false, ite_false, dite_eq_ite, ite_self]

@[simp] theorem getElem_reverse {as : Vector α n} (hk : k < n) : as.reverse[k] = as[n - 1 - k] := by
  cases as with | mk as H => _
  simp_rw [reverse_mk, getElem_mk, Array.getElem_reverse, H]

protected def finRange (n : ℕ) : Vector (Fin n) n := ⟨Array.finRange n, Array.size_finRange⟩

@[simp] theorem getElem_finRange (hi : i < n) : (Vector.finRange n)[i] = ⟨i, hi⟩ := by
  unfold Vector.finRange
  simp_rw [getElem_mk, Array.getElem_finRange]

@[simp] theorem getElem_mkVector {a : α} (hi : i < n) : (Vector.mkVector n a)[i] = a := by
  unfold Vector.mkVector
  simp_rw [getElem_mk, Array.getElem_mkArray]

def mapIdx (f : Fin n → α → β) (v : Vector α n) : Vector β n :=
  ⟨v.toArray.mapFinIdx fun i a => f (i.cast v.size_toArray) a,
  (Array.size_mapFinIdx _ _).trans v.size_toArray⟩

@[simp] theorem getElem_mapIdx (f : Fin n → α → β) (v : Vector α n) {i : ℕ} (hi : i < n) :
    (v.mapIdx f)[i] = f ⟨i, hi⟩ v[i] := by
  unfold mapIdx
  simp_rw [getElem_mk, Array.getElem_mapFinIdx, Fin.cast_mk, getElem_toArray]

structure Mem (v : Vector α n) (a : α) : Prop where
  val : a ∈ v.toArray

instance : Membership α (Vector α n) where
  mem := Mem

theorem mem_def {a : α} (v : Vector α n) : a ∈ v ↔ a ∈ v.toArray :=
  ⟨fun | .mk h => h, Vector.Mem.mk⟩

@[simp] theorem getElem_mem (v : Vector α n) {i : ℕ} (h : i < n) : v[i] ∈ v := by
  rw [Vector.mem_def, ← getElem_toArray]
  exact Array.getElem_mem (h.trans_eq v.size_toArray.symm)

theorem getElem_of_mem {a} (v : Vector α n) : a ∈ v → ∃ (i : Nat) (h : i < n), v[i]'h = a := by
  simp_rw [mem_def, Array.mem_iff_getElem, v.size_toArray, getElem_toArray, imp_self]

theorem getElem?_of_mem {a} (v : Vector α n) (h : a ∈ v) : ∃ i : Nat, v[i]? = some a := by
  simp_rw [getElem?_def]
  rcases (v.getElem_of_mem h) with ⟨i, hi, hiv⟩
  exact ⟨i, hiv ▸ dif_pos _⟩

theorem mem_of_getElem? (v : Vector α n) {i : Nat} {a : α} : v[i]? = some a → a ∈ v := by
  simp_rw [getElem?_def, Option.dite_none_right_eq_some, Option.some.injEq, forall_exists_index]
  exact fun _ h => h ▸ v.getElem_mem _

theorem mem_iff_getElem {a} (v : Vector α n) : a ∈ v ↔ ∃ (i : Nat) (h : i < n), v[i]'h = a :=
  ⟨v.getElem_of_mem, fun ⟨_, _, e⟩ => e ▸ getElem_mem ..⟩

theorem mem_iff_getElem? {a} (v : Vector α n) : a ∈ v ↔ ∃ i : Nat, v[i]? = some a := by
  simp_rw [mem_iff_getElem, getElem?_def, Option.dite_none_right_eq_some, Option.some.injEq]

@[simp] theorem getElem_take (a : Vector α n) (m : Nat) (hi : i < min m n) :
    (a.take m)[i] = a[i] := by
  cases a
  simp_rw [take_mk, getElem_mk, Array.getElem_take]

@[simp] theorem getElem_drop (a : Vector α n) (m : Nat) (hi : i < n - m) :
    (a.drop m)[i] = a[m + i] := by
  cases a
  simp_rw [drop_mk, getElem_mk, Array.getElem_extract]

theorem getElem_append (a : Vector α n) (b : Vector α m) (i : Nat) (hi : i < n + m) :
    (a ++ b)[i] = if h : i < n then a[i] else b[i - n] := by
  rcases a with ⟨a, rfl⟩
  rcases b with ⟨b, rfl⟩
  simp [Array.getElem_append, hi]

theorem getElem_append_left {a : Vector α n} {b : Vector α m} {i : Nat} (hi : i < n) :
    (a ++ b)[i] = a[i] := by simp [getElem_append, hi]

theorem getElem_append_right {a : Vector α n} {b : Vector α m} {i : Nat} (hi : n ≤ i)
    (h : i < n + m) : (a ++ b)[i] = b[i - n] := by
  rw [getElem_append, dif_neg (by omega)]

theorem getElem_eraseIdx (v : Vector α n) (hi : i < n) (hk : k < n - 1) :
    (v.eraseIdx i)[k] = if h : k < i then v[k] else v[k + 1]'(Nat.succ_lt_of_lt_pred hk) := by
  unfold eraseIdx
  simp_rw [getElem_mk, Array.getElem_eraseIdx, getElem_toArray]

theorem getElem_eraseIdx_left (v : Vector α n) (hi : i < n) (hki : k < i) :
    (v.eraseIdx i)[k] = v[k] := by
  simp_rw [getElem_eraseIdx, dif_pos hki]

theorem getElem_eraseIdx_right (v : Vector α n) (hki : i ≤ k) (hk : k < n - 1) :
    (v.eraseIdx i)[k] = v[k + 1] := by
  simp_rw [getElem_eraseIdx, dif_neg hki.not_lt]

@[simp] theorem getElem_eraseIdx_zero (v : Vector α n) (hk : k < n - 1) :
    (v.eraseIdx 0)[k] = v[k + 1] := getElem_eraseIdx_right _ (zero_le _) _

@[simp] theorem getElem_tail (v : Vector α n) (hi : i < n - 1) : (v.tail)[i] = v[i + 1] := by
  cases n
  · simp_rw [Nat.zero_sub, not_lt_zero'] at hi
  · unfold tail
    simp_rw [Nat.zero_lt_succ, dite_true, getElem_eraseIdx_zero]

@[simp] theorem getElem_tail' (v : Vector α (n + 1)) (hi : i < (n + 1) - 1) :
    @getElem (Vector α n) Nat α (fun _ i => i < n) instGetElemNatLt v.tail i hi = v[i + 1] :=
  getElem_tail _ _

@[simp] theorem getElem_singleton (a : α) (hi : i < 1) : (singleton a)[i] = a := by
  unfold singleton
  simp_rw [getElem_mk, List.getElem_toArray, List.getElem_singleton]

theorem cast_singleton_head_append_tail [NeZero n] (v : Vector α n) :
    (singleton (v.head) ++ v.tail).cast
    (Nat.add_comm _ _ ▸ Nat.sub_add_cancel NeZero.one_le) = v := by
  ext
  simp_rw [getElem_cast, getElem_append, getElem_singleton, getElem_tail]
  split_ifs with hi
  · simp_rw [Nat.lt_one_iff] at hi
    simp_rw [hi]
    rfl
  · simp_rw [Nat.sub_add_cancel (le_of_not_lt hi)]

@[simp] theorem back_succ (v : Vector α (n + 1)) : v.back = v[n] := by
  cases v with | mk as has => _
  unfold back back! Array.back! Array.get! Array.getD
  simp_rw [has, add_tsub_cancel_right, lt_add_iff_pos_right, zero_lt_one, dite_true,
    Array.get_eq_getElem, getElem_mk]

def foldl (f : (i : ℕ) → i < n → β → α → β) (init : β) (v : Vector α n) : β :=
  n.fold (fun i hi => (f i hi · v[i])) init

@[simp] theorem foldl_zero (f : (i : ℕ) → i < 0 → β → α → β) (init : β) (v : Vector α 0) :
    v.foldl f init = init := Nat.fold_zero _ _

theorem foldl_succ (f : (i : ℕ) → i < n + 1 → β → α → β) (init : β) (v : Vector α (n + 1)) :
    v.foldl f init = f n (by omega)
    (v.pop.foldl (fun i hi => f i (by omega)) init) v[n] := by
  unfold foldl
  simp_rw [Nat.fold_succ, Nat.add_one_sub_one, getElem_pop']

theorem foldl_succ_last (f : (i : ℕ) → i < n + 1 → β → α → β) (init : β) (v : Vector α (n + 1)) :
    v.foldl f init = v.tail.foldl (fun i hi => f (i + 1) (by omega))
    (f 0 (by omega) init v[0]) := by
  unfold foldl
  simp_rw [Nat.fold_succ_zero, Vector.getElem_tail, Nat.add_one_sub_one]

def foldr (f : (i : ℕ) → i < n → α → β → β) (init : β) (v : Vector α n) : β :=
  n.foldRev (fun i hi => f i hi v[i]) init

@[simp] theorem foldr_zero (f : (i : ℕ) → i < 0 → α → β → β) (init : β) (v : Vector α 0) :
    v.foldr f init = init := Nat.foldRev_zero _ _

theorem foldr_succ (f : (i : ℕ) → i < n + 1 → α → β → β) (init : β) (v : Vector α (n + 1)) :
    v.foldr f init = v.pop.foldr (fun i hi => f i (by omega)) (f n (by omega) v[n] init) := by
  unfold foldr
  simp_rw [Nat.foldRev_succ, Vector.getElem_pop, Nat.add_one_sub_one]

theorem foldr_succ_last (f : (i : ℕ) → i < n + 1 → α → β → β) (init : β) (v : Vector α (n + 1)) :
    v.foldr f init = f 0 (by omega) v[0]
    (v.tail.foldr (fun i hi => f (i + 1) (by omega)) init) := by
  unfold foldr
  simp_rw [Nat.foldRev_succ_zero, Vector.getElem_tail, Nat.add_one_sub_one]

def flatten {m : ℕ} (a : Vector (Vector α n) m) : Vector α (n * m) := match m with
  | 0 => #v[]
  | (_ + 1) => a.pop.flatten ++ a.back

theorem flatten_zero {a : Vector (Vector α n) 0} :
    a.flatten = #v[] := rfl

theorem flatten_succ {a : Vector (Vector α n) (m + 1)} :
    a.flatten = a.pop.flatten ++ a.back := rfl

@[simp] theorem getElem_flatten {a : Vector (Vector α n) m} (h : i < n * m) :
    (a.flatten)[i] = (a[i/n]'(Nat.div_lt_of_lt_mul h))[i % n]'
    (Nat.mod_lt _ (Nat.zero_lt_of_ne_zero (Nat.not_eq_zero_of_lt
    ((Nat.div_lt_of_lt_mul (h.trans_eq (mul_comm _ _))))))) := by
  simp_rw [Nat.mod_eq_sub]
  induction m with | zero => _ | succ m IH => _
  · simp_rw [mul_zero, not_lt_zero'] at h
  · simp_rw [flatten_succ, back_succ, Nat.add_one_sub_one]
    rcases lt_or_le i (n * m) with hi | hi
    · exact (getElem_append_left hi).trans (getElem_pop' _ _ _ ▸ IH _)
    · simp_rw [Nat.div_eq_of_lt_le (hi.trans_eq' (mul_comm _ _))
        (h.trans_eq (mul_comm n (m + 1)))]
      exact (getElem_append_right hi _)

def toChunks {m : ℕ} (v : Vector α (n * m)) : Vector (Vector α n) m := match m with
  | 0 => #v[]
  | (m + 1) => (toChunks ((v.take (n * m)).cast
      (min_eq_left (n.mul_succ m ▸ Nat.le_add_right _ _))) ).push
      ((v.drop (n * m)).cast ((n.mul_succ m).symm ▸
        add_comm (n * m) _ ▸ Nat.add_sub_cancel _ _))

theorem toChunks_zero (v : Vector α 0) : toChunks v (n := n) = #v[] := rfl

theorem toChunks_succ (v : Vector α (n * (m + 1))) :
    toChunks v = (toChunks ((v.take (n * m)).cast
      (min_eq_left (n.mul_succ m ▸ Nat.le_add_right _ _))) ).push
      ((v.drop (n * m)).cast ((n.mul_succ m).symm ▸
        add_comm (n * m) _ ▸ Nat.add_sub_cancel _ _)) := rfl

@[simp] theorem getElem_getElem_toChunks (v : Vector α (n * m)) (hi : i < m) (hj : j < n) :
  (v.toChunks)[i][j] = v[n*i + j]'
    (mul_comm m n ▸ Nat.lt_mul_of_div_lt (Nat.mul_add_div
    (Nat.zero_lt_of_ne_zero (Nat.not_eq_zero_of_lt hj)) _ _ ▸
    Nat.div_eq_of_lt hj ▸ Nat.add_zero _ ▸ hi)
    (Nat.zero_lt_of_ne_zero (Nat.not_eq_zero_of_lt hj))) := by
  induction m generalizing i with | zero => _ | succ m IH => _
  · simp_rw [not_lt_zero'] at hi
  · simp_rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at hi
    simp_rw [toChunks_succ]
    rcases hi with hi | hi
    · simp_rw [getElem_push_lt hi, IH, getElem_cast, getElem_take]
    · simp_rw [hi, getElem_push_last, getElem_cast, getElem_drop]

@[simp] theorem toChunks_flatten (v : Vector (Vector α n) m) : v.flatten.toChunks = v := by
  ext i _ j hj
  simp_rw [getElem_getElem_toChunks, getElem_flatten,
    Nat.mul_add_div (Nat.zero_lt_of_ne_zero (Nat.not_eq_zero_of_lt hj)), Nat.mul_add_mod,
    Nat.div_eq_of_lt hj, add_zero, Nat.mod_eq_of_lt hj]

@[simp] theorem flatten_toChunks (v : Vector α (n * m)) : v.toChunks.flatten = v := by
  ext i hi
  simp_rw [getElem_flatten, getElem_getElem_toChunks, Nat.div_add_mod]

end Vector

/--
A `PermOf n` is a permutation on `n` elements represented by two vectors, which we can
think of as an array of values and a corresponding array of indexes which are inverse to
one another. (One can flip the interpretation of indexes and values, and this is essentially
the inversion operation.)
It is designed to be a more performant version of `Equiv.Perm`.
-/
structure PermOf (n : ℕ) where
  /--
  Gives the `PermOf` as an vector of size `n`.
  -/
  protected fwdVector : Vector ℕ n
  /--
  Gives the inverse of the `PermOf` as a vector of size `n`.
  -/
  protected bwdVector : Vector ℕ n
  getElem_fwdVector_lt :
    ∀ {i : ℕ} (hi : i < n), fwdVector[i] < n := by decide
  getElem_bwdVector_getElem_fwdVector : ∀ {i : ℕ} (hi : i < n),
      bwdVector[fwdVector[i]]'(getElem_fwdVector_lt hi) = i := by decide
  deriving DecidableEq

namespace PermOf

open Function Equiv

variable {n : ℕ}

instance : Repr (PermOf n) where
  reprPrec a _ :=
  if n = 0 then
    "#v[]" else
    Std.Format.bracketFill
    "#v[" (Std.Format.joinSep (a.fwdVector.toList) ("," ++ Std.Format.line)) "]"

instance : One (PermOf n) where
  one := PermOf.mk (Vector.range n) (Vector.range n)
    (fun _ => Vector.getElem_range_lt _) (fun _ => by simp_rw [Vector.getElem_range])

instance : Inhabited (PermOf n) := ⟨1⟩

@[simp]
theorem default_eq : (default : PermOf n) = 1 := rfl

instance : Mul (PermOf n) where
  mul a b := {
    fwdVector := b.fwdVector.map (fun i => a.fwdVector[i]?.getD i)
    bwdVector := a.bwdVector.map (fun i => b.bwdVector[i]?.getD i)
    getElem_fwdVector_lt := fun {i} hi => by
      simp_rw [Vector.getElem_map,
        getElem?_pos a.fwdVector (b.fwdVector[i]) (b.getElem_fwdVector_lt hi),
        Option.getD_some, a.getElem_fwdVector_lt]
    getElem_bwdVector_getElem_fwdVector := fun {i} hi => by
      simp_rw [Vector.getElem_map,
        getElem?_pos a.fwdVector (b.fwdVector[i]) (b.getElem_fwdVector_lt hi),
        Option.getD_some, a.getElem_bwdVector_getElem_fwdVector,
        getElem?_pos b.bwdVector (b.fwdVector[i]) (b.getElem_fwdVector_lt hi),
        Option.getD_some, b.getElem_bwdVector_getElem_fwdVector]}

section GetElemVectorBijective

theorem getElem_fwdVector_injective (a : PermOf n) :
  ∀ {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n), a.fwdVector[i] = a.fwdVector[j] → i = j :=
  fun hi _ hj hij => (a.getElem_bwdVector_getElem_fwdVector hi).symm.trans
    (Eq.trans (by simp_rw [hij]) (a.getElem_bwdVector_getElem_fwdVector hj))

theorem fwdVector_toList_Nodup (a : PermOf n) : a.fwdVector.toList.Nodup := by
  rw [List.nodup_iff_injective_get]
  unfold Injective
  simp_rw [Fin.ext_iff, Fin.forall_iff, Array.length_toList, Vector.size_toArray,
    List.get_eq_getElem, Array.getElem_toList, Vector.getElem_toArray]
  exact fun _ hi _ hj => a.getElem_fwdVector_injective hi hj

theorem getElem_fwdVector_surjective (a : PermOf n) :
    ∀ {i : ℕ}, i < n → ∃ (j : ℕ), ∃ (hj : j < n), a.fwdVector[j] = i := by
  have H : Surjective (fun (i : Fin n) => Fin.mk a.fwdVector[i.1] (a.getElem_fwdVector_lt i.2)) :=
    Injective.surjective_of_fintype (Equiv.refl (Fin n)) fun _ _ => by
    simp_rw [Fin.mk.injEq, Fin.ext_iff]
    exact a.getElem_fwdVector_injective _ _
  unfold Surjective at H
  simp_rw [Fin.ext_iff, Fin.forall_iff, Fin.exists_iff] at H
  exact H

theorem getElem_bwdVector_lt (a : PermOf n) {i : ℕ} (hi : i < n) : a.bwdVector[i] < n := by
  rcases a.getElem_fwdVector_surjective hi with ⟨j, hj, rfl⟩
  simp_rw [a.getElem_bwdVector_getElem_fwdVector, hj]

theorem getElem_fwdVector_getElem_bwdVector (a : PermOf n) {i : ℕ} (hi : i < n) :
    a.fwdVector[a.bwdVector[i]]'(a.getElem_bwdVector_lt hi) = i := by
  rcases a.getElem_fwdVector_surjective hi with ⟨j, hj, rfl⟩
  simp_rw [a.getElem_bwdVector_getElem_fwdVector]

theorem getElem_bwdVector_injective (a : PermOf n) :
  ∀ {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n), a.bwdVector[i] = a.bwdVector[j] → i = j :=
  fun hi _ hj hij => (a.getElem_fwdVector_getElem_bwdVector hi).symm.trans
    (Eq.trans (by simp_rw [hij]) (a.getElem_fwdVector_getElem_bwdVector hj))

theorem bwdVector_toList_Nodup (a : PermOf n) : a.bwdVector.toList.Nodup := by
  rw [List.nodup_iff_injective_get]
  unfold Injective
  simp_rw [Fin.ext_iff, Fin.forall_iff, Array.length_toList, Vector.size_toArray,
    List.get_eq_getElem, Array.getElem_toList, Vector.getElem_toArray]
  exact fun _ hi _ hj => a.getElem_bwdVector_injective hi hj

theorem getElem_bwdVector_surjective (a : PermOf n) :
    ∀ {i : ℕ}, i < n → ∃ (j : ℕ), ∃ (hj : j < n), a.bwdVector[j] = i := by
  have H : Surjective (fun (i : Fin n) => Fin.mk a.bwdVector[i.1] (a.getElem_bwdVector_lt i.2)) :=
    Injective.surjective_of_fintype (Equiv.refl (Fin n)) fun _ _ => by
    simp_rw [Fin.mk.injEq, Fin.ext_iff]
    exact a.getElem_bwdVector_injective _ _
  unfold Surjective at H
  simp_rw [Fin.ext_iff, Fin.forall_iff, Fin.exists_iff] at H
  exact H

end GetElemVectorBijective

protected def mk' (fwdVector : Vector ℕ n) (bwdVector : Vector ℕ n)
    (getElem_bwdVector_lt : ∀ {i : ℕ} (hi : i < n), bwdVector[i] < n)
    (getElem_fwdVector_getElem_bwdVector : ∀ {i : ℕ} (hi : i < n),
    fwdVector[bwdVector[i]]'(getElem_bwdVector_lt hi) = i) :
  PermOf n :=
  let A : PermOf n := ⟨bwdVector, fwdVector,
    getElem_bwdVector_lt, getElem_fwdVector_getElem_bwdVector⟩
  ⟨fwdVector, bwdVector,
    A.getElem_bwdVector_lt, A.getElem_fwdVector_getElem_bwdVector⟩

section Mk'

@[simp] theorem mk'_fwdVector (a b : Vector ℕ n) {ha hab} :
    (PermOf.mk' a b ha hab).fwdVector = a := rfl

@[simp] theorem mk'_bwdVector (a b : Vector ℕ n) {ha hab} :
    (PermOf.mk' a b ha hab).bwdVector = b := rfl

instance : Inv (PermOf n) where
  inv a := PermOf.mk' a.bwdVector a.fwdVector
    a.getElem_fwdVector_lt a.getElem_bwdVector_getElem_fwdVector

@[simp] theorem inv_fwdVector (a : PermOf n) : a⁻¹.fwdVector = a.bwdVector := rfl
@[simp] theorem inv_bwdVector (a : PermOf n) : a⁻¹.bwdVector = a.fwdVector := rfl

end Mk'

instance : GetElem (PermOf n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.fwdVector[i]

section GetElem

@[simp]
theorem getElem_lt (a : PermOf n) {i : ℕ} (hi : i < n := by get_elem_tactic) : a[i] < n :=
  a.getElem_fwdVector_lt hi

@[simp]
theorem getElem_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_mk' (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk' a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_fwdVector (a : PermOf n)  {i : ℕ} (hi : i < n) : a.fwdVector[i] = a[i] := rfl

theorem fwdVector_eq_iff_forall_getElem_eq (a b : PermOf n) :
    a.fwdVector = b.fwdVector ↔ ∀ {i} (hi : i < n), a[i] = b[i] := by
  simp_rw [Vector.ext_iff, getElem_fwdVector]

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : PermOf n)[i] = i := Vector.getElem_range _

@[simp]
theorem getElem_mul (a b : PermOf n) {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]] := by
  refine (Vector.getElem_map _ _ _).trans ?_
  simp_rw [getElem?_pos a.fwdVector (b.fwdVector[i]) (b.getElem_fwdVector_lt hi),
    Option.getD_some, getElem_fwdVector]


section GetElemBijective

theorem getElem_injective (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n)
    (hij : a[i] = a[j]) : i = j := a.getElem_fwdVector_injective hi hj hij

@[simp] theorem getElem_inj (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (a : PermOf n) {i : ℕ} (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i := a.getElem_fwdVector_surjective hi

end GetElemBijective


section GetElemInv

@[simp]
theorem getElem_inv_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_inv_mk' (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk' a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_bwdVector (a : PermOf n)  {i : ℕ} (hi : i < n) :
  a.bwdVector[i] = a⁻¹[i] := rfl

theorem bwdVector_eq_iff_forall_getElem_eq (a b : PermOf n) :
    a.bwdVector = b.bwdVector ↔ ∀ {i} (hi : i < n), a⁻¹[i] = b⁻¹[i] := by
  simp_rw [Vector.ext_iff, getElem_bwdVector]

@[simp]
theorem getElem_inv_getElem (a : PermOf n) {i : ℕ} (hi : i < n) :
    a⁻¹[a[i]] = i := a.getElem_bwdVector_getElem_fwdVector hi

@[simp]
theorem getElem_getElem_inv (a : PermOf n) {i : ℕ} (hi : i < n) :
  a[a⁻¹[i]] = i := (a⁻¹).getElem_bwdVector_getElem_fwdVector hi

theorem eq_getElem_inv_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by
  rw [← (a⁻¹).getElem_inj (a.getElem_lt) hj, getElem_inv_getElem]

theorem self_eq_getElem_inv_iff (a : PermOf n) {i : ℕ} (hi : i < n) : i = a⁻¹[i] ↔ a[i] = i := by
  rw [← (a⁻¹).getElem_inj (a.getElem_lt) hi, getElem_inv_getElem]

theorem getElem_inv_eq_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by
  rw [← a.getElem_inj (a⁻¹.getElem_lt) hj, getElem_getElem_inv]

theorem getElem_inv_eq_self_iff (a : PermOf n) {i : ℕ} (hi : i < n) :
    a⁻¹[i] = i ↔ i = a[i] := by
  rw [← a.getElem_inj (a⁻¹.getElem_lt) hi, getElem_getElem_inv]

theorem ne_getElem_inv_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := (a.eq_getElem_inv_iff _ _).ne

theorem self_ne_getElem_inv_iff (a : PermOf n) {i : ℕ} (hi : i < n) :
    i ≠ a⁻¹[i] ↔ a[i] ≠ i := (a.eq_getElem_inv_iff _ _).ne

theorem getElem_inv_ne_iff (a : PermOf n) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := (a.getElem_inv_eq_iff _ _).ne

theorem getElem_inv_ne_self_iff (a : PermOf n) {i : ℕ} (hi : i < n):
    a⁻¹[i] ≠ i ↔ i ≠ a[i] := (a.getElem_inv_eq_iff _ _).ne

end GetElemInv

@[ext]
theorem ext {a b : PermOf n} (h : ∀ {i : ℕ} (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.fwdVector = b.fwdVector ∧ a.bwdVector = b.bwdVector by
    · rcases a ; rcases b ; simp_rw [mk.injEq]
      exact h
  simp_rw [fwdVector_eq_iff_forall_getElem_eq, bwdVector_eq_iff_forall_getElem_eq,
    a.getElem_inv_eq_iff _ (b⁻¹.getElem_lt _), h, getElem_getElem_inv, implies_true, and_self]

end GetElem

instance : Subsingleton (PermOf 0) where
  allEq a b := by simp_rw [PermOf.ext_iff, not_lt_zero', IsEmpty.forall_iff, implies_true]

instance : Subsingleton (PermOf 1) where
  allEq a b := by
    simp_rw [PermOf.ext_iff]
    intro _ hi
    have ha := a.getElem_lt (hi := hi)
    have hb := b.getElem_lt (hi := hi)
    rw [Nat.lt_one_iff] at ha hb
    exact ha.trans hb.symm

instance : Unique (PermOf 0) := Unique.mk' _
instance : Unique (PermOf 1) := Unique.mk' _

instance : Finite (PermOf n) := Finite.of_injective
  (fun a => (fun (i : Fin n) => (⟨a[i.1], a.getElem_lt⟩ : Fin n))) <| fun a b => by
    simp only [Prod.mk.injEq, and_imp, funext_iff, Fin.forall_iff, Fin.ext_iff]
    exact ext

instance : Group (PermOf n) := Group.ofLeftAxioms
  (fun _ _ _ => ext <| fun hi => by simp_rw [getElem_mul])
  (fun _ => ext <| fun hi => by simp_rw [getElem_mul, getElem_one])
  (fun _ => ext <| fun hi => by simp_rw [getElem_mul, getElem_one, getElem_inv_getElem])

section Group

theorem getElem_pow_eq_self_of_getElem_eq_self {a : PermOf n} {i k : ℕ} {hi : i < n}
  (hia : a[i] = i) : (a^k)[i] = i := by
  induction k with | zero => _ | succ k IH => _
  · simp_rw [pow_zero, getElem_one]
  · simp_rw [pow_succ, getElem_mul, hia, IH]

theorem getElem_inv_eq_self_of_getElem_eq_self {a : PermOf n} {i : ℕ} {hi : i < n} :
  a[i] = i → (a⁻¹)[i] = i := by simp_rw [getElem_inv_eq_self_iff, eq_comm, imp_self]

theorem getElem_inv_ne_self_of_getElem_ne_self {a : PermOf n} {i : ℕ} {hi : i < n} :
  a[i] ≠ i → (a⁻¹)[i] ≠ i := by simp_rw [ne_eq, getElem_inv_eq_self_iff, eq_comm, imp_self]

theorem getElem_zpow_eq_self_of_getElem_eq_self {a : PermOf n} {k : ℤ} {i : ℕ} {hi : i < n}
    (hia : a[i] = i) : (a^k)[i] = i := by
  cases k
  · exact getElem_pow_eq_self_of_getElem_eq_self hia
  · simp_rw [zpow_negSucc]
    exact (getElem_inv_eq_self_of_getElem_eq_self (getElem_pow_eq_self_of_getElem_eq_self hia))

@[simp]
theorem getElem_pow_add (a : PermOf n) {i x y : ℕ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [pow_add, getElem_mul]

@[simp]
theorem getElem_zpow_add (a : PermOf n) {i : ℕ} {x y : ℤ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [zpow_add, getElem_mul]

lemma isOfFinOrder (a : PermOf n) : IsOfFinOrder a := isOfFinOrder_of_finite _

lemma orderOf_pos (a : PermOf n) : 0 < orderOf a := by
  rw [orderOf_pos_iff]
  exact a.isOfFinOrder

end Group


@[irreducible] def FixLT (a : PermOf n) (m : ℕ) : Prop :=
    ∀ {i : ℕ}, i < m → ∀ {hi : i < n}, a[i] < m

section FixLT

variable {a : PermOf n} {i m : ℕ}

theorem fixLT_def :
    a.FixLT m ↔ ∀ {i : ℕ}, i < m → ∀ {hi : i < n}, a[i] < m := by
  unfold FixLT
  exact Iff.rfl

theorem FixLT.getElem_lt_of_lt (him : i < m) (ha : a.FixLT m)
    (hin : i < n := by get_elem_tactic) : a[i] < m := by
  unfold FixLT at ha
  exact ha him

theorem fixLT_of_lt_imp_getElem_lt (ha : ∀ {i}, i < m → ∀ {hi : i < n}, a[i] < m) : a.FixLT m := by
  unfold FixLT
  exact ha

theorem fixLT_eq : ∀ (a : PermOf n), a.FixLT n :=
  fun a => fixLT_of_lt_imp_getElem_lt (fun _ => a.getElem_lt)

theorem fixLT_ge (hnm : n ≤ m) : ∀ (a : PermOf n), a.FixLT m :=
  fun a => fixLT_of_lt_imp_getElem_lt (fun _ => a.getElem_lt.trans_le hnm)

theorem fixLT_succ : a.FixLT (n + 1) := a.fixLT_ge (Nat.le_succ _)

theorem FixLT.getElem_eq_self {a : PermOf (n + 1)} (ha : a.FixLT n) : a[n] = n := by
  rcases a.getElem_surjective (Nat.lt_succ_self _) with ⟨k, hk, hkn⟩
  simp_rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at hk
  rcases hk with hk | rfl
  · exact ((ha.getElem_lt_of_lt hk).ne hkn).elim
  · exact hkn

theorem fixLT_of_getElem_eq_self {a : PermOf (n + 1)} (ha : a[n] = n) : a.FixLT n :=
  fixLT_of_lt_imp_getElem_lt (fun {i} hi =>
    (Nat.le_of_lt_succ a.getElem_lt).lt_or_eq.elim id
    (fun h => (hi.ne (a.getElem_injective _ _ (h.trans ha.symm))).elim))

theorem fixLT_iff_getElem_eq_self {a : PermOf (n + 1)} : a.FixLT n ↔ a[n] = n :=
    ⟨FixLT.getElem_eq_self, fixLT_of_getElem_eq_self⟩

theorem fixLT_of_getElem_eq_getElem_eq {a : PermOf (n + 2)} (ha₁ : a[n + 1] = n + 1)
    (ha₂ : a[n] = n) : a.FixLT n :=
  fixLT_of_lt_imp_getElem_lt (fun {i} hi {_} => by
    have H := (Nat.le_of_lt_succ a.getElem_lt)
    rcases H.lt_or_eq with H | H
    · simp_rw [Nat.lt_succ_iff] at H
      rcases H.lt_or_eq with H | H
      · exact H
      · have H := getElem_injective _ _ _ (H.trans ha₂.symm)
        cases H
        simp_rw [lt_self_iff_false] at hi
    · have H := getElem_injective _ _ _ (H.trans ha₁.symm)
      cases H
      simp_rw [add_lt_iff_neg_left, not_lt_zero'] at hi)

theorem fixLT_zero : ∀ (a : PermOf n), a.FixLT 0 :=
  fun _ => fixLT_of_lt_imp_getElem_lt (fun h => (Nat.not_lt_zero _ h).elim)

theorem fixLT_one : (1 : PermOf n).FixLT m :=
  fixLT_of_lt_imp_getElem_lt (fun him => getElem_one _ ▸ him)

theorem FixLT.mul {b : PermOf n}
    (ha : a.FixLT m) (hb : b.FixLT m) : (a * b).FixLT m :=
  fixLT_of_lt_imp_getElem_lt (fun him _ => a.getElem_mul b _ ▸
    ha.getElem_lt_of_lt (hb.getElem_lt_of_lt him))

theorem FixLT.pow
    (ha : a.FixLT m) {k : ℕ} : (a^k).FixLT m := by
  induction k with | zero => _ | succ _ IH => _
  · exact pow_zero a ▸ fixLT_one
  · simp_rw [pow_succ]
    exact IH.mul ha

theorem FixLT.zpow (ha : a.FixLT m) {k : ℤ} : (a^k).FixLT m := by
  have H := (a.isOfFinOrder.mem_zpowers_iff_mem_range_orderOf (y := a^k)).mp
      (zpow_mem (Subgroup.mem_zpowers _) _)
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  rcases H with ⟨_, _, hn⟩
  simp_rw [← hn]
  exact ha.pow

theorem FixLT.inv (ha : a.FixLT m) : (a⁻¹).FixLT m := by
  have H := (a.isOfFinOrder.mem_zpowers_iff_mem_range_orderOf (y := a⁻¹)).mp
      (inv_mem (Subgroup.mem_zpowers _))
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  rcases H with ⟨_, _, hn⟩
  simp_rw [← hn]
  exact ha.pow

@[simp] theorem fixLT_inv_iff :
    (a⁻¹.FixLT m) ↔ (a.FixLT m) := ⟨fun ha => ha.inv, fun ha => ha.inv⟩

theorem fixLT_of_le_of_lt_imp_getElem_lt (hmn : m ≤ n)
    (ha : ∀ {i} (hi : i < m), a[i] < m) : a.FixLT m :=
  fixLT_of_lt_imp_getElem_lt (fun him => ha him)

@[simps!]
def fixLTSubgroup (n m : ℕ) : Subgroup (PermOf n) where
  carrier a := a.FixLT m
  mul_mem' ha hb := FixLT.mul ha hb
  one_mem' := fixLT_one
  inv_mem' ha := FixLT.inv ha

@[simp]
theorem mem_fixLTSubgroup_iff : a ∈ fixLTSubgroup n m ↔ a.FixLT m := Iff.rfl

theorem fixLTSubgroup_eq_top_of_ge (hnm : n ≤ m) : fixLTSubgroup n m = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_fixLTSubgroup_iff, fixLT_ge hnm, implies_true]

theorem fixLTSubgroup_eq_eq_top : fixLTSubgroup n n = ⊤ := fixLTSubgroup_eq_top_of_ge le_rfl

theorem fixLTSubgroup_zero_eq_top : fixLTSubgroup n 0 = ⊤ := by
  simp_rw [Subgroup.eq_top_iff', mem_fixLTSubgroup_iff, fixLT_zero, implies_true]

end FixLT

def ofVector (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : PermOf n where
  fwdVector := a
  bwdVector := (Vector.range n).map a.toList.indexOf
  getElem_fwdVector_lt := hx
  getElem_bwdVector_getElem_fwdVector := fun {i} hi => by
    simp_rw [Vector.getElem_map, Vector.getElem_range]
    exact a.toList.indexOf_getElem ha _ _

section OfVector

@[simp]
theorem getElem_ofVector {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) : (ofVector a hx ha)[i] = a[i] := rfl

@[simp] theorem ofVector_fwdVector (a : PermOf n) :
    ofVector a.fwdVector a.getElem_fwdVector_lt a.fwdVector_toList_Nodup = a :=
  ext <| fun _ => by simp_rw [getElem_ofVector, getElem_fwdVector]

@[simp] theorem ofVector_bwdVector (a : PermOf n) :
    ofVector a.bwdVector a.getElem_bwdVector_lt a.bwdVector_toList_Nodup = a⁻¹ :=
  ext <| fun _ => by simp_rw [getElem_ofVector, getElem_bwdVector]

end OfVector


def ofVectorInv (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : PermOf n := (ofVector a hx ha)⁻¹

section OfVectorInv

theorem getElem_ofVectorInv {a : Vector ℕ n} {hx : ∀ {x} (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) :
    (ofVectorInv a hx ha)[i] = a.toList.indexOf i := by
  unfold ofVectorInv
  unfold ofVector
  simp_rw [getElem_inv_mk, Vector.getElem_map, Vector.getElem_range]

theorem ofVectorInv_fwdVector (a : PermOf n) :
    ofVectorInv a.fwdVector a.getElem_fwdVector_lt a.fwdVector_toList_Nodup = a⁻¹ :=
  ext <| fun _ => by unfold ofVectorInv ; simp_rw [ofVector_fwdVector]

theorem ofVectorInv_bwdVector (a : PermOf n) :
    ofVectorInv a.bwdVector a.getElem_bwdVector_lt a.bwdVector_toList_Nodup = a :=
  ext <| fun _ => by unfold ofVectorInv ; simp_rw [ofVector_bwdVector, inv_inv]

end OfVectorInv


instance : MulAction (PermOf n) (Fin n) where
  smul a i := ⟨a[i.1], a.getElem_lt⟩
  one_smul _ := Fin.ext <| getElem_one _
  mul_smul _ _ _ := Fin.ext <| getElem_mul _ _ _

section MulActionFin

@[simp]
theorem val_smul (a : PermOf n) {i : Fin n} : (a • i : Fin n) = a[i.1] := rfl

@[simp]
theorem smul_mk (a : PermOf n) {i : ℕ} (hi : i < n) :
    (a • (⟨i, hi⟩ : Fin n)) = ⟨a[i], a.getElem_lt⟩ := Fin.ext a.val_smul

theorem getElem_eq_val_smul_mk (a : PermOf n) {i : ℕ} (hi : i < n) :
    a[i] = ↑(a • Fin.mk i hi) := by rw [smul_mk]

theorem smul_right_inj (a : PermOf n) {i j : Fin n} : a • i = a • j ↔ i = j := by
  simp_rw [Fin.ext_iff, val_smul, getElem_inj]

instance : FaithfulSMul (PermOf n) (Fin n) where
  eq_of_smul_eq_smul := by
    simp_rw [PermOf.ext_iff, Fin.ext_iff, Fin.forall_iff, val_smul, imp_self, implies_true]

section FaithfulSMul

theorem eq_iff_smul_eq_smul {a b : PermOf n} : a = b ↔ ∀ i : Fin n, a • i = b • i :=
  ⟨fun h _ => h ▸ rfl, eq_of_smul_eq_smul⟩

end FaithfulSMul

theorem period_pos (a : PermOf n) {i : Fin n} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

end MulActionFin

open Equiv.Perm in
/--
`PermOf n` is equivalent to `Perm (Fin n)`, and this equivalence respects the
multiplication (and, indeed, the scalar action on `Fin n`).
-/
@[simps! apply_apply_val apply_symm_apply_val]
def finPerm (n : ℕ) : PermOf n ≃* Perm (Fin n) where
  toFun a := ⟨(a • ·), (a⁻¹ • ·), inv_smul_smul _, smul_inv_smul _⟩
  invFun π := ⟨Vector.ofFn (Fin.val ∘ π), Vector.ofFn (Fin.val ∘ π.symm),
    fun _ => (Array.getElem_ofFn _ _ _).trans_lt (Fin.is_lt _),
    fun _ => by simp_rw [Vector.getElem_ofFn, comp_apply, Fin.eta, symm_apply_apply]⟩
  left_inv a := PermOf.ext <| fun _ => by simp_rw [coe_fn_mk, coe_fn_symm_mk, getElem_mk,
    Vector.getElem_ofFn, comp_apply, val_smul]
  right_inv π := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [coe_fn_mk, val_smul, getElem_mk,
    Vector.getElem_ofFn, Fin.eta, comp_apply]
  map_mul' a b := Equiv.ext <| fun _ => Fin.ext <| by simp_rw [mul_inv_rev, Perm.coe_mul,
    comp_apply, coe_fn_mk, val_smul, getElem_mul]

section FinPerm

@[simp]
theorem finPerm_symm_apply_getElem (π : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    ((finPerm n).symm π)[i] = π ⟨i, hi⟩ := by
  unfold finPerm
  simp_rw [MulEquiv.symm_mk, MulEquiv.coe_mk, coe_fn_symm_mk, getElem_mk, Vector.getElem_ofFn,
    comp_apply]

@[simp]
theorem finPerm_symm_apply_getElem_inv (π : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    ((finPerm n).symm π)⁻¹[i] = π⁻¹ ⟨i, hi⟩ := by
  rw [← map_inv, finPerm_symm_apply_getElem]

instance : Fintype (PermOf n) := Fintype.ofEquiv (Perm (Fin n)) (finPerm n).symm.toEquiv

end FinPerm

instance : MulAction (PermOf n) ℕ where
  smul a i := a[i]?.getD i
  one_smul k := by
    unfold HSMul.hSMul instHSMul
    rcases lt_or_le k n with hkn | hkn
    · simp_rw [getElem?_pos (1 : PermOf n) k hkn, Option.getD_some, getElem_one]
    · simp_rw [getElem?_neg (1 : PermOf n) k hkn.not_lt, Option.getD_none]
  mul_smul a b k := by
    unfold HSMul.hSMul instHSMul
    rcases lt_or_le k n with hkn | hkn
    · simp_rw [getElem?_pos (a * b) k hkn, getElem?_pos b k hkn, Option.getD_some,
        getElem?_pos a b[k] b.getElem_lt, Option.getD_some, getElem_mul]
    · simp_rw [getElem?_neg (a * b) k hkn.not_lt, getElem?_neg b k hkn.not_lt,
        Option.getD_none, getElem?_neg a k hkn.not_lt, Option.getD_none]

section MulActionNat

theorem smul_nat_def (a : PermOf n) (i : ℕ) :
    a • i = a[i]?.getD i := rfl

theorem smul_nat_eq_dite (a : PermOf n) (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i := by
  simp_rw [smul_nat_def, getElem?_def, apply_dite (fun (o : Option ℕ) => o.getD i),
    Option.getD_some, Option.getD_none]

theorem smul_of_lt (a : PermOf n) {i : ℕ} (h : i < n) : a • i = a[i] := by
  simp_rw [smul_nat_def, getElem?_pos a i h, Option.getD_some]

theorem smul_of_ge (a : PermOf n) {i : ℕ} (h : n ≤ i) : a • i = i := by
  simp_rw [smul_nat_def, getElem?_neg a i h.not_lt, Option.getD_none]

theorem smul_val (a : PermOf n) {i : Fin n} :
    a • i.1 = ((a • i) : Fin n) := a.smul_of_lt _

@[simp]
theorem smul_getElem (a b : PermOf n) {i : ℕ} (h : i < n) : a • b[i] = a[b[i]] :=
  a.smul_of_lt _

theorem smul_eq_iff (a : PermOf n) {i j : ℕ} :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [a.smul_of_lt hi, hi, hi.not_le, false_implies, forall_true_left, and_true]
  · simp_rw [a.smul_of_ge hi, hi, hi.not_lt, IsEmpty.forall_iff, forall_true_left, true_and]

theorem eq_smul_iff (a : PermOf n) {i j : ℕ} :
    i = a • j ↔ (∀ (hj : j < n), i = a[j]) ∧ (n ≤ j → i = j) := by
  simp_rw [eq_comm (a := i), smul_eq_iff]

theorem smul_eq_self_iff (a : PermOf n) {i : ℕ} :
    a • i = i ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [smul_eq_iff, implies_true, and_true]

theorem self_eq_smul_iff (a : PermOf n) {i : ℕ} :
    i = a • i ↔ ∀ (hi : i < n), i = a[i] := by
  simp_rw [eq_comm (a := i), smul_eq_self_iff]

theorem smul_eq_smul_same_iff {a b : PermOf n} {i : ℕ} :
  a • i = b • i ↔ ∀ (hi : i < n), a[i] = b[i] := by
  simp_rw [← inv_smul_eq_iff, ← mul_smul, smul_eq_self_iff, getElem_mul,
  forall_congr' fun h => b.getElem_inv_eq_iff (a.getElem_lt) h]

theorem eq_iff_smul_eq_smul_lt {a b : PermOf n} : a = b ↔ ∀ i < n, a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, PermOf.ext_iff]
  refine forall_congr' fun i => ?_
  rw [Classical.imp_iff_left_iff]
  exact (lt_or_le i n).imp id fun h => by simp_rw [h.not_lt, forall_false]

theorem eq_iff_smul_nat_eq_smul_nat {a b : PermOf n} :
    a = b ↔ ∀ {i : ℕ}, a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, PermOf.ext_iff]

instance : FaithfulSMul (PermOf n) ℕ where
  eq_of_smul_eq_smul := by
    simp_rw [eq_iff_smul_eq_smul_lt]
    exact fun h _ _ => h _

theorem smul_nat_right_inj (a : PermOf n) {i j : ℕ} : a • i = a • j ↔ i = j := by
  simp_rw [← inv_smul_eq_iff, inv_smul_smul]

@[simp]
theorem smul_lt_iff_lt (a : PermOf n) {i : ℕ} : a • i < n ↔ i < n := by
  rcases lt_or_le i n with h | h
  · simp_rw [h, iff_true, a.smul_of_lt h, getElem_lt]
  · simp_rw [h.not_lt, iff_false, not_lt, a.smul_of_ge h, h]

theorem smul_lt_of_lt (a : PermOf n) {i : ℕ} (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

theorem lt_of_smul_lt (a : PermOf n) {i : ℕ} (h : a • i < n) : i < n := a.smul_lt_iff_lt.mp h

theorem smul_eq_iff_eq_one (a : PermOf n) : (∀ i < n, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul_lt, one_smul]

theorem smul_eq_id_iff_eq_one (a : PermOf n) : ((a • ·) : Fin n → Fin n) = id ↔ a = 1 := by
  simp_rw [← one_smul_eq_id (PermOf n), funext_iff, eq_iff_smul_eq_smul]

theorem smul_nat_eq_iff_eq_one (a : PermOf n) : (∀ i : ℕ, a • i = i) ↔ a = 1 := by
  simp_rw [← smul_eq_iff_eq_one]
  exact ⟨fun h => fun _ _ => h _, fun h i => (i.lt_or_ge n).elim (h _) a.smul_of_ge⟩

theorem smul_nat_eq_id_iff_eq_one (a : PermOf n) : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [funext_iff, id_eq, smul_nat_eq_iff_eq_one]

theorem fixedBy_of_ge (a : PermOf n) {i : ℕ} (h : n ≤ i) :
    i ∈ MulAction.fixedBy ℕ a := by
  rw [MulAction.mem_fixedBy]
  exact a.smul_of_ge h

theorem Ici_subset_fixedBy (a : PermOf n) :
    Set.Ici n ⊆ MulAction.fixedBy ℕ a := fun _ => a.fixedBy_of_ge

theorem Ici_subset_fixedPoints :
    Set.Ici n ⊆ MulAction.fixedPoints (PermOf n) ℕ := fun _ hx a => a.smul_of_ge hx

open Pointwise in
theorem Iic_mem_set_fixedBy (a : PermOf n) :
    Set.Iio n ∈ MulAction.fixedBy (Set ℕ) a := Set.ext <| fun _ => by
  rw [← inv_inv a]
  simp_rw [Set.mem_inv_smul_set_iff, Set.mem_Iio, smul_lt_iff_lt]

theorem fixedBy_image_val_subset (a : PermOf n) :
    (MulAction.fixedBy (Fin n) a).image (Fin.val) ⊆ MulAction.fixedBy ℕ a := fun _ => by
  simp_rw [Set.mem_image, MulAction.mem_fixedBy, forall_exists_index, and_imp,
  Fin.forall_iff, Fin.ext_iff, smul_mk]
  rintro _ h ha rfl
  exact (a.smul_of_lt h).trans ha


theorem period_eq_one_of_ge (a : PermOf n) {i : ℕ} (hi : n ≤ i) : MulAction.period a i = 1 := by
  simp_rw [MulAction.period_eq_one_iff, a.smul_of_ge hi]

theorem period_eq_one_iff (a : PermOf n) {i : ℕ} :
    MulAction.period a i = 1 ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [MulAction.period_eq_one_iff]
  rcases lt_or_le i n with hi | hi
  · simp_rw [hi, forall_true_left, a.smul_of_lt hi]
  · simp_rw [hi.not_lt, forall_false, iff_true, a.smul_of_ge hi]

@[simp]
theorem getElem_pow_period (a : PermOf n) {i : ℕ} (hi : i < n) :
    (a ^ MulAction.period a i)[i] = i := by
  rw [← smul_of_lt _ hi, MulAction.pow_period_smul]

theorem getElem_pow_mod_period (a : PermOf n) {i : ℕ} (hi : i < n) (k : ℕ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt _ hi, MulAction.pow_mod_period_smul]

theorem getElem_zpow_mod_period (a : PermOf n) {i : ℕ} (hi : i < n) (k : ℤ) :
    (a^(k % MulAction.period a i))[i] = (a^k)[i] := by
  simp_rw [← smul_of_lt _ hi, MulAction.zpow_mod_period_smul]

theorem period_nat_pos (a : PermOf n) {i : ℕ} : 0 < MulAction.period a i :=
  MulAction.period_pos_of_orderOf_pos a.orderOf_pos _

theorem period_fin (a : PermOf n) {i : Fin n} :
    MulAction.period a i = MulAction.period a (i : ℕ) := by
  rw [le_antisymm_iff]
  refine ⟨MulAction.period_le_of_fixed (period_nat_pos _) (Fin.ext ?_),
    MulAction.period_le_of_fixed (period_pos _) ?_⟩
  · simp_rw [val_smul, getElem_pow_period]
  · simp_rw [smul_val, MulAction.pow_period_smul]

@[simp]
theorem period_mk (a : PermOf n) {i : ℕ} (hi : i < n) :
    MulAction.period a (Fin.mk i hi) = MulAction.period a i := a.period_fin

theorem period_eq_one_of_zero (a : PermOf 0) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_eq_one_of_one (a : PermOf 1) {i : ℕ} : MulAction.period a i = 1 := by
  rw [Unique.eq_default a, default_eq, MulAction.period_one]

theorem period_le_card_of_getElem_pow_mem (a : PermOf n) {i : ℕ} (hi : i < n)
  (s : Finset ℕ) : (∀ k < s.card + 1, (a ^ k)[i] ∈ s) → MulAction.period a i ≤ s.card := by
  simp_rw [← smul_of_lt _ hi]
  exact MulAction.period_le_card_of_smul_pow_mem _ _

theorem getElem_injOn_range_period (a : PermOf n) {i : ℕ} (hi : i < n) :
    Set.InjOn (fun k => (a ^ k)[i]) (Finset.range (MulAction.period a i)) := by
  simp_rw [← smul_of_lt _ hi]
  exact MulAction.smul_injOn_range_period _

theorem period_le_of_lt (a : PermOf n) {i : ℕ} (hi : i < n) : MulAction.period a i ≤ n := by
  refine (period_le_card_of_getElem_pow_mem a hi (Finset.range n) ?_).trans_eq
    (Finset.card_range _)
  simp_rw [Finset.card_range, Finset.mem_range, getElem_lt, implies_true]

theorem period_le_of_ne_zero [NeZero n] (a : PermOf n) {i : ℕ} : MulAction.period a i ≤ n := by
  rcases lt_or_le i n with hi | hi
  · exact a.period_le_of_lt hi
  · rw [a.period_eq_one_of_ge hi]
    exact NeZero.pos n

theorem exists_pos_le_pow_getElem_eq (a : PermOf n) {i : ℕ} (hi : i < n) :
    ∃ k, 0 < k ∧ k ≤ n ∧ (a ^ k)[i] = i :=
  ⟨MulAction.period a i, a.period_nat_pos, a.period_le_of_lt hi, a.getElem_pow_period _⟩

end MulActionNat


@[irreducible] def equiv {n m : ℕ} (a : PermOf n) (b : PermOf m) : Prop :=
  ∀ {i}, i < max m n → a • i = b • i

section equiv

variable {m l i : ℕ} {a : PermOf n} {b : PermOf m} {c : PermOf l}

theorem equiv_iff_smul_eq_of_lt :
    a.equiv b ↔ ∀ {i}, i < max m n → a • i = b • i := by
  unfold equiv
  exact Iff.rfl

instance {a : PermOf n} {b : PermOf m} : Decidable (a.equiv b) :=
  decidable_of_decidable_of_iff equiv_iff_smul_eq_of_lt.symm

theorem equiv_iff_smul_eq : a.equiv b ↔ ∀ {i : ℕ}, a • i = b • i :=
  ⟨fun h i => (lt_or_le i (max m n)).elim (equiv_iff_smul_eq_of_lt.mp h)
    (fun hmn => (a.smul_of_ge (le_of_max_le_right hmn)).trans
    (b.smul_of_ge (le_of_max_le_left hmn)).symm),
    fun h => equiv_iff_smul_eq_of_lt.mpr (fun _ => h)⟩

theorem equiv_iff_getElem_eq_getElem_and_getElem_eq_of_le (hnm : n ≤ m) :
    a.equiv b ↔ (∀ {i} (hi : i < n), a[i] = b[i]) ∧
    (∀ {i}, n ≤ i → ∀ (hi' : i < m), b[i] = i) := by
  simp_rw [equiv_iff_smul_eq_of_lt, max_eq_left hnm, smul_nat_eq_dite]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · intro i hi
    have H :=  dif_pos hi ▸ dif_pos (hi.trans_le hnm) ▸ h (hi.trans_le hnm)
    exact H
  · intro i hi hi'
    have H := dif_neg hi.not_lt ▸ dif_pos hi' ▸ h hi'
    exact H.symm
  · intro i hi'
    simp_rw [hi', dite_true]
    split_ifs with hi
    · exact h.1 _
    · exact (h.2 (le_of_not_lt hi) _).symm

theorem equiv.smul_eq (hab : a.equiv b) : ∀ {i : ℕ}, a • i = b • i :=
  equiv_iff_smul_eq.mp hab

theorem equiv.refl (a : PermOf n) : a.equiv a := by
  simp_rw [equiv_iff_smul_eq, implies_true]

theorem equiv.rfl : a.equiv a := equiv.refl a

theorem equiv.symm : a.equiv b → b.equiv a := by
  simp_rw [equiv_iff_smul_eq, eq_comm, imp_self]

theorem equiv_comm : a.equiv b ↔ b.equiv a :=
  ⟨equiv.symm, equiv.symm⟩

theorem equiv_iff_getElem_eq_getElem_and_getElem_eq_of_ge (hmn : m ≤ n) :
    a.equiv b ↔ (∀ {i} (hi : i < m), a[i] = b[i]) ∧
    (∀ {i}, m ≤ i → ∀ (hi' : i < n), a[i] = i) := by
  refine equiv_comm.trans
    ((equiv_iff_getElem_eq_getElem_and_getElem_eq_of_le hmn).trans ?_)
  simp_rw [and_congr_left_iff]
  exact fun _ => ⟨fun h _ _ => (h _).symm, fun h _ _ => (h _).symm⟩

theorem equiv.trans : a.equiv b → b.equiv c → a.equiv c := by
  simp_rw [equiv_iff_smul_eq]
  intro h₁ h₂
  exact (h₁.trans h₂)

@[simp] theorem equiv_one_iff_eq_one : a.equiv (1 : PermOf m) ↔ a = 1 := by
  simp_rw [equiv_iff_smul_eq, one_smul, smul_nat_eq_iff_eq_one]

@[simp] theorem one_equiv_iff_eq_one : (1 : PermOf m).equiv a ↔ a = 1 := by
  simp_rw [equiv_comm, equiv_one_iff_eq_one]

@[simp] theorem equiv_one_one : (1 : PermOf n).equiv (1 : PermOf m) := by
  simp_rw [equiv_one_iff_eq_one]

theorem equiv.inv_right (hab : a.equiv b⁻¹) : a⁻¹.equiv b := by
  simp_rw [equiv_iff_smul_eq, inv_smul_eq_iff, hab.smul_eq,
    inv_smul_smul, implies_true]

theorem equiv.inv_left (hab : a⁻¹.equiv b) : a.equiv b⁻¹ := by
  simp_rw [equiv_iff_smul_eq, eq_inv_smul_iff, hab.symm.smul_eq,
    inv_smul_smul, implies_true]

theorem equiv.inv_inv (hab : a.equiv b) : a⁻¹.equiv b⁻¹ := by
  simp_rw [equiv_iff_smul_eq, eq_inv_smul_iff, hab.symm.smul_eq,
    smul_inv_smul, implies_true]

@[simp] theorem equiv_inv_inv_iff : a⁻¹.equiv b⁻¹ ↔ a.equiv b :=
  ⟨fun hab => hab.inv_inv, fun hab => hab.inv_inv⟩

theorem equiv.mul_mul {a' : PermOf n} {b' : PermOf m} (hab : a.equiv b)
    (hab' : a'.equiv b') : (a*a').equiv (b*b') := by
  simp_rw [equiv_iff_smul_eq, mul_smul, hab.smul_eq, hab'.smul_eq, implies_true]

theorem equiv.eq {a' : PermOf n} (h : a.equiv a') : a = a' := by
  ext i hi
  simp_rw [← smul_of_lt _ hi, h.smul_eq]

@[simp] theorem equiv_iff_eq {a' : PermOf n} : a.equiv a' ↔ a = a' :=
  ⟨equiv.eq, fun h => h ▸ equiv.rfl⟩

@[simps!]
instance equivSubgroup (n m : ℕ) : Subgroup (PermOf n × PermOf m) where
  carrier a := a.1.equiv a.2
  mul_mem' := equiv.mul_mul
  one_mem' := equiv_one_one
  inv_mem' := equiv.inv_inv

@[simp] theorem mem_equivSubgroup_iff (ab : PermOf n × PermOf m) :
    ab ∈ equivSubgroup n m ↔ ab.1.equiv ab.2 := Iff.rfl

end equiv

/--
`ofNatPerm` maps a member of `Perm ℕ` which maps the subtype `< n` to itself to the corresponding
`PermOf n`.
-/
def ofNatPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) : PermOf n where
  fwdVector := (Vector.range n).map f
  bwdVector := (Vector.range n).map ⇑f⁻¹
  getElem_fwdVector_lt := fun {i} => by
    simp_rw [Vector.getElem_map, Vector.getElem_range, hf, imp_self]
  getElem_bwdVector_getElem_fwdVector := by
    simp only [Vector.getElem_map, Vector.getElem_range, Perm.inv_apply_self, implies_true]

section ofNatPerm

@[simp]
theorem getElem_ofNatPerm {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {i : ℕ}
    (hi : i < n) : (ofNatPerm f hf)[i] = f i := by
  unfold ofNatPerm
  simp_rw [getElem_mk, Vector.getElem_map, Vector.getElem_range]

@[simp]
theorem getElem_ofNatPerm_inv {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {i : ℕ} (hi : i < n) :
    (ofNatPerm f hf)⁻¹[i] = f⁻¹ i := by
  unfold ofNatPerm
  simp_rw [getElem_inv_mk, Vector.getElem_map, Vector.getElem_range]

@[simp]
theorem ofNatPerm_inv {f : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} :
    (ofNatPerm f hf)⁻¹ =
    ofNatPerm f⁻¹ (fun x => (hf (f⁻¹ x)).symm.trans (Perm.apply_inv_self _ _ ▸ Iff.rfl)) := rfl

@[simp]
theorem mul_ofNatPerm {f g : Perm ℕ} {hf : ∀ i, f i < n ↔ i < n} {hg : ∀ i, g i < n ↔ i < n} :
    (ofNatPerm f hf) * (ofNatPerm g hg) =
    ofNatPerm (f * g) (fun x => (hf (g x)).trans (hg x)) := by
  simp only [PermOf.ext_iff, getElem_mul, getElem_ofNatPerm, Perm.mul_apply, implies_true]

end ofNatPerm

/--
`natPerm` is the injective monoid homomorphism from `PermOf n` to `Perm ℕ`.
-/

def natPerm (n : ℕ) : PermOf n →* Perm ℕ :=
  (Perm.extendDomainHom Fin.equivSubtype).comp (finPerm n : PermOf _ →* Equiv.Perm (Fin n))

section NatPerm

@[simp]
theorem natPerm_apply_apply (a : PermOf n) {i : ℕ} : natPerm n a i = a • i := by
  unfold natPerm
  simp_rw [MonoidHom.comp_apply, MonoidHom.coe_coe, Perm.extendDomainHom_apply]
  rcases lt_or_le i n with hi | hi
  · simp_rw [Perm.extendDomain_apply_subtype _ Fin.equivSubtype hi, a.smul_of_lt hi,
      Fin.equivSubtype_symm_apply, Fin.equivSubtype_apply, finPerm_apply_apply_val]
  · simp_rw [Perm.extendDomain_apply_not_subtype _ Fin.equivSubtype hi.not_lt, a.smul_of_ge hi]

@[simp]
theorem natPerm_apply_symm_apply (a : PermOf n) {i : ℕ} : (natPerm n a).symm i = a⁻¹ • i := by
  rw [← Perm.inv_def, ← map_inv, natPerm_apply_apply]

@[simp]
theorem natPerm_lt_iff_lt (a : PermOf n) {i : ℕ} : natPerm n a i < n ↔ i < n := by
  rw [natPerm_apply_apply, smul_lt_iff_lt]

theorem natPerm_apply_apply_of_lt (a : PermOf n) {i : ℕ} (h : i < n) :
    natPerm n a i = a[i] := by rw [natPerm_apply_apply, a.smul_of_lt h]

theorem natPerm_apply_apply_of_ge (a : PermOf n) {i : ℕ} (h : n ≤ i) : natPerm n a i = i := by
  rw [natPerm_apply_apply, a.smul_of_ge h]

theorem natPerm_apply_symm_apply_of_lt (a : PermOf n) {i : ℕ} (h : i < n) :
    (natPerm n a)⁻¹ i = a⁻¹[i] := by
  simp_rw [← MonoidHom.map_inv, natPerm_apply_apply_of_lt _ h]

theorem natPerm_apply_symm_apply_of_ge (a : PermOf n) {i : ℕ} (h : n ≤ i) :
    (natPerm n a)⁻¹ i = i := by rw [← MonoidHom.map_inv, natPerm_apply_apply_of_ge _ h]

theorem natPerm_injective : Function.Injective (natPerm n) :=
  (Equiv.Perm.extendDomainHom_injective Fin.equivSubtype).comp (finPerm n).injective

theorem natPerm_inj {a b : PermOf n} : natPerm n a = natPerm n b ↔ a = b :=
  natPerm_injective.eq_iff

theorem natPerm_ofNatPerm (f : Perm ℕ) (hf : ∀ i, f i < n ↔ i < n) (i : ℕ) :
    natPerm n (ofNatPerm f hf) i = if i < n then f i else i := by
  rcases lt_or_le i n with hi | hi
  · simp_rw [natPerm_apply_apply_of_lt _ hi, getElem_ofNatPerm, hi, if_true]
  · simp_rw [natPerm_apply_apply_of_ge _ hi, hi.not_lt, if_false]

theorem ofNatPerm_natPerm (a : PermOf n) :
    ofNatPerm (natPerm n a) (fun _ => a.natPerm_lt_iff_lt) = a := by
  ext i hi
  simp_rw [getElem_ofNatPerm, a.natPerm_apply_apply_of_lt hi]

theorem apply_eq_of_ge_iff_exists_natPerm_apply (e : Perm ℕ) :
    (∀ i ≥ n, e i = i) ↔ ∃ a : PermOf n, natPerm n a = e := by
  refine ⟨fun h => ?_, ?_⟩
  · have H : ∀ i, e i < n ↔ i < n := fun i => by
      simp_rw [← not_le, not_iff_not]
      exact ⟨fun hi => by rwa [e.injective (h _ hi).symm], fun hi => (h _ hi).symm ▸ hi⟩
    use ofNatPerm e H
    simp_rw [Equiv.ext_iff, natPerm_ofNatPerm e H, ite_eq_left_iff, not_lt]
    exact fun _ hi => (h _ hi).symm
  · rintro ⟨a, rfl⟩ i hi
    exact a.natPerm_apply_apply_of_ge hi

theorem coe_natPerm_range : MonoidHom.range (natPerm (n := n)) =
    {e : Perm ℕ | ∀ i ≥ n, e i = i} := by
  simp_rw [Set.ext_iff, MonoidHom.coe_range, Set.mem_range, ge_iff_le, Set.mem_setOf_eq,
  apply_eq_of_ge_iff_exists_natPerm_apply, implies_true]

theorem equiv_iff_natPerm_eq {a : PermOf n} {m : ℕ} {b : PermOf m} :
    a.equiv b ↔ a.natPerm n = b.natPerm m := by
  simp_rw [Equiv.ext_iff, natPerm_apply_apply, equiv_iff_smul_eq]

theorem equiv.natPerm_eq {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.equiv b) : a.natPerm n = b.natPerm m := equiv_iff_natPerm_eq.mp hab

end NatPerm



/--
For `a` an `PermOf n`, `a.swap i j hi hj` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : PermOf n) (i j : ℕ) (hi : i < n) (hj : j < n) : PermOf n where
  fwdVector := a.fwdVector.swap i j
  bwdVector := a.bwdVector.map (fun k => Equiv.swap i j k)
  getElem_fwdVector_lt := fun _ => by
    simp_rw [Vector.getElem_swap_eq_getElem_swap_apply, getElem_fwdVector, getElem_lt]
  getElem_bwdVector_getElem_fwdVector := fun _ => by
    simp_rw [Vector.getElem_map, getElem_bwdVector, Vector.getElem_swap_eq_getElem_swap_apply,
      getElem_fwdVector, getElem_inv_getElem, swap_apply_self]

section Swap

variable (i j k : ℕ) (hi : i < n) (hj : j < n)

@[simp]
theorem getElem_swap (a : PermOf n) (hk : k < n) :
    (a.swap i j hi hj)[k] = a[Equiv.swap i j k]'(swap_prop (· < n) hk hi hj) :=
  Vector.getElem_swap_eq_getElem_swap_apply _ _ _ hi hj _ _

@[simp]
theorem getElem_inv_swap (a : PermOf n) (hk : k < n) :
    (a.swap i j hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.bwdVector.getElem_map _ _

theorem swap_smul_eq_smul_swap (a : PermOf n) :
    (a.swap i j hi hj) • k = a • (Equiv.swap i j k) := by
  rcases lt_or_ge k n with hk | hk
  · simp_rw [smul_of_lt _ (swap_prop (· < n) hk hi hj), smul_of_lt _ hk, getElem_swap]
  · simp_rw [Equiv.swap_apply_of_ne_of_ne (hk.trans_lt' hi).ne' (hk.trans_lt' hj).ne',
      smul_of_ge _ hk]

theorem swap_inv_eq_swap_apply_inv_smul (a : PermOf n) :
  (a.swap i j hi hj)⁻¹ • k = Equiv.swap i j (a⁻¹ • k) := by
  simp_rw [inv_smul_eq_iff, swap_smul_eq_smul_swap,
  ← swap_smul, smul_inv_smul, swap_apply_self]

theorem swap_smul_eq_swap_apply_smul (a : PermOf n) :
    (a.swap i j hi hj) • k = Equiv.swap (a • i) (a • j) (a • k) := by
  rw [swap_smul, swap_smul_eq_smul_swap]

theorem swap_inv_smul_eq_inv_smul_swap (a : PermOf n) : (a.swap i j hi hj)⁻¹ • k =
    a⁻¹ • (Equiv.swap (a • i) (a • j) k) := by
  simp_rw [swap_inv_eq_swap_apply_inv_smul, ← Equiv.swap_smul, inv_smul_smul]

theorem swap_smul_left (a : PermOf n) :
    (a.swap i j hi hj) • i = a • j := by rw [swap_smul_eq_smul_swap, swap_apply_left]

theorem swap_smul_right (a : PermOf n) :
  (a.swap i j hi hj) • j = a • i := by rw [swap_smul_eq_smul_swap, swap_apply_right]

theorem swap_smul_of_ne_of_ne (a : PermOf n) {k} :
  k ≠ i → k ≠ j → (a.swap i j hi hj) • k = a • k := by
  rw [swap_smul_eq_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

theorem swap_inv_smul_left (a : PermOf n) :
    (a.swap i j hi hj)⁻¹ • (a • i) = j := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_left, inv_smul_smul]

theorem swap_inv_smul_right (a : PermOf n) :
    (a.swap i j hi hj)⁻¹ • (a • j) = i := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_right, inv_smul_smul]

theorem swap_inv_smul_of_ne_of_ne (a : PermOf n) {k} :
  k ≠ a • i → k ≠ a • j → (a.swap i j hi hj)⁻¹ • k = a⁻¹ • k := by
  rw [swap_inv_smul_eq_inv_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (a : PermOf n) (i : ℕ) (hi hi' : i < n) : a.swap i i hi hi' = a := by
  ext : 1
  simp_rw [getElem_swap, Equiv.swap_self, Equiv.refl_apply]

@[simp]
theorem swap_swap (a : PermOf n) (i j : ℕ) (hi hi' : i < n) (hj hj' : j < n) :
    (a.swap i j hi hj).swap i j hi' hj' = a := by
  ext : 1
  simp_rw [getElem_swap, swap_apply_self]

theorem getElem_one_swap (hk : k < n) : (swap 1 i j hi hj)[k] = Equiv.swap i j k := by
  rw [getElem_swap, getElem_one]

theorem getElem_inv_one_swap (hk : k < n) : (swap 1 i j hi hj)⁻¹[k] = Equiv.swap i j k := by
  simp_rw [getElem_inv_swap, inv_one, getElem_one]

theorem one_swap_smul : (swap 1 i j hi hj) • k = Equiv.swap i j k := by
  rw [swap_smul_eq_smul_swap, one_smul]

theorem one_swap_inv_smul : (swap 1 i j hi hj)⁻¹ • k = Equiv.swap i j k := by
  simp_rw [swap_inv_smul_eq_inv_smul_swap, one_smul, inv_one, one_smul]

theorem one_swap_mul_self : swap 1 i j hi hj * swap 1 i j hi hj = 1 := by
  ext : 1
  simp_rw [getElem_mul, getElem_one_swap, swap_apply_self, getElem_one]

theorem one_swap_inverse : (swap 1 i j hi hj)⁻¹ = swap 1 i j hi hj := by
  ext : 1
  rw [getElem_one_swap, getElem_inv_one_swap]

theorem swap_eq_mul_one_swap (a : PermOf n) : a.swap i j hi hj = a * swap 1 i j hi hj := by
  ext : 1
  simp only [getElem_swap, getElem_mul, getElem_one]

theorem swap_eq_one_swap_mul (a : PermOf n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    a.swap i j hi hj = swap 1 _ _ hi' hj' * a := by
  rw [eq_iff_smul_eq_smul_lt]
  simp_rw [mul_smul, one_swap_smul, swap_smul_eq_smul_swap, swap_smul, implies_true]

theorem swap_inv_eq_one_swap_mul (a : PermOf n) :
    (a.swap i j hi hj)⁻¹ = swap 1 i j hi hj * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (a : PermOf n) (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    (a.swap i j hi hj)⁻¹ = a⁻¹ * swap 1 _ _ hi' hj' := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

theorem natPerm_swap (a : PermOf n) :
    natPerm n (swap a i j hi hj) = natPerm n a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, natPerm_apply_apply, swap_smul_eq_smul_swap]

@[simp]
theorem natPerm_one_swap  :
    natPerm n (swap 1 i j hi hj) = Equiv.swap i j := by simp_rw [natPerm_swap, map_one, one_mul]

end Swap

def actOnIndices {α : Type*} (a : PermOf n) (v : Vector α n) : Vector α n :=
  v.mapIdx (fun i _ => v[a[i.1]])

section ActOnIndices

variable {α : Type*}

@[simp] theorem getElem_actOnIndices (a : PermOf n) (v : Vector α n) {i : ℕ} (hi : i < n) :
    (a.actOnIndices v)[i] = v[a[i]] := Vector.getElem_mapIdx _ _ _

@[simp] theorem one_actOnIndices (v : Vector α n) :
    (1 : (PermOf n)).actOnIndices v = v := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, getElem_one, implies_true]

@[simp] theorem mul_actOnIndices (a b : PermOf n) (v : Vector α n) :
    (a * b).actOnIndices v = b.actOnIndices (a.actOnIndices v) := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, getElem_mul, implies_true]

@[simp] theorem actOnIndices_actOnIndices_inv (a : PermOf n) (v : Vector α n) :
    a.actOnIndices (a⁻¹.actOnIndices v) = v := by
  simp_rw [← mul_actOnIndices, inv_mul_cancel, one_actOnIndices]

@[simp] theorem actOnIndices_inv_actOnIndices (a : PermOf n) (v : Vector α n) :
    a⁻¹.actOnIndices (a.actOnIndices v) = v := by
  simp_rw [← mul_actOnIndices, mul_inv_cancel, one_actOnIndices]

theorem mem_of_mem_actOnIndices (a : PermOf n) {v : Vector α n} {x : α}
    (hx : x ∈ a.actOnIndices v) : x ∈ v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_actOnIndices] at hx
  rcases hx with ⟨i, hi, hix⟩
  exact ⟨a[i], a.getElem_lt, hix⟩

theorem mem_actOnIndices_of_mem (a : PermOf n) {v : Vector α n} {x : α}
    (hx : x ∈ v) : x ∈ a.actOnIndices v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_actOnIndices]
  rcases hx with ⟨i, hi, hix⟩
  refine ⟨a⁻¹[i], getElem_lt _, ?_⟩
  simp_rw [getElem_getElem_inv, hix]

theorem mem_onIndices_iff (a : PermOf n) {v : Vector α n} {x : α} :
    x ∈ a.actOnIndices v ↔ x ∈ v := ⟨a.mem_of_mem_actOnIndices, a.mem_actOnIndices_of_mem⟩

@[simp]
theorem actOnIndices_range (a : PermOf n) :
    a.actOnIndices (Vector.range n) = a.fwdVector := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, Vector.getElem_range,
    getElem_fwdVector, implies_true]

@[simp]
theorem inv_actOnIndices_range (a : PermOf n) :
    (a⁻¹).actOnIndices (Vector.range n) = a.bwdVector := by
  simp_rw [Vector.ext_iff, getElem_actOnIndices, Vector.getElem_range,
    getElem_bwdVector, implies_true]

end ActOnIndices

instance {α : Type u} : MulAction (PermOf n)ᵐᵒᵖ (Vector α n) where
  smul a v := a.unop.actOnIndices v
  one_smul _ := one_actOnIndices _
  mul_smul _ _ _ := mul_actOnIndices _ _ _

section MulActionMulOppositeVector

variable {α : Type*}

@[simp] theorem op_smul (a : PermOf n) (v : Vector α n) :
    (MulOpposite.op a) • v = a.actOnIndices v := rfl

@[simp] theorem unop_actOnIndices (a : (PermOf n)ᵐᵒᵖ) (v : Vector α n) :
    a.unop.actOnIndices v = a • v := rfl

end MulActionMulOppositeVector

def cycleOf (a : PermOf n) (x : ℕ) : Finset ℕ :=
  if h : x < n then (Finset.range n).image (fun k => (a ^ k)[x]) else {x}

theorem cycleOf_lt (a : PermOf n) {x : ℕ} (hx : x < n) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k)[x]) := by
  unfold cycleOf
  simp_rw [dif_pos hx, Finset.ext_iff, Finset.mem_image, Finset.mem_range]
  refine fun _ => ⟨fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos,
    by simp_rw [getElem_pow_mod_period, h]⟩, fun ⟨_, hlt, h⟩ =>
    ⟨_, (hlt.trans_le <| a.period_le_of_lt hx), h⟩⟩

theorem cycleOf_ge (a : PermOf n) {x : ℕ} (hx : n ≤ x) :
    a.cycleOf x = {x} := dif_neg (not_lt_of_le hx)

theorem card_cycleOf (a : PermOf n) (x : ℕ) : (a.cycleOf x).card = MulAction.period a x := by
  rcases lt_or_le x n with hx | hx
  · refine Eq.trans ?_ (Finset.card_range (MulAction.period a x))
    rw [a.cycleOf_lt hx, Finset.card_image_iff]
    exact getElem_injOn_range_period _ _
  · rw [a.cycleOf_ge hx, a.period_eq_one_of_ge hx, Finset.card_singleton]

theorem cycleOf_eq_map_smul_range_period (a : PermOf n) (x : ℕ) :
    a.cycleOf x = (Finset.range (MulAction.period a x)).image (fun k => (a ^ k) • x) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleOf_lt hx, smul_of_lt _ hx]
  · simp_rw [a.cycleOf_ge hx, smul_of_ge _ hx, Finset.ext_iff, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range, exists_and_right]
    exact fun _ => ⟨fun h => h ▸ ⟨⟨0, a.period_nat_pos⟩, rfl⟩, fun h => h.2.symm⟩

theorem mem_cycleOf_iff_exists_pow_lt_period_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i) • x = y := by
  rw [cycleOf_eq_map_smul_range_period]
  simp_rw [Finset.mem_image, Finset.mem_range]

theorem mem_cycleOf_iff_exists_pow_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_lt_period_smul]
  refine ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩,
    fun ⟨k, h⟩ => ⟨k % MulAction.period a x, Nat.mod_lt _ a.period_nat_pos, ?_⟩⟩
  simp_rw [MulAction.pow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_zpow_smul (a : PermOf n) {x y : ℕ} :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i) • x = y := by
  rw [mem_cycleOf_iff_exists_pow_smul]
  refine ⟨fun ⟨_, h⟩ => ⟨_, (zpow_natCast a _).symm ▸ h⟩,
    fun ⟨k, h⟩ => ⟨(k % MulAction.period a x).toNat, ?_⟩⟩
  simp_rw [← zpow_natCast, Int.toNat_of_nonneg
    (Int.emod_nonneg _ ((Nat.cast_ne_zero (R := ℤ)).mpr (a.period_nat_pos (i := x)).ne')),
    MulAction.zpow_mod_period_smul, h]

theorem mem_cycleOf_iff_exists_getElem_pow_lt_period (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, i < MulAction.period a x ∧ (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_lt_period_smul, smul_of_lt _ hx]

theorem mem_cycleOf_iff_exists_getElem_pow (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℕ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul, smul_of_lt _ hx]

theorem mem_cycleOf_iff_exists_getElem_zpow (a : PermOf n) {x y : ℕ} (hx : x < n) :
    y ∈ a.cycleOf x ↔ ∃ i : ℤ, (a ^ i)[x] = y := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul, smul_of_lt _ hx]

theorem self_mem_cycleOf (a : PermOf n) (x : ℕ) : x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨0, by simp only [pow_zero, one_smul]⟩

theorem nonempty_cycleOf (a : PermOf n) {x : ℕ} : (a.cycleOf x).Nonempty :=
  ⟨_, a.self_mem_cycleOf x⟩

theorem smul_mem_cycleOf (a : PermOf n) (x : ℕ) : (a • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨1, by simp only [pow_one]⟩

theorem smul_inv_mem_cycleOf (a : PermOf n) (x : ℕ) : (a⁻¹ • x) ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨-1, by simp only [zpow_neg, zpow_one]⟩

theorem smul_pow_mem_cycleOf (a : PermOf n) (x k : ℕ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_pow_smul]
  exact ⟨k, rfl⟩

theorem smul_zpow_mem_cycleOf (a : PermOf n) (x : ℕ) (k : ℤ) : (a ^ k) • x ∈ a.cycleOf x := by
  simp_rw [mem_cycleOf_iff_exists_zpow_smul]
  exact ⟨k, rfl⟩

theorem getElem_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) : a[x] ∈ a.cycleOf x := by
  convert a.smul_mem_cycleOf x
  rw [smul_of_lt _ hx]

theorem getElem_inv_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) : a⁻¹[x] ∈ a.cycleOf x := by
  convert a.smul_inv_mem_cycleOf x
  rw [smul_of_lt _ hx]

theorem getElem_pow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℕ):
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_pow_mem_cycleOf x k
  rw [smul_of_lt _ hx]

theorem getElem_zpow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℤ) :
    (a^k)[x] ∈ a.cycleOf x := by
  convert a.smul_zpow_mem_cycleOf x k
  rw [smul_of_lt _ hx]

theorem getElem_inv_pow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℕ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  convert a.getElem_zpow_mem_cycleOf hx (-(k : ℤ))
  simp_rw [inv_pow, zpow_neg, zpow_natCast]

theorem getElem_inv_zpow_mem_cycleOf (a : PermOf n) {x : ℕ} (hx : x < n) (k : ℤ) :
    ((a⁻¹)^k)[x] ∈ a.cycleOf x := by
  simp only [inv_zpow']
  exact a.getElem_zpow_mem_cycleOf hx (-k)

def CycleMinVectorAux (a : PermOf n) : ℕ → PermOf n × Vector ℕ n
  | 0 => ⟨1, Vector.range n⟩
  | 1 =>
    ⟨a, (Vector.range n).zipWith a.fwdVector min⟩
  | (i+2) =>
    let ⟨ρ, b⟩ := a.CycleMinVectorAux (i + 1)
    let ρ' := ρ ^ 2
    ⟨ρ', b.zipWith (ρ'.actOnIndices b) min⟩

@[simp]
theorem cycleMinAux_zero_fst (a : PermOf n) : (a.CycleMinVectorAux 0).1 = 1 := rfl

@[simp]
theorem cycleMinAux_succ_fst (a : PermOf n) (i : ℕ) :
    (a.CycleMinVectorAux (i + 1)).1 = a ^ (2 ^ i) := by
  induction' i with i IH
  · rw [pow_zero, pow_one]
    rfl
  · rw [pow_succ, pow_mul]
    exact IH ▸ rfl

def CycleMinVector (a : PermOf n) (i : ℕ) : Vector ℕ n := (a.CycleMinVectorAux i).2

@[simp]
theorem cycleMinAux_snd_val (a : PermOf n) {i : ℕ} :
    (a.CycleMinVectorAux i).2 = CycleMinVector a i := rfl

@[simp] theorem getElem_cycleMinVector_zero (a : PermOf n) {x : ℕ} (hx : x < n):
  (a.CycleMinVector 0)[x] = x := Vector.getElem_range _

theorem getElem_cycleMinVector_succ (a : PermOf n) {i x : ℕ}
    (hx : x < n) :
    (a.CycleMinVector (i + 1))[x] = min ((a.CycleMinVector i)[x])
    ((a.CycleMinVector i)[(a^2^i)[x]]) := by
  rcases i with (_ | i) <;>
  refine (Vector.getElem_zipWith _).trans ?_
  · simp_rw [Vector.getElem_range, getElem_fwdVector, pow_zero, pow_one,
      getElem_cycleMinVector_zero]
  · simp_rw [getElem_actOnIndices, cycleMinAux_snd_val,
      cycleMinAux_succ_fst, ← pow_mul, ← pow_succ]

@[simp] theorem getElem_cycleMinVector_le_self {a : PermOf n} {k i : ℕ}
    {hx : i < n}  : (a.CycleMinVector k)[i] ≤ i := by
  induction k generalizing a i with | zero => _ | succ k IH => _
  · simp_rw [getElem_cycleMinVector_zero, le_rfl]
  · simp_rw [getElem_cycleMinVector_succ, min_le_iff, IH, true_or]

@[simp] theorem getElem_one_cycleMinVector {k i : ℕ} (hi : i < n) :
    ((1 : PermOf n).CycleMinVector k)[i] = i := by
  induction k generalizing n i with | zero => _ | succ k IH => _
  · simp_rw [getElem_cycleMinVector_zero]
  · simp_rw [getElem_cycleMinVector_succ, one_pow, getElem_one, IH, min_self]

theorem one_cycleMinVector {k : ℕ} : (1 : PermOf n).CycleMinVector k = Vector.range n := by
  ext i hi
  simp_rw [getElem_one_cycleMinVector, Vector.getElem_range]

@[simp]
theorem getElem_cycleMinVector_lt (a : PermOf n) {i : ℕ} {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] < n := by
  induction' i with i IH generalizing x
  · simp_rw [getElem_cycleMinVector_zero]
    exact hx
  · simp_rw [getElem_cycleMinVector_succ, min_lt_iff, IH, true_or]

theorem min_getElem_cycleMinVector_getElem_cycleMinVector_getElem (a : PermOf n)
    {i x : ℕ} (hx : x < n) :
    min x ((a.CycleMinVector i)[a[x]]) = min (a.CycleMinVector i)[x] ((a^2^i)[x]) := by
  induction i generalizing a x with | zero => _ | succ i IH => _
  · simp_rw [getElem_cycleMinVector_zero, pow_zero, pow_one]
  · simp_rw [getElem_cycleMinVector_succ, ← min_assoc, IH, min_assoc, ← getElem_mul, pow_mul_comm',
      getElem_mul, IH, ← getElem_mul, ← pow_add, ← two_mul, ← pow_succ']

theorem getElem_cycleMinVector_eq_min'_getElem_pow_image_range (a : PermOf n)
    {i x : ℕ} (hx : x < n) :
    (a.CycleMinVector i)[x] =
    ((Finset.range (2^i)).image (fun k => (a ^ k)[x])).min'
      (Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.two_pow_pos i).ne')) := by
  induction i generalizing a x with | zero => _ | succ i IH => _
  · simp_rw [getElem_cycleMinVector_zero, pow_zero, Finset.range_one, Finset.image_singleton,
      pow_zero, getElem_one, Finset.min'_singleton]
  · simp_rw [getElem_cycleMinVector_succ, IH, le_antisymm_iff, getElem_pow_add,
      le_inf_iff, Finset.le_min'_iff, inf_le_iff, Finset.mem_image, Finset.mem_range,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine ⟨fun k hk => (lt_or_le k (2^i)).imp
      (fun hk' => Finset.min'_le _ _ ?_) (fun hk' => Finset.min'_le _ _ ?_),
      fun k hk => Finset.min'_le _ _ ?_, fun k hk => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [Finset.mem_image, Finset.mem_range]
    exacts [⟨k, hk', rfl⟩,
      ⟨k - 2^i, Nat.sub_lt_right_of_lt_add hk' (Nat.two_mul _ ▸ Nat.pow_succ' ▸ hk),
        (Nat.sub_add_cancel hk').symm ▸ rfl⟩,
      ⟨k, hk.trans (Nat.pow_lt_pow_of_lt one_lt_two (Nat.lt_succ_self _)), rfl⟩,
      ⟨k + 2^i, (Nat.pow_succ' ▸ Nat.two_mul _ ▸ (Nat.add_lt_add_right hk _)), rfl⟩]

lemma getElem_cycleMinVector_le_getElem_pow_lt (a : PermOf n) {i : ℕ} {x : ℕ}
    {k : ℕ} (hk : k < 2^i) (hx : x < n) :
    (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range]
  refine Finset.min'_le _ _ ?_
  simp_rw [Finset.mem_image, Finset.mem_range]
  exact ⟨k, hk, rfl⟩

lemma getElem_cycleMinVector_le (a : PermOf n) {i : ℕ} {x y : ℕ}
    {hx : x < n} (hk : ∃ k < 2^i, y = (a ^ k)[x]) :
    (a.CycleMinVector i)[x] ≤ y :=
  hk.choose_spec.2 ▸ a.getElem_cycleMinVector_le_getElem_pow_lt hk.choose_spec.1 _

lemma exists_lt_getElem_cycleMin_eq_getElem_pow (a : PermOf n) (i : ℕ) {x : ℕ}
      (hx : x < n) :
    ∃ k < 2^i, (a.CycleMinVector i)[x] = (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range]
  have H := Finset.min'_mem ((Finset.range (2^i)).image (fun k => (a ^ k)[x]))
    (Finset.image_nonempty.mpr (Finset.nonempty_range_iff.mpr (Nat.two_pow_pos i).ne'))
  simp_rw [Finset.mem_image, Finset.mem_range] at H
  exact ⟨H.choose, H.choose_spec.1, H.choose_spec.2.symm⟩

lemma le_getElem_cycleMin_iff (a : PermOf n) (i : ℕ) {x y : ℕ}
      (hx : x < n) :
    y ≤ (a.CycleMinVector i)[x] ↔ ∀ k < 2^i, y ≤ (a ^ k)[x] := by
  simp_rw [getElem_cycleMinVector_eq_min'_getElem_pow_image_range, Finset.le_min'_iff,
    Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

@[simp] theorem getElem_cycleMinVector_of_self_le_getElem {a : PermOf n} {k i : ℕ}
    {hx : i < n} (hxa : ∀ k, i ≤ (a^k)[i]) : (a.CycleMinVector k)[i] = i := by
  simp_rw [le_antisymm_iff, le_getElem_cycleMin_iff, hxa,
    getElem_cycleMinVector_le_self, implies_true, and_self]

@[simp] theorem getElem_zero_cycleMinVector [NeZero n]
    {a : PermOf n} {k : ℕ} : (a.CycleMinVector k)[0]'(NeZero.pos _) = 0 :=
  getElem_cycleMinVector_of_self_le_getElem (fun _ => zero_le _)

lemma getElem_cycleMinVector_eq_min'_cycleOf (a : PermOf n) {i : ℕ} {x : ℕ}
      (hai : MulAction.period a x ≤ 2^i) (hx : x < n) :
      (a.CycleMinVector i)[x] = (a.cycleOf x).min' a.nonempty_cycleOf := by
  refine le_antisymm (getElem_cycleMinVector_le _ ?_) (Finset.min'_le _ _ ?_)
  · have H := Finset.min'_mem (a.cycleOf x) a.nonempty_cycleOf
    simp_rw [mem_cycleOf_iff_exists_getElem_pow_lt_period _ hx] at H
    exact ⟨H.choose, H.choose_spec.1.trans_le hai, H.choose_spec.2.symm⟩
  · simp_rw [a.mem_cycleOf_iff_exists_getElem_pow hx]
    exact ⟨(a.exists_lt_getElem_cycleMin_eq_getElem_pow i hx).choose,
    ((a.exists_lt_getElem_cycleMin_eq_getElem_pow i hx).choose_spec).2.symm⟩

lemma getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow (a : PermOf n) {i : ℕ} {x : ℕ}
    (hx : x < n) (hai : MulAction.period a x ≤ 2^i) :
    ∀ k, (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := fun k => by
  simp_rw [a.getElem_cycleMinVector_eq_min'_cycleOf hai,
    Finset.min'_le _ _ (a.getElem_pow_mem_cycleOf hx k)]

lemma getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow (a : PermOf n) {i : ℕ} {x : ℕ}
      (hx : x < n) (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, (a.CycleMinVector i)[x] ≤ (a ^ k)[x] := fun k => by
  simp_rw [a.getElem_cycleMinVector_eq_min'_cycleOf hai,
    Finset.min'_le _ _ (a.getElem_zpow_mem_cycleOf hx k)]

lemma cycleMinVector_eq_apply_cycleMinVector (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : ∀ {x : ℕ}, MulAction.period a x ≤ 2^i) (hx : x < n) :
   (a.CycleMinVector i)[x] = (a.CycleMinVector i)[a[x]] := by
  simp_rw [getElem_cycleMinVector_eq_min'_cycleOf _ hai, le_antisymm_iff, Finset.le_min'_iff]
  refine ⟨fun y hy => Finset.min'_le _ _ ?_, fun y hy => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hx,
      mem_cycleOf_iff_exists_getElem_zpow _ (getElem_lt _)] at hy ⊢
  exacts [⟨hy.choose + 1, zpow_add_one a _ ▸ getElem_mul _ _ _ ▸ hy.choose_spec⟩,
      ⟨hy.choose - 1, zpow_sub_one a _ ▸ getElem_mul _ _ _ ▸
      inv_mul_cancel_right _ a ▸ hy.choose_spec⟩]

def CycleMin (a : PermOf n) (i : ℕ) (x : ℕ) : ℕ := (a.CycleMinVector i)[x]?.getD x

theorem getElem_cycleMinVector (a : PermOf n) (i : ℕ) {x : ℕ}
    (hx : x < n) : (a.CycleMinVector i)[x] = a.CycleMin i x :=
  (Vector.getD_of_lt _ _ _ _).symm

theorem cycleMin_of_lt (a : PermOf n) {i x : ℕ} (hx : x < n) :
    a.CycleMin i x = (a.CycleMinVector i)[x] := Vector.getD_of_lt _ _ _ _

theorem cycleMin_of_getElem {a b : PermOf n} {i x : ℕ} (hx : x < n) :
    a.CycleMin i (b[x]) = (a.CycleMinVector i)[b[x]] :=
  Vector.getD_of_lt _ _ _ _

theorem cycleMin_of_ge (a : PermOf n) {i x : ℕ} (hx : n ≤ x) :
    a.CycleMin i x = x := Vector.getD_of_ge _ _ _ hx

@[simp] theorem one_cycleMin {k x : ℕ} : (1 : PermOf n).CycleMin k x = x := by
  rcases lt_or_le x n with hx | hx
  · rw [cycleMin_of_lt _ hx, one_cycleMinVector, Vector.getElem_range]
  · rwa [cycleMin_of_ge]

@[simp]
theorem cycleMin_zero (a : PermOf n) {x : ℕ} :
  a.CycleMin 0 x = x := if hx : x < n then
    (a.cycleMin_of_lt hx).trans <| Array.getElem_range _ else a.cycleMin_of_ge (le_of_not_lt hx)

@[simp]
theorem cycleMin_succ (a : PermOf n) {i x : ℕ} :
    a.CycleMin (i + 1) x = min (a.CycleMin i x) (a.CycleMin i (a^2^i • x)) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [smul_of_lt _ hx, a.cycleMin_of_lt hx, cycleMin_of_getElem, getElem_cycleMinVector_succ]
  · simp_rw [smul_of_ge _ hx, a.cycleMin_of_ge hx, min_self]

@[simp]
theorem cycleMin_lt_iff_lt (a : PermOf n) {i : ℕ} {x : ℕ} :
    a.CycleMin i x < n ↔ x < n := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, hx, getElem_cycleMinVector_lt]
  · simp_rw [a.cycleMin_of_ge hx]

lemma cycleMin_le_smul_pow_lt_two_pow (a : PermOf n) {i : ℕ} (x : ℕ) {k : ℕ} (hk : k < 2^i) :
    a.CycleMin i x ≤ (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_pow_lt _ hk _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_pow_smul_of_period_le_two_pow (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) : ∀ k, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_pow_of_period_le_two_pow _ _ hai _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_zpow_smul_of_period_le_two_pow  (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    ∀ k : ℤ, a.CycleMin i x ≤ (a ^ k) • x := fun k => by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact getElem_cycleMinVector_le_getElem_zpow_of_period_le_two_pow _ _ hai _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx, le_rfl]

lemma cycleMin_le_self (a : PermOf n) (i : ℕ) {x : ℕ} :
    a.CycleMin i x ≤ x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx]
    exact getElem_cycleMinVector_le_self
  · simp_rw [a.cycleMin_of_ge hx, le_rfl]

lemma exists_lt_cycleMin_eq_smul_pow (a : PermOf n) (i : ℕ) {x : ℕ} :
    ∃ k < 2^i, a.CycleMin i x = (a ^ k) • x := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx, smul_of_lt _ hx]
    exact exists_lt_getElem_cycleMin_eq_getElem_pow _ _ _
  · simp_rw [a.cycleMin_of_ge hx, smul_of_ge _ hx]
    exact ⟨0, Nat.two_pow_pos _, trivial⟩

lemma cycleMin_eq_min'_cycleOf (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : MulAction.period a x ≤ 2^i) :
    a.CycleMin i x = (a.cycleOf x).min' a.nonempty_cycleOf := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [a.cycleMin_of_lt hx]
    exact getElem_cycleMinVector_eq_min'_cycleOf _  hai _
  · simp_rw [a.cycleMin_of_ge hx, a.cycleOf_ge hx]
    exact rfl

lemma cycleMin_eq_apply_cycleMin (a : PermOf n) (i : ℕ) {x : ℕ}
    (hai : ∀ {x : ℕ}, MulAction.period a x ≤ 2^i) :
    a.CycleMin i x = a.CycleMin i (a • x) := by
  rcases lt_or_le x n with hx | hx
  · simp_rw [cycleMin_eq_min'_cycleOf _ _ hai, le_antisymm_iff, Finset.le_min'_iff]
    refine ⟨fun y hy => Finset.min'_le _ _ ?_, fun y hy => Finset.min'_le _ _ ?_⟩ <;>
    simp_rw [mem_cycleOf_iff_exists_getElem_zpow _ hx,
      mem_cycleOf_iff_exists_getElem_zpow _ (a.smul_lt_of_lt hx), a.smul_of_lt hx] at hy ⊢
    exacts [⟨hy.choose + 1, zpow_add_one a _ ▸ getElem_mul _ _ _ ▸ hy.choose_spec⟩,
      ⟨hy.choose - 1, zpow_sub_one a _ ▸ getElem_mul _ _ _ ▸
      inv_mul_cancel_right _ a ▸ hy.choose_spec⟩]
  · simp_rw [a.cycleMin_of_ge hx]
    rw [a.cycleMin_of_ge (le_of_not_lt (a.lt_of_smul_lt.mt hx.not_lt)), a.smul_of_ge hx]

section Cast

variable {m n o : ℕ}

/--
`PermOf.cast` re-interprets an `PermOf n` as an `PermOf m`, where `n = m`.
-/
def cast (hnm : n = m) (a : PermOf n) : PermOf m where
  fwdVector := a.fwdVector.cast hnm
  bwdVector := a.bwdVector.cast hnm
  getElem_fwdVector_lt := fun _ => by
    simp_rw [Vector.getElem_cast, hnm.symm, getElem_fwdVector, getElem_lt]
  getElem_bwdVector_getElem_fwdVector :=
    fun hi => a.getElem_inv_getElem (hi.trans_eq hnm.symm)

@[simp]
theorem getElem_cast (hnm : n = m) (a : PermOf n) {i : ℕ} (hi : i < m):
    (a.cast hnm)[i] = a[i] := rfl

@[simp]
theorem getElem_inv_cast (hnm : n = m) (a : PermOf n) {i : ℕ} (hi : i < m):
    (a.cast hnm)⁻¹[i] = a⁻¹[i] := rfl

@[simp]
theorem cast_smul (hnm : n = m) (a : PermOf n) (i : ℕ) :
    (a.cast hnm) • i = a • i := by simp only [smul_nat_def, getElem?_def, getElem_cast, hnm]

@[simp] theorem cast_one (hnm : n = m) : (1 : PermOf n).cast hnm = 1 := by
  ext
  simp_rw [getElem_cast, getElem_one]

@[simp] theorem cast_eq_iff (hnm : n = m) {a : PermOf n} {b : PermOf m} :
    a.cast hnm = b ↔ a = b.cast hnm.symm := by
  simp_rw [PermOf.ext_iff, getElem_cast, hnm]

theorem cast_eq_one_iff (hnm : n = m) (a : PermOf n) : a.cast hnm = 1 ↔ a = 1 := by
  simp_rw [cast_eq_iff, cast_one]

@[simp]
theorem cast_inv (hnm : n = m) (a : PermOf n) :
    a⁻¹.cast hnm = (a.cast hnm)⁻¹ := rfl

@[simp]
theorem cast_mul (hnm : n = m) (a b : PermOf n) :
    (a * b).cast hnm = a.cast hnm * b.cast hnm := ext <| fun hi => by
  simp only [getElem_cast, getElem_mul]

theorem cast_eq_cast (hnm : n = m) (a : PermOf n) :
    hnm ▸ a = a.cast hnm := by cases hnm ; rfl

@[simp] theorem cast_symm {hnm : n = m} {hmb : m = n} (a : PermOf n) :
    (a.cast hnm).cast hmb = a := rfl

@[simp] theorem cast_trans {hnm : n = m} {hmo : m = o} (a : PermOf n) :
    (a.cast hnm).cast hmo = a.cast (hnm.trans hmo) := rfl

theorem cast_inj {a b : PermOf n} {hnm : n = m} : a.cast hnm = b.cast hnm ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [PermOf.ext_iff, getElem_cast]
  refine fun H _ hi => ?_
  exact H (hnm ▸ hi)

theorem cast_injective (h : n = m) : Function.Injective (cast h) := fun _ _ => cast_inj.mp

theorem cast_surjective (h : n = m) : Function.Surjective (cast h) :=
  fun a => ⟨a.cast h.symm, a.cast_symm⟩

/--
When `n = m`, `PermOf n` is multiplicatively equivalent to `PermOf m`.
-/

@[simps! apply symm_apply]
def castMulEquiv (hnm : n = m) : PermOf n ≃* PermOf m where
  toFun := cast hnm
  invFun := cast hnm.symm
  left_inv a := a.cast_symm
  right_inv a := a.cast_symm
  map_mul' := cast_mul hnm

@[simp] theorem cast_left_equiv_def {n' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n = m} :
    (a.cast hnm).equiv b ↔ a.equiv b := by
  simp_rw [equiv_iff_smul_eq, cast_smul]

@[simp] theorem cast_right_equiv_def {n' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n' = m} :
    a.equiv (b.cast hnm) ↔ a.equiv b := by
  simp_rw [equiv_iff_smul_eq, cast_smul]

@[simp] theorem cast_equiv_cast_iff_equiv {n' m' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n = m} {hnm' : n' = m'} :
    (a.cast hnm).equiv (b.cast hnm') ↔ a.equiv b := by
  simp_rw [cast_left_equiv_def, cast_right_equiv_def]

theorem cast_equiv_cast {k : ℕ}  {a : PermOf n} {hnm : n = m} {hnk : n = k} :
    (a.cast hnk).equiv (a.cast hnm) := by
  simp_rw [cast_equiv_cast_iff_equiv, equiv_iff_eq]


end Cast

def castGE {m n : ℕ} (hnm : n ≤ m) (a : PermOf n) : PermOf m where
  fwdVector := (a.fwdVector ++ (Vector.range (m - n)).map (· + n)).cast (Nat.add_sub_cancel' hnm)
  bwdVector := (a.bwdVector ++ (Vector.range (m - n)).map (· + n)).cast (Nat.add_sub_cancel' hnm)
  getElem_fwdVector_lt := fun {i} him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_append, getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range]
    rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true]
      exact a.getElem_lt.trans_le hnm
    · simp_rw [hin.not_lt, dite_false, Nat.sub_add_cancel hin, him]
  getElem_bwdVector_getElem_fwdVector := fun {i} him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_append, getElem_fwdVector, Vector.getElem_map,
      Vector.getElem_range, getElem_bwdVector]
    rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true, a.getElem_lt, dite_true, getElem_inv_getElem]
    · simp_rw [hin.not_lt, dite_false, Nat.sub_add_cancel hin, hin.not_lt, dite_false]

section CastGE

variable {n m k i : ℕ} {a : PermOf n}

theorem getElem_castGE {i : ℕ} {hi : i < m} {hnm : n ≤ m} :
    (a.castGE hnm)[i] = if hi : i < n then a[i] else i := by
  unfold castGE
  simp_rw [getElem_mk, Vector.getElem_cast, Vector.getElem_append, getElem_fwdVector,
    Vector.getElem_map, Vector.getElem_range]
  exact dite_congr rfl (fun _ => rfl) (fun hin => Nat.sub_add_cancel (le_of_not_lt hin))

@[simp]
theorem getElem_castGE_of_lt {hnm : n ≤ m} {i : ℕ} (hi : i < n) :
    (a.castGE hnm)[i] = a[i] := by
  simp_rw [getElem_castGE, hi, dite_true]

@[simp]
theorem getElem_castGE_of_ge {hnm : n ≤ m} {i : ℕ} (hi : n ≤ i) {h : i < m} :
    (a.castGE hnm)[i] = i := by
  simp_rw [getElem_castGE, hi.not_lt, dite_false]

@[simp]
theorem castGE_inv {hnm : n ≤ m} :
    a⁻¹.castGE hnm = (a.castGE hnm)⁻¹ := rfl

theorem getElem_inv_castGE (hnm : n ≤ m) {i : ℕ} {hi : i < m} :
    (a.castGE hnm)⁻¹[i] = if hi : i < n then a⁻¹[i] else i :=
  a.castGE_inv ▸ a⁻¹.getElem_castGE

@[simp]
theorem castGE_one {hnm : n ≤ m} : ((1 : PermOf n).castGE hnm) = 1 := by
  ext i hi : 1
  simp_rw [getElem_castGE, getElem_one, dite_eq_ite, ite_self]

@[simp]
theorem castGE_mul (hnm : n ≤ m) {a b : PermOf n} :
    (a * b).castGE hnm = a.castGE hnm * b.castGE hnm := by
  ext i
  simp_rw [getElem_castGE, getElem_mul, getElem_castGE]
  rcases lt_or_le i n with hi | hi
  · simp only [hi, dite_true, getElem_lt]
  · simp only [hi.not_lt, dite_false]


@[simp] theorem castGE_of_eq (hnm : n = m) (hnm' : n ≤ m := hnm.le) :
    a.castGE hnm' = a.cast hnm := by
  ext i hi
  simp_rw [getElem_castGE, getElem_cast, hi.trans_eq hnm.symm, dite_true]

@[simp] theorem castGE_trans {hnm : n ≤ m} {hmk : m ≤ k} :
    (a.castGE hnm).castGE hmk = a.castGE (hnm.trans hmk) := by
  ext i hi
  simp_rw [getElem_castGE]
  rcases lt_or_le i m with him | him
  · simp_rw [him, dite_true]
  · simp_rw [him.not_lt, (hnm.trans him).not_lt, dite_false]


theorem castGE_mul_castGE_of_le {m : ℕ} {b : PermOf m} (hnm : n ≤ m) :
    (a.castGE (le_max_left _ _)) * (b.castGE (le_max_right _ _)) =
    ((a.castGE hnm) * b).castGE (le_max_right _ _) := by
  ext
  simp only [getElem_mul, castGE_mul, castGE_trans]

theorem castGE_mul_castGE_of_ge {m : ℕ} {b : PermOf m} (hmn : m ≤ n) :
    (a.castGE (le_max_left _ _)) * (b.castGE (le_max_right _ _)) =
    (a * b.castGE hmn).castGE (le_max_left _ _) := by
  ext
  simp only [getElem_mul, castGE_mul, castGE_trans]

theorem fixLT_castGE {hnm : n ≤ m} (hnk : n ≤ k) : (a.castGE hnm).FixLT k :=
  fixLT_of_lt_imp_getElem_lt (fun hik => by
    simp_rw [getElem_castGE]
    split_ifs with hin
    · exact a.getElem_lt.trans_le hnk
    · exact hik)

theorem fixLT_castGE_eq {hnm : n ≤ m} : (a.castGE hnm).FixLT n := a.fixLT_castGE le_rfl

theorem castGE_mem_fixLTSubgroup {hnm : n ≤ m} (hnk : n ≤ k) :
    (a.castGE hnm) ∈ fixLTSubgroup m k := a.fixLT_castGE hnk

theorem castGE_mem_fixLTSubgroup_eq {hnm : n ≤ m} :
    (a.castGE hnm) ∈ fixLTSubgroup m n := a.fixLT_castGE_eq

theorem castLE_lt_imp_getElem_lt {hnm : n ≤ m} (him : i < n) : (a.castGE hnm)[i] < n := by
  simp_rw [getElem_castGE, him, dite_true]
  exact a.getElem_lt

theorem castGE_inj {a b : PermOf n} {hnm : n ≤ m} : castGE hnm a = castGE hnm b ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [PermOf.ext_iff, getElem_castGE]
  refine fun H _ hi => ?_
  specialize H (hi.trans_le hnm)
  simp_rw [hi, dite_true] at H
  exact H

theorem castGE_injective (hnm : n ≤ m) : Function.Injective (castGE hnm) :=
  fun _ _ => castGE_inj.mp

@[simps! apply_coe]
def castGEMonoidHom (hnm : n ≤ m) : PermOf n →* fixLTSubgroup m n where
  toFun a := ⟨a.castGE hnm, a.castGE_mem_fixLTSubgroup_eq⟩
  map_mul' := fun _ _ => Subtype.ext (castGE_mul hnm)
  map_one' := Subtype.ext <| by simp_rw [castGE_one, Subgroup.coe_one]

theorem castGEMonoidHom_injective {hnm : n ≤ m} :
    (⇑(castGEMonoidHom hnm)).Injective :=
  fun _ _ h => castGE_injective hnm (Subtype.ext_iff.mp h)

@[simp]
theorem castGE_smul {i : ℕ} {hnm : n ≤ m} :
    (a.castGE hnm) • i = a • i := by
  simp_rw [smul_nat_eq_dite, getElem_castGE, dite_eq_ite, ite_eq_left_iff, not_lt]
  intro hmi
  simp_rw [(hnm.trans hmi).not_lt, dite_false]

@[simp] theorem castGE_equiv {hnm : n ≤ m} :
    (a.castGE hnm).equiv a := by
  simp_rw [equiv_iff_smul_eq, castGE_smul, implies_true]

@[simp] theorem equiv_castGE {hnm : n ≤ m} : a.equiv (a.castGE hnm) :=
  castGE_equiv.symm

@[simp] theorem castGE_equiv_castGE_iff_equiv {n' m' : ℕ} {b : PermOf n'}
    {hnm : n ≤ m} {hnm' : n' ≤ m'} :
    (a.castGE hnm).equiv (b.castGE hnm') ↔ a.equiv b := by
  simp_rw [equiv_iff_smul_eq, castGE_smul]

theorem castGE_equiv_castGE {hnm : n ≤ m} {hnk : n ≤ k} :
    (a.castGE hnk).equiv (a.castGE hnm) := by
  simp_rw [castGE_equiv_castGE_iff_equiv, equiv_iff_eq]

theorem equiv_iff_eq_castGE_of_le {b : PermOf m} (hnm : n ≤ m) :
    a.equiv b ↔ b = a.castGE hnm := by
  simp_rw [PermOf.ext_iff, getElem_castGE]
  simp_rw [equiv_iff_smul_eq_of_lt, max_eq_left hnm, smul_nat_eq_dite]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · intro i hi
    have H :=  dif_pos hi ▸ h hi
    exact H.symm
  · intro i hi
    have H := h hi
    simp_rw [hi, dite_true, H]

theorem equiv_iff_eq_castGE_of_ge {b : PermOf m} (hmn : m ≤ n) :
    a.equiv b ↔ a = b.castGE hmn := by
  rw [equiv_comm, equiv_iff_eq_castGE_of_le hmn]

end CastGE

def castLE {m n : ℕ} (hmn : m ≤ n) (a : PermOf n) (ham : a.FixLT m) : PermOf m where
  fwdVector := (a.fwdVector.take m).cast (min_eq_left hmn)
  bwdVector := (a.bwdVector.take m).cast (min_eq_left hmn)
  getElem_fwdVector_lt := fun him => by
    simp_rw [Vector.getElem_cast, Vector.getElem_take, getElem_fwdVector, ham.getElem_lt_of_lt him]
  getElem_bwdVector_getElem_fwdVector := fun _ => by
    simp_rw [Vector.getElem_cast, Vector.getElem_take, getElem_bwdVector_getElem_fwdVector]

section CastLE

variable {m i k : ℕ} (a : PermOf n) (ham : a.FixLT m) {hmn : m ≤ n}

@[simp] theorem getElem_castLE (him : i < m) :
    (a.castLE hmn ham)[i] = a[i] := by
  unfold castLE
  simp_rw [getElem_mk, Vector.getElem_cast, Vector.getElem_take, getElem_fwdVector]

@[simp] theorem castLE_inv : a⁻¹.castLE hmn ham.inv = (a.castLE hmn ham)⁻¹ := rfl

theorem getElem_inv_castLE (him : i < m) :
    (a.castLE hmn ham)⁻¹[i] = a⁻¹[i]  := by
  simp_rw [← castLE_inv, getElem_castLE]

@[simp]
theorem castLE_one : ((1 : PermOf n).castLE hmn fixLT_one) = (1 : PermOf m) := by
  ext i hi : 1
  simp_rw [getElem_castLE, getElem_one]

@[simp]
theorem castLE_mul (hmn : m ≤ n) {a b : PermOf n} (ham : a.FixLT m) (hbm : b.FixLT m) :
    (a * b).castLE hmn (ham.mul hbm) = a.castLE hmn ham * b.castLE hmn hbm := by
  ext i
  simp only [getElem_mul, getElem_castLE]

@[simp] theorem castLE_of_eq {a : PermOf n} (ham : a.FixLT m) (hnm : n = m)
    (hnm' : m ≤ n := hnm.ge) : a.castLE hnm' ham = a.cast hnm := by
  ext i hi
  simp_rw [getElem_castLE, getElem_cast]

theorem FixLT.castLE {a : PermOf n} (ham : a.FixLT m) {hkn : k ≤ n} {hak : a.FixLT k} :
    (a.castLE hkn hak).FixLT m := fixLT_of_lt_imp_getElem_lt (fun hik => by
    simp_rw [getElem_castLE]
    exact ham.getElem_lt_of_lt hik)

@[simp] theorem castLE_trans {a : PermOf n} (ham : a.FixLT m) {hkn : k ≤ n} {hmk : m ≤ k}
    (hak : a.FixLT k) :
    (a.castLE hkn hak).castLE hmk ham.castLE = a.castLE (hmk.trans hkn) ham := by
  ext i hi
  simp_rw [getElem_castLE]

theorem castLE_castGE {hnm : n ≤ m} :
    (a.castGE hnm).castLE hnm a.fixLT_castGE_eq = a := by
  ext i hi
  simp_rw [getElem_castLE, a.getElem_castGE_of_lt hi]

theorem getElem_castGE_castLE_of_lt (hi : i < m) : ((a.castLE hmn ham).castGE hmn)[i] = a[i] := by
  simp_rw [getElem_castGE_of_lt hi, getElem_castLE]

theorem castLE_surjective (hmn : m ≤ n) (b : PermOf m) :
    ∃ (a : PermOf n), ∃ (ham : a.FixLT m), a.castLE hmn ham = b := by
  exact ⟨_, _, b.castLE_castGE⟩

@[simps! apply]
def castLEMonoidHom (hmn : m ≤ n) : fixLTSubgroup n m →* PermOf m where
  toFun a := castLE hmn a.1 a.2
  map_mul' a b := castLE_mul hmn a.2 b.2
  map_one' := castLE_one

theorem castLEMonoidHom_surjective {hmn : m ≤ n} :
  (⇑(castLEMonoidHom hmn)).Surjective := fun a => Subtype.exists.mpr (a.castLE_surjective hmn)

theorem castLE_smul_of_lt {i : ℕ} (him : i < m) :
    (a.castLE hmn ham) • i = a • i := by
  simp_rw [smul_of_lt _ him, smul_of_lt _ (him.trans_le hmn), getElem_castLE]

end CastLE

def castSucc (a : PermOf n) : PermOf (n + 1) := a.castGE (Nat.le_succ _)

section CastSucc

variable {n m k i : ℕ} {a : PermOf n}

theorem getElem_castSucc {i : ℕ} {hi : i < n + 1} :
    (a.castSucc)[i] = if hi : i = n then n else a[i] := by
  unfold castSucc
  simp_rw [getElem_castGE, ← (Nat.le_of_lt_succ hi).ge_iff_eq]
  rcases lt_or_le i n with hi' | hi'
  · simp_rw [dif_pos hi', dif_neg hi'.not_le]
  · simp_rw [dif_pos hi', dif_neg hi'.not_lt, ← hi'.le_iff_eq, Nat.le_of_lt_succ hi]

@[simp]
theorem getElem_castSucc_of_lt {i : ℕ} (hi : i < n) :
    (a.castSucc)[i] = a[i] := by
  simp_rw [getElem_castSucc, hi.ne, dite_false]

@[simp] theorem getElem_castSucc_of_eq : (a.castSucc)[n] = n := by
  simp_rw [getElem_castSucc, dite_true]

@[simp]
theorem castSucc_inv :
    a⁻¹.castSucc = (a.castSucc)⁻¹ := rfl

theorem getElem_inv_castSucc {i : ℕ} {hi : i < n + 1} :
    (a.castSucc)⁻¹[i] = if hi : i = n then n else a⁻¹[i] :=
  a.castSucc_inv ▸ a⁻¹.getElem_castSucc

@[simp]
theorem castSucc_one : (1 : PermOf n).castSucc = 1 := castGE_one

@[simp]
theorem castSucc_mul {a b : PermOf n} :
    (a * b).castSucc = a.castSucc * b.castSucc := castGE_mul _

@[simp] theorem castSucc_castSucc :
    a.castSucc.castSucc = a.castGE (by omega) := castGE_trans

@[simp] theorem castGE_castSucc (h : n ≤ m) :
    (a.castGE h).castSucc = a.castGE (h.trans (Nat.le_succ _)) := castGE_trans

@[simp] theorem castSucc_castGE (h : n + 1 ≤ m) :
    a.castSucc.castGE h = a.castGE ((Nat.le_succ _).trans h) := castGE_trans

theorem fixLT_castSucc (hnk : n ≤ k) : a.castSucc.FixLT k := fixLT_castGE hnk

theorem fixLT_castSucc_eq : (a.castSucc).FixLT n := a.fixLT_castSucc le_rfl

theorem castSucc_mem_fixLTSubgroup (hnk : n ≤ k) :
    a.castSucc ∈ fixLTSubgroup (n + 1) k := a.fixLT_castGE hnk

theorem castSucc_mem_fixLTSubgroup_eq :
    a.castSucc ∈ fixLTSubgroup (n + 1) n := a.fixLT_castGE_eq

theorem castSucc_lt_imp_getElem_lt (hi : i < n) : (a.castSucc)[i] < n := by
  simp_rw [getElem_castSucc, hi.ne, dite_false]
  exact a.getElem_lt

theorem castSucc_inj {a b : PermOf n} : a.castSucc = b.castSucc ↔ a = b := castGE_inj

theorem castSucc_injective : Function.Injective (castSucc (n := n)) :=
  fun _ _ => castSucc_inj.mp

@[simps! apply_coe]
def castSuccMonoidHom : PermOf n →* fixLTSubgroup (n + 1) n where
  toFun a := ⟨a.castSucc, a.castSucc_mem_fixLTSubgroup_eq⟩
  map_mul' := fun _ _ => Subtype.ext castSucc_mul
  map_one' := Subtype.ext <| by simp_rw [castSucc_one, Subgroup.coe_one]

theorem castSuccMonoidHom_injective :
    (⇑(castSuccMonoidHom (n := n))).Injective :=
  fun _ _ h => castSucc_injective (Subtype.ext_iff.mp h)

@[simp]
theorem castSucc_smul {i : ℕ} :
    a.castSucc • i = a • i := castGE_smul

@[simp] theorem castSucc_equiv:
  a.castSucc.equiv a := by simp_rw [equiv_iff_smul_eq, castSucc_smul, implies_true]

@[simp] theorem equiv_castSucc : a.equiv a.castSucc :=
  castSucc_equiv.symm

@[simp] theorem castSucc_equiv_castSucc_iff_equiv {n' : ℕ} {b : PermOf n'} :
    a.castSucc.equiv b.castSucc ↔ a.equiv b := by
  simp_rw [equiv_iff_smul_eq, castSucc_smul]

theorem castSucc_equiv_castSucc :
    a.castSucc.equiv a.castSucc := by
  simp_rw [castSucc_equiv_castSucc_iff_equiv, equiv_iff_eq]

end CastSucc

def castPred (a : PermOf (n + 1)) (ha : a[n] = n) : PermOf n :=
    a.castLE (Nat.le_succ _) (a.fixLT_of_getElem_eq_self ha)

section CastPred

variable {m i k : ℕ} (a : PermOf (n + 1)) (ha : a[n] = n)

@[simp] theorem getElem_castPred (him : i < n) :
    (a.castPred ha)[i] = a[i] := getElem_castLE _ _ _

@[simp] theorem castPred_inv {ha : a⁻¹[n] = n} : a⁻¹.castPred ha =
    (a.castPred ((a.getElem_inv_eq_iff _ _).mp ha).symm)⁻¹ := rfl

theorem getElem_inv_castPred (hi : i < n) :
    (a.castPred ha)⁻¹[i] = a⁻¹[i]  := getElem_inv_castLE _ _ _

@[simp]
theorem castPred_one :
    ((1 : PermOf (n + 1)).castPred (getElem_one _)) = (1 : PermOf n) := castLE_one

@[simp]
theorem castPred_mul' {a b : PermOf (n + 1)} (hb : b[n] = n) {hab : (a * b)[n] = n} :
    (a * b).castPred hab =
    a.castPred (by simpa only [getElem_mul, hb] using hab) * b.castPred hb :=
  castLE_mul _ _ _

@[simp]
theorem castPred_mul {a b : PermOf (n + 1)} (ha : a[n] = n) (hb : b[n] = n) :
    (a * b).castPred (by simp_rw [getElem_mul, hb, ha]) = a.castPred ha * b.castPred hb :=
  castLE_mul _ _ _

theorem FixLT.castPred {a : PermOf (n + 1)} (ha : a[n] = n) {hak : a.FixLT m} :
    (a.castPred ha).FixLT m := FixLT.castLE hak

@[simp] theorem castPred_trans {a : PermOf (n + 2)} (ha₁ : a[n + 1] = n + 1)
    (ha₂ : a[n] = n) :
    (a.castPred ha₁).castPred (by simp_rw [getElem_castPred, ha₂]) =
    a.castLE (Nat.le_add_right _ _) (a.fixLT_of_getElem_eq_getElem_eq ha₁ ha₂):= castLE_trans _ _

@[simp] theorem castPred_castSucc {a : PermOf n} :
    a.castSucc.castPred getElem_castSucc_of_eq = a := castLE_castGE _

theorem getElem_castSucc_castPred_of_lt (hi : i < n) :
    ((a.castPred ha).castSucc)[i] = a[i] := getElem_castGE_castLE_of_lt _ _ hi

theorem castPred_surjective (b : PermOf n) :
    ∃ (a : PermOf (n + 1)), ∃ (ha : a[n] = n), a.castPred ha = b :=
  ⟨_, _, b.castPred_castSucc⟩

@[simps! apply]
def castPredMonoidHom : fixLTSubgroup (n + 1) n →* PermOf n where
  toFun  := fun ⟨a, h⟩ => a.castPred h.getElem_eq_self
  map_mul' a b := castPred_mul a.2.getElem_eq_self b.2.getElem_eq_self
  map_one' := by simp_rw [castPred_one]

theorem castPredMonoidHom_surjective :
  (⇑(castPredMonoidHom (n := n))).Surjective := fun a => Subtype.exists.mpr
    (by rcases a.castPred_surjective with ⟨b, hb, h⟩ ;
        exact ⟨b, fixLT_of_getElem_eq_self hb, h⟩)

theorem castPred_smul_of_lt {i : ℕ} (hi : i < n) :
    (a.castPred ha) • i = a • i := castLE_smul_of_lt _ _ hi

theorem castPred_smul_of_eq : (a.castPred ha) • n = a • n := by
  rw [smul_of_ge _ le_rfl, smul_of_lt _ (Nat.lt_succ_self _), ha]

@[simp] theorem castPred_equiv : (a.castPred ha).equiv a := by
  simp_rw [equiv_iff_smul_eq_of_lt, sup_of_le_left (Nat.le_succ _), Nat.lt_succ_iff,
    le_iff_eq_or_lt]
  rintro i (rfl | hi)
  · simp_rw [castPred_smul_of_eq]
  · exact castPred_smul_of_lt _ _ hi

@[simp] theorem equiv_castPred : a.equiv (a.castPred ha) :=
  (a.castPred_equiv ha).symm

theorem castPred_cast {hnm : n + 1 = m + 1} {ha : (cast hnm a)[m] = m} :
    (a.cast hnm).castPred ha =
    (a.castPred (by rw [getElem_cast] at ha ; simp_rw [Nat.succ_injective hnm, ha])).cast
    (Nat.succ_injective hnm) := by
  ext
  simp_rw [getElem_cast, getElem_castPred, getElem_cast]

end CastPred

def castOfFixLT {m n : ℕ} (a : PermOf n) (ham : a.FixLT m) :
    PermOf m where
  fwdVector := ((a.fwdVector.take m) ++ (Vector.range (m - n)).map (· + n)).cast
    (Nat.add_comm _ _ ▸ Nat.sub_add_min_cancel m n)
  bwdVector := ((a.bwdVector.take m) ++ (Vector.range (m - n)).map (· + n)).cast
    (Nat.add_comm _ _ ▸ Nat.sub_add_min_cancel m n)
  getElem_fwdVector_lt := fun {i} him => by
    simp_rw [Vector.getElem_cast]
    simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take, getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range, getElem_bwdVector, him, true_and]
    rcases lt_or_le m n with hmn | hmn
    · simp_rw [him.trans hmn, dite_true]
      exact ham.getElem_lt_of_lt him
    · rcases lt_or_le i n with hin | hin
      · simp_rw [hin, dite_true]
        exact a.getElem_lt.trans_le hmn
      · simp_rw [hin.not_lt, dite_false, min_eq_right hmn, Nat.sub_add_cancel hin, him]
  getElem_bwdVector_getElem_fwdVector := fun {i} him => by
    simp_rw [Vector.getElem_cast]
    simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take, getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range, getElem_bwdVector, him, true_and]
    rcases lt_or_le m n with hmn | hmn
    · simp_rw [him.trans hmn, dite_true, getElem_lt, and_true, getElem_inv_getElem,
        ham.getElem_lt_of_lt him, dite_true]
    · rcases lt_or_le i n with hin | hin
      · simp_rw [hin, dite_true, getElem_lt, and_true, getElem_inv_getElem,
          ham.getElem_lt_of_lt him, dite_true]
      · simp_rw [hin.not_lt, dite_false, min_eq_right hmn, Nat.sub_add_cancel hin,
          hin.not_lt, and_false, dite_false]

section CastOfFixLT

variable {m i : ℕ} (a : PermOf n) (ham : a.FixLT m)

@[simp] theorem getElem_castOfFixLT (him : i < m) :
    (a.castOfFixLT ham)[i] = if hin : i < n then a[i] else i := by
  unfold castOfFixLT
  simp_rw [getElem_mk, Vector.getElem_cast]
  simp only [Vector.getElem_append, lt_inf_iff, Vector.getElem_take, getElem_fwdVector,
      Vector.getElem_map, Vector.getElem_range, getElem_bwdVector, him, true_and]
  rcases lt_or_le m n with hmn | hmn
  · simp_rw [him.trans hmn, dite_true]
  · rcases lt_or_le i n with hin | hin
    · simp_rw [hin, dite_true]
    · simp_rw [hin.not_lt, dite_false, min_eq_right hmn, Nat.sub_add_cancel hin]

@[simp] theorem castOfSmulLtOfLt_inv :
    (a.castOfFixLT ham)⁻¹ = a⁻¹.castOfFixLT ham.inv := by
  ext
  unfold castOfFixLT
  simp_rw [getElem_inv_mk, inv_fwdVector, inv_bwdVector, getElem_mk]

theorem getElem_castOfFixLT_inv (him : i < m) :
    (a.castOfFixLT ham)⁻¹[i] = if hin : i < n then a⁻¹[i] else i := by
  simp_rw [castOfSmulLtOfLt_inv, getElem_castOfFixLT]

theorem castOfFixLT_eq_cast (hnm : n = m) :
    a.castOfFixLT ham = a.cast hnm := by
  ext _ hi
  simp_rw [getElem_castOfFixLT, getElem_cast, hnm ▸ hi, dite_true]

theorem castOfFixLT_eq_castGE (hnm : n ≤ m) :
    a.castOfFixLT ham = a.castGE hnm := by
  ext _ hi
  simp_rw [getElem_castOfFixLT, getElem_castGE]

theorem castOfFixLT_eq_castLT (hmn : m ≤ n) :
    a.castOfFixLT ham = a.castLE hmn ham := by
  ext _ hi
  simp_rw [getElem_castOfFixLT, getElem_castLE, hi.trans_le hmn, dite_true]

@[simp]
theorem castOfFixLT_one : ((1 : PermOf n).castOfFixLT fixLT_one) = (1 : PermOf m) := by
  ext i hi : 1
  simp_rw [getElem_castOfFixLT, getElem_one, dite_eq_ite, ite_self]

@[simp]
theorem castOfFixLT_mul {a b : PermOf n} (ham : a.FixLT m) (hbm : b.FixLT m)
    (habm := FixLT.mul ham hbm) :
    (a * b).castOfFixLT habm = a.castOfFixLT ham * b.castOfFixLT hbm := by
  ext i
  simp only [getElem_mul, getElem_castOfFixLT]
  rcases lt_or_le i n with hi | hi
  · simp only [hi, dite_true, getElem_lt]
  · simp only [hi.not_lt, dite_false]

theorem fixLT_castOfFixLT {a : PermOf n} {ha : a.FixLT m} :
    (a.castOfFixLT ha).FixLT n := fixLT_of_lt_imp_getElem_lt <| fun hi _ => by
  simp_rw [getElem_castOfFixLT, hi, dite_true, getElem_lt]

theorem FixLT.castOfFixLT_of_le {a : PermOf n} {ham : a.FixLT m} (hnm : n ≤ m) :
    (a.castOfFixLT ham).castOfFixLT fixLT_castOfFixLT = a := ext <| fun {i} hin => by
  simp_rw [getElem_castOfFixLT, dite_eq_ite, hin, dite_true, ite_eq_left_iff, not_lt]
  intro him
  exact (hnm.not_lt (him.trans_lt hin)).elim

theorem castOfFixLT_surjective_of_le (hmn : m ≤ n) {b : PermOf m} (hbm : b.FixLT n) :
    ∃ (a : PermOf n), ∃ (han : a.FixLT m), a.castOfFixLT han = b :=
  ⟨_, _, hbm.castOfFixLT_of_le hmn⟩

theorem castOfFixLT_inj_of_ge {a b : PermOf n} (hnm : n ≤ m) :
    a.castOfFixLT (a.fixLT_ge hnm) = b.castOfFixLT (b.fixLT_ge hnm) ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [PermOf.ext_iff, getElem_castOfFixLT]
  refine fun H _ hi => ?_
  specialize H (hi.trans_le hnm)
  simp_rw [hi, dite_true] at H
  exact H

theorem castOfFixLT_injective_of_ge (hnm : n ≤ m) :
    Function.Injective (fun (a : PermOf n) => a.castOfFixLT (a.fixLT_ge hnm)) :=
  fun _ _ => (castOfFixLT_inj_of_ge hnm).mp

theorem castOfFixLT_bijective_of_eq (hmn : m = n) :
    Function.Bijective (fun (a : PermOf n) =>
    (a.castOfFixLT (hmn ▸ a.fixLT_eq) : PermOf m)) :=
  ⟨castOfFixLT_injective_of_ge hmn.ge,
    fun b => ⟨_, (hmn ▸ b.fixLT_eq : b.FixLT n).castOfFixLT_of_le hmn.le⟩⟩

@[simps! apply_coe]
def castOfFixLTMonoidHom (n m : ℕ) : fixLTSubgroup n m →* fixLTSubgroup m n where
  toFun a := ⟨a.1.castOfFixLT a.2, fixLT_castOfFixLT⟩
  map_one' := Subtype.ext castOfFixLT_one
  map_mul' a b := Subtype.ext (castOfFixLT_mul a.2 b.2)

theorem castOfFixLTMonoidHom_surjective_of_le (hmn : m ≤ n) :
    Surjective (castOfFixLTMonoidHom n m) := fun b => by
  simp_rw [Subtype.exists, mem_fixLTSubgroup_iff, Subtype.ext_iff]
  exact castOfFixLT_surjective_of_le hmn b.2

theorem castOfFixLTMonoidHom_injective_of_ge (hnm : n ≤ m) :
    Injective (castOfFixLTMonoidHom n m) := fun a b => by
  simp_rw [Subtype.ext_iff, castOfFixLTMonoidHom_apply_coe,
    castOfFixLT_inj_of_ge hnm, imp_self]

theorem castOfFixLTMonoidHom_bijective_of_eq (hmn : m = n) :
    Bijective (castOfFixLTMonoidHom n m) :=
  ⟨castOfFixLTMonoidHom_injective_of_ge hmn.ge, castOfFixLTMonoidHom_surjective_of_le hmn.le⟩

@[simps! apply_coe symm_apply_coe]
def castOfFixLTMulEquivEq (hmn : m = n) : fixLTSubgroup n m ≃* fixLTSubgroup m n where
  toFun := castOfFixLTMonoidHom n m
  invFun := castOfFixLTMonoidHom m n
  left_inv a := Subtype.ext <| by
    simp_rw [castOfFixLTMonoidHom_apply_coe]
    exact FixLT.castOfFixLT_of_le hmn.ge
  right_inv a := Subtype.ext <| by
    simp_rw [castOfFixLTMonoidHom_apply_coe]
    exact FixLT.castOfFixLT_of_le hmn.le
  map_mul' a b := map_mul _ _ _

theorem castOfFixLT_smul_eq_smul_of_lt {i : ℕ} (hi : i < m) :
    (a.castOfFixLT ham) • i = a • i := by
  simp_rw [smul_of_lt _ hi, getElem_castOfFixLT]
  rcases lt_or_le i n with hin | hin
  · simp_rw [hin, dite_true, smul_of_lt _ hin]
  · simp_rw [hin.not_lt, dite_false, smul_of_ge _ hin]

end CastOfFixLT

def minLen {n : ℕ} (a : PermOf n) : ℕ := match n with
  | 0 => 0
  | (n + 1) => if ha : a[n] = n then (a.castPred ha).minLen else n + 1

section MinLen

@[simp] theorem minLen_zero {a : PermOf 0} : a.minLen = 0 := rfl

theorem minLen_succ {a : PermOf (n + 1)} :
    a.minLen = if ha : a[n] = n then (a.castPred ha).minLen else n + 1 := rfl

theorem minLen_succ_of_getElem_eq {a : PermOf (n + 1)} (ha : a[n] = n) :
    a.minLen = (a.castPred ha).minLen := by
  simp_rw [minLen_succ, ha, dite_true]

theorem minLen_succ_of_getElem_ne {a : PermOf (n + 1)} (ha : a[n] ≠ n) :
    a.minLen = n + 1 := by
  simp_rw [minLen_succ, ha, dite_false]

@[simp] theorem minLen_le {a : PermOf n} : a.minLen ≤ n := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero, le_rfl]
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha]
      exact IH.trans (Nat.le_succ _)
    · simp_rw [minLen_succ_of_getElem_ne ha, le_rfl]

@[simp] theorem succ_minLen_le_of_getElem_eq {a : PermOf (n + 1)} (ha : a[n] = n) :
    a.minLen ≤ n := by simp_rw [minLen_succ_of_getElem_eq ha, minLen_le]

theorem minLen_one : (1 : PermOf n).minLen = 0 := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · rw [minLen_succ_of_getElem_eq (getElem_one _), castPred_one, IH]


@[simp] theorem minLen_inv {a : PermOf n} : a⁻¹.minLen = a.minLen := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha,
        minLen_succ_of_getElem_eq (getElem_inv_eq_self_of_getElem_eq_self ha), castPred_inv, IH]
    · simp_rw [minLen_succ_of_getElem_ne ha,
        minLen_succ_of_getElem_ne (getElem_inv_ne_self_of_getElem_ne_self ha)]

@[simp] theorem minLen_cast {m : ℕ} {a : PermOf n} {hnm : n = m} :
    (a.cast hnm).minLen = a.minLen := by
  cases hnm
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · simp_rw [minLen_succ, getElem_cast, castPred_cast, IH]

theorem minLen_castPred {a : PermOf (n + 1)} {ha : a[n] = n} :
    (a.castPred ha).minLen = a.minLen := (minLen_succ_of_getElem_eq _).symm

@[simp] theorem minLen_castSucc {a : PermOf n} :
    a.castSucc.minLen = a.minLen := by
  rw [minLen_succ_of_getElem_eq (getElem_castSucc_of_eq), castPred_castSucc]

@[simp] theorem minLen_castGE {m : ℕ} {a : PermOf n} {hnm : n ≤ m} :
    (a.castGE hnm).minLen = a.minLen := by
  induction m generalizing n with | zero => _ | succ m IH => _
  · simp_rw [nonpos_iff_eq_zero] at hnm
    cases hnm
    simp_rw [minLen_zero]
  · rcases hnm.eq_or_lt with rfl | hnm
    · simp_rw [castGE_of_eq, minLen_cast]
    · simp_rw [Nat.lt_succ_iff] at hnm
      simp_rw [← castGE_castSucc hnm, minLen_castSucc, IH]

@[simp] theorem getElem_of_ge_minLen {a : PermOf n} {i : ℕ} (hi : a.minLen ≤ i) {hi' : i < n} :
    a[i] = i := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [not_lt_zero'] at hi'
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha] at hi
      simp_rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at hi'
      rcases hi' with hi' | rfl
      · exact ((a.getElem_castPred ha hi').symm).trans (IH hi)
      · exact ha
    · simp_rw [minLen_succ_of_getElem_ne ha] at hi
      exact (hi'.not_le hi).elim

theorem equiv.minLen_le {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.equiv b) : a.minLen ≤ m := by
  rcases Nat.le_or_le m n with hmn | hnm
  · simp_rw [equiv_iff_eq_castGE_of_ge hmn] at hab
    simp_rw [hab, minLen_castGE]
    exact b.minLen_le
  · exact (a.minLen_le).trans hnm

theorem equiv.minLen_le' {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : b.equiv a) : a.minLen ≤ m := hab.symm.minLen_le

end MinLen

def minPerm {n : ℕ} (a : PermOf n) : PermOf a.minLen := match n with
  | 0 => 1
  | (n + 1) =>
    if ha : a[n] = n
    then (a.castPred ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm
    else a.cast (minLen_succ_of_getElem_ne ha).symm

section MinPerm

@[simp] theorem minPerm_zero {a : PermOf 0} : a.minPerm = 1 := rfl

theorem minPerm_succ {a : PermOf (n + 1)} :
    a.minPerm = if ha : a[n] = n
    then (a.castPred ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm
    else a.cast (minLen_succ_of_getElem_ne ha).symm := rfl

@[simp] theorem minPerm_succ_of_getElem_eq {a : PermOf (n + 1)}  (ha : a[n] = n) :
    a.minPerm = (a.castPred ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm := by
  simp_rw [minPerm_succ, ha, dite_true]

@[simp] theorem minPerm_succ_of_getElem_ne {a : PermOf (n + 1)} (ha : a[n] ≠ n) :
    a.minPerm = a.cast (minLen_succ_of_getElem_ne ha).symm := by
  simp_rw [minPerm_succ, ha, dite_false]

@[simp] theorem getElem_minPerm {a : PermOf n} {i : ℕ} (hi : i < a.minLen) :
    (a.minPerm)[i] = a[i]'(hi.trans_le minLen_le) := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minPerm_zero, Unique.eq_default a, default_eq, getElem_one]
  · by_cases ha : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha, getElem_cast, IH, getElem_castPred]
    · simp_rw [minPerm_succ_of_getElem_ne ha, getElem_cast]

@[simp] theorem getElem_inv_minPerm {a : PermOf n} {i : ℕ} (hi : i < a.minLen) :
    (a.minPerm)⁻¹[i] = a⁻¹[i]'(hi.trans_le minLen_le) := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minPerm_zero, Unique.eq_default a, default_eq, inv_one, getElem_one]
  · by_cases ha : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha, getElem_inv_cast, IH, getElem_inv_castPred]
    · simp_rw [minPerm_succ_of_getElem_ne ha, getElem_inv_cast]

theorem minPerm_equiv {a : PermOf n} : a.minPerm.equiv a := by
  simp_rw [equiv_iff_getElem_eq_getElem_and_getElem_eq_of_le minLen_le,
    getElem_minPerm, implies_true, true_and]
  exact getElem_of_ge_minLen

theorem equiv_minPerm {a : PermOf n} : a.equiv a.minPerm :=
  minPerm_equiv.symm

@[simp] theorem minPerm_smul {a : PermOf n} {i : ℕ} :
    a.minPerm • i = a • i := by simp_rw [minPerm_equiv.smul_eq]

@[simp] theorem equiv_minPerm_right {a : PermOf n} {m : ℕ} {b : PermOf m} :
    a.equiv b.minPerm ↔ a.equiv b := by
  simp_rw [equiv_iff_smul_eq, minPerm_equiv.smul_eq]

@[simp] theorem equiv_minPerm_left {a : PermOf n} {m : ℕ} {b : PermOf m} :
    a.minPerm.equiv b ↔ a.equiv b := by
  simp_rw [equiv_iff_smul_eq, minPerm_equiv.smul_eq]

theorem equiv_minPerm_minPerm {a : PermOf n} {m : ℕ} {b : PermOf m} :
    a.minPerm.equiv b.minPerm ↔ a.equiv b := by
  simp_rw [equiv_minPerm_right, equiv_minPerm_left]

theorem equiv.minPerm_left {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.equiv b) : a.minPerm.equiv b :=
  equiv_minPerm_left.mpr hab

theorem equiv.minPerm_right {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.equiv b) : a.equiv b.minPerm :=
  equiv_minPerm_right.mpr hab

theorem equiv.minPerm_minPerm {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.equiv b) : a.minPerm.equiv b.minPerm :=
  equiv_minPerm_minPerm.mpr hab

theorem minPerm_one : (1 : PermOf n).minPerm = (1 : PermOf 0).cast minLen_one.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_one]

@[simp] theorem minPerm_inv {a : PermOf n} :
    a⁻¹.minPerm = a.minPerm⁻¹.cast minLen_inv.symm := by
  ext
  simp_rw [getElem_minPerm, cast_inv, getElem_inv_cast, getElem_inv_minPerm]

@[simp] theorem minPerm_cast {m : ℕ} {a : PermOf n} (hnm : n = m) :
    (a.cast hnm).minPerm = a.minPerm.cast minLen_cast.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_minPerm]

@[simp] theorem minPerm_castPred {a : PermOf (n + 1)} {ha : a[n] = n} :
    (a.castPred ha).minPerm = a.minPerm.cast (minLen_succ_of_getElem_eq _) := by
  ext
  simp_rw [getElem_minPerm, getElem_castPred, getElem_cast, getElem_minPerm]

@[simp] theorem minPerm_castSucc {a : PermOf n} :
    a.castSucc.minPerm = a.minPerm.cast minLen_castSucc.symm := by
  ext i hi
  simp_rw [minLen_castSucc] at hi
  simp_rw [getElem_minPerm, getElem_cast,
    getElem_castSucc_of_lt (hi.trans_le minLen_le), getElem_minPerm]

@[simp] theorem minPerm_castGE {m : ℕ} {a : PermOf n} (hnm : n ≤ m) :
    (a.castGE hnm).minPerm = a.minPerm.cast minLen_castGE.symm := by
  ext i hi
  simp_rw [minLen_castGE] at hi
  simp_rw [getElem_minPerm, getElem_cast,
    getElem_castGE_of_lt (hi.trans_le minLen_le), getElem_minPerm]

@[simp] theorem minLen_minPerm {a : PermOf n} : a.minPerm.minLen = a.minLen := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minPerm_zero, Unique.eq_default, Unique.default_eq (1 : PermOf 0)]
  · by_cases ha : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha, minLen_cast, IH, minLen_castPred]
    · simp_rw [minPerm_succ_of_getElem_ne ha, minLen_cast]

@[simp] theorem minPerm_minPerm {a : PermOf n} :
    a.minPerm.minPerm = a.minPerm.cast minLen_minPerm.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_minPerm]

theorem equiv.minLen_eq {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.equiv b) : a.minLen = b.minLen :=
  le_antisymm (minLen_minPerm ▸ hab.minPerm_minPerm.minLen_le)
    (minLen_minPerm ▸ hab.symm.minPerm_minPerm.minLen_le)

theorem equiv_minPerm_inv_inv_minPerm {a : PermOf n} : a⁻¹.minPerm.equiv (a.minPerm)⁻¹ := by
  simp_rw [equiv_minPerm_left, equiv_inv_inv_iff, equiv_minPerm_right, equiv_iff_eq]

end MinPerm

end PermOf

@[simps!]
instance SigmaPermOf : Setoid (Σ n, PermOf n) where
  r a b := a.2.equiv b.2
  iseqv := ⟨fun _ => PermOf.equiv.rfl, PermOf.equiv.symm, PermOf.equiv.trans⟩

namespace SigmaPermOf

open PermOf

theorem equiv_def {a b : Σ n, PermOf n} :
    a ≈ b ↔ a.2.equiv b.2 := Iff.rfl

instance {a b : (n : ℕ) × PermOf n} : Decidable (a ≈ b) :=
  decidable_of_decidable_of_iff equiv_def.symm

theorem sigma_eq_of_eq_of_equiv : ∀ {a b : Σ n, PermOf n}, a.1 = b.1 → a ≈ b → a = b
  | ⟨n, a⟩, ⟨m, b⟩, hab, heq => by
    dsimp only at hab
    subst hab
    simp_rw [equiv_def] at heq
    simpa using heq

theorem sigma_eq_iff_eq_of_equiv {a b : Σ n, PermOf n} : a = b ↔ a.1 = b.1 ∧ a ≈ b :=
  ⟨fun h => h ▸ ⟨rfl, Setoid.refl _⟩, fun h => sigma_eq_of_eq_of_equiv h.1 h.2⟩

instance : Mul (Σ n, PermOf n) where
  mul := fun ⟨n, a⟩ ⟨m, b⟩ =>
  ⟨max n m, (a.castGE (le_max_left _ _)) * (b.castGE (le_max_right _ _))⟩

theorem mul_eq_max_castGE {a b : Σ n, PermOf n} : a * b =
    ⟨max a.1 b.1, (a.2.castGE (le_max_left _ _)) * (b.2.castGE (le_max_right _ _))⟩ := rfl

instance : One (Σ n, PermOf n) where
  one := ⟨0, 1⟩

theorem one_eq_zero_one : (1 : Σ n, PermOf n) = ⟨0, 1⟩ := rfl

theorem equiv_one_iff_snd_eq_one {a : Σ n, PermOf n} :
    a ≈ 1 ↔ a.2 = 1 := by
  simp_rw [equiv_def, one_eq_zero_one, equiv_one_iff_eq_one]

instance : Inv (Σ n, PermOf n) where
  inv := fun ⟨_, a⟩ => ⟨_, a⁻¹⟩

theorem inv_eq_mk_inv {a : Σ n, PermOf n} : a⁻¹ = ⟨a.1, a.2⁻¹⟩ := rfl

instance : DivisionMonoid (Σ n, PermOf n) where
  mul_assoc := (fun ⟨n, a⟩ ⟨m, b⟩ ⟨l, c⟩ => by
    simp_rw [sigma_eq_iff_eq_of_equiv, mul_eq_max_castGE, max_assoc, true_and,
      equiv_def, castGE_mul, castGE_trans, mul_assoc]
    exact castGE_equiv_castGE.mul_mul
      (castGE_equiv_castGE.mul_mul castGE_equiv_castGE))
  one_mul := (fun ⟨n, a⟩ => by simp_rw [sigma_eq_iff_eq_of_equiv,
    mul_eq_max_castGE, one_eq_zero_one, Nat.zero_max, true_and,
    equiv_def, castGE_one, one_mul, castGE_equiv])
  mul_one := (fun ⟨n, a⟩ => by simp_rw [sigma_eq_iff_eq_of_equiv,
    mul_eq_max_castGE, one_eq_zero_one, Nat.max_zero, true_and,
    equiv_def, castGE_one, mul_one, castGE_equiv])
  inv_inv _ := rfl
  mul_inv_rev _ _ := by
    simp_rw [sigma_eq_iff_eq_of_equiv, mul_eq_max_castGE, inv_eq_mk_inv, equiv_def,
      equiv_iff_smul_eq, mul_inv_rev, mul_smul, inv_smul_eq_iff, castGE_smul,
      smul_inv_smul, implies_true, max_comm, and_true]
  inv_eq_of_mul _ _ := by
    simp_rw [sigma_eq_iff_eq_of_equiv, mul_eq_max_castGE, inv_eq_mk_inv, one_eq_zero_one,
      Nat.max_eq_zero_iff, and_imp, equiv_def, equiv_one_iff_eq_one, equiv_iff_smul_eq,
      eq_iff_smul_nat_eq_smul_nat, mul_smul, castGE_smul, one_smul, inv_smul_eq_iff]
    exact fun ha hb hab => ⟨ha.trans hb.symm, hab.symm⟩

theorem equiv_mul_mul_of_equiv_equiv {a b c d : Σ n, PermOf n} :
    a ≈ b → c ≈ d → a*c ≈ b*d := by
  simp_rw [equiv_def, mul_eq_max_castGE, equiv_iff_smul_eq, mul_smul, castGE_smul]
  exact fun hab hcd => by simp_rw [hab, hcd, implies_true]

theorem equiv_iff_mul_inv_equiv_one {a b : Σ n, PermOf n} : a ≈ b ↔ a * b⁻¹ ≈ 1 := by
  simp_rw [equiv_def, mul_eq_max_castGE, inv_eq_mk_inv, one_eq_zero_one,
    equiv_one_iff_eq_one, equiv_iff_smul_eq, castGE_inv, mul_inv_eq_one,
    eq_iff_smul_nat_eq_smul_nat, castGE_smul]

theorem equiv_iff_inv_mul_equiv_one {a b : Σ n, PermOf n} : a ≈ b ↔ b⁻¹ * a ≈ 1 := by
  simp_rw [equiv_def, mul_eq_max_castGE, inv_eq_mk_inv, one_eq_zero_one,
    equiv_one_iff_eq_one, equiv_iff_smul_eq, castGE_inv, inv_mul_eq_one,
    eq_iff_smul_nat_eq_smul_nat, castGE_smul, eq_comm]

theorem inv_equiv_inv_of_equiv {a b : Σ n, PermOf n} : a ≈ b → a⁻¹ ≈ b⁻¹ := by
  simp_rw [equiv_def,  inv_eq_mk_inv, equiv_iff_smul_eq, inv_smul_eq_iff]
  exact fun H => by simp_rw [H, smul_inv_smul, implies_true]

theorem equiv_iff_inv_equiv_inv {a b : Σ n, PermOf n} : a ≈ b ↔ a⁻¹ ≈ b⁻¹ :=
  ⟨inv_equiv_inv_of_equiv, inv_equiv_inv_of_equiv⟩

@[simp] theorem mul_inv_equiv_one {a : Σ n, PermOf n} : a * a⁻¹ ≈ 1 := by
  simp_rw [equiv_def, mul_eq_max_castGE, inv_eq_mk_inv, one_eq_zero_one,
    equiv_one_iff_eq_one, castGE_inv, mul_inv_cancel]

@[simp] theorem inv_mul_equiv_one {a : Σ n, PermOf n} : a⁻¹ * a ≈ 1 := by
  simp_rw [equiv_def, mul_eq_max_castGE, inv_eq_mk_inv, one_eq_zero_one,
    equiv_one_iff_eq_one, castGE_inv, inv_mul_cancel]

instance equivSubmonoid : Submonoid ((Σ n, PermOf n) × (Σ n, PermOf n)) where
  carrier a := a.1 ≈ a.2
  mul_mem' := equiv_mul_mul_of_equiv_equiv
  one_mem' := Setoid.refl 1

def minRep (a : Σ n, PermOf n) : Σ n, PermOf n := ⟨a.2.minLen, a.2.minPerm⟩

section MinRep

variable {n : ℕ}

@[simp] theorem minRep_mk {a : PermOf n} : minRep ⟨n, a⟩ = ⟨a.minLen, a.minPerm⟩ := rfl

@[simp] theorem minRep_fst {a : Σ n, PermOf n} : (minRep a).fst = a.snd.minLen := rfl

@[simp] theorem minRep_snd {a : Σ n, PermOf n} : (minRep a).snd = a.snd.minPerm := rfl

theorem minRep_minRep {a : Σ n, PermOf n} : minRep (minRep a) = minRep a := by
  cases a
  simp_rw [minRep_mk, sigma_eq_iff_eq_of_equiv, minLen_minPerm, equiv_def,
    minPerm_minPerm, cast_left_equiv_def, equiv_iff_eq, and_self]

@[simp] theorem minRep_equiv {a : Σ n, PermOf n} : minRep a ≈ a := by
  simp_rw [equiv_def]
  exact minPerm_equiv

theorem minRep_eq_of_equiv {a b : Σ n, PermOf n} : a ≈ b → minRep a = minRep b := by
  simp_rw [sigma_eq_iff_eq_of_equiv, equiv_def]
  exact fun h => ⟨h.minLen_eq, h.minPerm_minPerm⟩

theorem equiv_of_minRep_eq {a b : Σ n, PermOf n} : minRep a = minRep b → a ≈ b := by
  simp_rw [sigma_eq_iff_eq_of_equiv, equiv_def]
  exact fun h => equiv_minPerm_minPerm.mp h.2

theorem minRep_eq_iff_equiv {a b : Σ n, PermOf n} : minRep a = minRep b ↔ a ≈ b :=
  ⟨equiv_of_minRep_eq, minRep_eq_of_equiv⟩

@[simp] theorem minRep_one : minRep (1 : Σ n, PermOf n) = 1 := by
  simp_rw [one_eq_zero_one, minRep_mk, minLen_zero, minPerm_zero]

@[simp] theorem minRep_inv {a : Σ n, PermOf n} : minRep a⁻¹ = (minRep a)⁻¹ := by
  cases a
  simp_rw [inv_eq_mk_inv, minRep_mk, sigma_eq_iff_eq_of_equiv, minLen_inv, equiv_def,
    equiv_minPerm_inv_inv_minPerm, and_self]

@[simp] theorem minRep_mul {a b : Σ n, PermOf n} : minRep (a * b) ≈ minRep a * minRep b := by
  cases a ; cases b
  simp_rw [mul_eq_max_castGE, minRep_mk, equiv_def, equiv_minPerm_left]
  exact equiv.mul_mul (by simp_rw [castGE_equiv_castGE_iff_equiv, equiv_minPerm])
    (by simp_rw [castGE_equiv_castGE_iff_equiv, equiv_minPerm])

end MinRep

end SigmaPermOf

@[reducible] def FinitePerm : Type := Quotient SigmaPermOf

namespace FinitePerm

open PermOf SigmaPermOf

instance : DecidableEq FinitePerm := Quotient.decidableEq

instance : One FinitePerm := ⟨Quotient.mk _ 1⟩

theorem one_eq_one_class : (1 : FinitePerm) = ⟦1⟧ := rfl

instance : Mul FinitePerm :=
  ⟨(Quotient.map₂ (· * ·) (fun _ _ ha _ _ => equiv_mul_mul_of_equiv_equiv ha) · ·)⟩

theorem mul_eq_mul_class {a b : Σ n, PermOf n} :
    ⟦a⟧ * ⟦b⟧ = (⟦a * b⟧ : FinitePerm) := Quotient.map₂_mk _ _ _ _

instance : Inv FinitePerm := ⟨(Quotient.map (·⁻¹) (fun _ _ => inv_equiv_inv_of_equiv) ·)⟩

theorem inv_eq_inv_class {a : Σ n, PermOf n} :
    (⟦a⟧ : FinitePerm)⁻¹ = (⟦a⁻¹⟧ : FinitePerm) := Quotient.map_mk _ _ _

instance : Group FinitePerm where
  mul_assoc a b c := Quotient.inductionOn₃ a b c (by
    simp_rw [mul_eq_mul_class, mul_assoc, implies_true])
  one_mul a := Quotient.inductionOn a (by
    simp_rw [one_eq_one_class, mul_eq_mul_class, one_mul, implies_true])
  mul_one a := Quotient.inductionOn a (by
    simp_rw [one_eq_one_class, mul_eq_mul_class, mul_one, implies_true])
  inv_mul_cancel a := Quotient.inductionOn a (by
    simp_rw [one_eq_one_class, inv_eq_inv_class, mul_eq_mul_class, Quotient.eq_iff_equiv]
    exact fun _ => inv_mul_equiv_one)

def mk : (Σ n, PermOf n) →* FinitePerm where
  toFun a := ⟦a⟧
  map_one' := one_eq_one_class.symm
  map_mul' _ _ := mul_eq_mul_class.symm

theorem mk_eq_mk' {a : Σ n, PermOf n} : mk a = ⟦a⟧ := rfl

@[simp low] theorem mk_map_inv {a : Σ n, PermOf n} : mk a⁻¹ = (mk a)⁻¹ := inv_eq_inv_class.symm

@[simp low] theorem mk_map_div {a b : Σ n, PermOf n} :
  mk (a / b) = mk a / mk b := map_div' _ (fun _ => mk_map_inv) _ _

theorem mk_eq_mk_iff {a b : Σ n, PermOf n} : mk a = mk b ↔ a ≈ b := Quotient.eq_iff_equiv

theorem mk_one {n : ℕ} : mk ⟨n, 1⟩ = 1 := by
  simp_rw [one_eq_one_class, one_eq_zero_one,  mk_eq_mk', Quotient.eq_iff_equiv,
    equiv_def, equiv_one_one]

theorem mk_mul {n : ℕ} {a b : PermOf n} : mk ⟨n, a * b⟩ = mk ⟨n, a⟩ * mk ⟨n, b⟩ := by
  simp_rw [mk_eq_mk', mul_eq_mul_class, mul_eq_max_castGE, Quotient.eq_iff_equiv,
    equiv_def, equiv_iff_smul_eq, mul_smul, castGE_smul, implies_true]

theorem mk_sound {a b : Σ n, PermOf n} : a ≈ b → mk a = mk b := Quotient.sound

theorem mk_minRep {a : Σ n, PermOf n} : mk (minRep a) = mk a := by
  simp_rw [mk_eq_mk_iff, minRep_equiv]

theorem ind {β : FinitePerm → Prop} : (∀ (a : Σ n, PermOf n), β (mk a)) → ∀ q, β q :=
  Quotient.ind

def lift : OneHom FinitePerm (Σ n, PermOf n) where
  toFun := Quotient.lift minRep (fun _ _ => minRep_eq_of_equiv)
  map_one' := minRep_one

instance : Repr FinitePerm := ⟨fun a i => Std.Format.bracketFill "⟦" (reprPrec (lift a) i) "⟧"⟩

@[simp] theorem lift_mk' {a : Σ n, PermOf n} : lift ⟦a⟧ = minRep a := rfl

@[simp] theorem lift_mk {a : Σ n, PermOf n} : lift (mk a) = minRep a := rfl

@[simp] theorem mk'_lift {a : FinitePerm} : ⟦a.lift⟧ = a := Quotient.inductionOn a
  (fun _ => by simp_rw [lift_mk', Quotient.eq_iff_equiv] ; exact minRep_equiv)

@[simp] theorem mk_lift {a : FinitePerm} : mk (a.lift) = a :=
  Quotient.inductionOn a (fun _ => by simp_rw [lift_mk', mk_minRep, mk_eq_mk'])

@[simp] theorem minRep_lift {a : FinitePerm} : minRep a.lift = a.lift :=
  Quotient.inductionOn a (fun _ => by simp_rw [lift_mk', minRep_minRep])

@[ext] theorem ext {a b : FinitePerm} : a.lift = b.lift → a = b := Quotient.inductionOn₂ a b
  (fun _ _ => by simp_rw [lift_mk', Quotient.eq_iff_equiv] ; exact equiv_of_minRep_eq)

@[simp] theorem lift_inv {a : FinitePerm} : lift a⁻¹ = (lift a)⁻¹ :=
  Quotient.inductionOn a (fun _ => by simp_rw [inv_eq_inv_class, lift_mk', minRep_inv])
@[simp] theorem lift_mul {a b : FinitePerm} : lift (a * b) ≈ lift a * lift b :=
  Quotient.inductionOn₂ a b (fun _ _ => by simp_rw [mul_eq_mul_class, lift_mk', minRep_mul])

def ofPermOf (n : ℕ) : PermOf n →* FinitePerm where
  toFun a := mk ⟨n, a⟩
  map_one' := mk_one
  map_mul' _ _ := mk_mul

def ofVector {n : ℕ} (a : Vector ℕ n) (hx : ∀ {x} (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : FinitePerm := ofPermOf n (PermOf.ofVector a hx ha)

end FinitePerm
