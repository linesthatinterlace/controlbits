import Batteries.Data.Vector.Lemmas
import CBConcrete.Lib.Array
import CBConcrete.Lib.Nat
import Mathlib.Algebra.Order.Star.Basic

namespace Vector

variable {α β γ : Type*} {n m k i j : ℕ}

@[simp]
theorem getD_of_lt (a : Vector α n) (x : α) (i : ℕ) (h : i < n) : a[i]?.getD x = a[i] := by
  simp_rw [getElem?_pos a i h, Option.getD_some]

@[simp]
theorem getD_of_ge (a : Vector α n) (x : α) (i : ℕ) (h : n ≤ i) : a[i]?.getD x = x := by
  rw [getElem?_neg a i h.not_lt, Option.getD_none]


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


theorem mem_def {a : α} (v : Vector α n) : a ∈ v ↔ a ∈ v.toArray :=
  ⟨fun | .mk h => h, Vector.Mem.mk⟩

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

@[simp] theorem getElem_singleton' (a : α) (hi : i < 1) : (singleton a)[i] = a := by
  unfold singleton
  simp_rw [getElem_mk, List.getElem_toArray, List.getElem_singleton]

theorem cast_singleton_head_append_tail [NeZero n] (v : Vector α n) :
    (singleton (v.head) ++ v.tail).cast
    (Nat.add_comm _ _ ▸ Nat.sub_add_cancel NeZero.one_le) = v := by
  ext
  simp_rw [getElem_cast, getElem_append, getElem_singleton', getElem_tail]
  split_ifs with hi
  · simp_rw [Nat.lt_one_iff] at hi
    simp_rw [hi]
    rfl
  · simp_rw [Nat.sub_add_cancel (le_of_not_lt hi)]

@[simp] theorem back_succ (v : Vector α (n + 1)) : v.back = v[n] := by
  cases v with | mk as has => _
  unfold back
  simp_rw [add_tsub_cancel_right]

end Vector
