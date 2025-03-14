import Batteries.Data.Vector.Lemmas
import CBConcrete.Lib.Array
import CBConcrete.Lib.Equiv
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

theorem getElem_range_lt {n i : ℕ} (hi : i < n) : (range n)[i] < n :=
  (getElem_range i hi).trans_lt hi

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

/-
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
-/
/-
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
-/

@[simp] theorem getElem_take' (xs : Vector α n) (j : Nat) (hi : i < min j n) :
    (xs.take j)[i] = xs[i] := getElem_take _ _ (hi.trans_eq (min_comm _ _))

end Vector
