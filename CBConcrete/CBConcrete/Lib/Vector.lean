import Batteries.Data.Vector.Lemmas
import CBConcrete.Lib.Array
import CBConcrete.Lib.Nat
import Mathlib.Algebra.Order.Star.Basic

namespace Vector

variable {α β γ : Type*} {n m k i j : ℕ}

attribute [grind =] getElem_mk

@[simp]
theorem getD_of_lt (a : Vector α n) (x : α) (i : ℕ) (h : i < n) : a[i]?.getD x = a[i] := by
  simp_rw [getElem?_pos a i h, Option.getD_some]

@[simp]
theorem getD_of_ge (a : Vector α n) (x : α) (i : ℕ) (h : n ≤ i) : a[i]?.getD x = x := by
  rw [getElem?_neg a i h.not_gt, Option.getD_none]

@[grind =]
theorem getElem_swapIfInBounds {as : Vector α n} {i j k : ℕ} (hk : k < n) :
    (as.swapIfInBounds i j)[k] =
    if h : i < n ∧ j < n then (as.swap i j)[k] else as[k] := by
  grind [swapIfInBounds]

theorem mem_def {a : α} (v : Vector α n) : a ∈ v ↔ a ∈ v.toArray :=
  ⟨fun | .mk h => h, Vector.Mem.mk⟩

theorem getElem_eraseIdx_left (v : Vector α n) (hi : i < n) (hki : k < i) :
    (v.eraseIdx i)[k] = v[k] := by
  simp_rw [getElem_eraseIdx, dif_pos hki]

theorem getElem_eraseIdx_right (v : Vector α n) (hki : i ≤ k) (hk : k < n - 1) :
    (v.eraseIdx i)[k] = v[k + 1] := by
  simp_rw [getElem_eraseIdx, dif_neg hki.not_gt]

@[simp] theorem getElem_eraseIdx_zero (v : Vector α n) (hk : k < n - 1) :
    (v.eraseIdx 0)[k] = v[k + 1] := getElem_eraseIdx_right _ (zero_le _) _

@[simp] theorem getElem_tail' (v : Vector α (n + 1)) (hi : i < (n + 1) - 1) :
    @getElem (Vector α n) Nat α (fun _ i => i < n) instGetElemNatLt v.tail i hi = v[i + 1] :=
  getElem_tail _

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
  · simp_rw [Nat.sub_add_cancel (le_of_not_gt hi)]

@[simp] theorem back_succ (v : Vector α (n + 1)) : v.back = v[n] := by
  cases v with | mk as has => _
  unfold back
  simp_rw [add_tsub_cancel_right]

@[simp, grind =]
theorem swap_same {xs : Vector α n} {i : Nat} {hi} : xs.swap i i hi hi = xs := by grind

@[simp, grind =]
theorem swapIfInBounds_same {xs : Vector α n} {i : Nat}: xs.swapIfInBounds i i = xs := by grind

def bswap (xs : Vector α n) (b : Bool) (i j : Nat) (hi : i < n := by get_elem_tactic)
    (hj : j < n := by get_elem_tactic) : Vector α n :=
  ⟨xs.toArray.bswap b i j (by grind) (by grind), by grind⟩

@[grind =] theorem getElem_bswap {xs : Vector α n} {b : Bool} {i j : Nat} {hi hj}
    (hk : k < (xs.bswap b i j hi hj).size) :
    (xs.bswap b i j hi hj)[k] = bif b then (xs.swap i j)[k]'(by grind) else xs[k]'(by grind) :=
  Array.getElem_bswap _

@[simp]
theorem bswap_true {xs : Vector α n} {i j : Nat} {hi hj} :
    xs.bswap true i j hi hj = xs.swap i j hi hj := by grind

@[simp]
theorem bswap_false {xs : Vector α n} {i j : Nat} {hi hj} :
    xs.bswap false i j hi hj = xs := by grind

def bswapIfInBounds (xs : Vector α n) (b : Bool) (i j : @& Nat) : Vector α n :=
  ⟨xs.toArray.bswapIfInBounds b i j, by grind⟩

@[grind =] theorem getElem_bswapIfInBounds {xs : Vector α n} {b : Bool} {i j : Nat}
    (hk : k < (xs.bswapIfInBounds b i j).size) :
    (xs.bswapIfInBounds b i j)[k] =
    bif b then (xs.swapIfInBounds i j)[k]'(by grind) else xs[k]'(by grind) :=
  Array.getElem_bswapIfInBounds _

@[simp]
theorem bswapIfInBounds_true {xs : Vector α n} {i j : Nat} :
    xs.bswapIfInBounds true i j  = xs.swapIfInBounds i j := by grind

@[simp]
theorem bswapIfInBounds_false {xs : Vector α n} {i j : Nat} :
    xs.bswapIfInBounds false i j = xs := by grind

attribute [grind =] pop_push

@[elab_as_elim, induction_eliminator, grind =]
def induction {C : ∀ {n : ℕ}, Vector α n → Sort*} (empty : C #v[])
    (push : ∀ (n : ℕ) (xs : Vector α n) (x : α), C xs → C (xs.push x)) :
    {n : ℕ} → (xs : Vector α n) → C xs
  | 0, xs => xs.eq_empty ▸ empty
  | _ + 1, xs => xs.push_pop_back ▸ push _ _ _ (induction empty push _)

@[simp]
theorem induction_empty {C : ∀ {n : ℕ}, Vector α n → Sort*} (empty : C #v[])
    (push : ∀ (n : ℕ) (xs : Vector α n) (x : α), C xs → C (xs.push x)) :
  induction empty push #v[] = empty := by grind

@[simp]
theorem induction_push {C : ∀ {n : ℕ}, Vector α n → Sort*} (empty : C #v[])
    (push : ∀ (n : ℕ) (xs : Vector α n) (x : α), C xs → C (xs.push x)) (xs : Vector α n) (x : α) :
    induction empty push (xs.push x) = push ((n + 1) - 1) xs x (induction empty push xs) := by grind

@[elab_as_elim, cases_eliminator, grind =]
def cases {C : ∀ {n : ℕ}, Vector α n → Sort*}
    (empty : C #v[])
    (push : ∀ (n : ℕ) (xs : Vector α n) (x : α), C (xs.push x))
    {n : ℕ} (v : Vector α n) : C v := v.induction empty (fun _ _ _ _ => push _ _ _)

@[simp]
theorem cases_empty {C : ∀ {n : ℕ}, Vector α n → Sort*} (empty : C #v[])
    (push : ∀ (n : ℕ) (xs : Vector α n) (x : α), C (xs.push x)) :
  cases empty push #v[] = empty := by grind

@[simp]
theorem cases_push {C : ∀ {n : ℕ}, Vector α n → Sort*} (empty : C #v[])
    (push : ∀ (n : ℕ) (xs : Vector α n) (x : α), C (xs.push x)) (xs : Vector α n) (x : α) :
    cases empty push (xs.push x) = push ((n + 1) - 1) xs x := by grind

theorem exists_getElem_push (f : α → Prop) {c : Vector α n} (b : α) {k : Nat}  :
    (∃ (hk : k < n + 1), f (c.push b)[k]) ↔ k = n ∧ f b ∨ ∃ (hk : k < n), f c[k] := by grind

theorem forall_getElem_push (f : α → Prop) {c : Vector α n} (b : α) {k : Nat}  :
    (∀ (hk : k < n + 1), f (c.push b)[k]) ↔ (k = n → f b) ∧ ∀ (hk : k < n), f c[k] := by grind


end Vector
