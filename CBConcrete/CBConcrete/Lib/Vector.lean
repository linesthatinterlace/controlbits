import Batteries.Data.Vector.Lemmas
import CBConcrete.Lib.Array
import CBConcrete.Lib.Nat
import CBConcrete.Lib.Fin
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
    if h₁ : k = i ∧ j < n then as[j] else if h₂ : k = j ∧ i < n then as[i] else as[k] := by
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
theorem swapIfInBounds_same {xs : Vector α n} {i : Nat} : xs.swapIfInBounds i i = xs := by grind

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

theorem back_push {v : Vector α n} {a : α} : (v.push a).back = a := by grind

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
    induction empty push (xs.push x) = push ((n + 1) - 1) xs x (induction empty push xs) := by
  grind [pop_push]

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
    cases empty push (xs.push x) = push ((n + 1) - 1) xs x := by grind [pop_push]

theorem exists_getElem_push (f : α → Prop) {c : Vector α n} (b : α) {k : Nat} :
    (∃ (hk : k < n + 1), f (c.push b)[k]) ↔ k = n ∧ f b ∨ ∃ (hk : k < n), f c[k] := by grind

theorem forall_getElem_push (f : α → Prop) {c : Vector α n} (b : α) {k : Nat} :
    (∀ (hk : k < n + 1), f (c.push b)[k]) ↔ (k = n → f b) ∧ ∀ (hk : k < n), f c[k] := by grind

variable {v : Vector α n}

open Function

def Nodup (v : Vector α n) : Prop := ∀ {i} (hi : i < n) {j} (hj : j < n), v[i] = v[j] → i = j

section Nodup

@[grind =]
theorem Nodup.getElem_inj_iff {i j : ℕ} {hi : i < n} {hj : j < n}
    (hv : v.Nodup) : v[i] = v[j] ↔ i = j := ⟨hv _ _, fun h => h ▸ rfl⟩

theorem Nodup.getElem_ne_iff {i j : ℕ} {hi : i < n} {hj : j < n}
    (hv : v.Nodup) : v[i] ≠ v[j] ↔ i ≠ j := by simp_rw [ne_eq, hv.getElem_inj_iff]

@[grind =]
theorem nodup_iff_getElem_ne_getElem :
    v.Nodup ↔ ∀ {i j}, (hij : i < j) → (hj : j < n) → v[i] ≠ v[j] :=
  ⟨by grind, fun _ _ _ _ _ => Function.mtr <| by grind⟩

theorem nodup_iff_injective_getElem : v.Nodup ↔ Injective (fun (i : Fin n) => v[(i : ℕ)]) := by
  unfold Injective Nodup
  simp_rw [Fin.ext_iff, Fin.forall_iff]

theorem nodup_iff_injective_get : v.Nodup ↔ Injective v.get := by
  simp_rw [nodup_iff_injective_getElem]
  exact Iff.rfl

theorem toList_nodup_iff_nodup : v.toList.Nodup ↔ v.Nodup := by
  grind [List.pairwise_iff_getElem]

theorem Nodup.nodup_toList (hv : v.Nodup) : v.toList.Nodup := toList_nodup_iff_nodup.mpr hv

theorem _root_.List.Nodup.nodup_of_nodup_toList (hv : v.toList.Nodup) : v.Nodup :=
  toList_nodup_iff_nodup.mp hv

instance nodupDecidable [DecidableEq α] : Decidable v.Nodup :=
  decidable_of_decidable_of_iff toList_nodup_iff_nodup

end Nodup

theorem getElem_getElem_flip {a b : Vector ℕ n}
    (H : ∀ {i} {hi : i < n}, ∃ (hi' : a[i] < n), b[a[i]] = i) {i hi} :
    (∃ (hi' : b[i] < n), a[b[i]'(hi : i < n)] = i) := by
  have := (Fin.surj_of_inj (f := (⟨a[·.val], by grind⟩)) <|
    fun i j hij => by have := congrArg (b[·.val]) hij; grind) <| Fin.mk _ hi
  grind

end Vector
