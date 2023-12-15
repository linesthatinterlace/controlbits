import Mathlib.Data.Fin.Tuple.Basic
import Controlbits.Nat
import Mathlib.Data.Fintype.Basic

namespace Fin

lemma modNat_two_eq_zero_or_one (q : Fin (m*2)): modNat q = 0 ∨ modNat q = 1 :=
(exists_fin_two ).mp ⟨_, rfl⟩

lemma coe_succAbove_le {i : Fin (m)} {j : Fin (m + 1)} : (j.succAbove i : ℕ) ≤ i + 1 := by
  simp only [succAbove, dite_val, coe_castSucc, val_succ]
  split_ifs
  · exact Nat.le_succ _
  · rfl

lemma coe_le_succAbove {i : Fin (m)} {j : Fin (m + 1)} : i ≤ (j.succAbove i : ℕ) := by
  simp only [succAbove, dite_val, coe_castSucc, val_succ]
  split_ifs
  · rfl
  · exact Nat.le_succ _

lemma succAbove_succAbove_left_eq_right {i : Fin (m)} {j : Fin (m + 1)} :
(j.succAbove i).succAbove i = if castSucc i < j then succ i else castSucc i := by
  simp_rw [ext_iff, succAbove, lt_def, dite_val, coe_castSucc, val_succ,
    apply_ite (fun z => if (i : ℕ) < z then (i : ℕ) else (i + 1 : ℕ)),
    if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]

lemma succAbove_succAbove_left_ne_right {i : Fin (m)} {j : Fin (m + 1)} (h : t ≠ i) :
(j.succAbove i).succAbove t = if t < i then t.castSucc else t.succ := by
  simp_rw [ext_iff, succAbove, lt_def, dite_val, coe_castSucc, val_succ,
    apply_ite (fun z => if (t : ℕ) < z then (t : ℕ) else (t + 1 : ℕ)), Nat.lt_succ_iff, val_fin_le,
    h.le_iff_lt, val_fin_lt, ite_self]

lemma succAbove_succAbove_left {i : Fin m} {j : Fin (m + 1)} : (j.succAbove i).succAbove t =
    if t = i then
    if t.castSucc < j then t.succ else t.castSucc else
    if t < i then t.castSucc else t.succ := by
    rcases eq_or_ne t i with (h | h)
    · simp_rw [if_pos h, h, succAbove_succAbove_left_eq_right]
    · simp_rw [if_neg h, succAbove_succAbove_left_ne_right h]

lemma succAbove_castSucc_left {i t : Fin m} : i.castSucc.succAbove t =
    if i ≤ t then t.succ else t.castSucc := by
    simp_rw [← succAbove_last, succAbove_succAbove_left, succAbove_last,
    if_pos (castSucc_lt_last _)]
    by_cases h : i ≤ t
    · rw [if_pos h, if_neg h.not_lt, ite_self]
    · rw [if_neg h, if_pos (lt_of_not_le h), if_neg (ne_of_not_le h).symm]

lemma succAbove_succ_left {i t : Fin m} : (i.succ).succAbove t =
    if t ≤ i then t.castSucc else t.succ := by
    simp_rw [← succAbove_zero, succAbove_succAbove_left, succAbove_zero]
    by_cases h : t ≤ i
    · rw [if_pos h, if_neg (not_lt_zero _), ite_eq_left_iff]
      exact fun h₂ => if_pos (h.lt_of_ne h₂)
    · rw [if_neg h, if_neg (ne_of_not_le h), if_neg (lt_of_not_le h).not_lt]

lemma succAbove_castSucc_succ_left_succAbove_right {i : Fin (m)} {j : Fin (m + 1)} :
    (i.succ.castSucc).succAbove (j.succAbove i) =
    if i.castSucc < j then i.castSucc.castSucc else i.succ.succ := by
      simp_rw [ext_iff, succAbove, lt_def, coe_castSucc]
      by_cases h : (i : ℕ) < j
      · simp_rw [if_pos h, ← lt_def, if_pos (castSucc_lt_succ _)]
      · simp_rw [if_neg h, if_neg (lt_irrefl _)]

lemma succAbove_succ_castSucc_left_succAbove_right {i : Fin (m)} {j : Fin (m + 1)} :
    (i.castSucc.succ).succAbove (j.succAbove i) =
    if i.castSucc < j then i.castSucc.castSucc else i.succ.succ := by
      simp_rw [succ_castSucc, succAbove_castSucc_succ_left_succAbove_right]

lemma succAbove_le_castSucc_castSucc_succAbove_right {i : Fin (m)} {j : Fin (m + 1)}
  {t : Fin (m + 2)} (ht : t ≤ i.castSucc.castSucc) : t.succAbove (j.succAbove i) =
    if i.castSucc < j then i.succ.castSucc else i.succ.succ := by
      simp_rw [ext_iff, succAbove, lt_def, coe_castSucc]
      simp_rw [le_def, coe_castSucc] at ht
      by_cases h : (i : ℕ) < j
      · simp_rw [if_pos h, coe_castSucc, if_neg (ht.not_lt), val_succ, coe_castSucc]
      · simp_rw [if_neg h, val_succ, if_neg (Nat.le_succ_of_le ht).not_lt, val_succ]

lemma succAbove_succ_castSucc_lt_succAbove_right {i : Fin (m)} {j : Fin (m + 1)}
  {t : Fin (m + 2)} (ht : i.succ.castSucc < t) : t.succAbove (j.succAbove i) =
    if i.castSucc < j then i.castSucc.castSucc else i.succ.castSucc := by
      simp_rw [ext_iff, succAbove, lt_def, coe_castSucc]
      simp_rw [lt_def, coe_castSucc, val_succ] at ht
      by_cases h : (i : ℕ) < j
      · simp_rw [if_pos h, coe_castSucc, if_pos ((Nat.lt_succ_self _).trans ht), coe_castSucc]
      · simp_rw [if_neg h, val_succ, if_pos ht]

lemma succAbove_succAbove_right {i : Fin (m)} {j : Fin (m + 1)} {t : Fin (m + 2)}:
t.succAbove (j.succAbove i) =
  if i.castSucc < j then
  if t ≤ i.castSucc.castSucc then i.succ.castSucc else i.castSucc.castSucc else
  if t ≤ i.succ.castSucc then i.succ.succ else i.succ.castSucc := by
  by_cases ht : (t ≤ i.succ.castSucc)
  · rw [if_pos ht]
    by_cases ht₂ : (t ≤ i.castSucc.castSucc)
    · rw [if_pos ht₂, succAbove_le_castSucc_castSucc_succAbove_right ht₂]
    · simp_rw [le_antisymm ht (succ_castSucc _ ▸ castSucc_lt_iff_succ_le.mp (lt_of_not_le ht₂)),
      succAbove_castSucc_succ_left_succAbove_right, Fin.le_castSucc_iff, succ_castSucc,
      if_neg (lt_irrefl _)]
  · rw [if_neg ht,
    if_neg ((castSucc_lt_castSucc_iff.mpr (castSucc_lt_succ i)).trans (lt_of_not_le ht)).not_le,
    succAbove_succ_castSucc_lt_succAbove_right (lt_of_not_le ht)]

lemma castSucc_le_castSucc_iff {n : Nat} {a : Fin n} {b : Fin n} :
castSucc a ≤ castSucc b ↔ a ≤ b := Iff.rfl

lemma pred_lt_iff {i : Fin (m)} {j : Fin (m + 1)} (h : j ≠ 0) : pred j h < i ↔ j ≤ castSucc i := by
  rw [ne_eq, Fin.ext_iff, val_zero] at h
  rw [lt_def, le_def, coe_pred, coe_castSucc, ← Nat.pred_eq_sub_one]
  exact ⟨Nat.le_of_pred_lt, fun H => lt_of_lt_of_le (Nat.pred_lt h) H⟩

lemma le_pred_iff {i : Fin (m)} {j : Fin (m + 1)} (h : j ≠ 0) : i ≤ pred j h ↔ castSucc i < j := by
  rw [lt_iff_not_le, ← pred_lt_iff h, not_lt]

lemma castLT_eq_iff_eq_castSucc {n : ℕ} (i : Fin (n + 1)) (hi : (i : ℕ) < n) (j : Fin n) :
  castLT i hi = j ↔ i = castSucc j :=
  ⟨fun h => by simp_rw [← h, castSucc_castLT], fun h => by simp_rw [h, castLT_castSucc]⟩

lemma coe_succ_predAbove_of_le_castSucc {i : Fin (m + 1)} {j : Fin (m + 2)}
  (h : j ≤ castSucc i) : (succ (predAbove i j) : ℕ) = j + 1 := by
  simp_rw [predAbove, dif_neg h.not_lt, val_succ, coe_castLT]

lemma coe_castSucc_predAbove_of_castSucc_lt {i : Fin (m + 1)} {j : Fin (m + 2)}
  (h : castSucc i < j) : (castSucc (predAbove i j) : ℕ) = j - 1 := by
  simp_rw [predAbove, dif_pos h, coe_castSucc, coe_pred]

lemma castSucc_predAbove_eq_of_le_castSucc (h : j ≤ castSucc i) : castSucc (predAbove i j) = j := by
  simp_rw [predAbove, dif_neg h.not_lt, castSucc_castLT]

lemma succ_predAbove_eq_of_castSucc_lt (h : castSucc i < j) : succ (predAbove i j) = j := by
  simp_rw [predAbove, dif_pos h, succ_pred]

lemma castSucc_predAbove_le (i : Fin m) (j) : castSucc (predAbove i j) ≤ j := by
  rcases j.succAbove_lt_ge i with (h | h)
  · exact (castSucc_lt_succ _).le.trans (succ_predAbove_eq_of_castSucc_lt h).le
  · rw [castSucc_predAbove_eq_of_le_castSucc h]

lemma le_succ_predAbove (i : Fin m) (j) : j ≤ succ (predAbove i j) := by
  rcases j.succAbove_lt_ge i with (h | h)
  · rw [succ_predAbove_eq_of_castSucc_lt h]
  · exact (castSucc_predAbove_eq_of_le_castSucc h).symm.le.trans (castSucc_lt_succ _).le

lemma le_castSucc_predAbove_of_le_castSucc (h : j ≤ castSucc i) : j ≤ castSucc (predAbove i j) :=
  (castSucc_predAbove_eq_of_le_castSucc h).symm.le

lemma succ_predAbove_le_of_castSucc_lt (h : castSucc i < j) : succ (predAbove i j) ≤ j :=
  (succ_predAbove_eq_of_castSucc_lt h).le

lemma castSucc_predAbove_lt_iff_castSucc_lt {i : Fin m} {j : Fin (m + 1)} :
  castSucc (predAbove i j) < j ↔ castSucc i < j := by
  refine ⟨?_, ?_⟩
  · simp_rw [lt_iff_not_le]
    exact (le_castSucc_predAbove_of_le_castSucc).mt
  · rw [castSucc_lt_iff_succ_le (i := i.predAbove j)]
    exact succ_predAbove_le_of_castSucc_lt

lemma castSucc_predAbove_eq_iff_le_castSucc {i : Fin (m + 1)} {j : Fin (m + 2)} :
  castSucc (predAbove i j) = j ↔ j ≤ castSucc i := by
    simp_rw [eq_iff_le_not_lt, castSucc_predAbove_le, true_and,
    castSucc_predAbove_lt_iff_castSucc_lt, not_lt]

lemma lt_succ_predAbove_iff_le_castSucc {i : Fin (m + 1)} {j : Fin (m + 2)} :
  j < succ (predAbove i j) ↔ j ≤ castSucc i := by
  refine' ⟨?_, ?_⟩
  · rw [← not_imp_not, not_le, not_lt]
    exact succ_predAbove_le_of_castSucc_lt
  · simp_rw [← le_castSucc_iff]
    exact le_castSucc_predAbove_of_le_castSucc

lemma succ_predAbove_eq_iff_castSucc_lt {i : Fin (m + 1)} {j : Fin (m + 2)} :
  succ (predAbove i j) = j ↔ castSucc i < j := by
  rw [← castSucc_predAbove_lt_iff_castSucc_lt, castSucc_lt_iff_succ_le,
    le_antisymm_iff, and_iff_left_iff_imp]
  exact fun _ => le_succ_predAbove _ _

lemma predAbove_eq : predAbove i j = i ↔ j = castSucc i ∨ j = succ i := by
  simp_rw [or_comm (a := j = castSucc i), predAbove, dite_eq_iff, pred_eq_iff_eq_succ,
    castLT_eq_iff_eq_castSucc, exists_prop]
  exact ⟨Or.imp (And.right) (And.right),
    Or.imp (fun h => ⟨h ▸ castSucc_lt_succ _, h⟩) (fun h => ⟨h ▸ lt_irrefl _, h⟩)⟩

lemma predAbove_lt {i : Fin (m + 1)} {j : Fin (m + 2)} : predAbove i j < i ↔ j < castSucc i := by
  simp_rw [predAbove, lt_def, ite_val, coe_castSucc, coe_castLT, coe_pred]
  refine' ⟨fun h => lt_of_not_le (fun h2 => h.not_le
    (h2.eq_or_lt.elim (fun h3 => _) (fun h3 => _) )), fun h => _⟩
  · simp_rw [dif_neg h3.symm.le.not_lt]
    exact h2
  · simp_rw [dif_pos h3, ← Nat.pred_eq_sub_one]
    exact Nat.le_pred_of_lt h3
  · simp_rw [dif_neg h.le.not_lt]
    exact h

lemma predAbove_gt {i : Fin (m + 1)} {j : Fin (m + 2)} : i < predAbove i j ↔ succ i < j := by
  simp_rw [predAbove, lt_def, ite_val, coe_castSucc, coe_castLT, coe_pred, val_succ]
  refine' ⟨fun h => lt_of_not_le (fun h2 => h.not_le
    (h2.eq_or_lt.elim (fun h3 => _) (fun h3 => _) )), fun h => _⟩
  · simp_rw [h3, dif_pos (Nat.lt_succ_self _)]
    exact (Nat.pred_succ _).le
  · rw [Nat.lt_succ_iff] at h3
    simp_rw [dif_neg h3.not_lt]
    exact h3
  · simp_rw [dif_pos ((Nat.lt_succ_self _).trans h)]
    exact Nat.lt_sub_of_add_lt h

lemma succAbove_succAbove_predAbove {i : Fin (m + 1)} {j : Fin (m + 2)} :
(j.succAbove i).succAbove (i.predAbove j) = j := by
  simp_rw [succAbove_succAbove_left, predAbove_eq, predAbove_lt,
    castSucc_predAbove_lt_iff_castSucc_lt, ite_eq_iff', succ_predAbove_eq_iff_castSucc_lt, imp_self,
    castSucc_predAbove_eq_iff_le_castSucc, not_lt, true_and, imp_self, implies_true, true_and,
    not_or, and_imp]
  exact fun H _ => ⟨le_of_lt, fun H2 => lt_of_le_of_ne H2 (Ne.symm H)⟩

lemma succAbove_succAbove_predAbove_succAbove {j : Fin (m + 2)} :
(j.succAbove i).succAbove ((i.predAbove j).succAbove k) = j.succAbove (i.succAbove k) := by
  ext ; simp only [succAbove, predAbove, lt_def, coe_castSucc, ite_val, coe_pred,
    coe_castLT, dite_eq_ite, dite_val, val_succ]
  rcases lt_or_le (i : ℕ) (j : ℕ) with (h | h) <;>
  rcases lt_or_le (k : ℕ) (i : ℕ) with (h₂ | h₂)
  · simp_rw [if_pos h, if_pos (Nat.lt_sub_one_of_lt_of_lt h₂ h), if_pos h₂, if_pos (h₂.trans h)]
  · simp_rw [if_pos h, if_neg h₂.not_lt, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff,
      apply_ite (fun z => if z < (i : ℕ) then z else z + 1), if_neg h₂.not_lt,
      if_neg (Nat.le_succ_of_le h₂).not_lt]
  · simp_rw [if_neg h.not_lt, if_pos h₂, apply_ite (fun z => if z < (i + 1 : ℕ) then z else z + 1),
      if_pos (lt_of_lt_of_le h₂ (Nat.le_succ _)), Nat.succ_lt_succ_iff, if_pos h₂]
  · simp_rw [if_neg h.not_lt, if_neg (h.trans h₂).not_lt, Nat.succ_lt_succ_iff, if_neg h₂.not_lt,
      if_neg ((h.trans h₂).trans (Nat.le_succ _)).not_lt]

lemma insertNth_succAbove_insertNth_predAbove {p : Fin m → α} {j : Fin (m + 2)} :
(succAbove j i).insertNth y ((predAbove i j).insertNth x p)  =
  j.insertNth x (insertNth i y p) := by
  simp_rw [insertNth_eq_iff, succAbove_succAbove_predAbove,
    insertNth_apply_succAbove, insertNth_apply_same, true_and,
    succAbove_succAbove_predAbove_succAbove, insertNth_apply_succAbove]

theorem cons_eq_iff {n : ℕ} {α : Fin (n + 1) → Type u}
 {x : α 0} {p : (j : Fin n) → α (j.succ)} {q : (j : Fin (n + 1)) → α j} :
cons x p = q ↔ q 0 = x ∧ p = fun (j : Fin n) => q (j.succ) := by
  simp_rw [Function.funext_iff, Fin.forall_fin_succ, Fin.cons_succ, Fin.cons_zero, eq_comm]

theorem eq_cons_iff {n : ℕ} {α : Fin (n + 1) → Type u} {x : α 0}
  {p : (j : Fin n) → α (j.succ)} {q : ∀ j, α j} :
    q = cons x p ↔ q 0 = x ∧ p = fun (j : Fin n) ↦ q (j.succ) := eq_comm.trans cons_eq_iff

lemma insertNth_succ_insertNth_zero {i : Fin (n + 1)} {x : α} {y : α} {p : Fin n → α} :
  insertNth (α := fun _ => α) (i.succ) y (insertNth 0 x p) =
  insertNth 0 x (insertNth i y p) := by
  simp_rw [insertNth_eq_iff, succ_succAbove_zero, zero_succAbove, succ_succAbove_succ,
  ← zero_succAbove, insertNth_apply_succAbove, insertNth_apply_same, and_self]



theorem exists_unique_succAbove_eq {n : ℕ} {y : Fin (n + 1)}{x : Fin (n + 1)} (h : x ≠ y) :
∃! (z : Fin n), Fin.succAbove y z = x := h.lt_or_lt.by_cases
    (fun hlt => ⟨_, succAbove_castLT hlt,
    fun _ H => (Fin.succAbove_right_injective (x := y)) ((succAbove_castLT hlt).symm ▸ H)⟩)
    (fun hlt => ⟨_, succAbove_pred hlt,
    fun _ H => (Fin.succAbove_right_injective (x := y)) ((succAbove_pred hlt).symm ▸ H)⟩)

def predAbove! {n : ℕ} (y : Fin (n + 1)) (x : Fin (n + 1)) (h : x ≠ y) : Fin n :=
    Fintype.choose _ (Fin.exists_unique_succAbove_eq h)

lemma succAbove_predAbove! {y : Fin (n + 1)} {x : Fin (n + 1)} (hij : x ≠ y) :
  y.succAbove (y.predAbove! x hij) = x := Fintype.choose_spec _ (Fin.exists_unique_succAbove_eq hij)

lemma predAbove!_below {y : Fin (n + 1)} {x : Fin (n + 1)} (hij : x < y) (hij' : x ≠ y := hij.ne) :
  y.predAbove! x hij' = x.castLT (lt_of_lt_of_le hij (le_last _)) := by
  apply Fin.succAbove_right_injective (x := y)
  simp_rw [succAbove_predAbove!, succAbove_castLT hij]

lemma predAbove!_above {y : Fin (n + 1)} {x : Fin (n + 1)} (hij : y < x)
  (hij' : x ≠ y := hij.ne.symm) :
  y.predAbove! x hij' = x.pred (lt_of_le_of_lt (zero_le _) hij).ne.symm := by
  apply Fin.succAbove_right_injective (x := y)
  simp_rw [succAbove_predAbove!, succAbove_pred hij]

lemma coe_predAbove!_below {y : Fin (n + 1)} {x : Fin (n + 1)} (hij : x < y)
  (hij' : x ≠ y := hij.ne) : (y.predAbove! x hij' : ℕ) = x :=
  by simp_rw [predAbove!_below hij, coe_castLT]

lemma coe_predAbove!_above {y : Fin (n + 1)} {x : Fin (n + 1)} (hij : y < x)
  (hij' : x ≠ y := hij.ne.symm) : (y.predAbove! x hij' : ℕ) = x - 1 :=
  by simp_rw [predAbove!_above hij, coe_pred]

lemma predAbove!_succAbove {i : Fin (n + 1)} {k : Fin n}
  (h : succAbove i k ≠ i := succAbove_ne _ _) : predAbove! i (succAbove i k) h = k := by
  rcases (succAbove_ne i k).lt_or_lt with (h | h)
  · rw [predAbove!_below h, castLT_succAbove ((succAbove_lt_iff _ _).mp h)]
  · rw [predAbove!_above h, pred_succAbove ((lt_succAbove_iff _ _).mp h)]

lemma predAbove!_lt_last_eq_predAbove {i : Fin (n + 1)} {j : Fin (n + 2)} {hij : j ≠ i.castSucc}
  : (i.castSucc).predAbove! j hij = predAbove i j := by
  rcases hij.lt_or_lt with (h | h)
  · rw [predAbove!_below h, predAbove_below _ _ h.le, ext_iff,
      coe_castPred _ (h.trans (Fin.castSucc_lt_last _)), coe_castLT]
  · rw [predAbove!_above h, predAbove_above _ _ h]

lemma predAbove!_zero {y : Fin (n + 2)} (hij : y ≠ 0) (hij' : 0 ≠ y := hij.symm) :
  y.predAbove! 0 hij' = 0 := (predAbove!_below (hij'.lt_of_le (zero_le _))) ▸ rfl

lemma predAbove!_zero_left {z : Fin (n + 1)}  (hij : z.succ ≠ 0 := Fin.succ_ne_zero _):
  (0 : Fin (n + 2)).predAbove! (z.succ) hij = z := predAbove!_succAbove _

lemma coe_succAbove_below {y : Fin (n + 1)} {z : Fin n} (h : (z : ℕ) < y) :
  (y.succAbove z : ℕ) = z := by simp_rw [succAbove_below _ _ h, coe_castSucc]

lemma coe_succAbove_above {y : Fin (n + 1)} {z : Fin n} (h : (y : ℕ) ≤ z) :
  (y.succAbove z : ℕ) = z + 1 := by simp_rw [succAbove_above _ _ h, val_succ]

lemma succAbove_castLT_left_of_coe_lt_gt {i j : Fin (m + 2)} {k : Fin m} (h : j < i)
    (h₂ : (k : ℕ) < j) (h' : j < last (m + 1) := lt_of_lt_of_le h (le_last _))
    : (castLT j h').succAbove k = castSucc k := succAbove_below _ _ h₂

lemma succAbove_castLT_left_of_coe_le {j : Fin (m + 2)} {k : Fin m} (h : (j : ℕ) ≤ k)
    (h' : j < last (m + 1) := lt_def.mpr (lt_of_le_of_lt h (k.prop.trans (Nat.lt_succ_self _)))) :
    (castLT j h').succAbove k = succ k := succAbove_above _ _ h

lemma succAbove_pred_left_of_coe_gt {j : Fin (m + 2)} {k : Fin m} (h : (k + 1 : ℕ) < j)
    (h' : j ≠ 0 := Fin.pos_iff_ne_zero.mp (lt_def.mpr (lt_of_le_of_lt (Nat.zero_le _) h))) :
    (pred j h').succAbove k = castSucc k := by
    refine succAbove_below _ _ ?_
    rw [lt_def, coe_castSucc, coe_pred]
    exact Nat.lt_sub_of_add_lt h

lemma succAbove_pred_left_of_coe_gt_le {i j : Fin (m + 2)} {k : Fin m} (h : i < j)
  (h₂ : (j : ℕ) ≤ k + 1) (h' : j ≠ 0 := Fin.pos_iff_ne_zero.mp (lt_of_le_of_lt (zero_le _) h)) :
    (pred j h').succAbove k = succ k := by
    refine succAbove_above _ _ ?_
    rw [le_def, coe_castSucc, coe_pred]
    exact Nat.sub_le_of_le_add h₂

lemma succAbove_castSucc_of_coe_gt {i : Fin (m + 2)} {k : Fin m} (h : (k : ℕ) < i):
  i.succAbove (castSucc k) = castSucc (castSucc k) := succAbove_below _ _ h

lemma succAbove_castSucc_of_coe_le {i : Fin (m + 2)} {k : Fin m} (h : (i : ℕ) ≤ k):
  i.succAbove (castSucc k) = castSucc (succ k) := succ_castSucc _ ▸ succAbove_above _ _ h

lemma succAbove_succ_of_coe_gt {i : Fin (m + 2)} {k : Fin m} (h : (k + 1 : ℕ) < i):
  i.succAbove (succ k) = castSucc (succ k) := succAbove_below _ _ h

lemma succAbove_succ_of_coe_le {i : Fin (m + 2)} {k : Fin m} (h : (i : ℕ) ≤ k + 1):
  i.succAbove (succ k) = succ (succ k) := succAbove_above _ _ h

lemma _root_.Nat.not_gt_lt_succ {a b : ℕ} (h : b < a) (h₂ : a < b + 1) : False :=
    (Nat.le_of_lt_succ h₂).not_lt h

lemma succAbove_succAbove_predAbove!_symm {j : Fin (m + 2)} {i : Fin (m + 2)} {k : Fin m}
  (hij : j ≠ i) (hij' : i ≠ j := hij.symm) :
i.succAbove ((predAbove! i j hij).succAbove k) = j.succAbove ((predAbove! j i hij').succAbove k) := by
  wlog h : j < i generalizing i j with H ; exact (H _ _ (hij.lt_or_lt.resolve_left h)).symm
  rw [predAbove!_below h, predAbove!_above h]
  rcases lt_or_le (k : ℕ) (j : ℕ) with (h₂ | h₂)
  · simp only [succAbove_castLT_left_of_coe_lt_gt h h₂,
    succAbove_pred_left_of_coe_gt (lt_of_le_of_lt (Nat.succ_le_of_lt h₂) h),
    succAbove_castSucc_of_coe_gt, h₂, (h₂.trans h)]
  · rw [succAbove_castLT_left_of_coe_le h₂]
    rcases lt_or_le (k + 1: ℕ) (i : ℕ) with (h₃ | h₃) <;>
    [rw [succAbove_pred_left_of_coe_gt h₃] ; rw [succAbove_pred_left_of_coe_gt_le h h₃]]
    · rw [succAbove_castSucc_of_coe_le h₂, succAbove_succ_of_coe_gt h₃]
    · simp only [succAbove_succ_of_coe_le, (h₂.trans (Nat.lt_succ_self _).le), h₃]

lemma insertNth_succAbove_insertNth_predAbove'' {p : Fin m → α} {j : Fin (m + 2)} :
(succAbove j i).insertNth y ((predAbove i j).insertNth x p)  =
  j.insertNth x (insertNth i y p) := by
  simp_rw [insertNth_eq_iff, succAbove_succAbove_predAbove,
    insertNth_apply_succAbove, insertNth_apply_same, true_and,
    succAbove_succAbove_predAbove_succAbove, insertNth_apply_succAbove]

@[simp]
lemma insertNth_apply_ne {p : Fin m → α} {i j : Fin (m + 1)} (hij : i ≠ j) :
  insertNth j x p i = p (predAbove! j i hij) := by
  nth_rewrite 1 [← succAbove_predAbove! hij]
  rw [insertNth_apply_succAbove]

lemma insertNth_apply {p : Fin m → α} {i j : Fin (m + 1)} :
  insertNth j x p i = if h : i = j then x else p (predAbove! j i h) := by
  rcases (eq_or_ne i j) with (rfl | h)
  · rw [insertNth_apply_same, dif_pos rfl]
  · rw [insertNth_apply_ne h, dif_neg h]

lemma insertNth_apply_predAbove! {p : Fin m → α} {i j : Fin (m + 2)} (hij : i ≠ j) :
    insertNth j x (insertNth (predAbove! j i hij) y p) i = y :=by
    rw [insertNth_apply_ne hij, insertNth_apply_same]

lemma insertNth_insertNth_predAbove!_symm {p : Fin m → α} {i j : Fin (m + 2)} (hij : i ≠ j)
    (hij' : j ≠ i := hij.symm) :
    i.insertNth y ((i.predAbove! j hij').insertNth x p) =
    j.insertNth x (insertNth (j.predAbove! i hij) y p) := by
    simp_rw [insertNth_eq_iff, succAbove_predAbove!, insertNth_apply_predAbove!,
    insertNth_apply_same, true_and, succAbove_succAbove_predAbove!_symm hij.symm,
    insertNth_apply_succAbove]

lemma rev_last {m : ℕ} : (last m).rev = 0 := by
  rw [ext_iff, val_rev, val_last, val_zero, tsub_self]

lemma rev_zero {m : ℕ} : (0 : Fin (m + 1)).rev = (last m) := rfl

lemma lt_last_iff_ne_last {i : Fin (m + 1)} : i < last m ↔ i ≠ last m := lt_top_iff_ne_top

lemma rev_eq_zero_iff_last {i : Fin (m + 1)} : i.rev = 0 ↔ i = last m := by
  convert rev_inj
  exact rev_last.symm

lemma rev_ne_zero_iff_ne_last {i : Fin (m + 1)} : i.rev ≠ 0 ↔ i ≠ last m := by
  simp_rw [ne_eq, rev_eq_zero_iff_last]

lemma rev_pos_iff_lt_last {i : Fin (m + 1)} : 0 < i.rev ↔ i < last m := by
  simp_rw [lt_last_iff_ne_last, pos_iff_ne_zero]
  exact rev_ne_zero_iff_ne_last

lemma eq_zero_iff_rev_eq_last {i : Fin (m + 1)} : i = 0 ↔ i.rev = last m := by
  convert rev_rev i ▸ rev_eq_zero_iff_last

lemma ne_zero_iff_rev_ne_last {i : Fin (m + 1)} : i ≠ 0 ↔ i.rev ≠ last m := by
  convert rev_rev i ▸ rev_ne_zero_iff_ne_last

lemma pos_iff_rev_lt_last {i : Fin (m + 1)} : 0 < i ↔ i.rev < last m := by
  convert rev_rev i ▸ rev_pos_iff_lt_last

lemma rev_castSucc_eq_succ_rev {i : Fin m} : i.castSucc.rev = i.rev.succ := by
  simp_rw [ext_iff, val_rev, coe_castSucc, val_succ, val_rev,
    tsub_add_eq_add_tsub (Nat.succ_le_of_lt i.isLt)]

lemma rev_succ_eq_csucc_rev {i : Fin m}: i.succ.rev = i.rev.castSucc := by
  simp_rw [ext_iff, val_rev, coe_castSucc, val_succ, val_rev,
    Nat.succ_sub_succ_eq_sub]

lemma last_zero : last 0 = 0 := rfl

lemma last_one : last 1 = 1 := rfl

lemma last_zero_add_one : last (0 + 1) = 1 := rfl

end Fin
