import Controlbits.BitResiduum
import Controlbits.Fin

namespace Fin

lemma castLT_zero' [NeZero n] [NeZero m] (h := (Nat.pos_of_ne_zero (NeZero.ne n))):
castLT (0 : Fin m) h = 0 := rfl

lemma insertNth_succ_cons {j : Fin (m + 1)} {x y : α} {p : Fin m → α} :
    insertNth (α := fun _ => α) (succ j) x (cons y p) =
    cons y (insertNth j x p) := by
  simp_rw [insertNth_eq_iff, cons_succ, insertNth_apply_same, Function.funext_iff,
    forall_fin_succ, succ_succAbove_zero, cons_zero, succ_succAbove_succ, cons_succ,
    insertNth_apply_succAbove, implies_true, and_self]

lemma insertNth_castSucc_snoc {j : Fin (m + 1)} {x y : α} {p : Fin m → α} :
    insertNth (α := fun _ => α) (castSucc j) x (snoc p y) =
    snoc (insertNth j x p) y := by
  simp_rw [insertNth_eq_iff, snoc_castSucc, insertNth_apply_same, Function.funext_iff, true_and,
    forall_fin_succ', castSucc_succAbove_last, snoc_last, castSucc_succAbove_castSucc,
    snoc_castSucc, insertNth_apply_succAbove, implies_true, and_self]

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


def predPAbove {n : ℕ} (p : Fin (n + 1)) (i : Fin n) : Fin n :=
(p.succAbove i).predAbove! p (succAbove_ne _ _).symm

lemma predPAbove_def {p : Fin (n + 1)} {i : Fin n} : p.predPAbove i =
(p.succAbove i).predAbove! p (succAbove_ne _ _).symm := rfl

lemma succAbove_of_succAbove_predPAbove {p : Fin (n + 1)} {i : Fin n} :
  (p.succAbove i).succAbove (p.predPAbove i) = p := by
  rw [predPAbove_def, succAbove_predAbove!]

lemma predPAbove_of_succAbove_predPAbove {p : Fin (n + 1)} {i : Fin n} :
  (p.succAbove i).predPAbove (p.predPAbove i) = i := by
  simp_rw [predPAbove_def, succAbove_predAbove!, predAbove!_succAbove]

lemma predPAbove_predAbove! {y : Fin (n + 1)} {x : Fin (n + 1)} (hij : x ≠ y)
  (hij' : y ≠ x := hij.symm) : y.predPAbove (y.predAbove! x hij) = x.predAbove! y hij' := by
  simp_rw [predPAbove_def, succAbove_predAbove! hij]

#eval [0, 1, 2, 3].map (((3 : Fin 5).predPAbove) ∘ ((0 : Fin 5).predPAbove))

lemma predPAbove_predPAbove_predPAbove {y : Fin (n + 1)} {x : Fin (n + 1)} (hij : x ≠ y) :
  x.predPAbove (y.predPAbove (y.predAbove! x hij)) = y.predAbove! x hij := by
  simp_rw [predPAbove_predAbove! hij, predPAbove_predAbove! hij.symm]

lemma predPAbove_above {p : Fin (n + 1)} {i : Fin n} (h : p ≤ i.castSucc) :
p.predPAbove i = castLT p (lt_of_le_of_lt h (castSucc_lt_last _)) := by
  rw [predPAbove_def, predAbove!_below ((lt_succAbove_iff _ _).mpr h)]

lemma predPAbove_below {p : Fin (n + 1)} {i : Fin n} (h : i.castSucc < p) :
p.predPAbove i = pred p (lt_of_le_of_lt (zero_le _) h).ne.symm := by
  rw [predPAbove_def, predAbove!_above ((succAbove_lt_iff _ _).mpr h)]

lemma predPAbove_predPAbove_predPAbove' {y : Fin (n + 1)} {x : Fin (n + 1)} (hij : x ≠ y) :
  x.predPAbove (y.predPAbove k) = x.predPAbove (y.predPAbove k') := by
  rcases le_or_lt y (k.castSucc) with (h | h) <;>
  rcases le_or_lt y (k'.castSucc) with (h' | h')
  · rw [predPAbove_above h, predPAbove_above h']
  · rw [predPAbove_above h, predPAbove_below h']
    rcases lt_trichotomy x y with (hxy | rfl | hxy)
    · rw [predPAbove_above, predPAbove_above]
      rw [le_castSucc_iff]
      simp
      exact hxy
      simp [hxy.le]
    · rw [predPAbove_above, predPAbove_below]
    · sorry
  · rw [predPAbove_below h, predPAbove_above h']
  · rw [predPAbove_below h, predPAbove_below h']
/-
def succAbove_predPAbove_equiv : Equiv.Perm (Fin (n + 1) × Fin n) where
  toFun := fun ⟨p, i⟩ => (p.succAbove i, p.predPAbove i)
  invFun := fun ⟨p, i⟩ => (p.succAbove i, p.predPAbove i)
  left_inv _ := by simp_rw [predPAbove_of_succAbove_predPAbove, succAbove_of_succAbove_predPAbove]
  right_inv _ := by simp_rw [predPAbove_of_succAbove_predPAbove, succAbove_of_succAbove_predPAbove]

lemma predPAbove_eq {p : Fin (n + 1)} {i : Fin n}:
predPAbove p i = predAbove i p := by
  rw [predAbove]
  split_ifs with H
  · exact predPAbove_below H
  · exact predPAbove_above (le_of_not_lt H)

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

end Fin

lemma getBit_succAbove (k : Fin (m + 1)) (j : Fin (m + 2)) (q : Fin (2^(m + 2))) :
    getBit (j.succAbove k) q = getBit k (getRes j q) := by
    simp_rw [getBit_apply, getRes_apply, getBitRes_apply, Equiv.symm_apply_apply]

lemma getBitRes_symm_getBitRes_symm_comm {i j : Fin (m + 2)} (hij : i ≠ j) (b₁ b₂ p)
  (hij' : j ≠ i := hij.symm) :
    (getBitRes j).symm (b₁, (getBitRes (j.predAbove! i hij)).symm (b₂, p)) =
    (getBitRes i).symm (b₂, (getBitRes (i.predAbove! j hij')).symm (b₁, p)) := by
    simp_rw [getBitRes_symm_apply, Equiv.symm_apply_apply,
    Fin.insertNth_insertNth_predAbove!_symm hij]

lemma getBitRes_snd_getBitRes_snd_comm {i j : Fin (m + 2)} (hij : i ≠ j) (q : Fin (2^(m + 2)))
    (hij' : j ≠ i := hij.symm) :
    ((getBitRes (j.predAbove! i hij)) ((getBitRes j) q).2).2 =
    ((getBitRes (i.predAbove! j hij')) ((getBitRes i) q).2).2 := by
    simp_rw [getBitRes_apply, Equiv.symm_apply_apply,
    Fin.succAbove_succAbove_predAbove!_symm hij hij']

lemma fst_getBitRes_eq_fst_getBitRes_snd_getBitRes {i j : Fin (m + 2)} (hij : i ≠ j)
    (q : Fin (2^(m + 2))) : ((getBitRes i) q).1 =
    ((getBitRes (j.predAbove! i hij)) ((getBitRes j) q).2).1 := by
    simp_rw [getBitRes_apply, Equiv.symm_apply_apply, Fin.succAbove_predAbove! hij]

lemma getBitRes_symm_getBitRes_symm_op (k : Fin (m + 1)) (j : Fin (m + 2)) (b₁ b₂ p)
(hjk : j ≠ Fin.succAbove j k := (Fin.succAbove_ne _ _).symm) :
    (getBitRes j).symm (b₁, (getBitRes k).symm (b₂, p)) =
    (getBitRes (j.succAbove k)).symm (b₂,
    (getBitRes ((j.succAbove k).predAbove! j hjk)).symm (b₁, p)) := by
    nth_rewrite 1 [← Fin.predAbove!_succAbove (i := j) (k := k)]
    apply getBitRes_symm_getBitRes_symm_comm

lemma getBitRes_snd_getBitRes_snd_op (k : Fin (m + 1)) (j : Fin (m + 2)) (q : Fin (2^(m + 2)))
  (hjk : j ≠ Fin.succAbove j k := (Fin.succAbove_ne _ _).symm) :
    ((getBitRes k) ((getBitRes j) q).2).2 =
    ((getBitRes ((j.succAbove k).predAbove! j hjk))
    ((getBitRes (j.succAbove k)) q).2).2 := by
    nth_rewrite 1 [← Fin.predAbove!_succAbove (i := j) (k := k)]
    apply getBitRes_snd_getBitRes_snd_comm

lemma getBitRes_fst_getBitRes_eq_getBitRes_fst (k : Fin (m + 1)) (j : Fin (m + 2))
    (q : Fin (2^(m + 2))) : ((getBitRes k) ((getBitRes j) q).2).1 =
    ((getBitRes (j.succAbove k)) q).1 := by
    nth_rewrite 1 [← Fin.predAbove!_succAbove (i := j) (k := k)]
    exact (fst_getBitRes_eq_fst_getBitRes_snd_getBitRes _ _).symm

lemma mergeBitRes_mergeBitRes_comm {i j : Fin (m + 2)} (hij : i ≠ j) (hij' : j ≠ i := hij.symm) :
    mergeBitRes j b₁ (mergeBitRes (j.predAbove! i hij) b₂ p)  =
    mergeBitRes i b₂ (mergeBitRes (i.predAbove! j hij') b₁ p) :=
    by apply getBitRes_symm_getBitRes_symm_comm

lemma getRes_getRes_comm {i j : Fin (m + 2)} (hij : i ≠ j) (hij' : j ≠ i := hij.symm)
    (q : Fin (2^(m + 2))) :
    getRes (j.predAbove! i hij) (getRes j q) = getRes (i.predAbove! j hij') (getRes i q) := by
    apply getBitRes_snd_getBitRes_snd_comm

lemma mergeBitRes_mergeBitRes_op (k : Fin (m + 1)) (j : Fin (m + 2))
    (hjk : j ≠ Fin.succAbove j k := (Fin.succAbove_ne _ _).symm) :
    mergeBitRes j b₁ (mergeBitRes k b₂ p) =
    mergeBitRes (j.succAbove k) b₂ (mergeBitRes ((j.succAbove k).predAbove! j hjk) b₁ p) := by
    apply getBitRes_symm_getBitRes_symm_op

lemma getRes_getRes_op (k : Fin (m + 1)) (j : Fin (m + 2))
    (hjk : j ≠ Fin.succAbove j k := (Fin.succAbove_ne _ _).symm) : getRes k (getRes j q) =
    getRes ((j.succAbove k).predAbove! j hjk) (getRes (j.succAbove k) q) := by
    apply getBitRes_snd_getBitRes_snd_op

lemma getBit_getRes_eq_getBit (k : Fin (m + 1)) (j : Fin (m + 2)) (q : Fin (2^(m + 2))) :
    getBit k (getRes j q) = getBit (j.succAbove k) q := by
    apply getBitRes_fst_getBitRes_eq_getBitRes_fst

lemma mergeBitRes_eq_mergeBitRes_mergeBitRes_predAbove! {i j : Fin (m + 2)} (hij : i ≠ j)
    (q : Fin (2^(m + 2))) : mergeBitRes i b q = mergeBitRes j (getBit (i.predAbove! j hij.symm) q)
    (mergeBitRes (j.predAbove! i hij) b (getRes (i.predAbove! j hij.symm) q)) := by
    nth_rewrite 1 [← mergeBitRes_getBit_getRes (q := q) (i := i.predAbove! j hij.symm)]
    simp_rw [mergeBitRes_mergeBitRes_comm hij]

lemma mergeBitRes_eq_mergeBitRes_succAbove (k : Fin (m + 1)) (j : Fin (m + 2))
    (hjk : j ≠ Fin.succAbove j k := (Fin.succAbove_ne _ _).symm) :
    mergeBitRes j b q = mergeBitRes (j.succAbove k) (getBit k q)
    (mergeBitRes ((j.succAbove k).predAbove! j hjk) b (getRes k q)) := by
    nth_rewrite 1 [← mergeBitRes_getBit_getRes (q := q) (i := k)]
    rw [mergeBitRes_mergeBitRes_op]

lemma getBit_eq_getBit_getRes {i j : Fin (m + 2)} (hij : i ≠ j) (q : Fin (2^(m + 2))):
    getBit i q = getBit (j.predAbove! i hij) (getRes j q) := by
    apply fst_getBitRes_eq_fst_getBitRes_snd_getBitRes hij

lemma getRes_eq_mergeBitRes_getBit_getRes_getRes {i j : Fin (m + 2)} (hij : i ≠ j) :
    getRes i q = mergeBitRes (i.predAbove! j hij.symm) (getBit j q)
    (getRes (j.predAbove! i hij) (getRes j q)) := by
    simp_rw [eq_mergeBitRes_iff, getRes_getRes_comm hij,
    getBit_eq_getBit_getRes hij.symm, true_and]

lemma mergeBitRes_predAbove {i j : Fin (m + 2)} (hij : i ≠ j) :
    mergeBitRes (i.predAbove! j hij.symm) b p =
    getRes i (mergeBitRes j b (mergeBitRes (j.predAbove! i hij) (getBit i q) p)) := by
    simp_rw [getRes_eq_mergeBitRes_getBit_getRes_getRes hij, getBit_mergeBitRes, getRes_mergeBitRes]

lemma getBit_predAbove {i j : Fin (m + 2)} (hij : i ≠ j) (q : Fin (2^(m + 1))):
    getBit (j.predAbove! i hij) q = getBit i (mergeBitRes j b q) := by
    rw [getBit_eq_getBit_getRes hij, getRes_mergeBitRes]

lemma getRes_predAbove {i j : Fin (m + 2)} (hij : i ≠ j) (hij' : j ≠ i := hij.symm)
    (q : Fin (2^(m + 1))) : getRes (j.predAbove! i hij) p = getRes (i.predAbove! j hij')
    (getRes i (mergeBitRes j b p)) := by
    rw [getRes_getRes_comm hij.symm, getRes_mergeBitRes]

lemma mergeBitRes_succAbove (k : Fin (m + 1)) (j : Fin (m + 2))
    (hjk : j ≠ Fin.succAbove j k := (Fin.succAbove_ne _ _).symm) :
    mergeBitRes (j.succAbove k) b₂ q = mergeBitRes j (getBit ((j.succAbove k).predAbove! j hjk) q)
    (mergeBitRes k b₂ (getRes ((j.succAbove k).predAbove! j hjk) q)) := by
    rw [mergeBitRes_mergeBitRes_op k j hjk, mergeBitRes_getBit_getRes]

lemma getRes_succAbove (k : Fin (m + 1)) (j : Fin (m + 2))
    (q : Fin (2^(m + 2))) (hjk : j ≠ Fin.succAbove j k := (Fin.succAbove_ne _ _).symm) :
    getRes (j.succAbove k) q =
    mergeBitRes ((j.succAbove k).predAbove! j hjk) (getBit j q) (getRes k (getRes j q)) := by
    rw [getRes_eq_mergeBitRes_getBit_getRes_getRes hjk.symm, Fin.predAbove!_succAbove]

lemma flipBit_succAbove_apply {i j : Fin (m + 2)} (hij : i ≠ j) :
flipBit i q = mergeBitRes j (getBit j q) (flipBit (j.predAbove! i hij) (getRes j q)) := by
    simp_rw [flipBit_apply, mergeBitRes_mergeBitRes_comm hij, getBit_eq_getBit_getRes hij,
    getRes_eq_mergeBitRes_getBit_getRes_getRes hij]

lemma getBit_flipBit_ne {i : Fin (m + 1)} (hij : i ≠ j) : getBit i (flipBit j q) = getBit i q := by
  rcases Fin.exists_succAbove_eq hij with ⟨k, rfl⟩
  cases m
  · exact k.elim0
  · simp_rw [getBit_succAbove, getRes_flipBit]

lemma flipBit_bitInvar (h : i ≠ j) : bitInvar i ⇑(flipBit j) :=
  bitInvar_of_getBit_apply_eq_getBit (fun _ => (getBit_flipBit_ne h))

lemma resCondFlip_succAbove_apply {i j : Fin (m + 2)} (hij : i ≠ j) :
  resCondFlip i c q = mergeBitRes j (getBit j q) ((resCondFlip (j.predAbove! i hij) fun p =>
  c (mergeBitRes (i.predAbove! j hij.symm) (getBit j q) p)) (getRes j q)) := by
  simp_rw [resCondFlip_apply, getRes_eq_mergeBitRes_getBit_getRes_getRes hij,
    Bool.apply_cond (fun x => mergeBitRes j (getBit j q) x), mergeBitRes_getBit_getRes,
    flipBit_succAbove_apply hij]

lemma resCondFlip_succAbove_eq (c) {i j : Fin (m + 2)} (hij : i ≠ j) :
  resCondFlip i c = bitInvarMulEquiv j
  (fun b => resCondFlip (j.predAbove! i hij) (fun p => c (mergeBitRes (i.predAbove! j hij.symm) b p))) := by
  ext ; simp_rw [resCondFlip_succAbove_apply hij, bitInvarMulEquiv_apply_coe_apply, endoOfBoolArrowEndo_def]

lemma getBit_resCondFlip_ne {i : Fin (m + 1)} (hij : i ≠ j) :
  getBit i (resCondFlip j c q) = getBit i q := by
  rw [resCondFlip_apply]
  rcases (c (getRes j q)).dichotomy with (h | h) <;> simp_rw [h]
  · rw [cond_false]
  · rw [cond_true, getBit_flipBit_ne hij]

lemma resCondFlip_bitInvar (h : i ≠ j) : bitInvar i ⇑(resCondFlip j c) :=
  bitInvar_of_getBit_apply_eq_getBit (fun _ => (getBit_resCondFlip_ne h))

lemma resCondFlip_mem_bitInvarSubmonoid (h : i ≠ j) : ⇑(resCondFlip j c) ∈ bitInvarSubmonoid i :=
  resCondFlip_bitInvar h

lemma resCondFlip_mem_bitInvarSubgroup (h : i ≠ j) : resCondFlip j c ∈ bitInvarSubgroup i :=
  resCondFlip_mem_bitInvarSubmonoid h
-/
