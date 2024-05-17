import Mathlib.Tactic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Ring.Defs
import Controlbits.Bool
import Controlbits.Fin
import Controlbits.Equivs
import Controlbits.Submonoid
import Controlbits.FunctionEnd

section BitRes

section GetMerge

def getBitRes (i : Fin (m + 1)) : Fin (2^(m + 1)) ≃ Bool × Fin (2^m) :=
calc
  _ ≃ (Fin (m + 1) → Fin 2)   := finFunctionFinEquiv.symm
  _ ≃ Fin 2 × (Fin m → Fin 2) := Equiv.piFinSuccAbove _ i
  _ ≃ _                       := finTwoEquiv.prodCongr finFunctionFinEquiv

@[simp]
lemma getBitRes_apply (j : Fin (m + 1)) (q : Fin (2 ^ (m + 1))) : (getBitRes j) q =
  (finTwoEquiv (finFunctionFinEquiv.symm q j),
  finFunctionFinEquiv (fun i => finFunctionFinEquiv.symm q (j.succAbove i))) := rfl

@[simp]
lemma getBitRes_symm_apply (i : Fin (m + 1)) (bp : Bool × Fin (2 ^ m)) : (getBitRes i).symm bp =
  finFunctionFinEquiv (i.insertNth (finTwoEquiv.symm bp.fst) (finFunctionFinEquiv.symm bp.snd)) :=
  rfl

def getBit (i : Fin (m + 1)) : Fin (2^(m + 1)) → Bool := Prod.fst ∘ (getBitRes i)

def getRes (i : Fin (m + 1)) : Fin (2^(m + 1)) → Fin (2^m) := Prod.snd ∘ (getBitRes i)

def mergeBitRes (i : Fin (m + 1)) := Function.curry (getBitRes i).symm

lemma getBit_apply : getBit i q = (getBitRes i q).fst := rfl

lemma getRes_apply : getRes i q = (getBitRes i q).snd := rfl

lemma mergeBitRes_apply : mergeBitRes i b p = (getBitRes i).symm (b, p) := rfl

lemma getBitRes_apply_zero : getBitRes i 0 = (false, 0) := by
ext <;> simp only [getBitRes_apply, finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply,
  Fin.val_zero', Nat.zero_div, Nat.zero_mod, Fin.zero_eta, finTwoEquiv_apply, zero_ne_one,
  decide_False, Equiv.ofRightInverseOfCardLE_apply, Fin.val_zero, zero_mul, Finset.sum_const_zero]

lemma getBit_apply_zero : getBit i 0 = false := by
rw [getBit_apply, getBitRes_apply_zero]

lemma getRes_apply_zero : getRes i 0 = 0 := by
rw [getRes_apply, getBitRes_apply_zero]

lemma mergeBitRes_apply_false_zero : mergeBitRes i false 0 = 0 := by
rw [mergeBitRes_apply, ← getBitRes_apply_zero (i := i), Equiv.symm_apply_apply]

lemma getBitRes_apply_two_pow {i : Fin (m + 1)}: getBitRes i ⟨2^(i : ℕ),
  pow_lt_pow_right one_lt_two i.isLt⟩ = (true, 0) := by
  ext
  · simp only [getBitRes_apply, finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply,
    gt_iff_lt, zero_lt_two, pow_pos, Nat.div_self, Nat.one_mod, Fin.mk_one, finTwoEquiv_apply,
    decide_True, Equiv.ofRightInverseOfCardLE_apply]
  · simp only [getBitRes_apply, finFunctionFinEquiv_apply_val, finFunctionFinEquiv_symm_apply_val,
    Fin.val_zero', Finset.sum_eq_zero_iff, Finset.mem_univ, mul_eq_zero, forall_true_left]
    refine' fun x => Or.inl _
    rcases (Fin.succAbove_ne i x).lt_or_lt with h | h <;> rw [Fin.lt_iff_val_lt_val] at h
    · rw [Nat.pow_div h.le zero_lt_two, Nat.pow_mod, Nat.mod_self,
        Nat.zero_pow (Nat.sub_pos_of_lt h), Nat.zero_mod]
    · rw [Nat.div_eq_of_lt (pow_lt_pow_right one_lt_two h), Nat.zero_mod]

lemma getBit_apply_two_pow {i : Fin (m + 1)} : getBit i ⟨2^(i : ℕ),
  pow_lt_pow_right one_lt_two i.isLt⟩ = true := by
  rw [getBit_apply, getBitRes_apply_two_pow]

lemma getBit_apply_zero_one : getBit 0 (1 : Fin (2^(m + 1))) = true := by
  convert getBit_apply_two_pow
  rw [Fin.val_one', Nat.mod_eq_of_lt (Nat.one_lt_pow' _ _ ), Fin.val_zero, pow_zero]

lemma getRes_apply_two_pow {i : Fin (m + 1)} :
  getRes i ⟨2^(i : ℕ), pow_lt_pow_right one_lt_two i.isLt⟩ = 0 := by
  rw [getRes_apply, getBitRes_apply_two_pow]

lemma mergeBitRes_apply_true_zero {i : Fin (m + 1)} :
  mergeBitRes i true 0 = ⟨2^(i : ℕ), pow_lt_pow_right one_lt_two i.isLt⟩ := by
  rw [mergeBitRes_apply, ← getBitRes_apply_two_pow (i := i), Equiv.symm_apply_apply]

def getBitResZero : Fin (2^(m + 1)) ≃ Bool × Fin (2^m) :=
 calc
  _ ≃ _ := finProdFinEquiv.symm
  _ ≃ _ := Equiv.prodComm ..
  _ ≃ _ := finTwoEquiv.prodCongr (Equiv.refl _)

lemma getBitResZero_apply : getBitResZero q = (finTwoEquiv q.modNat, q.divNat) := rfl

lemma getBitResZero_symm_apply : getBitResZero.symm (b, p) =
  finProdFinEquiv (p, bif b then 1 else 0) := by cases b <;> rfl

lemma getBitRes_zero : getBitRes (0 : Fin (m + 1)) = getBitResZero := by
  ext q : 1
  simp_rw [getBitRes_apply, getBitResZero_apply, Fin.zero_succAbove, finFunctionFinEquiv,
    Equiv.ofRightInverseOfCardLE_symm_apply, Fin.val_zero, pow_zero, Nat.div_one,
    finTwoEquiv_apply, Fin.val_succ, Equiv.ofRightInverseOfCardLE_apply,
    Nat.pow_eq, Prod.mk.injEq, decide_eq_decide, Fin.ext_iff, Fin.val_one, Fin.coe_modNat,
    Finset.sum_fin_eq_sum_range, dite_eq_ite, Fin.coe_divNat, true_and]
  rw [Finset.sum_ite_of_true (h := fun _ H => (Finset.mem_range.mp H))]
  refine' Nat.eq_of_mul_eq_mul_left (zero_lt_two)
    (add_right_cancel (b := (q : ℕ) / 2 ^ 0 % 2 * 2 ^ 0) _)
  simp_rw [Finset.mul_sum, mul_left_comm (2 : ℕ), ← Nat.pow_succ', Nat.succ_eq_add_one,
  ← Finset.sum_range_succ' (fun x => (q : ℕ) / 2 ^ x % 2 * 2 ^ x), pow_zero, Nat.div_one,
    mul_one, Nat.div_add_mod, Finset.sum_range, ← finFunctionFinEquiv_symm_apply_val,
    ← finFunctionFinEquiv_apply_val, Equiv.apply_symm_apply]

lemma getBitRes_zero_apply : getBitRes (0 : Fin (m + 1)) q = (finTwoEquiv q.modNat, q.divNat) := by
  simp_rw [getBitRes_zero, getBitResZero_apply]

lemma getBitRes_zero_symm_apply : (getBitRes (0 : Fin (m + 1))).symm (b, p) =
  finProdFinEquiv (p, bif b then 1 else 0) := by simp_rw [getBitRes_zero, getBitResZero_symm_apply]

lemma getBit_zero : getBit 0 q = finTwoEquiv q.modNat := by
  simp_rw [getBit_apply, getBitRes_zero_apply]

lemma getRes_zero : getRes 0 q = q.divNat := by
  simp_rw [getRes_apply, getBitRes_zero_apply]

lemma mergeBitRes_zero : mergeBitRes 0 b p = finProdFinEquiv (p, (bif b then 1 else 0)) := by
  simp_rw [mergeBitRes_apply, getBitRes_zero_symm_apply]

lemma mergeBitRes_zero_divNat_modNat : ((mergeBitRes 0 b p).divNat, (mergeBitRes 0 b p).modNat) =
  (p, (bif b then 1 else 0)) := by
  simp_rw [← finProdFinEquiv_symm_apply, Equiv.symm_apply_eq]
  exact mergeBitRes_zero

lemma mergeBitRes_zero_divNat : (mergeBitRes 0 b p).divNat = p :=
(Prod.ext_iff.mp (mergeBitRes_zero_divNat_modNat (b := b) (p := p))).1

lemma mergeBitRes_zero_modNat : (mergeBitRes 0 b p).modNat = bif b then 1 else 0 :=
(Prod.ext_iff.mp (mergeBitRes_zero_divNat_modNat (b := b) (p := p))).2

lemma mergeBitRes_zero_apply_true_zero_eq_one : mergeBitRes (0 : Fin (m + 1)) true 0 = 1 := by
  simp_rw [mergeBitRes_zero, Fin.ext_iff, finProdFinEquiv_apply_val, Fin.val_zero', mul_zero,
  add_zero, Bool.cond_true, Fin.val_one, Fin.val_one', ← Nat.pow_succ,
  Nat.mod_eq_of_lt (Nat.one_lt_pow' _ _ )]

lemma mergeBitRes_true_base_eq_one : mergeBitRes (m := 0) i true p = 1 := by
rw [Fin.eq_zero p, Fin.eq_zero i] ; exact mergeBitRes_zero_apply_true_zero_eq_one

lemma mergeBitRes_false_base_eq_zero : mergeBitRes (m := 0) i false p = 0 := by
rw [Fin.eq_zero p] ; exact mergeBitRes_apply_false_zero

lemma getBit_base : getBit (m := 0) i q = decide (q = 1) := by
  rw [Fin.eq_zero i]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

lemma getRes_base : getRes (m := 0) i q = 0 := by
  rw [Fin.eq_zero i]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

def getBitResSucc (i : Fin (m + 1)) : Fin (2^(m + 2)) ≃ Bool × Fin (2^(m + 1)) :=
calc
  _ ≃ _ := getBitRes 0
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes 0).symm

lemma getBitResSucc_apply {i : Fin (m + 1)} :
    getBitResSucc i q = (((getBitRes i) ((getBitRes 0) q).2).1,
    (getBitRes 0).symm (((getBitRes 0) q).1, ((getBitRes i) ((getBitRes 0) q).2).2)) := rfl

lemma getBitResSucc_symm_apply {i : Fin (m + 1)} : (getBitResSucc i).symm (b, p) =
    (getBitRes 0).symm ((getBitRes 0 p).1, (getBitRes i).symm (b, (getBitRes 0 p).2)) := rfl

lemma getBitRes_succ {i : Fin (m + 1)} : getBitRes (i.succ) = getBitResSucc i := by
  simp_rw [Equiv.ext_iff, getBitResSucc_apply,
    getBitRes_apply, getBitRes_symm_apply, Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_zero, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_succ, true_and, implies_true]

lemma getBitRes_succ_apply {i : Fin (m + 1)} : getBitRes (i.succ) q =
    (((getBitRes i) ((getBitRes 0) q).2).1,
    (getBitRes 0).symm (((getBitRes 0) q).1, ((getBitRes i) ((getBitRes 0) q).2).2)) := by
  rw [getBitRes_succ, getBitResSucc_apply]

lemma getBitRes_succ_symm_apply {i : Fin (m + 1)} : (getBitRes (i.succ)).symm (b, p) =
    (getBitRes 0).symm ((getBitRes 0 p).1, (getBitRes i).symm (b, (getBitRes 0 p).2)) := by
  rw [getBitRes_succ, getBitResSucc_symm_apply]

lemma getRes_succ (i : Fin (m + 1)) : getRes (i.succ) q =
    mergeBitRes 0 (getBit 0 q) (getRes i (getRes 0 q)) := by
  simp_rw [getRes_apply, mergeBitRes_apply, getBit_apply, getBitRes_succ_apply]

lemma getBit_succ (i : Fin (m + 1)) :
    getBit (i.succ) q = getBit i (getRes 0 q) := by
  simp_rw [getRes_apply, getBit_apply, getBitRes_succ_apply]

lemma mergeBitRes_succ (i : Fin (m + 1)) : mergeBitRes i.succ b q =
    mergeBitRes 0 (getBit 0 q) (mergeBitRes i b (getRes 0 q)) := by
  simp_rw [mergeBitRes_apply, getBit_apply, getRes_apply, getBitRes_succ_symm_apply]

lemma getBitResLast_symm_apply : getBitResZero.symm (b, p) =
  finProdFinEquiv (p, bif b then 1 else 0) := by cases b <;> rfl

def getBitResCastSucc (i : Fin (m + 1)) : Fin (2^(m + 2)) ≃ Bool × Fin (2^(m + 1)) :=
calc
  _ ≃ _ := getBitRes (Fin.last _)
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes (Fin.last _)).symm

lemma getBitResCastSucc_apply {i : Fin (m + 1)} :
    getBitResCastSucc i q = (((getBitRes i) ((getBitRes (Fin.last _)) q).2).1,
    (getBitRes (Fin.last _)).symm (((getBitRes (Fin.last _)) q).1,
    ((getBitRes i) ((getBitRes (Fin.last _)) q).2).2)) := rfl

lemma getBitResCastSucc_symm_apply {i : Fin (m + 1)} : (getBitResCastSucc i).symm (b, p) =
    (getBitRes (Fin.last _)).symm ((getBitRes (Fin.last _) p).1,
    (getBitRes i).symm (b, (getBitRes (Fin.last _) p).2)) := rfl

lemma getBitRes_castSucc {i : Fin (m + 1)} : getBitRes (i.castSucc) = getBitResCastSucc i := by
  simp_rw [Equiv.ext_iff, getBitResCastSucc_apply,
    getBitRes_apply, getBitRes_symm_apply, Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_last, Fin.castSucc_succAbove_last,
    Fin.castSucc_succAbove_castSucc, true_and, implies_true]

lemma getBitRes_castSucc_apply {i : Fin (m + 1)} : getBitRes (i.castSucc) q =
    (((getBitRes i) ((getBitRes (Fin.last _)) q).2).1,
    (getBitRes (Fin.last _)).symm (((getBitRes (Fin.last _)) q).1,
    ((getBitRes i) ((getBitRes (Fin.last _)) q).2).2)) := by
  rw [getBitRes_castSucc, getBitResCastSucc_apply]

lemma getBitRes_castSucc_symm_apply {i : Fin (m + 1)} : (getBitRes (i.castSucc)).symm (b, p) =
    (getBitRes (Fin.last _)).symm ((getBitRes (Fin.last _) p).1,
    (getBitRes i).symm (b, (getBitRes (Fin.last _) p).2)) := by
  rw [getBitRes_castSucc, getBitResCastSucc_symm_apply]

lemma getRes_castSucc (i : Fin (m + 1)) : getRes (i.castSucc) q =
    mergeBitRes (Fin.last _) (getBit (Fin.last _) q) (getRes i (getRes (Fin.last _) q)) := by
  simp_rw [getRes_apply, mergeBitRes_apply, getBit_apply, getBitRes_castSucc_apply]

lemma getBit_castSucc (i : Fin (m + 1)) :
    getBit (i.castSucc) q = getBit i (getRes (Fin.last _) q) := by
  simp_rw [getRes_apply, getBit_apply, getBitRes_castSucc_apply]

lemma mergeBitRes_castSucc (i : Fin (m + 1)) : mergeBitRes i.castSucc b q =
    mergeBitRes (Fin.last _) (getBit (Fin.last _) q) (mergeBitRes i b (getRes (Fin.last _) q)) := by
  simp_rw [mergeBitRes_apply, getBit_apply, getRes_apply, getBitRes_castSucc_symm_apply]

def getBitResSuccAbove (j : Fin (m + 2)) (i : Fin (m + 1)) :
  Fin (2^(m + 2)) ≃ Bool × Fin (2^(m + 1)) :=
calc
  _ ≃ _ := getBitRes j
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes i)
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := (Equiv.prodComm _ _).prodCongr (Equiv.refl _)
  _ ≃ _ := (Equiv.prodAssoc _ _ _)
  _ ≃ _ := (Equiv.refl _).prodCongr (getBitRes (i.predAbove j)).symm

lemma getBitResSuccAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
    getBitResSuccAbove j i q = (((getBitRes i) ((getBitRes j) q).2).1,
    (getBitRes (i.predAbove j)).symm (((getBitRes j) q).1,
    ((getBitRes i) ((getBitRes j) q).2).2)) := rfl

lemma getBitResSuccAbove_symm_apply : (getBitResSuccAbove j i).symm (b, p) =
    (getBitRes j).symm ((getBitRes (i.predAbove j) p).1,
    (getBitRes i).symm (b, (getBitRes (i.predAbove j) p).2)) := rfl

lemma getBitRes_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} :
  getBitRes (j.succAbove i) = getBitResSuccAbove j i := by
  simp_rw [Equiv.ext_iff, getBitResSuccAbove_apply,
    getBitRes_apply, getBitRes_symm_apply, Equiv.symm_apply_apply,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Fin.eq_insertNth_iff, Fin.succAbove_succAbove_predAbove,
    Fin.succAbove_succAbove_predAbove_succAbove, true_and, implies_true]

lemma getBitRes_succAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} : getBitRes (j.succAbove i) q =
    (((getBitRes i) ((getBitRes j) q).2).1,
    (getBitRes (i.predAbove j)).symm (((getBitRes j) q).1,
    ((getBitRes i) ((getBitRes j) q).2).2)) := by
  rw [getBitRes_succAbove, getBitResSuccAbove_apply]

lemma getBitRes_succAbove_symm_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
    (getBitRes (j.succAbove i)).symm (b, p) =
    (getBitRes j).symm ((getBitRes (i.predAbove j) p).1,
    (getBitRes i).symm (b, (getBitRes (i.predAbove j) p).2)) := by
  rw [getBitRes_succAbove, getBitResSuccAbove_symm_apply]

lemma getRes_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} : getRes (j.succAbove i) q =
    mergeBitRes (i.predAbove j) (getBit j q) (getRes i (getRes j q)) := by
  simp_rw [getRes_apply, mergeBitRes_apply, getBit_apply, getBitRes_succAbove_apply]

lemma getBit_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} :
    getBit (j.succAbove i) q = getBit i (getRes j q) := by
  simp_rw [getRes_apply, getBit_apply, getBitRes_succAbove_apply]

lemma mergeBitRes_succAbove {j : Fin (m + 2)} {i : Fin (m + 1)} : mergeBitRes (j.succAbove i) b q =
    mergeBitRes j (getBit (i.predAbove j) q) (mergeBitRes i b (getRes (i.predAbove j) q)) := by
  simp_rw [mergeBitRes_apply, getBit_apply, getRes_apply, getBitRes_succAbove_symm_apply]

@[simp]
lemma getBit_mergeBitRes : getBit i (mergeBitRes i b p) = b := by
simp_rw [getBit_apply, mergeBitRes_apply, Equiv.apply_symm_apply]

@[simp]
lemma getRes_mergeBitRes  : getRes i (mergeBitRes i b p) = p := by
simp_rw [getRes_apply, mergeBitRes_apply, Equiv.apply_symm_apply]

@[simp]
lemma mergeBitRes_getBit_getRes : mergeBitRes i (getBit i q) (getRes i q) = q := by
simp_rw [getRes_apply, mergeBitRes_apply, getBit_apply, Prod.mk.eta, Equiv.symm_apply_apply]

lemma mergeBitRes_surj (i : Fin (m + 1)) (q : Fin (2^(m + 1))) :
  ∃ b p, mergeBitRes i b p = q :=
  ⟨getBit i q, getRes i q, mergeBitRes_getBit_getRes⟩

lemma mergeBitRes_Bool_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) :
  b₁ = b₂ := by
  have h₂ := (congrArg (getBit i) h) ; simp only [getBit_mergeBitRes] at h₂ ; exact h₂

lemma mergeBitRes_Fin_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) :
  p₁ = p₂ := by
  have h₂ := (congrArg (getRes i) h) ; simp_rw [getRes_mergeBitRes] at h₂ ; exact h₂

lemma mergeBitRes_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) :
  b₁ = b₂ ∧ p₁ = p₂ :=
  ⟨mergeBitRes_Bool_inj i h, mergeBitRes_Fin_inj i h⟩

lemma mergeBitRes_inj_iff (i : Fin (m + 1)) : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂ ↔
  b₁ = b₂ ∧ p₁ = p₂ :=
  ⟨mergeBitRes_inj i, by rintro ⟨rfl, rfl⟩ ; rfl⟩

lemma getRes_getBit_inj (i : Fin (m + 1)) (h₁ : getBit i q₁ = getBit i q₂)
  (h₂ : getRes i q₁ = getRes i q₂) : q₁ = q₂ :=
  by rw [← mergeBitRes_getBit_getRes (i := i) (q := q₁), h₁, h₂, mergeBitRes_getBit_getRes]

lemma getRes_getBit_inj_iff (i : Fin (m + 1)) :
getBit i q₁ = getBit i q₂ ∧ getRes i q₁ = getRes i q₂ ↔ q₁ = q₂ :=
⟨and_imp.mpr (getRes_getBit_inj i), by rintro rfl ; exact ⟨rfl, rfl⟩⟩

lemma mergeBitRes_eq_iff :
  mergeBitRes i b p = q ↔ (getBit i q = b) ∧ (getRes i q = p) :=
⟨fun H => H ▸ ⟨getBit_mergeBitRes, getRes_mergeBitRes⟩, fun ⟨rfl, rfl⟩ => mergeBitRes_getBit_getRes⟩

lemma eq_mergeBitRes_iff :
    q = mergeBitRes i b p ↔ (getBit i q = b) ∧ (getRes i q = p) := by
    rw [← mergeBitRes_eq_iff, eq_comm]

lemma mergeBitRes_ne_iff :
    mergeBitRes i b p ≠ q ↔ (getBit i q ≠ b) ∨ (getRes i q ≠ p) := by
    simp_rw [ne_eq, mergeBitRes_eq_iff, Decidable.not_and_iff_or_not]

lemma ne_mergeBitRes_iff :
    q ≠ mergeBitRes i b p ↔ (getBit i q ≠ b) ∨ (getRes i q ≠ p) := by
    rw [← mergeBitRes_ne_iff, ne_comm]

lemma mergeBitRes_getRes_of_getBit_eq (h : getBit i q = b) : mergeBitRes i b (getRes i q) = q := by
simp_rw [← h, mergeBitRes_getBit_getRes]

lemma mergeBitRes_getRes_cases (i : Fin (m + 1)) (q : Fin (2^(m + 1))) :
(getBit i q = false ∧ mergeBitRes i false (getRes i q) = q) ∨
(getBit i q = true ∧ mergeBitRes i true (getRes i q) = q) := by
  rcases (getBit i q).dichotomy with (h | h) <;>
  simp_rw [h, mergeBitRes_getRes_of_getBit_eq h, false_and, and_self]
  · simp_rw [or_false]
  · simp_rw [or_true]

lemma mergeBitRes_getBit_of_getRes_eq (h : getRes i q = p) : mergeBitRes i (getBit i q) p = q := by
simp_rw [← h, mergeBitRes_getBit_getRes]

lemma mergeBitRes_inv (h₁ : getBit i q = b) (h₂ : getRes i q = p) : mergeBitRes i b p = q := by
simp_rw [← h₁, ← h₂, mergeBitRes_getBit_getRes]

lemma getRes_inv (i : Fin (m + 1)) (h : mergeBitRes i (getBit i q) p = q) : getRes i q = p := by
  rcases mergeBitRes_surj i q with ⟨b, p', rfl⟩ ; rw [getRes_mergeBitRes]
  exact (mergeBitRes_Fin_inj i h).symm

lemma getBit_inv (i : Fin (m + 1)) (h : mergeBitRes i b (getRes i q) = q) : getBit i q = b := by
  rcases mergeBitRes_surj i q with ⟨b', p', rfl⟩ ; rw [getBit_mergeBitRes]
  exact (mergeBitRes_Bool_inj i h).symm

lemma forall_iff_forall_mergeBitRes (i : Fin (m + 1)) {pr : Fin (2^(m + 1)) → Prop} :
  (∀ (q : Fin (2^(m + 1))), pr q) ↔ (∀ b p, pr (mergeBitRes i b p)) :=
  ⟨fun h _ _ => h _, fun h q => by rcases mergeBitRes_surj i q with ⟨b, p, rfl⟩ ; exact h _ _⟩

lemma forall_iff_forall_mergeBitRes_bool (i : Fin (m + 1)) {pr : Fin (2^(m + 1)) → Prop} :
  (∀ (q : Fin (2^(m + 1))), pr q) ↔
  (∀ p, pr (mergeBitRes i false p)) ∧ (∀ p, pr (mergeBitRes i true p)) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩,
    fun h q => by rcases mergeBitRes_surj i q with ⟨(h|h), p, rfl⟩
                  · exact h.1 _
                  · exact h.2 _⟩

lemma exists_iff_exists_mergeBitRes (i : Fin (m + 1)) {pr : Fin (2^(m + 1)) → Prop} :
(∃ (q : Fin (2^(m + 1))), pr q) ↔ (∃ b p, pr (mergeBitRes i b p)) :=
⟨ fun ⟨q, hq⟩ => ⟨getBit i q, getRes i q, mergeBitRes_getBit_getRes ▸ hq⟩,
  fun ⟨b, p, hbp⟩ => ⟨mergeBitRes i b p, hbp⟩⟩

lemma getBit_surj (i : Fin (m + 1)) (q : Fin (2^(m + 1))) :
  ∃ p, mergeBitRes i (getBit i q) p = q :=
  ⟨getRes i q, mergeBitRes_getBit_getRes⟩

lemma getRes_surj (i : Fin (m + 1)) (q : Fin (2^(m + 1))) :
  ∃ b, mergeBitRes i b (getRes i q) = q :=
  ⟨getBit i q, mergeBitRes_getBit_getRes⟩

lemma ne_iff_getBit_ne_or_getRes_ne (i : Fin (m + 1)) :
getBit i q₁ ≠ getBit i q₂ ∨ getRes i q₁ ≠ getRes i q₂ ↔ q₁ ≠ q₂  := by
rw [ne_eq q₁, ← getRes_getBit_inj_iff i, not_and_or]

lemma ne_of_getBit_ne (i : Fin (m + 1)) (h : getBit i q₁ ≠ getBit i q₂) :
q₁ ≠ q₂ := (ne_iff_getBit_ne_or_getRes_ne i).mp (Or.inl h)

lemma ne_of_getRes_ne (i : Fin (m + 1)) (h : getRes i q₁ ≠ getRes i q₂) :
q₁ ≠ q₂ := (ne_iff_getBit_ne_or_getRes_ne i).mp (Or.inr h)

end GetMerge

section bitInvar

def bitInvar (i : Fin (m + 1)) (f : Function.End (Fin (2^(m + 1)))) : Prop :=
∀ q, getBit i (f q) = getBit i q

@[simp]
lemma bitInvar_iff_getBit_apply_eq_getBit :
  bitInvar i f ↔ ∀ q, getBit i (f q) = getBit i q := Iff.rfl

lemma bitInvar_of_getBit_apply_eq_getBit {f : Function.End (Fin (2^(m + 1)))}
  (h : ∀ q, getBit i (f q) = getBit i q) : bitInvar i f :=
  bitInvar_iff_getBit_apply_eq_getBit.mpr h

lemma getBit_apply_eq_getBit_of_bitInvar (h : bitInvar i f) : getBit i (f q) = getBit i q :=
bitInvar_iff_getBit_apply_eq_getBit.mp h _

lemma bitInvar_comp_of_bitInvar (hf : bitInvar i f) (hg : bitInvar i g) : bitInvar i (f ∘ g) :=
  fun q => by simp_rw [Function.comp_apply, hf (g q), hg q]

lemma bitInvar_mul_of_bitInvar (hf : bitInvar i f) (hg : bitInvar i g) : bitInvar i (f * g) :=
  bitInvar_comp_of_bitInvar hf hg

lemma bitInvar_of_comp_bitInvar_bitInvar (hfg : bitInvar i (f ∘ g)) (h : bitInvar i f) :
  bitInvar i g := fun q => by rw [← h (g q), ← hfg q, Function.comp_apply]

lemma bitInvar_of_mul_bitInvar_bitInvar (hfg : bitInvar i (f * g)) (h : bitInvar i f) :
  bitInvar i g := bitInvar_of_comp_bitInvar_bitInvar hfg h

lemma id_bitInvar : bitInvar i id := fun _ => rfl

lemma one_bitInvar : bitInvar i 1 := id_bitInvar

lemma bitInvar_of_rightInverse_bitInvar (hfg : Function.RightInverse g f) (h : bitInvar i f) :
  bitInvar i g := bitInvar_of_comp_bitInvar_bitInvar (hfg.comp_eq_id ▸ id_bitInvar) h

lemma bitInvar_of_leftInverse_bitInvar (hfg : Function.LeftInverse g f) (h : bitInvar i g) :
  bitInvar i f := bitInvar_of_rightInverse_bitInvar hfg h

lemma mergeBitRes_getBit_getRes_apply_eq_apply_of_bitinvar (h : bitInvar i f) :
mergeBitRes i (getBit i q) (getRes i (f q)) = f q := by
  rw [← h q, mergeBitRes_getBit_getRes]

@[simp]
lemma mergeBitRes_getRes_apply_mergeBitRes_of_bitinvar (h : bitInvar i f) :
mergeBitRes i b (getRes i (f (mergeBitRes i b p))) = f (mergeBitRes i b p) := by
  convert (getBit_mergeBitRes ▸ mergeBitRes_getBit_getRes_apply_eq_apply_of_bitinvar h)

lemma symm_bitInvar_iff_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} :
  bitInvar i ⇑π.symm ↔ bitInvar i ⇑π :=
  ⟨bitInvar_of_leftInverse_bitInvar π.left_inv, bitInvar_of_rightInverse_bitInvar π.right_inv⟩

lemma symm_bitInvar_of_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i ⇑π) :
  bitInvar i ⇑π.symm := symm_bitInvar_iff_bitInvar.mpr h

lemma bitInvar_of_symm_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i ⇑π.symm) :
bitInvar i ⇑π := symm_bitInvar_iff_bitInvar.mp h

lemma inv_bitInvar_iff_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} :
  bitInvar i (⇑π⁻¹) ↔ bitInvar i ⇑π := symm_bitInvar_iff_bitInvar

lemma inv_bitInvar_of_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i ⇑π) :
  bitInvar i (⇑π⁻¹) := symm_bitInvar_of_bitInvar h

lemma bitInvar_of_inv_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))}
  (h : bitInvar i (⇑π⁻¹)) : bitInvar i ⇑π := bitInvar_of_symm_bitInvar h

lemma bitInvar_mulPerm_of_bitInvar {π ρ : Equiv.Perm (Fin (2^(m + 1)))} (hπ : bitInvar i ⇑π)
  (hρ : bitInvar i ⇑ρ) : bitInvar i ⇑(π*ρ) :=
  Equiv.Perm.coe_mul _ _ ▸ bitInvar_mul_of_bitInvar hπ hρ

lemma bitInvar_of_mulPerm_bitInvar_bitInvar {π ρ : Equiv.Perm (Fin (2^(m + 1)))}
  (hfg : bitInvar i ⇑(π*ρ : Equiv.Perm (Fin (2^(m + 1))))) (h : bitInvar i ⇑π) : bitInvar i ⇑ρ :=
  bitInvar_of_mul_bitInvar_bitInvar hfg h

lemma onePerm_bitInvar {i : Fin (m + 1)} : bitInvar i ⇑(1 : Equiv.Perm (Fin (2^(m + 1)))) :=
one_bitInvar

section Submonoid

def bitInvarSubmonoid (i : Fin (m + 1)) : Submonoid (Function.End (Fin (2^(m + 1)))) where
  carrier f := bitInvar i f
  mul_mem' ha hb := bitInvar_mul_of_bitInvar ha hb
  one_mem' := one_bitInvar

@[simp]
lemma mem_bitInvarSubmonoid {i : Fin (m + 1)} : f ∈ bitInvarSubmonoid i ↔ bitInvar i f := Iff.rfl

lemma mem_bitInvarSubmonoid_of_bitInvar {i : Fin (m + 1)} (h : bitInvar i f) :
  f ∈ bitInvarSubmonoid i := h

lemma bitInvar_of_mem_bitInvarSubmonoid {i : Fin (m + 1)} (h : f ∈ bitInvarSubmonoid i) :
  bitInvar i f := h

end Submonoid

section Subgroup

def bitInvarSubgroup (i : Fin (m + 1)) : Subgroup (Equiv.Perm (Fin (2^(m + 1)))) where
  carrier π := bitInvar i ⇑π
  mul_mem' ha hb := bitInvar_mulPerm_of_bitInvar ha hb
  one_mem' := one_bitInvar
  inv_mem' ha := inv_bitInvar_of_bitInvar ha

@[simp]
lemma mem_bitInvarSubgroup_iff_coe_mem_bitInvarSubmonoid {i : Fin (m + 1)} :
  ∀ π, π ∈ bitInvarSubgroup i ↔ ⇑π ∈ bitInvarSubmonoid i := fun _ => Iff.rfl

lemma mem_bitInvarSubgroup_of_coe_mem_bitInvarSubmonoid {i : Fin (m + 1)}
  {π : Equiv.Perm (Fin (2^(m + 1)))} (h : ⇑π ∈ bitInvarSubmonoid i) : π ∈ bitInvarSubgroup i := h

lemma coe_mem_bitInvarSubmonoid_of_mem_bitInvarSubgroup {i : Fin (m + 1)}
  {π : Equiv.Perm (Fin (2^(m + 1)))} (h : π ∈ bitInvarSubgroup i) : ⇑π ∈ bitInvarSubmonoid i := h

lemma mem_bitInvarSubgroup_iff_coe_unit_mem {i : Fin (m + 1)}: ∀ π, π ∈ bitInvarSubgroup i ↔
  (Equiv.Perm.equivUnitsEnd π).val ∈ bitInvarSubmonoid i :=
  mem_bitInvarSubgroup_iff_coe_mem_bitInvarSubmonoid

end Subgroup

section Equivs

def endoOfBoolArrowEndo (i : Fin (m + 1)) (f : Bool → Function.End (Fin (2^m))) :
  Function.End (Fin (2^(m + 1))) :=
  fun q => mergeBitRes i (getBit i q) (f (getBit i q) (getRes i q))

@[simp]
lemma endoOfBoolArrowEndo_def {i : Fin (m + 1)} {f : Bool → Function.End (Fin (2^m))}
  {q : Fin (2^(m + 1))} :
  endoOfBoolArrowEndo i f q = mergeBitRes i (getBit i q) (f (getBit i q) (getRes i q)) := rfl

lemma endoOfBoolArrowEndo_bitInvar {i : Fin (m + 1)} (f : Bool → Function.End (Fin (2^m))) :
  bitInvar i (endoOfBoolArrowEndo i f) := by
  simp_rw [bitInvar_iff_getBit_apply_eq_getBit, endoOfBoolArrowEndo_def,
    getBit_mergeBitRes, implies_true]

lemma endoOfBoolArrowEndo_mem_bitInvarSubmonoid {i : Fin (m + 1)}
  (f : Bool → Function.End (Fin (2^m))) : (endoOfBoolArrowEndo i f) ∈ bitInvarSubmonoid i :=
  endoOfBoolArrowEndo_bitInvar f

lemma endoOfBoolArrowEndo_comp {i : Fin (m + 1)} (f g : Bool → Function.End (Fin (2^m))) :
  endoOfBoolArrowEndo i (fun b => (f b) ∘ (g b)) = endoOfBoolArrowEndo i f ∘ endoOfBoolArrowEndo i g
  := by simp_rw [Function.End.ext_iff, Function.comp_apply, endoOfBoolArrowEndo_def,  getBit_mergeBitRes,
    getRes_mergeBitRes, Function.comp_apply, implies_true]

lemma endoOfBoolArrowEndo_mul {i : Fin (m + 1)} (f g : Bool → Function.End (Fin (2^m))) :
  endoOfBoolArrowEndo i (f * g) = endoOfBoolArrowEndo i f * endoOfBoolArrowEndo i g
  := endoOfBoolArrowEndo_comp _ _

def boolArrowEndoOfEndo (i : Fin (m + 1)) (f : Function.End (Fin (2^(m + 1)))) :
  Bool → Function.End (Fin (2^m)) := fun b p => getRes i (f (mergeBitRes i b p))

@[simp]
lemma boolArrowEndoOfEndo_def {i : Fin (m + 1)} {f : Function.End (Fin (2^(m + 1)))}
{b : Bool} {p : Fin (2^m)} : boolArrowEndoOfEndo i f b p = getRes i (f (mergeBitRes i b p)) := rfl

lemma endoOfBoolArrowEndo_rightInverse (i : Fin (m + 1)) :
Function.RightInverse (endoOfBoolArrowEndo i) (boolArrowEndoOfEndo i) := fun f => by
  ext ; simp_rw [boolArrowEndoOfEndo_def, endoOfBoolArrowEndo_def, getBit_mergeBitRes,
    getRes_mergeBitRes]

lemma endoOfBoolArrowEndo_leftInvOn (i : Fin (m + 1)) :
  Set.LeftInvOn (endoOfBoolArrowEndo i) (boolArrowEndoOfEndo i) (bitInvar i) := fun f hf => by
  ext q ; simp_rw [endoOfBoolArrowEndo_def, boolArrowEndoOfEndo_def, mergeBitRes_getBit_getRes,
    mergeBitRes_getRes_of_getBit_eq (hf q)]

lemma boolArrowEndoOfEndo_leftInverse (i : Fin (m + 1)) :
  Function.LeftInverse (boolArrowEndoOfEndo i) (endoOfBoolArrowEndo i) :=
  endoOfBoolArrowEndo_rightInverse _

lemma boolArrowEndoOfEndo_rightInvOn (i : Fin (m + 1)) :
  Set.RightInvOn (boolArrowEndoOfEndo i) (endoOfBoolArrowEndo i) (bitInvar i) :=
  endoOfBoolArrowEndo_leftInvOn _

@[simps!]
def bitInvarMulEquivEnd (i : Fin (m + 1)) :
(Bool → Function.End (Fin (2^m))) ≃* bitInvarSubmonoid i where
  toFun feo := ⟨endoOfBoolArrowEndo i feo, endoOfBoolArrowEndo_mem_bitInvarSubmonoid feo⟩
  invFun f := boolArrowEndoOfEndo i f.val
  left_inv := boolArrowEndoOfEndo_leftInverse i
  right_inv f := Subtype.ext (boolArrowEndoOfEndo_rightInvOn i f.prop)
  map_mul' _ _ := Subtype.ext (endoOfBoolArrowEndo_mul _ _)

def bitInvarMulEquiv (i : Fin (m + 1)) : (Bool → Equiv.Perm (Fin (2^m))) ≃* bitInvarSubgroup i :=
  ((Equiv.Perm.equivUnitsEnd).arrowCongr (Equiv.refl _)).trans <|
  MulEquiv.piUnits.symm.trans <|
  (Units.mapEquiv (bitInvarMulEquivEnd i)).trans <|
  (Equiv.Perm.equivUnitsEnd.subgroupMulEquivUnitsType (mem_bitInvarSubgroup_iff_coe_unit_mem)).symm

@[simp]
lemma bitInvarMulEquiv_apply_coe_apply (i : Fin (m + 1))
  (πeo : Bool → Equiv.Perm (Fin (2 ^ m))) : ⇑((bitInvarMulEquiv i) πeo).val =
  endoOfBoolArrowEndo i fun b => ⇑(πeo b) := rfl

@[simp]
lemma bitInvarMulEquiv_apply_coe_symm_apply (i : Fin (m + 1))
  (πeo : Bool → Equiv.Perm (Fin (2 ^ m))) : ⇑((bitInvarMulEquiv i) πeo).val.symm =
  endoOfBoolArrowEndo i fun b => ⇑(πeo b)⁻¹ := rfl

@[simp]
lemma bitInvarMulEquiv_symm_apply_apply (i : Fin (m + 1)) (π : ↥(bitInvarSubgroup i)):
  ⇑(((bitInvarMulEquiv i).symm) π b) = boolArrowEndoOfEndo i (⇑π.val) b := rfl

@[simp]
lemma bitInvarMulEquiv_symm_apply_symm_apply (i : Fin (m + 1)) (π : ↥(bitInvarSubgroup i)):
  ⇑(((bitInvarMulEquiv i).symm) π b).symm = boolArrowEndoOfEndo i (⇑π⁻¹.val) b := rfl

-- Extra lemmas

lemma endoOfBoolArrowEndo_leftInverse_apply {i : Fin (m + 1)}
  {f g : Bool → Function.End (Fin (2^m))}
  (hfg : ∀ b : Bool, (Function.LeftInverse (f b) (g b))) :
  Function.LeftInverse (endoOfBoolArrowEndo i f) (endoOfBoolArrowEndo i g) := fun q => by
  simp_rw [endoOfBoolArrowEndo_def, getBit_mergeBitRes, getRes_mergeBitRes,
    hfg (getBit i q) (getRes i q), mergeBitRes_getBit_getRes]

lemma endoOfBoolArrowEndo_rightInverse_apply {i : Fin (m + 1)}
  {f g : Bool → Function.End (Fin (2^m))}
  (hfg : ∀ b : Bool, (Function.RightInverse (f b) (g b))) :
  Function.RightInverse (endoOfBoolArrowEndo i f) (endoOfBoolArrowEndo i g) :=
  endoOfBoolArrowEndo_leftInverse_apply hfg

lemma boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarLeft {i : Fin (m + 1)}
  {f g: Function.End (Fin (2^(m + 1)))} (hfg : Function.LeftInverse f g) (hf : bitInvar i f)
  {b : Bool} : Function.LeftInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  fun q => by simp_rw [boolArrowEndoOfEndo_def,
    mergeBitRes_getRes_apply_mergeBitRes_of_bitinvar (bitInvar_of_leftInverse_bitInvar hfg hf),
    hfg (mergeBitRes i b q), getRes_mergeBitRes]

lemma boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarLeft {i : Fin (m + 1)}
  {f g: Function.End (Fin (2^(m + 1)))} (hfg : Function.RightInverse f g) (hf : bitInvar i f)
  {b : Bool} : Function.RightInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  fun q => by simp_rw [boolArrowEndoOfEndo_def, mergeBitRes_getRes_apply_mergeBitRes_of_bitinvar hf,
    hfg (mergeBitRes i b q), getRes_mergeBitRes]

lemma boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (Fin (2^(m + 1)))} (hfg : Function.LeftInverse f g) (hg : bitInvar i g)
  {b : Bool} : Function.LeftInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarLeft hfg hg

lemma boolArrowEndoOfEndo_rightInverse_apply_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (Fin (2^(m + 1)))} (hfg : Function.RightInverse f g) (hg : bitInvar i g)
  {b : Bool} : Function.RightInverse (boolArrowEndoOfEndo i f b) (boolArrowEndoOfEndo i g b) :=
  boolArrowEndoOfEndo_leftInverse_apply_ofBitInvarLeft hfg hg

lemma boolArrowEndoOfEndo_comp_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (Fin (2^(m + 1)))} (hg : bitInvar i g) {b : Bool} :
  boolArrowEndoOfEndo i (f ∘ g) b = boolArrowEndoOfEndo i f b ∘ boolArrowEndoOfEndo i g b := by
  ext ; simp_rw [boolArrowEndoOfEndo_def, Function.comp_apply, boolArrowEndoOfEndo_def,
    mergeBitRes_getRes_apply_mergeBitRes_of_bitinvar hg]

lemma boolArrowEndoOfEndo_mul_ofBitInvarRight {i : Fin (m + 1)}
  {f g: Function.End (Fin (2^(m + 1)))} (hg : bitInvar i g) :
  boolArrowEndoOfEndo i (f * g) = boolArrowEndoOfEndo i f * boolArrowEndoOfEndo i g := by
  ext : 1 ; exact boolArrowEndoOfEndo_comp_ofBitInvarRight hg

end Equivs

end bitInvar

section FlipBit

def flipBit (i : Fin (m + 1)) : Equiv.Perm (Fin (2^(m + 1))) :=
(getBitRes i).symm.permCongr <| boolInversion.prodCongr (Equiv.refl _)

lemma flipBit_apply {i : Fin (m + 1)} :
flipBit i q = mergeBitRes i (!(getBit i q)) (getRes i q) := rfl

lemma flipBit_base : flipBit (m := 0) i = Equiv.swap 0 1 := by
  simp_rw [Equiv.ext_iff, flipBit_apply, Fin.eq_zero i]
  exact Fin.forall_fin_two.mpr ⟨rfl, rfl⟩

lemma flipBit_zero_apply : flipBit 0 q = finProdFinEquiv (q.divNat, q.modNat.rev) := by
  simp_rw [flipBit_apply, getBit_zero, Nat.pow_eq, finTwoEquiv_apply,
    getRes_zero, mergeBitRes_zero, Bool.cond_not, Bool.cond_decide]
  rcases Fin.modNat_two_eq_zero_or_one q with (h | h) <;> simp_rw [h] <;> rfl

@[simp]
lemma flipBit_mergeBitRes : flipBit i (mergeBitRes i b p) = mergeBitRes i (!b) p := by
rw [flipBit_apply, getBit_mergeBitRes, getRes_mergeBitRes]

lemma flipBit_mergeBitRes_false : flipBit i (mergeBitRes i false k) = mergeBitRes i true k :=
flipBit_mergeBitRes (b := false)

lemma flipBit_mergeBitRes_true : flipBit i (mergeBitRes i true k) = mergeBitRes i false k :=
flipBit_mergeBitRes (b := true)

lemma flipBit_mergeBitRes_zero : flipBit 0 (mergeBitRes 0 b p) =
  finProdFinEquiv (p, bif b then 0 else 1) := by
  simp_rw [flipBit_zero_apply, mergeBitRes_zero_divNat,
    mergeBitRes_zero_modNat, Bool.apply_cond (Fin.rev)]
  rfl

lemma flipBit_mergeBitRes_zero_true : flipBit 0 (mergeBitRes 0 true p) = finProdFinEquiv (p, 0) :=
flipBit_mergeBitRes_zero (b := true)

lemma flipBit_mergeBitRes_zero_false : flipBit 0 (mergeBitRes 0 false p) = finProdFinEquiv (p, 1) :=
flipBit_mergeBitRes_zero (b := false)

lemma mergeBitRes_getRes_of_getBit_not (h : getBit i q = !b) :
mergeBitRes i b (getRes i q) = flipBit i q := by
simp_rw [flipBit_apply, h, Bool.not_not]

lemma mergeBitRes_getRes_cases_flipBit (i : Fin (m + 1)) (q) (b) :
  (getBit i q = b ∧ mergeBitRes i b (getRes i q) = q) ∨
  ((getBit i q = !b) ∧ mergeBitRes i b (getRes i q) = flipBit i q) :=
  (Bool.eq_or_eq_not (getBit i q) b).elim
    (fun h => Or.inl (And.intro h (mergeBitRes_getRes_of_getBit_eq h)))
    (fun h => Or.inr (And.intro h (mergeBitRes_getRes_of_getBit_not h)))

lemma flipBit_succ : flipBit (i.succ) q = mergeBitRes 0 (getBit 0 q) (flipBit i (getRes 0 q)) := by
  simp_rw [flipBit_apply, getBit_succ, getRes_succ, mergeBitRes_succ,
  getBit_mergeBitRes, getRes_mergeBitRes]

lemma flipBit_castSucc : flipBit (i.castSucc) q =
  mergeBitRes (Fin.last _) (getBit (Fin.last _) q) (flipBit i (getRes (Fin.last _) q)) := by
  simp_rw [flipBit_apply, getBit_castSucc, getRes_castSucc, mergeBitRes_castSucc,
  getBit_mergeBitRes, getRes_mergeBitRes]

lemma flipBit_succAbove {j : Fin (m + 2)} : flipBit (j.succAbove i) q =
  mergeBitRes j (getBit j q) (flipBit i (getRes j q)) := by
  simp_rw [flipBit_apply, getBit_succAbove, getRes_succAbove, mergeBitRes_succAbove,
  getBit_mergeBitRes, getRes_mergeBitRes]

lemma eq_flipBit_iff : q = flipBit i r ↔ getBit i q = (!getBit i r) ∧
    getRes i q = getRes i r := by
  rcases mergeBitRes_surj i q with ⟨bq, pq, rfl⟩;
  rcases mergeBitRes_surj i r with ⟨br, pr, rfl⟩
  simp_rw [flipBit_mergeBitRes, getBit_mergeBitRes, getRes_mergeBitRes,
    mergeBitRes_inj_iff]

@[simp]
lemma flipBit_flipBit : flipBit i (flipBit i q) = q := by
  simp_rw [flipBit_apply (q := q), flipBit_mergeBitRes,
    Bool.not_not, mergeBitRes_getBit_getRes]

@[simp]
lemma flipBit_symm : (flipBit i).symm = flipBit i := rfl

@[simp]
lemma flipBit_inv : (flipBit i)⁻¹ = flipBit i := rfl

@[simp]
lemma flipBit_mul_self : (flipBit i) * (flipBit i) = 1 := by
  rw [mul_eq_one_iff_inv_eq]
  exact flipBit_inv

@[simp]
lemma flipBit_mul_cancel_right : ρ * (flipBit i) * (flipBit i) = ρ := by
  rw [mul_assoc, flipBit_mul_self, mul_one]

@[simp]
lemma flipBit_mul_cancel_left : (flipBit i) * ((flipBit i) * ρ)  = ρ := by
  rw [← mul_assoc, flipBit_mul_self, one_mul]

@[simp]
lemma getBit_flipBit : getBit i (flipBit i q) = !(getBit i q) := by
  simp_rw [flipBit_apply, getBit_mergeBitRes]

@[simp]
lemma getRes_flipBit : getRes i (flipBit i q) = getRes i q := by
  rw [flipBit_apply, getRes_mergeBitRes]

lemma getBit_flipBit_of_ne {i j : Fin (m + 1)} (h : i ≠ j) :
    getBit i (flipBit j q) = getBit i q := by
  cases m
  · exact (h ((Fin.subsingleton_one).elim i j)).elim
  · rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
    simp_rw [getBit_succAbove, getRes_flipBit]

lemma flipBit_bitInvar_of_ne {i j : Fin (m + 1)} (h : i ≠ j) : bitInvar i ⇑(flipBit j) :=
  bitInvar_of_getBit_apply_eq_getBit (fun _ => getBit_flipBit_of_ne h)

lemma getBit_zero_flipBit_succ {i : Fin m} :
    getBit 0 (flipBit (i.succ) q) = getBit 0 q := by
  cases m
  · exact i.elim0
  · rw [flipBit_succ, getBit_mergeBitRes]

lemma getBit_succ_flipBit_zero {i : Fin m} :
    getBit (i.succ) (flipBit 0 q) = getBit (i.succ) q := by
  cases m
  · exact i.elim0
  · simp_rw [getBit_succ, getRes_flipBit]

lemma flipBit_succ_bitInvar_zero {i : Fin m} : bitInvar 0 ⇑(flipBit (i.succ)) :=
  bitInvar_of_getBit_apply_eq_getBit (fun _ => getBit_zero_flipBit_succ)

lemma flipBit_zero_bitInvar_succ {i : Fin m} : bitInvar (i.succ) ⇑(flipBit 0) :=
  bitInvar_of_getBit_apply_eq_getBit (fun _ => getBit_succ_flipBit_zero)

end FlipBit

@[simp]
lemma flipBit_ne_self (q) : flipBit i q ≠ q := by
  apply ne_of_getBit_ne i
  rw [getBit_flipBit, ne_eq, Bool.not_not_eq]

lemma getRes_zero_eq_and_getBit_zero_opp_of_lt_of_flipBit_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) :
getBit 0 r = false ∧ getBit 0 q = true ∧ getRes 0 r = getRes 0 q := by
rcases mergeBitRes_surj 0 q with ⟨bq, pq, rfl⟩; rcases mergeBitRes_surj 0 r with ⟨br, pr, rfl⟩
simp_rw [flipBit_mergeBitRes, getBit_mergeBitRes, getRes_mergeBitRes,
  Fin.lt_iff_val_lt_val, mergeBitRes_zero, finProdFinEquiv_apply_val, Bool.cond_not, add_comm,
  Bool.apply_cond (Fin.val), Fin.val_one, Fin.val_zero] at hf h ⊢
rcases Nat.eq_false_true_of_cond_succ_lt_of_cond_succ_lt h hf with ⟨hr, hq, he⟩
exact ⟨hr, hq, Fin.ext (Nat.eq_of_mul_eq_mul_left zero_lt_two he)⟩

lemma eq_flipBit_of_lt_of_flipBit_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) : r = flipBit 0 q := by
rcases getRes_zero_eq_and_getBit_zero_opp_of_lt_of_flipBit_gt h hf with ⟨hr, hq, hrq⟩
simp only [eq_flipBit_iff, hr, hq, hrq, Bool.not_true, and_self]

section CondFlipBit

def condFlipBitCore (i : Fin (m + 1)) (c : Fin (2^m) → Bool) : Function.End (Fin (2^(m + 1))) :=
  fun q => bif c (getRes i q) then flipBit i q else q

lemma condFlipBitCore_condFlipBitCore : condFlipBitCore i c (condFlipBitCore i c q) = q := by
rcases (c (getRes i q)).dichotomy with h | h <;>
simp only [condFlipBitCore, h, cond_true, cond_false, getRes_flipBit, flipBit_flipBit]

def condFlipBit (i : Fin (m + 1)) (c : Fin (2^m) → Bool) : Equiv.Perm (Fin (2^(m + 1))) where
  toFun := condFlipBitCore i c
  invFun := condFlipBitCore i c
  left_inv _ := condFlipBitCore_condFlipBitCore
  right_inv _ := condFlipBitCore_condFlipBitCore

lemma condFlipBit_apply :
condFlipBit i c q = bif c (getRes i q) then flipBit i q else q := rfl

lemma condFlipBit_def :
condFlipBit i c = fun q => bif c (getRes i q) then flipBit i q else q := rfl

lemma condFlipBit_apply_eq_mergeBitRes : condFlipBit i c q =
mergeBitRes i (xor (c (getRes i q)) (getBit i q)) (getRes i q) := by
rw [condFlipBit_apply] ; cases (c (getRes i q))
· rw [cond_false, Bool.false_xor, mergeBitRes_getBit_getRes]
· rw [cond_true, Bool.true_xor, flipBit_apply]

lemma condFlipBit_base : condFlipBit (m := 0) i c = bif c 0 then Equiv.swap 0 1 else 1 := by
  ext q : 1
  rw [condFlipBit_apply, Fin.eq_zero (getRes i q), flipBit_base]
  cases (c 0) <;> rfl

lemma condFlipBit_mergeBitRes : condFlipBit i c (mergeBitRes i b p) =
mergeBitRes i (xor (c p) b) p := by
rw [condFlipBit_apply_eq_mergeBitRes, getRes_mergeBitRes, getBit_mergeBitRes]

@[simp]
lemma condFlipBit_symm : (condFlipBit i c).symm = condFlipBit i c := rfl

@[simp]
lemma condFlipBit_inv : (condFlipBit i c)⁻¹ = condFlipBit i c := rfl

@[simp]
lemma condFlipBit_condFlipBit : condFlipBit i c (condFlipBit i c q) = q :=
  (condFlipBit i c).left_inv _

@[simp]
lemma condFlipBit_mul_self : (condFlipBit i c) * (condFlipBit i c) = 1 := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply,
  condFlipBit_condFlipBit, Equiv.Perm.coe_one, id_eq]

@[simp]
lemma condFlipBit_mul_cancel_right : ρ * (condFlipBit i c) * (condFlipBit i c) = ρ := by
  rw [mul_assoc, condFlipBit_mul_self, mul_one]

@[simp]
lemma condFlipBit_mul_cancel_left : (condFlipBit i c) * ((condFlipBit i c) * ρ) = ρ := by
  rw [← mul_assoc, condFlipBit_mul_self, one_mul]

lemma condFlipBit_flipBit_of_all_true : flipBit i = condFlipBit i (Function.const _ true) := by
  ext
  rw [condFlipBit_apply]
  rfl

lemma condFlipBit_refl_of_all_false : Equiv.refl _ = condFlipBit i (Function.const _ false) := rfl

lemma condFlipBit_apply_comm :
condFlipBit i c (condFlipBit i d q) = condFlipBit i d (condFlipBit i c q) := by
simp_rw [condFlipBit_apply_eq_mergeBitRes, getRes_mergeBitRes,
  getBit_mergeBitRes, Bool.xor_left_comm]

lemma condFlipBit_comm :
(condFlipBit i c) * (condFlipBit i d) = (condFlipBit i d) * (condFlipBit i c) := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, condFlipBit_apply_comm]

lemma condFlipBit_apply_comm_flipBit :
  condFlipBit i c (flipBit i q) = flipBit i (condFlipBit i c q) := by
  rw [condFlipBit_flipBit_of_all_true, condFlipBit_apply_comm]

lemma condFlipBit_comm_flipBit :
  (condFlipBit i c) * (flipBit i) = (flipBit i) * (condFlipBit i c) := by
  rw [condFlipBit_flipBit_of_all_true, condFlipBit_comm]

lemma condFlipBit_apply_flipBit :
condFlipBit i c (flipBit i q) = bif c (getRes i q) then q else flipBit i q := by
  rw [condFlipBit_apply_comm_flipBit]
  rcases (c (getRes i q)).dichotomy with h | h <;> rw [condFlipBit_apply, h]
  · simp_rw [cond_false]
  · simp_rw [cond_true, flipBit_flipBit]

@[simp]
lemma getRes_condFlipBit : getRes i (condFlipBit i c q) = getRes i q := by
rcases (c (getRes i q)).dichotomy with h | h  <;> rw [condFlipBit_apply, h]
· rfl
· rw [cond_true, getRes_flipBit]

lemma getBit_condFlipBit : getBit i (condFlipBit i c q) =
bif c (getRes i q) then !(getBit i q) else getBit i q := by
rcases (c (getRes i q)).dichotomy with hc | hc <;>
simp only [condFlipBit_apply, cond_false, hc, cond_true, getBit_flipBit]

lemma getBit_condFlipBit' : getBit i (condFlipBit i c q) =
xor (c (getRes i q)) (getBit i q) := by
rcases (c (getRes i q)).dichotomy with hc | hc <;>
simp only [condFlipBit_apply, hc, cond_false, cond_true,
  Bool.false_xor, Bool.true_xor, getBit_flipBit]

lemma getBit_condFlipBit'' : getBit i (condFlipBit i c q) =
bif (getBit i q) then !(c (getRes i q)) else c (getRes i q) := by
rcases (getBit i q).dichotomy with hc | hc <;>
simp only [getBit_condFlipBit', hc, Bool.xor_false, Bool.xor_true, cond_true, cond_false]

lemma getBit_condFlipBit_of_ne {i j : Fin (m + 1)} (hij: i ≠ j):
  getBit i ((condFlipBit j c) q) = getBit i q := by
  rw [condFlipBit_apply]
  rcases (c (getRes j q)).dichotomy with (h | h) <;> simp_rw [h]
  · rw [cond_false]
  · rw [cond_true, getBit_flipBit_of_ne hij]

lemma condFlipBit_bitInvar_of_ne {i j : Fin (m + 1)} (h : i ≠ j) : bitInvar i ⇑(condFlipBit j c) :=
  bitInvar_of_getBit_apply_eq_getBit (fun _ => getBit_condFlipBit_of_ne h)

lemma condFlipBit_succ_apply {i : Fin (m + 1)} : condFlipBit (Fin.succ i) c q =
    mergeBitRes 0 (getBit 0 q) ((condFlipBit i fun p =>
    c (mergeBitRes 0 (getBit 0 q) p)) (getRes 0 q)) := by
    simp_rw [condFlipBit_apply_eq_mergeBitRes, mergeBitRes_succ, getRes_succ, getBit_succ,
    getBit_mergeBitRes, getRes_mergeBitRes]

lemma condFlipBit_succAbove_apply {j : Fin (m + 2)} {i : Fin (m + 1)} :
  condFlipBit (j.succAbove i) c q =
    mergeBitRes j (getBit j q) ((condFlipBit i fun p =>
    c (mergeBitRes (i.predAbove j) (getBit j q) p)) (getRes j q)) := by
    simp_rw [condFlipBit_apply, getRes_succAbove,
    Bool.apply_cond (fun x => mergeBitRes j (getBit j q) x), mergeBitRes_getBit_getRes,
    flipBit_succAbove]

lemma condFlipBit_zero_apply : condFlipBit 0 c q =
  bif c (q.divNat) then
  finProdFinEquiv (q.divNat, q.modNat.rev)
  else q := by
  rw [condFlipBit_apply, flipBit_zero_apply, getRes_zero]

lemma condFlipBit_zero_mergeBitRes :
condFlipBit 0 c (mergeBitRes 0 b p) = finProdFinEquiv (p, bif xor (c p) b then 1 else 0) := by
  simp_rw [condFlipBit_mergeBitRes, mergeBitRes_zero]

lemma condFlipBit_zero_mergeBitRes_true  :
condFlipBit 0 c (mergeBitRes 0 true p) = finProdFinEquiv (p, bif c p then 0 else 1) := by
  simp_rw [condFlipBit_zero_mergeBitRes, Bool.xor_true, Bool.cond_not]

lemma condFlipBit_zero_mergeBitRes_false :
condFlipBit 0 c (mergeBitRes 0 false p) = finProdFinEquiv (p, bif c p then 1 else 0) := by
  simp_rw [condFlipBit_zero_mergeBitRes, Bool.xor_false]

end CondFlipBit

section Equivs

lemma condFlipBit_succ_eq_bitInvarMulEquiv_apply (i : Fin (m + 1)) (c :  Fin (2 ^ (m + 1)) → Bool) :
condFlipBit (i.succ) c = (bitInvarMulEquiv 0)
  (fun b => condFlipBit i (fun p => c (mergeBitRes 0 b p))) :=
  Equiv.ext (fun _ => condFlipBit_succ_apply ▸ rfl)

lemma condFlipBit_one_succ_eq_bitInvarMulEquiv_apply (c :  Fin (2 ^ (m + 1)) → Bool) :
condFlipBit 1 c = (bitInvarMulEquiv 0) (fun b => condFlipBit 0 (fun p => c (mergeBitRes 0 b p))) :=
  condFlipBit_succ_eq_bitInvarMulEquiv_apply 0 c

lemma condFlipBit_succAbove_eq_bitInvarMulEquiv_apply (c) (j : Fin (m + 2)) (i : Fin (m + 1)) :
condFlipBit (j.succAbove i) c = (bitInvarMulEquiv j)
  (fun b => condFlipBit i (fun p => c (mergeBitRes (i.predAbove j) b p))) :=
  Equiv.ext (fun _ => condFlipBit_succAbove_apply ▸ rfl)

end Equivs

end BitRes
