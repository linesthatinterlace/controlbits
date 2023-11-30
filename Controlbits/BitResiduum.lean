import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Tactic
import Controlbits.Bool
import Controlbits.Fin
import Controlbits.Equivs

-- FACTOR
@[simp]
lemma finTwoEquiv_apply : ∀ j, finTwoEquiv j = decide (j = 1) := by
  simp_rw [Fin.forall_fin_two, finTwoEquiv, Equiv.coe_fn_mk, Matrix.cons_val_zero, zero_ne_one,
    decide_False, Matrix.cons_val_one, Matrix.head_cons, decide_True, and_self]

@[simp]
lemma finTwoEquiv_symm_apply : ∀ j, finTwoEquiv.symm j = bif j then 1 else 0 := by
  simp_rw [Bool.forall_bool, cond_false, cond_true, finTwoEquiv, Equiv.coe_fn_symm_mk, and_self]

section BitRes

section GetMerge

@[simps!]
def getBitRes (i : Fin (m + 1)) : Fin (2^(m + 1)) ≃ Bool × Fin (2^m) :=
calc
  _ ≃ (Fin (m + 1) → Fin 2)   := finFunctionFinEquiv.symm
  _ ≃ Fin 2 × (Fin m → Fin 2) := Equiv.piFinSuccAboveEquiv _ i
  _ ≃ _                       := finTwoEquiv.prodCongr finFunctionFinEquiv

def getBit (i : Fin (m + 1)) : Fin (2^(m + 1)) → Bool := Prod.fst ∘ (getBitRes i)

def getRes (i : Fin (m + 1)) : Fin (2^(m + 1)) → Fin (2^m) := Prod.snd ∘ (getBitRes i)

def mergeBitRes (i : Fin (m + 1)) := Function.curry (getBitRes i).symm

lemma getBit_apply : getBit i q = (getBitRes i q).fst := rfl

lemma getRes_apply : getRes i q = (getBitRes i q).snd := rfl

lemma mergeBitRes_apply : mergeBitRes i b p = (getBitRes i).symm (b, p) := rfl

lemma getBitRes_apply' : getBitRes i q = (getBit i q, getRes i q) := rfl

lemma getBitRes_symm_apply' : (getBitRes i).symm bp = mergeBitRes i bp.fst bp.snd := rfl

lemma getBitRes_apply_zero : getBitRes i 0 = (false, 0) := by
ext <;> simp only [getBitRes_apply, finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply,
  Fin.val_zero', Nat.zero_div, Nat.zero_mod, Fin.zero_eta, zero_ne_one, decide_False,
  Equiv.ofRightInverseOfCardLE_apply, Fin.val_zero, zero_mul, Finset.sum_const_zero]

lemma getBit_apply_zero : getBit i 0 = false := by
rw [getBit_apply, getBitRes_apply_zero]

lemma getRes_apply_zero : getRes i 0 = 0 := by
rw [getRes_apply, getBitRes_apply_zero]

lemma mergeBitRes_apply_false_zero : mergeBitRes i false 0 = 0 := by
rw [mergeBitRes_apply, ← getBitRes_apply_zero (i := i), Equiv.symm_apply_apply]

lemma getBitRes_apply_two_pow {i : Fin (m + 1)}: getBitRes i ⟨2^(i : ℕ), pow_lt_pow one_lt_two i.isLt⟩ = (true, 0) := by
ext
· simp only [getBitRes_apply, finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply,
  gt_iff_lt, zero_lt_two, pow_pos, Nat.div_self, Nat.one_mod, Fin.mk_one, decide_True,
  Equiv.ofRightInverseOfCardLE_apply]
· simp only [getBitRes_apply, finFunctionFinEquiv_apply_val, finFunctionFinEquiv_symm_apply_val, Fin.val_zero',
  Finset.sum_eq_zero_iff, Finset.mem_univ, mul_eq_zero, forall_true_left]
  refine' fun x => Or.inl _
  rcases (Fin.succAbove_ne i x).lt_or_lt with h | h <;> rw [Fin.lt_iff_val_lt_val] at h
  · rw [Nat.pow_div h.le zero_lt_two, Nat.pow_mod, Nat.mod_self, Nat.zero_pow (Nat.sub_pos_of_lt h), Nat.zero_mod]
  · rw [Nat.div_eq_of_lt (pow_lt_pow one_lt_two h), Nat.zero_mod]

lemma getBit_apply_two_pow {i : Fin (m + 1)} : getBit i ⟨2^(i : ℕ), pow_lt_pow one_lt_two i.isLt⟩ = true := by
rw [getBit_apply, getBitRes_apply_two_pow]

lemma getBit_apply_zero_one : getBit 0 (1 : Fin (2^(m + 1))) = true := by
convert getBit_apply_two_pow
rw [Fin.val_one', Nat.mod_eq_of_lt (Nat.one_lt_pow' _ _ ), Fin.val_zero, pow_zero]

lemma getRes_apply_two_pow {i : Fin (m + 1)} : getRes i ⟨2^(i : ℕ), pow_lt_pow one_lt_two i.isLt⟩ = 0 := by
rw [getRes_apply, getBitRes_apply_two_pow]

lemma mergeBitRes_apply_true_zero {i : Fin (m + 1)} : mergeBitRes i true 0 = ⟨2^(i : ℕ), pow_lt_pow one_lt_two i.isLt⟩ := by
rw [mergeBitRes_apply, ← getBitRes_apply_two_pow (i := i), Equiv.symm_apply_apply]

lemma coe_mergeBitRes_apply_true_zero : (mergeBitRes (i : Fin (m + 1)) true 0 : ℕ) = 2^(i : ℕ) := by
simp_rw [mergeBitRes_apply_true_zero]

lemma coe_mergeBitRes_zero_apply_true_zero : (mergeBitRes (0 : Fin (m + 1)) true 0 : ℕ) = 1 := by
simp_rw [coe_mergeBitRes_apply_true_zero, Fin.val_zero, pow_zero]

lemma mergeBitRes_zero_apply_true_zero_eq_one : mergeBitRes (0 : Fin (m + 1)) true 0 = 1 := by
simp_rw [Fin.ext_iff, coe_mergeBitRes_zero_apply_true_zero, Fin.val_one', Nat.mod_eq_of_lt (Nat.one_lt_pow' _ _ )]

lemma mergeBitRes_true_base_eq_one : mergeBitRes (m := 0) i true p = 1 := by
rw [Fin.eq_zero p, Fin.eq_zero i] ; exact mergeBitRes_zero_apply_true_zero_eq_one

lemma mergeBitRes_false_base_eq_zero : mergeBitRes (m := 0) i false p = 0 := by
rw [Fin.eq_zero p] ; exact mergeBitRes_apply_false_zero

lemma coe_mergeBitRes_true_base : (mergeBitRes (m := 0) i true p : ℕ) = 1 := by
  rw [mergeBitRes_true_base_eq_one]
  rfl

lemma getBit_base : getBit (m := 0) i q = decide (q = 1) := by
  rw [Fin.eq_zero i]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

lemma getRes_base : getRes (m := 0) i q = 0 := by
  rw [Fin.eq_zero i]
  rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

@[reducible]
def getBitResZero : Fin (2^(m + 1)) ≃ Bool × Fin (2^m) :=
 calc
  Fin (2^(m + 1)) ≃ Fin (2^m * 2) := finCongr (Nat.pow_succ 2 m)
  Fin (2^m * 2) ≃ Fin (2^m) × Fin 2 := finProdFinEquiv.symm
  Fin (2^m) × Fin 2 ≃ Fin 2 × Fin (2^m) := Equiv.prodComm ..
  _ ≃ _ := finTwoEquiv.prodCongr (Equiv.refl _)

lemma getBitResZero_apply : getBitResZero q = (finTwoEquiv q.modNat, q.divNat) := by
  simp only [Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.trans_apply,
    finProdFinEquiv_symm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod_map, finTwoEquiv_apply, Fin.ext_iff, Fin.coe_modNat, finCongr_apply_coe,
    Fin.val_one, id_eq, Nat.add_eq, Nat.add_zero, Nat.pow_eq, Prod.ext_iff, Fin.coe_divNat,
    and_self]

lemma getBitResZero_symm_apply : getBitResZero.symm (b, p) = finProdFinEquiv (p, bif b then 1 else 0) := by
  simp only [Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Equiv.coe_refl, Prod_map, id_eq,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk, finCongr_symm, Equiv.symm_symm,
    Fin.ext_iff, finCongr_apply_coe, finProdFinEquiv_apply_val, add_left_inj]
  cases b <;> rfl

lemma getBitRes_zero : getBitRes (0 : Fin (m + 1)) = getBitResZero := by
  ext q : 1
  simp_rw [getBitRes, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.trans_apply,
    Equiv.piFinSuccAboveEquiv_apply, Fin.zero_succAbove, Equiv.prodCongr_apply, Prod_map,
    finProdFinEquiv_symm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.coe_refl, id_eq,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, Fin.coe_modNat, Fin.coe_divNat,
    finFunctionFinEquiv_symm_apply_val, Fin.val_zero, pow_zero, Nat.div_one,
    finCongr_apply_coe, finFunctionFinEquiv_apply_val, true_and, finFunctionFinEquiv,
    Equiv.ofRightInverseOfCardLE_symm_apply, Fin.val_succ, Finset.sum_fin_eq_sum_range, dite_eq_ite]
  rw [Finset.sum_ite_of_true (h := fun _ H => (Finset.mem_range.mp H))]
  refine' Nat.eq_of_mul_eq_mul_left (zero_lt_two) (add_right_cancel (b := (q : ℕ) / 2 ^ 0 % 2 * 2 ^ 0) _)
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

lemma getBit_zero_coe : getBit 0 q = decide ((q : ℕ) % 2 = 1) := by
  simp_rw [getBit_zero, Fin.modNat, finTwoEquiv_apply]
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · simp_rw [h, Fin.mk_zero, zero_ne_one]
  · simp_rw [h, Fin.mk_one]

lemma getRes_zero : getRes 0 q = q.divNat := by
  simp_rw [getRes_apply, getBitRes_zero_apply]

lemma coe_getRes_zero : (getRes 0 q : ℕ) = q / 2 := by
  simp_rw [getRes_zero, Fin.coe_divNat]

lemma mergeBitRes_zero : mergeBitRes 0 b p = finProdFinEquiv (p, bif b then 1 else 0) := by
  simp_rw [mergeBitRes_apply, getBitRes_zero_symm_apply]

lemma coe_mergeBitRes_zero : (mergeBitRes 0 b p : ℕ) = 2 * p + (bif b then 1 else 0) := by
  simp_rw [mergeBitRes_zero, finProdFinEquiv_apply_val, add_comm (2 * (p : ℕ)),
  Bool.apply_cond (Fin.val), Fin.val_one, Fin.val_zero]

lemma mergeBitRes_zero_true : mergeBitRes 0 true p = finProdFinEquiv (p, 1) := by
  simp_rw [mergeBitRes_zero]
  rfl

lemma mergeBitRes_zero_false : mergeBitRes 0 false p = finProdFinEquiv (p, 0):= by
  simp_rw [mergeBitRes_zero]
  rfl

lemma mergeBitRes_zero_divNat_modNat : ((mergeBitRes 0 b p).divNat, (mergeBitRes 0 b p).modNat) =
  (p, (bif b then 1 else 0)) := by
  simp_rw [← finProdFinEquiv_symm_apply, Equiv.symm_apply_eq]
  exact mergeBitRes_zero

lemma mergeBitRes_zero_divNat : (mergeBitRes 0 b p).divNat = p :=
(Prod.ext_iff.mp (mergeBitRes_zero_divNat_modNat (b := b) (p := p))).1

lemma mergeBitRes_zero_modNat : (mergeBitRes 0 b p).modNat = bif b then 1 else 0 :=
(Prod.ext_iff.mp (mergeBitRes_zero_divNat_modNat (b := b) (p := p))).2

lemma coe_mergeBitRes_zero_true : (mergeBitRes 0 true p : ℕ) = 2 * p + 1 := by
  simp_rw [coe_mergeBitRes_zero, cond_true]

lemma coe_mergeBitRes_zero_false : (mergeBitRes 0 false p : ℕ) = 2 * p := by
  simp_rw [coe_mergeBitRes_zero, cond_false, add_zero]

@[simp]
lemma getBit_mergeBitRes (i : Fin (m + 1)) : getBit i (mergeBitRes i b p) = b := by
simp_rw [getBit_apply, mergeBitRes_apply, Equiv.apply_symm_apply]

lemma ne_mergeBitRes_of_getBit_ne (i : Fin (m + 1)) (h : getBit i q ≠ b) :
q ≠ mergeBitRes i b p := by rintro rfl ; exact h (getBit_mergeBitRes i)

@[simp]
lemma getRes_mergeBitRes (i : Fin (m + 1)) : getRes i (mergeBitRes i b p) = p := by
simp_rw [getRes_apply, mergeBitRes_apply, Equiv.apply_symm_apply]

lemma ne_mergeBitRes_of_getRes_ne (i : Fin (m + 1)) (h : getRes i q ≠ p) :
q ≠ mergeBitRes i b p := by rintro rfl ; exact h (getRes_mergeBitRes i)

lemma getBit_succAbove_eq_getBit_getRes : getBit (j.succAbove i) q = getBit i (getRes j q) := by
simp_rw [getBit_apply, getRes_apply, getBitRes_apply, Equiv.symm_apply_apply]

lemma getBit_eq_getBit_succAbove_mergeBitRes (j : Fin (m + 2)) :
getBit i p = getBit (j.succAbove i) (mergeBitRes j b p) := by
simp only [getBit_succAbove_eq_getBit_getRes, getRes_mergeBitRes]

lemma getBit_eq_getBit_predAbove_getRes_succAbove (i : Fin (m + 1)) :
getBit j q = getBit (i.predAbove j) (getRes (j.succAbove i) q) := by
  simp_rw [getBit_apply, getRes_apply, getBitRes_apply, Equiv.symm_apply_apply,
    Fin.succAbove_succAbove_predAbove]

lemma exists_getBit_eq_getBit_getRes {j : Fin (m + 2)} (h : i ≠ j) :
∃ k, j.succAbove k = i ∧ ∀ {q}, getBit i q = getBit k (getRes j q) := by
rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
use k ; exact ⟨rfl, getBit_succAbove_eq_getBit_getRes⟩

@[simp]
lemma mergeBitRes_getBit_getRes : mergeBitRes i (getBit i q) (getRes i q) = q := by
simp_rw [getRes_apply, mergeBitRes_apply, getBit_apply, Prod.mk.eta, Equiv.symm_apply_apply]

lemma getRes_getRes_eq_getRes_predAbove_getRes_succAbove :
getRes i (getRes j q) = getRes (i.predAbove j) (getRes (j.succAbove i) q) := by
  simp_rw [getRes_apply, getBitRes_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq,
  Fin.succAbove_succAbove_predAbove_succAbove_eq_succAbove_succAbove]

lemma getRes_succAbove_eq_mergeBitRes_predAbove_getBit_getRes_getRes :
getRes (j.succAbove i) q = mergeBitRes (i.predAbove j) (getBit j q) (getRes i (getRes j q)) := by
  rw [getBit_eq_getBit_predAbove_getRes_succAbove i,
  getRes_getRes_eq_getRes_predAbove_getRes_succAbove]
  rw [mergeBitRes_getBit_getRes]

lemma getRes_succ_eq_mergeBitRes_zero_getBit_zero_getRes_getRes_zero :
getRes (i.succ) q = mergeBitRes 0 (getBit 0 q) (getRes i (getRes 0 q)) := by
  simp_rw [← Fin.zero_succAbove]
  exact getRes_succAbove_eq_mergeBitRes_predAbove_getBit_getRes_getRes

lemma mergeBitRes_mergeBitRes_eq_mergeBitRes_succAbove_mergeBitRes_predAbove : mergeBitRes j b₁ (mergeBitRes i b₂ p) =
mergeBitRes (j.succAbove i) b₂ (mergeBitRes (i.predAbove j) b₁ p) := by
  simp_rw [mergeBitRes_apply, getBitRes]
  simp only [Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.symm_trans_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod_map, Equiv.symm_symm,
    Equiv.piFinSuccAboveEquiv_symm_apply, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [Fin.insertNth_insertNth_eq_insertNth_succAbove_insertNth_predAbove]

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

lemma mergeBitRes_Bool_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) : b₁ = b₂ := by
  have h₂ := (congrArg (getBit i) h) ; simp only [getBit_mergeBitRes] at h₂ ; exact h₂

lemma mergeBitRes_Fin_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) : p₁ = p₂ := by
  have h₂ := (congrArg (getRes i) h) ; simp_rw [getRes_mergeBitRes] at h₂ ; exact h₂

lemma mergeBitRes_inj (i : Fin (m + 1)) (h : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂) : b₁ = b₂ ∧ p₁ = p₂ :=
⟨mergeBitRes_Bool_inj i h, mergeBitRes_Fin_inj i h⟩

lemma mergeBitRes_inj_iff (i : Fin (m + 1)) : mergeBitRes i b₁ p₁ = mergeBitRes i b₂ p₂ ↔ b₁ = b₂ ∧ p₁ = p₂ :=
⟨mergeBitRes_inj i, by rintro ⟨rfl, rfl⟩ ; rfl⟩

lemma mergeBitRes_surj (i : Fin (m + 1)) (q : Fin (2^(m + 1))) : ∃ b p, mergeBitRes i b p = q :=
⟨getBit i q, getRes i q, mergeBitRes_getBit_getRes⟩

lemma getRes_inv (i : Fin (m + 1)) (h : mergeBitRes i (getBit i q) p = q) : getRes i q = p := by
  rcases mergeBitRes_surj i q with ⟨b, p', rfl⟩ ; rw [getRes_mergeBitRes]
  exact (mergeBitRes_Fin_inj i h).symm

lemma getBit_inv (i : Fin (m + 1)) (h : mergeBitRes i b (getRes i q) = q) : getBit i q = b := by
  rcases mergeBitRes_surj i q with ⟨b', p', rfl⟩ ; rw [getBit_mergeBitRes]
  exact (mergeBitRes_Bool_inj i h).symm

lemma forall_iff_forall_mergeBitRes (i : Fin (m + 1)) {pr : Fin (2^(m + 1)) → Prop} :
(∀ (q : Fin (2^(m + 1))), pr q) ↔ (∀ p, pr (mergeBitRes i false p)) ∧ (∀ p, pr (mergeBitRes i true p)) :=
⟨ fun h => ⟨fun _ => h _, fun _ => h _⟩,
  fun h q => by rcases mergeBitRes_surj i q with ⟨(h|h), p, rfl⟩
                · exact h.1 _
                · exact h.2 _⟩

lemma exists_iff_exists_mergeBitRes (i : Fin (m + 1)) {pr : Fin (2^(m + 1)) → Prop} :
(∃ (q : Fin (2^(m + 1))), pr q) ↔ (∃ b p, pr (mergeBitRes i b p)) :=
⟨ fun ⟨q, hq⟩ => ⟨getBit i q, getRes i q, mergeBitRes_getBit_getRes ▸ hq⟩,
  fun ⟨b, p, hbp⟩ => ⟨mergeBitRes i b p, hbp⟩⟩

lemma getBit_surj (i : Fin (m + 1)) (q : Fin (2^(m + 1))) : ∃ p, mergeBitRes i (getBit i q) p = q :=
⟨getRes i q, mergeBitRes_getBit_getRes⟩

lemma getRes_surj (i : Fin (m + 1)) (q : Fin (2^(m + 1))) : ∃ b, mergeBitRes i b (getRes i q) = q :=
⟨getBit i q, mergeBitRes_getBit_getRes⟩

lemma getRes_getBit_inj (i : Fin (m + 1)) (h₁ : getBit i q₁ = getBit i q₂) (h₂ : getRes i q₁ = getRes i q₂) :
q₁ = q₂ := by rw [← mergeBitRes_getBit_getRes (i := i) (q := q₁), h₁, h₂, mergeBitRes_getBit_getRes]

lemma getRes_getBit_inj_iff (i : Fin (m + 1)) :
getBit i q₁ = getBit i q₂ ∧ getRes i q₁ = getRes i q₂ ↔ q₁ = q₂ :=
⟨and_imp.mpr (getRes_getBit_inj i), by rintro rfl ; exact ⟨rfl, rfl⟩⟩

lemma ne_iff_getBit_ne_or_getRes_ne (i : Fin (m + 1)) :
getBit i q₁ ≠ getBit i q₂ ∨ getRes i q₁ ≠ getRes i q₂ ↔ q₁ ≠ q₂  := by
rw [ne_eq q₁, ← getRes_getBit_inj_iff i, not_and_or]

lemma ne_of_getBit_ne (i : Fin (m + 1)) (h : getBit i q₁ ≠ getBit i q₂) :
q₁ ≠ q₂ := (ne_iff_getBit_ne_or_getRes_ne i).mp (Or.inl h)

lemma ne_of_getRes_ne (i : Fin (m + 1)) (h : getRes i q₁ ≠ getRes i q₂) :
q₁ ≠ q₂ := (ne_iff_getBit_ne_or_getRes_ne i).mp (Or.inr h)

end GetMerge

section bitInvar

abbrev bitInvar (i : Fin (m + 1)) (f : Fin (2^(m + 1)) → Fin (2^(m + 1))) : Prop :=
∀ b bp, bp.fst = b → ((getBitRes i).conj f bp).fst = b

lemma bitInvar_iff_getBit_apply_mergeBitRes_Bool_cases : bitInvar i f ↔
(∀ p, getBit i (f (mergeBitRes i false p)) = false) ∧ (∀ p, getBit i (f (mergeBitRes i true p)) = true) := by
simp_rw [bitInvar, Equiv.conj_apply, getBit_apply, Prod.forall, Bool.forall_bool, forall_true_left,
  IsEmpty.forall_iff, forall_const, and_true, true_and, mergeBitRes_apply]

lemma bitInvar_iff_getBit_apply_eq_getBit : bitInvar i f ↔ ∀ q, getBit i (f q) = getBit i q := by
simp_rw [bitInvar_iff_getBit_apply_mergeBitRes_Bool_cases,
forall_iff_forall_mergeBitRes i, getBit_mergeBitRes]

lemma bitInvar_of_getBit_apply_mergeBitRes_Bool_cases {f : Fin (2^(m + 1)) → Fin (2^(m + 1))}
(h₁ : ∀ p, getBit i (f (mergeBitRes i false p)) = false) (h₂ : ∀ p, getBit i (f (mergeBitRes i true p)) = true) :
bitInvar i f := bitInvar_iff_getBit_apply_mergeBitRes_Bool_cases.mpr ⟨h₁, h₂⟩

lemma bitInvar_of_getBit_apply_eq_getBit {f : Fin (2^(m + 1)) → Fin (2^(m + 1))}
(h : ∀ q, getBit i (f q) = getBit i q) : bitInvar i f := bitInvar_iff_getBit_apply_eq_getBit.mpr h

lemma getBit_apply_mergeBitRes_false_eq_false_of_bitInvar (h : bitInvar i f) :
getBit i (f (mergeBitRes i false p)) = false := (bitInvar_iff_getBit_apply_mergeBitRes_Bool_cases.mp h).1 _

lemma getBit_apply_mergeBitRes_true_eq_true_of_bitInvar (h : bitInvar i f) :
getBit i (f (mergeBitRes i true p)) = true := (bitInvar_iff_getBit_apply_mergeBitRes_Bool_cases.mp h).2 _

lemma getBit_apply_mergeBitRes_Bool_eq_Bool_of_bitInvar (h : bitInvar i f) :
getBit i (f (mergeBitRes i b p)) = b := by
cases b ;
· exact getBit_apply_mergeBitRes_false_eq_false_of_bitInvar h
· exact getBit_apply_mergeBitRes_true_eq_true_of_bitInvar h

@[simp]
lemma mergeBitRes_getRes_apply_mergeBitRes_of_bitinvar (h : bitInvar i f) :
mergeBitRes i b (getRes i (f (mergeBitRes i b p))) = f (mergeBitRes i b p) := by
  rcases getBit_surj i (f (mergeBitRes i b p)) with ⟨r, hr⟩
  rw [getBit_apply_mergeBitRes_Bool_eq_Bool_of_bitInvar h] at hr
  rw [← hr, getRes_mergeBitRes]

lemma bitInvar_comp_of_bitInvar (hf : bitInvar i f) (hg : bitInvar i g) : bitInvar i (f ∘ g) := by
  rw [bitInvar_iff_getBit_apply_eq_getBit] at hf hg ⊢
  simp_rw [Function.comp_apply, hf, hg, implies_true]

lemma getBit_apply_eq_getBit_of_bitInvar (h : bitInvar i f) : getBit i (f q) = getBit i q :=
bitInvar_iff_getBit_apply_eq_getBit.mp h _

lemma bitInvar_of_rightInverse_bitInvar (h : bitInvar i f) (hfg : Function.RightInverse g f) :
bitInvar i g := by
  rw [bitInvar_iff_getBit_apply_eq_getBit] at h ⊢
  intros q
  rw [← h (g q), hfg]

lemma symm_bitInvar_of_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i π) :
  bitInvar i π.symm := bitInvar_of_rightInverse_bitInvar h π.right_inv

lemma bitInvar_of_symm_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i π.symm) :
bitInvar i π := bitInvar_of_rightInverse_bitInvar h π.left_inv

lemma inv_bitInvar_of_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i π) :
  bitInvar i (π⁻¹ : Equiv.Perm (Fin (2^(m + 1)))) := symm_bitInvar_of_bitInvar h

lemma bitInvar_of_inv_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))}
  (h : bitInvar i (π⁻¹ : Equiv.Perm (Fin (2^(m + 1))))) : bitInvar i π := bitInvar_of_symm_bitInvar h

lemma mul_bitInvar_of_bitInvar {π ρ : Equiv.Perm (Fin (2^(m + 1)))} (hπ : bitInvar i π)
  (hρ : bitInvar i ρ) :
  bitInvar i (π*ρ : Equiv.Perm (Fin (2^(m + 1)))) := by convert bitInvar_comp_of_bitInvar hπ hρ

lemma id_bitInvar : bitInvar i id :=
bitInvar_of_getBit_apply_eq_getBit (by simp only [id_eq, forall_const])

lemma one_bitInvar {i : Fin (m + 1)} : bitInvar i (1 : Equiv.Perm (Fin (2^(m + 1)))) := id_bitInvar

section Subgroup

def bitInvarSubgroup (i : Fin (m + 1)) : Subgroup (Equiv.Perm (Fin (2^(m + 1)))) where
  carrier π := bitInvar i π
  mul_mem' ha hb := mul_bitInvar_of_bitInvar ha hb
  one_mem' := one_bitInvar
  inv_mem' ha := inv_bitInvar_of_bitInvar ha

lemma mem_bitInvarSubgroup {i : Fin (m + 1)} {π : Equiv.Perm (Fin (2^(m + 1)))} :
  π ∈ bitInvarSubgroup i ↔ bitInvar i π := Iff.rfl

lemma mem_bitInvarSubgroup_of_bitInvar {i : Fin (m + 1)} {π : Equiv.Perm (Fin (2^(m + 1)))}
  (h : bitInvar i π) : π ∈ bitInvarSubgroup i := h

lemma bitInvar_of_mem_bitInvarSubgroup {i : Fin (m + 1)} {π : Equiv.Perm (Fin (2^(m + 1)))}
  (h : π ∈ bitInvarSubgroup i) : bitInvar i π := h

end Subgroup

end bitInvar

section FlipBit

-- FACTOR

@[simps!]
def boolInversion : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

def flipBit (i : Fin (m + 1)) : Equiv.Perm (Fin (2^(m + 1))) :=
(getBitRes i).symm.permCongr <| (boolInversion).prodCongr (Equiv.refl _)

lemma flipBit_apply {i : Fin (m + 1)} :
flipBit i q = mergeBitRes i (!(getBit i q)) (getRes i q) := rfl

lemma flipBit_base : flipBit (m := 0) i = Equiv.swap 0 1 := by
  simp_rw [Equiv.ext_iff, flipBit_apply, Fin.eq_zero i]
  exact Fin.forall_fin_two.mpr ⟨rfl, rfl⟩

lemma flipBit_zero_apply : flipBit 0 q = finProdFinEquiv (q.divNat, q.modNat.rev) := by
  simp_rw [flipBit_apply, getBit_zero, Nat.add_eq, Nat.add_zero, Nat.pow_eq, finTwoEquiv_apply,
    getRes_zero, mergeBitRes_zero, Bool.cond_not, Bool.cond_decide]
  rcases Fin.modNat_two_eq_zero_or_one q with (h | h) <;> simp_rw [h] <;> rfl

lemma coe_flipBit_zero_apply : (flipBit 0 q : ℕ) = 2 * q.divNat + q.modNat.rev := by
simp_rw [flipBit_zero_apply, finProdFinEquiv_apply_val, add_comm]

@[simp]
lemma flipBit_mergeBitRes : flipBit i (mergeBitRes i b p) = mergeBitRes i (!b) p := by
rw [flipBit_apply, getBit_mergeBitRes, getRes_mergeBitRes]

lemma flipBit_mergeBitRes_false : flipBit i (mergeBitRes i false k) = mergeBitRes i true k :=
flipBit_mergeBitRes (b := false)

lemma flipBit_mergeBitRes_true : flipBit i (mergeBitRes i true k) = mergeBitRes i false k :=
flipBit_mergeBitRes (b := true)

lemma flipBit_mergeBitRes_zero : flipBit 0 (mergeBitRes 0 b p) =
  finProdFinEquiv (p, bif b then 0 else 1) := by
  simp_rw [flipBit_zero_apply, mergeBitRes_zero_divNat, mergeBitRes_zero_modNat, Bool.apply_cond (Fin.rev)]
  rfl

lemma flipBit_mergeBitRes_zero_true : flipBit 0 (mergeBitRes 0 true p) = finProdFinEquiv (p, 0) :=
flipBit_mergeBitRes_zero (b := true)

lemma flipBit_mergeBitRes_zero_false : flipBit 0 (mergeBitRes 0 false p) = finProdFinEquiv (p, 1) :=
flipBit_mergeBitRes_zero (b := false)

lemma coe_flipBit_mergeBitRes_zero : (flipBit 0 (mergeBitRes 0 b p) : ℕ) =
  2 * p + (bif b then 0 else 1) := by
  simp_rw [flipBit_apply, coe_mergeBitRes_zero, getRes_mergeBitRes, getBit_mergeBitRes, Bool.cond_not]

lemma coe_flipBit_mergeBitRes_zero_true : (flipBit 0 (mergeBitRes 0 true p) : ℕ) = 2 * p :=
coe_flipBit_mergeBitRes_zero

lemma coe_flipBit_mergeBitRes_zero_false : (flipBit 0 (mergeBitRes 0 false p) : ℕ) = 2 * p + 1 :=
coe_flipBit_mergeBitRes_zero

lemma mergeBitRes_getRes_of_getBit_not (h : getBit i q = !b) :
mergeBitRes i b (getRes i q) = flipBit i q := by
simp_rw [flipBit_apply, h, Bool.not_not]

lemma mergeBitRes_getRes_cases_flipBit (i : Fin (m + 1)) (q) (b) :
  (getBit i q = b ∧ mergeBitRes i b (getRes i q) = q) ∨
  ((getBit i q = !b) ∧ mergeBitRes i b (getRes i q) = flipBit i q) :=
  (Bool.eq_or_eq_not (getBit i q) b).elim
    (fun h => Or.inl (And.intro h (mergeBitRes_getRes_of_getBit_eq h)))
    (fun h => Or.inr (And.intro h (mergeBitRes_getRes_of_getBit_not h)))

lemma flipBit_succAbove_eq_mergeBitRes_getBit_flipBit_getRes :
flipBit (j.succAbove i) q = mergeBitRes j (getBit j q) (flipBit i (getRes j q)) := by
simp_rw [flipBit_apply, getBit_succAbove_eq_getBit_getRes,
  getRes_succAbove_eq_mergeBitRes_predAbove_getBit_getRes_getRes,
  mergeBitRes_mergeBitRes_eq_mergeBitRes_succAbove_mergeBitRes_predAbove (j := j)]

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

lemma getBit_flipBit_ne {i : Fin (m + 1)} (h : i ≠ j) : getBit i (flipBit j q) = getBit i q := by
  cases m
  · exact (h (subsingleton_fin_one.elim i j)).elim
  · rcases exists_getBit_eq_getBit_getRes h with ⟨k, rfl, hk2⟩
    simp_rw [hk2, getRes_flipBit]

lemma flipBit_bitInvar (h : i ≠ j) : bitInvar i (flipBit j) :=
bitInvar_of_getBit_apply_eq_getBit (fun _ => (getBit_flipBit_ne h))

lemma flipBit_mem_bitInvarSubgroup (h : i ≠ j) : flipBit j ∈ bitInvarSubgroup i :=
mem_bitInvarSubgroup.mpr (flipBit_bitInvar h)

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
  Fin.lt_iff_val_lt_val, Fin.ext_iff, coe_mergeBitRes_zero, Bool.cond_not] at hf h ⊢
rcases Nat.eq_false_true_of_cond_succ_lt_of_cond_succ_lt h hf with ⟨hr, hq, he⟩
exact ⟨hr, hq, Nat.eq_of_mul_eq_mul_left zero_lt_two he⟩

lemma eq_flipBit_of_lt_of_flipBit_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) : r = flipBit 0 q := by
rcases getRes_zero_eq_and_getBit_zero_opp_of_lt_of_flipBit_gt h hf with ⟨hr, hq, hrq⟩
simp only [eq_flipBit_iff, hr, hq, hrq, Bool.not_true, and_self]

section ResCondFlip

def resCondFlipCore (i : Fin (m + 1)) (c : Fin (2^m) → Bool) : Fin (2^(m + 1)) → Fin (2^(m + 1)) :=
  fun q => bif c (getRes i q) then flipBit i q else q

lemma resCondFlipCore_resCondFlipCore : resCondFlipCore i c (resCondFlipCore i c q) = q := by
rcases (c (getRes i q)).dichotomy with h | h <;>
simp only [resCondFlipCore, h, cond_true, cond_false, getRes_flipBit, flipBit_flipBit]

def resCondFlip (i : Fin (m + 1)) (c : Fin (2^m) → Bool) : Equiv.Perm (Fin (2^(m + 1))) where
  toFun := resCondFlipCore i c
  invFun := resCondFlipCore i c
  left_inv _ := resCondFlipCore_resCondFlipCore
  right_inv _ := resCondFlipCore_resCondFlipCore

lemma resCondFlip_apply :
resCondFlip i c q = bif c (getRes i q) then flipBit i q else q := rfl

lemma resCondFlip_base : resCondFlip (m := 0) i c = bif c 0 then Equiv.swap 0 1 else 1 := by
  ext
  rw [resCondFlip_apply, flipBit_base, getRes_base]
  cases (c 0) <;> simp only [cond_false, Equiv.Perm.one_apply, cond_true]

lemma resCondFlip_eq_mergeBitRes_xor_residuum : resCondFlip i c q =
mergeBitRes i (xor (c (getRes i q)) (getBit i q)) (getRes i q) := by
rcases (c (getRes i q)).dichotomy with h | h <;> rw [resCondFlip_apply, h]
· rw [cond_false, Bool.false_xor, mergeBitRes_getBit_getRes]
· rw [cond_true, Bool.true_xor, flipBit_apply]

lemma resCondFlip_mergeBitRes : resCondFlip i c (mergeBitRes i b p) =
bif c p then mergeBitRes i (!b) p else mergeBitRes i b p := by
rw [resCondFlip_apply, getRes_mergeBitRes, flipBit_mergeBitRes]

lemma resCondFlip_mergeBitRes' : resCondFlip i c (mergeBitRes i b p) =
mergeBitRes i (xor (c p) b) p := by
rw [resCondFlip_eq_mergeBitRes_xor_residuum, getRes_mergeBitRes, getBit_mergeBitRes]

@[simp]
lemma resCondFlip_symm : (resCondFlip i c).symm = resCondFlip i c := rfl

@[simp]
lemma resCondFlip_inv : (resCondFlip i c)⁻¹ = resCondFlip i c := rfl

@[simp]
lemma resCondFlip_resCondFlip : resCondFlip i c (resCondFlip i c q) = q := (resCondFlip i c).left_inv _

@[simp]
lemma resCondFlip_mul_self : (resCondFlip i c) * (resCondFlip i c) = 1 := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, resCondFlip_resCondFlip, Equiv.Perm.coe_one, id_eq]

@[simp]
lemma resCondFlip_mul_cancel_right : ρ * (resCondFlip i c) * (resCondFlip i c) = ρ := by
  rw [mul_assoc, resCondFlip_mul_self, mul_one]

@[simp]
lemma resCondFlip_mul_cancel_left : (resCondFlip i c) * ((resCondFlip i c) * ρ) = ρ := by
  rw [← mul_assoc, resCondFlip_mul_self, one_mul]

lemma resCondFlip_flipBit_of_all_true : flipBit i = resCondFlip i (Function.const _ true) := by
  ext
  rw [resCondFlip_apply]
  rfl

lemma resCondFlip_refl_of_all_false : Equiv.refl _ = resCondFlip i (Function.const _ false) := rfl

lemma resCondFlip_apply_comm :
resCondFlip i c (resCondFlip i d q) = resCondFlip i d (resCondFlip i c q) := by
simp_rw [resCondFlip_eq_mergeBitRes_xor_residuum, getRes_mergeBitRes,
  getBit_mergeBitRes, Bool.xor_left_comm]

lemma resCondFlip_comm :
(resCondFlip i c) * (resCondFlip i d) = (resCondFlip i d) * (resCondFlip i c) := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, resCondFlip_apply_comm]

lemma resCondFlip_apply_comm_flipBit : resCondFlip i c (flipBit i q) = flipBit i (resCondFlip i c q) := by
  rw [resCondFlip_flipBit_of_all_true, resCondFlip_apply_comm]

lemma resCondFlip_comm_flipBit : (resCondFlip i c) * (flipBit i) = (flipBit i) * (resCondFlip i c) := by
  rw [resCondFlip_flipBit_of_all_true, resCondFlip_comm]

lemma resCondFlip_apply_flipBit :
resCondFlip i c (flipBit i q) = bif c (getRes i q) then q else flipBit i q := by
  rw [resCondFlip_apply_comm_flipBit]
  rcases (c (getRes i q)).dichotomy with h | h <;> rw [resCondFlip_apply, h]
  · simp_rw [cond_false]
  · simp_rw [cond_true, flipBit_flipBit]

@[simp]
lemma getRes_resCondFlip : getRes i (resCondFlip i c q) = getRes i q := by
rcases (c (getRes i q)).dichotomy with h | h  <;> rw [resCondFlip_apply, h]
· rfl
· rw [cond_true, getRes_flipBit]

lemma getBit_resCondFlip : getBit i (resCondFlip i c q) =
bif c (getRes i q) then !(getBit i q) else getBit i q := by
rcases (c (getRes i q)).dichotomy with hc | hc <;>
simp only [resCondFlip_apply, cond_false, hc, cond_true, getBit_flipBit]

lemma getBit_resCondFlip' : getBit i (resCondFlip i c q) =
xor (c (getRes i q)) (getBit i q) := by
rcases (c (getRes i q)).dichotomy with hc | hc <;>
simp only [resCondFlip_apply, hc, cond_false, cond_true,
  Bool.false_xor, Bool.true_xor, getBit_flipBit]

lemma getBit_resCondFlip'' : getBit i (resCondFlip i c q) =
bif (getBit i q) then !(c (getRes i q)) else c (getRes i q) := by
rcases (getBit i q).dichotomy with hc | hc <;>
simp only [getBit_resCondFlip', hc, Bool.xor_false, Bool.xor_true, cond_true, cond_false]

lemma getBit_resCondFlip_ne {i : Fin (m + 1)} (hij : i ≠ j) : getBit i (resCondFlip j c q) = getBit i q := by
  rw [resCondFlip_apply]
  rcases (c (getRes j q)).dichotomy with (h | h) <;> simp_rw [h]
  · rw [cond_false]
  · rw [cond_true, getBit_flipBit_ne hij]

lemma resCondFlip_bitInvar (h : i ≠ j) : bitInvar i (resCondFlip j c) :=
bitInvar_of_getBit_apply_eq_getBit (fun _ => (getBit_resCondFlip_ne h))

lemma resCondFlip_mem_bitInvar_subgroup (h : i ≠ j) : resCondFlip j c ∈ bitInvarSubgroup i :=
mem_bitInvarSubgroup_of_bitInvar (resCondFlip_bitInvar h)

lemma resCondFlip_succ_bitInvar_zero {i : Fin (m + 1)} : bitInvar 0 (resCondFlip i.succ c) :=
resCondFlip_bitInvar (Fin.succ_ne_zero _).symm

lemma resCondFlip_succ_mem_bitInvar_zero_subgroup {i : Fin (m + 1)} :
  bitInvar 0 (resCondFlip i.succ c) :=
  mem_bitInvarSubgroup_of_bitInvar (resCondFlip_bitInvar (Fin.succ_ne_zero _).symm)

lemma resCondFlip_succAbove_apply {i : Fin (m + 1)} {j : Fin (m + 2)}:
(resCondFlip (j.succAbove i) c) q =
mergeBitRes j (getBit j q) ((resCondFlip i fun p => c (mergeBitRes (i.predAbove j) (getBit j q) p)) (getRes j q)) := by
  simp_rw [resCondFlip_apply, getRes_succAbove_eq_mergeBitRes_predAbove_getBit_getRes_getRes]
  rcases (c (mergeBitRes (i.predAbove j) (getBit j q) (getRes i (getRes j q)))).dichotomy with (h | h) <;>
  rw [h]
  · simp_rw [cond_false, mergeBitRes_getBit_getRes]
  · simp_rw [cond_true]
    exact flipBit_succAbove_eq_mergeBitRes_getBit_flipBit_getRes

lemma resCondFlip_succ_apply {i : Fin (m + 1)} : resCondFlip (Fin.succ i) c q =
  mergeBitRes 0 (getBit 0 q) ((resCondFlip i fun p => c (mergeBitRes 0 (getBit 0 q) p)) (getRes 0 q)) := resCondFlip_succAbove_apply (j := 0)

lemma resCondFlip_last_succ_apply {i : ℕ} {q : Fin (2 ^ (i + 1 + 1))} {c : Fin (2 ^ (i + 1)) → Bool}:
resCondFlip (Fin.last (i.succ)) c q = mergeBitRes 0 (getBit 0 q) ((resCondFlip (Fin.last i) fun p =>
  c (mergeBitRes 0 (getBit 0 q) p)) (getRes 0 q)) := by
  exact Fin.succ_last _ ▸ resCondFlip_succ_apply

lemma resCondFlip_zero_apply : resCondFlip 0 c q =
  bif c (q.divNat) then
  finProdFinEquiv (q.divNat, q.modNat.rev)
  else q := by
  rw [resCondFlip_apply, flipBit_zero_apply, getRes_zero]

lemma coe_resCondFlip_zero_apply :
(resCondFlip 0 c q : ℕ) = bif c (q.divNat) then ((2 * q.divNat + q.modNat.rev) : ℕ) else q := by
  simp_rw [resCondFlip_apply, Bool.apply_cond (Fin.val), coe_flipBit_zero_apply, getRes_zero]

lemma resCondFlip_zero_mergeBitRes :
resCondFlip 0 c (mergeBitRes 0 b p) = finProdFinEquiv (p, bif xor (c p) b then 1 else 0) := by
  simp_rw [resCondFlip_mergeBitRes', mergeBitRes_zero]

lemma coe_resCondFlip_zero_mergeBitRes :
(resCondFlip 0 c (mergeBitRes 0 b p) : ℕ) = 2 * p + bif xor (c p) b then 1 else 0 := by
  simp_rw [resCondFlip_mergeBitRes', coe_mergeBitRes_zero]

lemma resCondFlip_zero_mergeBitRes_true  :
resCondFlip 0 c (mergeBitRes 0 true p) = finProdFinEquiv (p, bif c p then 0 else 1) := by
  simp_rw [resCondFlip_zero_mergeBitRes, Bool.xor_true, Bool.cond_not]

lemma resCondFlip_zero_mergeBitRes_false :
resCondFlip 0 c (mergeBitRes 0 false p) = finProdFinEquiv (p, bif c p then 1 else 0) := by
  simp_rw [resCondFlip_zero_mergeBitRes, Bool.xor_false]

lemma coe_resCondFlip_zero_mergeBitRes_true :
(resCondFlip 0 c (mergeBitRes 0 true p) : ℕ) = 2 * p + bif c p then 0 else 1 := by
  simp_rw [coe_resCondFlip_zero_mergeBitRes, Bool.xor_true, Bool.cond_not]

lemma coe_resCondFlip_zero_mergeBitRes_false :
(resCondFlip 0 c (mergeBitRes 0 false p) : ℕ) = 2 * p + bif c p then 1 else 0 := by
  simp_rw [coe_resCondFlip_zero_mergeBitRes, Bool.xor_false]

end ResCondFlip

section Equivs

def unweavePowTwoTuple (i : Fin (m + 1)) : (Fin (2^(m + 1)) → α) ≃ (Bool → (Fin (2^m) → α)) :=
calc
  _ ≃ _ := Equiv.arrowCongr ((getBitRes i).trans (Equiv.boolProdEquivSum _)) (Equiv.refl _)
  _ ≃ _ := Equiv.sumArrowEquivProdArrow _ _ _
  _ ≃ _ := (Equiv.boolArrowEquivProd _).symm

lemma unweavePowTwoTuple_apply {c : Fin (2^(m + 1)) → α} :
unweavePowTwoTuple i c = fun b p => c (mergeBitRes i b p) := by
  ext b p
  cases b <;> rfl

def unweaveOddTuplePowTwoTuple (i : Fin (m + 1)) :
  (Fin (2*n + 1) → Fin (2 ^ (m + 1)) → α) ≃ (Bool → Fin (2*n + 1) → Fin (2^m) → α) :=
calc
  _ ≃ _ := Equiv.arrowCongr (Equiv.refl _) (unweavePowTwoTuple i)
  _ ≃ _ := Equiv.piComm _

@[simp]
lemma unweaveOddTuplePowTwoTuple_apply :
  unweaveOddTuplePowTwoTuple i cb = fun b t p => cb t (mergeBitRes i b p) := by
  ext b t p
  cases b <;> rfl

@[simp]
lemma unweaveOddTuplePowTwoTuple_symm_apply { cb : (Bool → Fin (2*n + 1) → Fin (2^m) → α)}:
  (unweaveOddTuplePowTwoTuple i).symm cb = fun t q => cb (getBit i q) t (getRes i q) := by
  simp_rw [Equiv.symm_apply_eq, unweaveOddTuplePowTwoTuple_apply, getBit_mergeBitRes, getRes_mergeBitRes]

lemma splitOffFirstLast_unweaveOddTuplePowTwoTuple_snd
(cb : Fin (2*(n + 1) + 1) → Fin (2^(m + 1)) → α) (b) :
  (splitOffFirstLast ((unweaveOddTuplePowTwoTuple i) cb b)).2 =
  unweaveOddTuplePowTwoTuple i ((splitOffFirstLast cb).2) b := rfl

lemma splitOffFirstLast_unweaveOddTuplePowTwoTuple_fst_snd (cb : Fin (2*(n + 1) + 1) → Fin (2^(m + 1)) → α) (b) :
(splitOffFirstLast ((unweaveOddTuplePowTwoTuple i) cb b)).1.2 =
  fun p => (splitOffFirstLast cb).1.2 (mergeBitRes i b p) := by
  simp_rw [unweaveOddTuplePowTwoTuple_apply, splitOffFirstLast_apply]

lemma splitOffFirstLast_unweaveOddTuplePowTwoTuple_fst_fst (cb : Fin (2*(n + 1) + 1) → Fin (2^(m + 1)) → α) (b) :
(splitOffFirstLast ((unweaveOddTuplePowTwoTuple i) cb b)).1.1 =
  fun p => (splitOffFirstLast cb).1.1 (mergeBitRes i b p) := by
  simp_rw [unweaveOddTuplePowTwoTuple_apply, splitOffFirstLast_apply]

@[simps]
def boolArrowPermOfMemBitInvar (i : Fin (m + 1)) (π : Equiv.Perm (Fin (2^(m + 1))))
  (h : π ∈ bitInvarSubgroup i) (b : Bool) : Equiv.Perm (Fin (2^m)) where
  toFun p := getRes i <| π (mergeBitRes i b p)
  invFun p := getRes i <| π⁻¹ (mergeBitRes i b p)
  left_inv p := by
    simp_rw [mergeBitRes_getRes_apply_mergeBitRes_of_bitinvar h,
        Equiv.Perm.inv_apply_self, getRes_mergeBitRes]
  right_inv p := by
    simp_rw [mergeBitRes_getRes_apply_mergeBitRes_of_bitinvar ((bitInvarSubgroup i).inv_mem h),
        Equiv.Perm.apply_inv_self, getRes_mergeBitRes]

@[simps]
def memBitInvarOfBoolArrowPerm (i : Fin (m + 1)) (πeo : Bool → Equiv.Perm (Fin (2^m))) :
  Equiv.Perm (Fin (2^(m + 1))) where
    toFun q := mergeBitRes i (getBit i q) (πeo (getBit i q) (getRes i q))
    invFun q := mergeBitRes i (getBit i q) ((πeo (getBit i q))⁻¹ (getRes i q))
    left_inv q := by
      simp_rw [getBit_mergeBitRes, getRes_mergeBitRes, Equiv.Perm.inv_apply_self,
        mergeBitRes_getBit_getRes]
    right_inv q := by
      simp_rw [getBit_mergeBitRes, getRes_mergeBitRes, Equiv.Perm.apply_inv_self,
        mergeBitRes_getBit_getRes]

lemma memBitInvarOfBoolArrowPerm_bitInvar {i : Fin (m + 1)} {πeo : Bool → Equiv.Perm (Fin (2^m))} :
  memBitInvarOfBoolArrowPerm i πeo ∈ bitInvarSubgroup i := by
  refine bitInvar_iff_getBit_apply_eq_getBit.mpr (fun q => ?_)
  simp_rw [memBitInvarOfBoolArrowPerm_apply, getBit_mergeBitRes]

@[simps]
def bitInvarMulEquiv (i : Fin (m + 1)) :
(Bool → Equiv.Perm (Fin (2^m))) ≃* bitInvarSubgroup i  where
  toFun πeo := ⟨memBitInvarOfBoolArrowPerm i πeo, memBitInvarOfBoolArrowPerm_bitInvar⟩
  invFun π b := boolArrowPermOfMemBitInvar i π π.prop b
  left_inv π := by
    ext : 2
    simp_rw  [boolArrowPermOfMemBitInvar_apply, memBitInvarOfBoolArrowPerm_apply,
      getBit_mergeBitRes, getRes_mergeBitRes]
  right_inv π := by
    ext : 2
    simp_rw [memBitInvarOfBoolArrowPerm_apply, boolArrowPermOfMemBitInvar_apply,
      mergeBitRes_getBit_getRes,
      mergeBitRes_getRes_of_getBit_eq (getBit_apply_eq_getBit_of_bitInvar π.prop)]
  map_mul' π ρ := by
    ext
    dsimp only [boolArrowPermOfMemBitInvar_apply, memBitInvarOfBoolArrowPerm_apply, id_eq,
      eq_mpr_eq_cast, Equiv.toFun_as_coe, Equiv.coe_fn_mk, Pi.mul_apply, Equiv.Perm.coe_mul,
      Function.comp_apply, Submonoid.mk_mul_mk]
    simp_rw [getBit_mergeBitRes, getRes_mergeBitRes]

lemma resCondFlip_succAbove_eq
  (c) (i : Fin (m + 1)) (j : Fin (m + 2)) : resCondFlip (j.succAbove i) c = bitInvarMulEquiv j
  (fun b => resCondFlip i (fun p => c (mergeBitRes (i.predAbove j) b p))) := by
  ext q : 1
  simp_rw [resCondFlip_succAbove_apply, bitInvarMulEquiv_apply_coe, memBitInvarOfBoolArrowPerm_apply]

lemma resCondFlip_succ_eq_bitInvarMulEquiv_apply (c) (i : Fin (m + 1)) :
resCondFlip (i.succ) c = (bitInvarMulEquiv 0) (fun b => resCondFlip i (fun p => c (mergeBitRes 0 b p))) :=
  resCondFlip_succAbove_eq c i 0

lemma resCondFlip_one_succ_eq_bitInvarMulEquiv_apply (c :  Fin (2 ^ (m + 1)) → Bool) :
resCondFlip 1 c = (bitInvarMulEquiv 0) (fun b => resCondFlip 0 (fun p => c (mergeBitRes 0 b p))) :=
  resCondFlip_succ_eq_bitInvarMulEquiv_apply (c := c) 0

lemma bitInvarMulEquiv_symm_apply_resCondFlip_succAbove_eq (c) (i : Fin (m + 1)) (j : Fin (m + 2)) :
(bitInvarMulEquiv j).symm ⟨resCondFlip (j.succAbove i) c, resCondFlip_bitInvar (Fin.succAbove_ne _ _).symm⟩ =
  fun b => resCondFlip i (fun p => c (mergeBitRes (i.predAbove j) b p)) := by
  ext
  simp_rw [resCondFlip_succAbove_eq, bitInvarMulEquiv_apply_coe, bitInvarMulEquiv_symm_apply,
    boolArrowPermOfMemBitInvar_apply, memBitInvarOfBoolArrowPerm_apply, getBit_mergeBitRes,
    getRes_mergeBitRes]

lemma bitInvarMulEquiv_symm_apply_resCondFlip_succ_eq (c) (i : Fin (m + 1)) :
(bitInvarMulEquiv 0).symm ⟨resCondFlip (i.succ) c, resCondFlip_succ_bitInvar_zero⟩ =
  fun b => resCondFlip i (fun p => c (mergeBitRes 0 b p)) :=
  bitInvarMulEquiv_symm_apply_resCondFlip_succAbove_eq c i 0

lemma bitInvarMulEquiv_symm_apply_resCondFlip_succAbove_eq_apply (c) (i : Fin (m + 1)) (j : Fin (m + 2)) :
(bitInvarMulEquiv j).symm ⟨resCondFlip (j.succAbove i) c, resCondFlip_bitInvar (Fin.succAbove_ne _ _).symm⟩ b =
  resCondFlip i (fun p => c (mergeBitRes (i.predAbove j) b p)) := by
  simp_rw [bitInvarMulEquiv_symm_apply_resCondFlip_succAbove_eq]

lemma bitInvarMulEquiv_symm_apply_resCondFlip_succ_eq_apply (c) (i : Fin (m + 1)) :
(bitInvarMulEquiv 0).symm ⟨resCondFlip (i.succ) c, resCondFlip_succ_bitInvar_zero⟩ b =
  resCondFlip i (fun p => c (mergeBitRes 0 b p)) :=
  bitInvarMulEquiv_symm_apply_resCondFlip_succAbove_eq_apply c i 0

end Equivs

end BitRes
