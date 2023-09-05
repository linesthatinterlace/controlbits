import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Order

section BitRes

section GetMerge

@[simps! apply]
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

lemma getBitRes_apply_zero : getBitRes i 0 = (false, 0) := by
ext <;> simp only [getBitRes_apply, finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply, Fin.val_zero',
  Nat.zero_div, Nat.zero_mod, Fin.mk_zero, Equiv.ofRightInverseOfCardLE_apply, Fin.val_zero, zero_mul,
  Finset.sum_const_zero]

lemma getBit_apply_zero : getBit i 0 = false := by
rw [getBit_apply, getBitRes_apply_zero]

lemma getRes_apply_zero : getRes i 0 = 0 := by
rw [getRes_apply, getBitRes_apply_zero]

lemma mergeBitRes_apply_false_zero : mergeBitRes i false 0 = 0 := by
rw [mergeBitRes_apply, ← getBitRes_apply_zero (i := i), Equiv.symm_apply_apply]

lemma getBitRes_apply_two_pow {i : Fin (m + 1)}: getBitRes i ⟨2^(i : ℕ), pow_lt_pow one_lt_two i.isLt⟩ = (true, 0) := by
ext
· simp only [getBitRes_apply, finFunctionFinEquiv, Equiv.ofRightInverseOfCardLE_symm_apply, gt_iff_lt, pow_pos,
  Nat.div_self, Nat.one_mod, Fin.mk_one, Equiv.ofRightInverseOfCardLE_apply]
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
simp_rw [coe_mergeBitRes_apply_true_zero, Fin.val_zero]

lemma mergeBitRes_zero_apply_true_zero_eq_one : mergeBitRes (0 : Fin (m + 1)) true 0 = 1 := by
simp_rw [Fin.ext_iff, coe_mergeBitRes_zero_apply_true_zero, Fin.val_one', Nat.mod_eq_of_lt (Nat.one_lt_pow' _ _ )]

lemma mergeBitRes_true_fin_one_eq_one : mergeBitRes (i : Fin 1) true p = 1 := by
rw [Fin.eq_zero p, Fin.eq_zero i] ; exact mergeBitRes_zero_apply_true_zero_eq_one

lemma mergeBitRes_false_fin_one_eq_zero : mergeBitRes (i : Fin 1) false p = 0 := by
rw [Fin.eq_zero p] ; exact mergeBitRes_apply_false_zero

lemma coe_mergeBitRes_true_fin_one : (mergeBitRes (i : Fin 1) true p : ℕ) = 1 := by
rw [mergeBitRes_true_fin_one_eq_one] ; rfl

lemma getBit_fin_one : getBit (i : Fin 1) q = decide (q = 1) := by
rw [Fin.eq_zero i]
rcases Fin.exists_fin_two.mp ⟨q, rfl⟩ with (rfl | rfl) <;> rfl

@[reducible]
def getBitResZero : Fin (2^(m + 1)) ≃ Bool × Fin (2^m) :=
 calc
  Fin (2^(m + 1)) ≃ Fin (2^m * 2) := finCongr (Nat.pow_succ 2 m)
  Fin (2^m * 2) ≃ Fin (2^m) × Fin 2 := finProdFinEquiv.symm
  Fin (2^m) × Fin 2 ≃ Fin 2 × Fin (2^m) := Equiv.prodComm ..
  _ ≃ _ := finTwoEquiv.prodCongr (Equiv.refl _)

lemma getBitRes_zero : getBitRes (0 : Fin (m + 1)) = getBitResZero := by
ext q
· simp_rw [getBitRes, finFunctionFinEquiv, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.trans_apply,
  Equiv.ofRightInverseOfCardLE_symm_apply, Equiv.piFinSuccAboveEquiv_apply, Fin.val_zero, pow_zero, Nat.div_one,
  Fin.zero_succAbove, Fin.val_succ, Equiv.prodCongr_apply, Prod_map,
  finProdFinEquiv_symm_apply, Fin.modNat, finCongr_apply_coe, Equiv.prodComm_apply,
  Prod.swap_prod_mk]
· simp_rw [getBitRes, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.trans_apply,
  Equiv.piFinSuccAboveEquiv_apply, Fin.zero_succAbove, Equiv.prodCongr_apply, Prod_map, finFunctionFinEquiv_apply_val,
  finFunctionFinEquiv_symm_apply_val, Fin.val_succ, Finset.sum_fin_eq_sum_range, dite_eq_ite,
  finProdFinEquiv_symm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.coe_refl, id_eq, Fin.coe_divNat,
  finCongr_apply_coe]
  rw [Finset.sum_ite_of_true (h := fun _ H => (Finset.mem_range.mp H))]
  apply Nat.eq_of_mul_eq_mul_left (zero_lt_two)
  apply add_right_cancel (b := (q : ℕ) / 2 ^ 0 % 2 * 2 ^ 0)
  simp_rw [Finset.mul_sum, mul_left_comm (2 : ℕ), ← Nat.pow_succ', Nat.succ_eq_add_one,
  ← Finset.sum_range_succ' (fun x => (q : ℕ) / 2 ^ x % 2 * 2 ^ x), pow_zero, Nat.div_one,
    mul_one, Nat.div_add_mod, Finset.sum_range, ← finFunctionFinEquiv_symm_apply_val,
    ← finFunctionFinEquiv_apply_val, Equiv.apply_symm_apply]

lemma getBit_zero : getBit 0 q = decide ((q : ℕ) % 2 = 1) := by
simp_rw [getBit_apply, getBitRes_zero, Equiv.instTransSortSortSortEquivEquivEquiv_trans, finTwoEquiv,
  Equiv.trans_apply, finProdFinEquiv_symm_apply, Fin.modNat, finCongr_apply_coe, Equiv.prodComm_apply,
  Prod.swap_prod_mk, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Equiv.coe_refl, Prod_map]
rcases Nat.mod_two_eq_zero_or_one q with h | h
· simp_rw [h, Fin.mk_zero]
· simp_rw [h, Fin.mk_one]

lemma coe_getresiduum_zero : (getRes 0 q : ℕ) = q / 2 := by
simp_rw [getRes_apply, getBitRes_zero, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.trans_apply,
  finProdFinEquiv_symm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.prodCongr_apply, Equiv.coe_refl, Prod_map,
  id_eq, Fin.coe_divNat, finCongr_apply_coe]

lemma coe_mergeBitRes_zero : (mergeBitRes 0 b p : ℕ) = 2 * p + (bif b then 1 else 0) := by
simp_rw [mergeBitRes_apply, getBitRes_zero, Equiv.instTransSortSortSortEquivEquivEquiv_trans,
  finProdFinEquiv, finTwoEquiv, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply,
  Equiv.coe_fn_symm_mk, Equiv.coe_refl, Prod_map, id_eq, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
  finCongr_symm, Equiv.symm_symm, Equiv.coe_fn_mk, add_comm (b := 2 * (p : ℕ)), finCongr_apply_mk, add_right_inj]
cases b <;> rfl

lemma coe_mergeBitRes_true_zero : (mergeBitRes 0 true p : ℕ) = 2 * p + 1 := by
simp_rw [coe_mergeBitRes_zero, cond_true]

lemma coe_mergeBitRes_false_zero : (mergeBitRes 0 false p : ℕ) = 2 * p := by
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

lemma exists_getBit_eq_getBit_getRes {j : Fin (m + 2)} (h : i ≠ j) :
∃ k, j.succAbove k = i ∧ ∀ {q}, getBit i q = getBit k (getRes j q) := by
rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
use k ; exact ⟨rfl, getBit_succAbove_eq_getBit_getRes⟩

lemma getBit_eq_getBit_succAbove_mergeBitRes (j : Fin (m + 2)) :
getBit i p = getBit (j.succAbove i) (mergeBitRes j b p) := by
simp only [getBit_succAbove_eq_getBit_getRes, getRes_mergeBitRes]

@[simp]
lemma mergeBitRes_getBit_getRes : mergeBitRes i (getBit i q) (getRes i q) = q := by
simp_rw [getRes_apply, mergeBitRes_apply, getBit_apply, Prod.mk.eta, Equiv.symm_apply_apply]

@[simp]
lemma mergeBitRes_getRes_of_getBit_eq (h : getBit i q = b) : mergeBitRes i b (getRes i q) = q := by
simp_rw [← h, mergeBitRes_getBit_getRes]

lemma mergeBitRes_getRes_cases (i : Fin (m + 1)) (q : Fin (2^(m + 1))) :
(getBit i q = false ∧ mergeBitRes i false (getRes i q) = q) ∨
(getBit i q = true ∧ mergeBitRes i true (getRes i q) = q) := by
rcases (getBit i q).dichotomy with (h | h) <;> simp_rw [h, mergeBitRes_getRes_of_getBit_eq h, false_and]

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

section Invars

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

-- TODO: version of this for residuumInvar

lemma mergeBitRes_getRes_apply_mergeBitRes_eq_apply_mergeBitRes (h : bitInvar i f) :
mergeBitRes i b (getRes i (f (mergeBitRes i b p))) = f (mergeBitRes i b p) := by
rcases getBit_surj i (f (mergeBitRes i b p)) with ⟨r, hr⟩
rw [getBit_apply_mergeBitRes_Bool_eq_Bool_of_bitInvar h] at hr
rw [← hr, getRes_mergeBitRes]

lemma getBit_apply_eq_getBit_of_bitInvar (h : bitInvar i f) : getBit i (f q) = getBit i q :=
bitInvar_iff_getBit_apply_eq_getBit.mp h _

lemma symm_bitInvar_of_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i π) :
bitInvar i π.symm := by rw [bitInvar_iff_getBit_apply_eq_getBit] at h ⊢
                        intros q ; rw [← h (π.symm q), π.apply_symm_apply]

lemma bitInvar_of_symm_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i π.symm) :
bitInvar i π := by rw [← π.symm_symm] ; exact symm_bitInvar_of_bitInvar h

lemma inv_bitInvar_of_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvar i π) :
bitInvar i (π⁻¹ : Equiv.Perm (Fin (2^(m + 1)))) := symm_bitInvar_of_bitInvar h

lemma bitInvar_of_inv_bitInvar {π : Equiv.Perm (Fin (2^(m + 1)))}
(h : bitInvar i (π⁻¹ : Equiv.Perm (Fin (2^(m + 1))))) : bitInvar i π :=
bitInvar_of_symm_bitInvar h

lemma id_bitInvar : bitInvar i id :=
bitInvar_of_getBit_apply_eq_getBit (by simp only [id_eq, forall_const])

end bitInvar

section residuumInvar

def residuumInvar (i : Fin (m + 1)) (f : Fin (2^(m + 1)) → Fin (2^(m + 1))) : Prop :=
∀ p bp, bp.snd = p → ((getBitRes i).conj f bp).snd = p

lemma residuumInvar_iff_getRes_apply_mergeBitRes_Bool_cases : residuumInvar i f ↔
(∀ p, getRes i (f (mergeBitRes i false p)) = p) ∧ (∀ p, getRes i (f (mergeBitRes i true p)) = p) := by
simp_rw [residuumInvar, Equiv.conj_apply, getRes_apply, Prod.forall, mergeBitRes_apply, forall_eq,
  Bool.forall_bool, forall_and]

lemma residuumInvar_iff_getRes_apply_eq_getRes :
residuumInvar i f ↔ ∀ q, getRes i (f q) = getRes i q := by
simp_rw [residuumInvar_iff_getRes_apply_mergeBitRes_Bool_cases,
forall_iff_forall_mergeBitRes i, getRes_mergeBitRes]

lemma residuumInvar_of_getRes_apply_mergeBitRes_Bool_cases {f : Fin (2^(m + 1)) → Fin (2^(m + 1))}
(h₁ : ∀ p, getRes i (f (mergeBitRes i false p)) = p) (h₂ : ∀ p, getRes i (f (mergeBitRes i true p)) = p) :
residuumInvar i f := residuumInvar_iff_getRes_apply_mergeBitRes_Bool_cases.mpr ⟨h₁, h₂⟩

lemma residuumInvar_of_getRes_apply_eq_getBit {f : Fin (2^(m + 1)) → Fin (2^(m + 1))}
(h : ∀ q, getRes i (f q) = getRes i q) : residuumInvar i f :=
residuumInvar_iff_getRes_apply_eq_getRes.mpr h

lemma getRes_apply_mergeBitRes_false_eq_false_of_residuumInvar (h : residuumInvar i f) :
getRes i (f (mergeBitRes i false p)) = p :=
(residuumInvar_iff_getRes_apply_mergeBitRes_Bool_cases.mp h).1 _

lemma getRes_apply_mergeBitRes_true_eq_true_of_residuumInvar (h : residuumInvar i f) :
getRes i (f (mergeBitRes i true p)) = p :=
(residuumInvar_iff_getRes_apply_mergeBitRes_Bool_cases.mp h).2 _

lemma getRes_apply_mergeBitRes_Bool_eq_Bool_of_residuumInvar (h : residuumInvar i f) :
getRes i (f (mergeBitRes i b p)) = p := by
cases b ;
· exact getRes_apply_mergeBitRes_false_eq_false_of_residuumInvar h
· exact getRes_apply_mergeBitRes_true_eq_true_of_residuumInvar h

lemma getRes_apply_eq_getRes_of_residuumInvar (h : residuumInvar i f) :
getRes i (f q) = getRes i q := residuumInvar_iff_getRes_apply_eq_getRes.mp h _

lemma symm_residuumInvar_of_residuumInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : residuumInvar i π) :
residuumInvar i π.symm := by  rw [residuumInvar_iff_getRes_apply_eq_getRes] at h ⊢ ;
                                  intros q ; rw [← h (π.symm q), π.apply_symm_apply]

lemma residuumInvar_of_symm_residuumInvar {π : Equiv.Perm (Fin (2^(m + 1)))} (h : residuumInvar i π.symm) :
residuumInvar i π := by rw [← π.symm_symm] ; exact symm_residuumInvar_of_residuumInvar h

lemma id_residuumInvar : residuumInvar i id :=
residuumInvar_of_getRes_apply_eq_getBit (by simp only [id_eq, forall_const])

end residuumInvar

lemma id_of_bitInvar_residuumInvar (h₁ : bitInvar i f) (h₂ : residuumInvar i f) : f = id := by
ext q : 1 ; rw [id_eq]
exact getRes_getBit_inj i (getBit_apply_eq_getBit_of_bitInvar h₁)
  (getRes_apply_eq_getRes_of_residuumInvar h₂)

lemma id_iff_bitInvar_residuumInvar : (bitInvar i f) ∧ (residuumInvar i f) ↔ f = id :=
⟨fun h => id_of_bitInvar_residuumInvar h.1 h.2 , fun h => h ▸ ⟨id_bitInvar, id_residuumInvar⟩⟩

end Invars

section FlipBit

def boolInversion : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

def flipBit (i : Fin (m + 1)) : Equiv.Perm (Fin (2^(m + 1))) :=
(getBitRes i).symm.permCongr <| (boolInversion).prodCongr (Equiv.refl _)

lemma flipBit_fin_one : flipBit (m := 0) i = Equiv.swap 0 1 := by simp_rw [Fin.eq_zero i]

lemma flipBit_apply : flipBit i q = (getBitRes i).symm (!(getBitRes i q).fst, (getBitRes i q).snd) := rfl

lemma flipBit_eq_mergeBitRes_not_getBit_getRes {i : Fin (m + 1)} :
flipBit i q = mergeBitRes i (!(getBit i q)) (getRes i q) := by
rw [flipBit_apply, mergeBitRes_apply, getBit_apply, getRes_apply]

lemma coe_flipBit_zero_apply : (flipBit 0 q : ℕ) =
2 * (getRes 0 q) + bif !(getBit 0 q) then 1 else 0 := by
simp only [flipBit_eq_mergeBitRes_not_getBit_getRes, getBit_zero, coe_mergeBitRes_zero,
  coe_getresiduum_zero, Bool.cond_not]

@[simp]
lemma flipBit_mergeBitRes : flipBit i (mergeBitRes i b p) = mergeBitRes i (!b) p := by
rw [flipBit_eq_mergeBitRes_not_getBit_getRes, getBit_mergeBitRes, getRes_mergeBitRes]

lemma flipBit_mergeBitRes_false : flipBit i (mergeBitRes i false k) = mergeBitRes i true k :=
flipBit_mergeBitRes (b := false)

lemma flipBit_mergeBitRes_true : flipBit i (mergeBitRes i true k) = mergeBitRes i false k :=
flipBit_mergeBitRes (b := true)

@[simp]
lemma mergeBitRes_getRes_of_getBit_not (h : getBit i q = !b) :
mergeBitRes i b (getRes i q) = flipBit i q := by
simp_rw [flipBit_eq_mergeBitRes_not_getBit_getRes, h, Bool.not_not]

lemma mergeBitRes_getRes_cases_flipBit (i : Fin (m + 1)) (q) (b):
(getBit i q = b ∧ mergeBitRes i b (getRes i q) = q) ∨
((getBit i q = !b) ∧ mergeBitRes i b (getRes i q) = flipBit i q) := by
cases b <;> rcases (getBit i q).dichotomy with (h | h) <;> simp [h]

lemma eq_flipBit_zero_iff : q = flipBit 0 r ↔ getBit 0 q = (!getBit 0 r) ∧
getRes 0 q = getRes 0 r := by
rcases mergeBitRes_surj 0 q with ⟨bq, pq, rfl⟩;
rcases mergeBitRes_surj 0 r with ⟨br, pr, rfl⟩
simp_rw [flipBit_mergeBitRes, getBit_mergeBitRes, getRes_mergeBitRes,
  mergeBitRes_inj_iff]

@[simp]
lemma flipBit_flipBit : flipBit i (flipBit i q) = q := by
rw [flipBit_eq_mergeBitRes_not_getBit_getRes, flipBit_mergeBitRes,
  Bool.not_not, mergeBitRes_getBit_getRes]

@[simp]
lemma flipBit_symm : (flipBit i).symm = flipBit i := by ext q : 1 ; rw [Equiv.symm_apply_eq, flipBit_flipBit]

@[simp]
lemma flipBit_inv : (flipBit i)⁻¹ = flipBit i := flipBit_symm

@[simp]
lemma flipBit_mul_self : (flipBit i) * (flipBit i) = 1 := by
rw [mul_eq_one_iff_inv_eq] ; exact flipBit_inv

@[simp]
lemma flipBit_mul_cancel_right : ρ * (flipBit i) * (flipBit i) = ρ := by
rw [mul_assoc, flipBit_mul_self, mul_one]

@[simp]
lemma flipBit_mul_cancel_left : (flipBit i) * ((flipBit i) * ρ)  = ρ := by
rw [← mul_assoc, flipBit_mul_self, one_mul]

@[simp]
lemma getBit_flipBit : getBit i (flipBit i q) = !(getBit i q) := by
simp_rw [flipBit_eq_mergeBitRes_not_getBit_getRes, getBit_mergeBitRes]

@[simp]
lemma getRes_flipBit : getRes i (flipBit i q) = getRes i q := by
rw [flipBit_eq_mergeBitRes_not_getBit_getRes, getRes_mergeBitRes]

lemma getBit_flipBit_ne {i : Fin (m + 1)} (h : i ≠ j) : getBit i (flipBit j q) = getBit i q := by
cases m
· exact (h (subsingleton_fin_one.elim i j)).elim
· rcases exists_getBit_eq_getBit_getRes h with ⟨k, rfl, hk2⟩
  simp_rw [hk2, getRes_flipBit]

lemma flipBit_bitInvar (h : i ≠ j) : bitInvar i (flipBit j) :=
bitInvar_of_getBit_apply_eq_getBit (fun _ => (getBit_flipBit_ne h) )

lemma flipBit_residuumInvar : residuumInvar i (flipBit i) :=
residuumInvar_of_getRes_apply_eq_getBit (fun _ => getRes_flipBit)
end FlipBit

@[simp]
lemma flipBit_ne_self : flipBit i q ≠ q := by
apply ne_of_getBit_ne i
rw [getBit_flipBit, ne_eq, Bool.not_not_eq]

lemma eq_false_true_of_cond_succ_lt_of_cond_succ_lt
(hmn : (m + bif bm then 1 else 0) < n + bif bn then 1 else 0)
(hnm : (n + bif bn then 0 else 1) < m + bif bm then 0 else 1) :
bm = false ∧ bn = true ∧ (m = n) := by
cases bm <;> cases bn <;>
simp only [false_and, and_false, true_and, and_self, cond_true, cond_false, add_zero, add_lt_add_iff_right] at *
· exact hmn.not_lt hnm
· rw [Nat.lt_succ_iff] at hnm hmn
  exact le_antisymm hmn hnm
· exact (add_lt_iff_neg_left.mp (add_assoc _ 1 1 ▸
    lt_trans ((add_lt_add_iff_right 1).mpr hnm) hmn)).not_le zero_le_two
· exact hmn.not_lt hnm

lemma getRes_zero_eq_and_getBit_zero_opp_of_lt_of_flipBit_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) :
getBit 0 r = false ∧ getBit 0 q = true ∧ getRes 0 r = getRes 0 q := by
rcases mergeBitRes_surj 0 q with ⟨bq, pq, rfl⟩; rcases mergeBitRes_surj 0 r with ⟨br, pr, rfl⟩
simp_rw [flipBit_mergeBitRes, getBit_mergeBitRes, getRes_mergeBitRes,
  Fin.lt_iff_val_lt_val, Fin.ext_iff, coe_mergeBitRes_zero, Bool.cond_not] at hf h ⊢
rcases eq_false_true_of_cond_succ_lt_of_cond_succ_lt h hf with ⟨hr, hq, he⟩
exact ⟨hr, hq, Nat.eq_of_mul_eq_mul_left zero_lt_two he⟩

lemma eq_flipBit_of_lt_of_flipBit_gt (h : r < q)
(hf : flipBit 0 q < flipBit 0 r) : r = flipBit 0 q := by
rcases getRes_zero_eq_and_getBit_zero_opp_of_lt_of_flipBit_gt h hf with ⟨hr, hq, hrq⟩
simp only [eq_flipBit_zero_iff, hr, hq, hrq, Bool.not_true, and_self]

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

lemma resCondFlip_eq_mergeBitRes_xor_residuum : resCondFlip i c q =
mergeBitRes i (xor (c (getRes i q)) (getBit i q)) (getRes i q) := by
rcases (c (getRes i q)).dichotomy with h | h <;> rw [resCondFlip_apply, h]
· rw [cond_false, Bool.xor_false_left, mergeBitRes_getBit_getRes]
· rw [cond_true, Bool.true_xor, flipBit_eq_mergeBitRes_not_getBit_getRes]

@[simp]
lemma resCondFlip_resCondFlip : resCondFlip i c (resCondFlip i c q) = q :=
(resCondFlip i c).left_inv q

lemma resCondFlip_apply_comm :
resCondFlip i c (resCondFlip i d q) = resCondFlip i d (resCondFlip i c q) := by
simp_rw [resCondFlip_eq_mergeBitRes_xor_residuum, getRes_mergeBitRes,
  getBit_mergeBitRes, Bool.xor_left_comm]

lemma resCondFlip_comm :
(resCondFlip i c) * (resCondFlip i d) = (resCondFlip i d) * (resCondFlip i c) := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, resCondFlip_apply_comm]

@[simp]
lemma resCondFlip_symm : (resCondFlip i c).symm = (resCondFlip i c) := rfl

@[simp]
lemma resCondFlip_inv : (resCondFlip i c)⁻¹ = resCondFlip i c := rfl

@[simp]
lemma resCondFlip_mul_self : (resCondFlip i c) * (resCondFlip i c) = 1 := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, resCondFlip_resCondFlip, Equiv.Perm.coe_one, id_eq]

lemma resCondFlip_flipBit_of_all_true : flipBit i = resCondFlip i (Function.const _ true) := by
ext ; rw [resCondFlip_apply] ; rfl

lemma resCondFlip_refl_of_all_false : Equiv.refl _ = resCondFlip i (Function.const _ false) :=
rfl

lemma resCondFlip_apply_comm_flipBit : resCondFlip i c (flipBit i q) = flipBit i (resCondFlip i c q) := by
rw [resCondFlip_flipBit_of_all_true, resCondFlip_apply_comm]

lemma resCondFlip_comm_flipBit :
(resCondFlip i c) * (flipBit i) = (flipBit i) * (resCondFlip i c) := by
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
  Bool.xor_false_left, Bool.true_xor, getBit_flipBit]

lemma getBit_resCondFlip'' : getBit i (resCondFlip i c q) =
bif (getBit i q) then !(c (getRes i q)) else c (getRes i q) := by
rcases (getBit i q).dichotomy with hc | hc <;>
simp only [getBit_resCondFlip', hc, Bool.xor_false_right, Bool.xor_true, cond_true, cond_false]

lemma resCondFlip_mergeBitRes : resCondFlip i c (mergeBitRes i b p) =
bif c p then mergeBitRes i (!b) p else mergeBitRes i b p := by
rw [resCondFlip_apply, getRes_mergeBitRes, flipBit_mergeBitRes]

lemma resCondFlip_mergeBitRes' : resCondFlip i c (mergeBitRes i b p) =
mergeBitRes i (xor (c p) b) p := by
rw [resCondFlip_eq_mergeBitRes_xor_residuum,getRes_mergeBitRes, getBit_mergeBitRes]

end ResCondFlip

end BitRes