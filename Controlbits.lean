import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Combinatorics.Derangements.Basic

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

lemma mergeBitRes_true_fin_one_eq_one : mergeBitRes (i : Fin 1) true 0 = 1 := by
rw [Fin.eq_zero i] ; exact mergeBitRes_zero_apply_true_zero_eq_one

lemma coe_mergeBitRes_true_fin_one : (mergeBitRes (i : Fin 1) true 0 : ℕ) = 1 := by
rw [Fin.eq_zero i] ; exact coe_mergeBitRes_zero_apply_true_zero

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
  Fin.zero_succAbove, Fin.val_succ, Equiv.prodCongr_apply, Prod_map, Equiv.ofRightInverseOfCardLE_apply,
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
  Prod.swap_prod_mk, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Equiv.coe_refl, Prod_map, id_eq]
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

lemma flipBit_apply : flipBit i q = (getBitRes i).symm (!(getBitRes i q).fst, (getBitRes i q).snd) := rfl

lemma flipBit_eq_mergeBitRes_not_getBit_getRes {i : Fin (m + 1)} :
flipBit i q = mergeBitRes i (!(getBit i q)) (getRes i q) := by
rw [flipBit_apply, mergeBitRes_apply, getBit_apply, getRes_apply]

@[simp]
lemma coe_flipBit_zero : (flipBit 0 q : ℕ) =
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

lemma flipBit_mem_derangements {i : Fin (m + 1)} : (flipBit i) ∈ derangements (Fin (2^(m + 1))) :=
fun _ => flipBit_ne_self

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

lemma resCondFlip_apply_def :
resCondFlip i c q = bif c (getRes i q) then flipBit i q else q := rfl

lemma resCondFlip_eq_mergeBitRes_xor_residuum : resCondFlip i c q =
mergeBitRes i (xor (c (getRes i q)) (getBit i q)) (getRes i q) := by
rcases (c (getRes i q)).dichotomy with h | h <;> rw [resCondFlip_apply_def, h]
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
ext ; rw [resCondFlip_apply_def] ; rfl

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
rcases (c (getRes i q)).dichotomy with h | h <;> rw [resCondFlip_apply_def, h]
· simp_rw [cond_false]
· simp_rw [cond_true, flipBit_flipBit]

@[simp]
lemma getRes_resCondFlip : getRes i (resCondFlip i c q) = getRes i q := by
rcases (c (getRes i q)).dichotomy with h | h  <;> rw [resCondFlip_apply_def, h]
· rfl
· rw [cond_true, getRes_flipBit]

lemma getBit_resCondFlip : getBit i (resCondFlip i c q) =
bif c (getRes i q) then !(getBit i q) else getBit i q := by
rcases (c (getRes i q)).dichotomy with hc | hc <;>
simp only [resCondFlip_apply_def, cond_false, hc, cond_true, getBit_flipBit]

lemma getBit_resCondFlip' : getBit i (resCondFlip i c q) =
xor (c (getRes i q)) (getBit i q) := by
rcases (c (getRes i q)).dichotomy with hc | hc <;>
simp only [resCondFlip_apply_def, hc, cond_false, cond_true,
  Bool.xor_false_left, Bool.true_xor, getBit_flipBit]

lemma getBit_resCondFlip'' : getBit i (resCondFlip i c q) =
bif (getBit i q) then !(c (getRes i q)) else c (getRes i q) := by
rcases (getBit i q).dichotomy with hc | hc <;>
simp only [getBit_resCondFlip', hc, Bool.xor_false_right, Bool.xor_true, cond_true, cond_false]

lemma resCondFlip_mergeBitRes : resCondFlip i c (mergeBitRes i b p) =
bif c p then mergeBitRes i (!b) p else mergeBitRes i b p := by
rw [resCondFlip_apply_def, getRes_mergeBitRes, flipBit_mergeBitRes]

lemma resCondFlip_mergeBitRes' : resCondFlip i c (mergeBitRes i b p) =
mergeBitRes i (xor (c p) b) p := by
rw [resCondFlip_eq_mergeBitRes_xor_residuum,getRes_mergeBitRes, getBit_mergeBitRes]

end ResCondFlip

end BitRes

section ControlBits

section FoldFin
open Nat

def foldFin (i : Fin (2*m + 1)) : Fin (m + 1) := m - (dist i m)

lemma le_bit0 : m ≤ 2*m := le_mul_of_pos_left zero_lt_two

lemma lt_bit1 : m < 2*m + 1 := lt_succ_of_le le_bit0

lemma foldFinCast_of_le (hn : n ≤ m) : foldFin (n : Fin (2*m + 1)) = n := by
rw [foldFin, Fin.coe_ofNat_eq_mod, mod_eq_of_lt (lt_of_le_of_lt hn lt_bit1), Nat.dist_eq_sub_of_le hn,
cast_sub hn, sub_sub_cancel]

lemma foldFinZero : foldFin 0 = (0 : Fin (2*m + 1)) := foldFinCast_of_le (Nat.zero_le _)

lemma foldFinCast_of_ge (hn₁ : m ≤ n) (hn₂ : n < 2*m + 1) : foldFin (n : Fin (2*m + 1)) = 2*m - n := by
rw [foldFin, Fin.coe_ofNat_eq_mod, mod_eq_of_lt hn₂, Nat.dist_eq_sub_of_le_right hn₁, cast_sub hn₁]
ring

lemma foldFin2M: foldFin (2*m : ℕ) = (0 : Fin (m + 1)) := by
rw [foldFinCast_of_ge le_bit0 (lt_succ_self _), cast_mul, cast_two, sub_self]

lemma foldFinM : foldFin (m : ℕ) = (m : Fin (m + 1)) := foldFinCast_of_le (le_refl _)
end FoldFin



section Reimplementation

section CycleMin

variable {α : Type u} [Fintype α] [DecidableEq α] {π : Equiv.Perm α}

-- Definition 2.1

def CycleFull (π : Equiv.Perm α) (x : α) : Finset α :=
if Function.IsFixedPt π x then {x} else (π.cycleOf x).support

@[simp]
lemma cycleFull_of_fixed (h : Function.IsFixedPt π x) : CycleFull π x = {x} := dif_pos h

@[simp]
lemma cycleFull_of_not_fixed (h : ¬ Function.IsFixedPt π x) : CycleFull π x = (π.cycleOf x).support :=
dif_neg h

@[simp]
lemma mem_cycleFull_iff : y ∈ CycleFull π x ↔ π.SameCycle x y := by
by_cases h₂ : Function.IsFixedPt π x
· simp_rw [cycleFull_of_fixed h₂, Finset.mem_singleton]
  refine ⟨?_, ?_⟩
  · rintro rfl ; exact ⟨0, rfl⟩
  · rintro hb ; rcases (Equiv.Perm.SameCycle.exists_pow_eq' hb) with ⟨_, _, _, rfl⟩
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h₂ _
· simp_rw [cycleFull_of_not_fixed h₂, Equiv.Perm.mem_support_cycleOf_iff' h₂]

lemma self_mem_cycleFull : x ∈ CycleFull π x := by simp_rw [mem_cycleFull_iff] ; exact ⟨0, rfl⟩

lemma apply_mem_cycleFull : π x ∈ CycleFull π x := by simp_rw [mem_cycleFull_iff] ; exact ⟨1, rfl⟩

lemma pow_apply_mem_cycleFull : (π^(k : ℕ)) x ∈ CycleFull π x :=
by simp_rw [mem_cycleFull_iff] ; exact ⟨k, rfl⟩

lemma cycleFull_nonempty : Finset.Nonempty (CycleFull π x) := ⟨x, self_mem_cycleFull⟩

lemma singleton_subset_cycleFull : {x} ⊆ CycleFull π x := by
rintro y hy ; rw [Finset.mem_singleton] at hy ; rw [hy] ; exact self_mem_cycleFull

lemma fixedPt_iff_cycleFull_singleton : Function.IsFixedPt π x ↔ CycleFull π x = {x} := by
refine ⟨?_, ?_⟩
· exact cycleFull_of_fixed
· have hx := apply_mem_cycleFull (π := π) (x := x) ; rintro h
  rw [h, Finset.mem_singleton] at hx ; exact hx

lemma card_cycleFull_ne_zero : (CycleFull π x).card ≠ 0 := Finset.card_ne_zero_of_mem self_mem_cycleFull

lemma card_cycleFull_pos : 0 < (CycleFull π x).card := cycleFull_nonempty.card_pos

lemma one_le_card_cycleFull : 1 ≤ (CycleFull π x).card := cycleFull_nonempty.card_pos

lemma card_cycleFull_eq_one_iff_fixedPt : (CycleFull π x).card = 1 ↔ Function.IsFixedPt π x := by
rw [Finset.card_eq_one, fixedPt_iff_cycleFull_singleton] ; refine ⟨?_, ?_⟩
· have h := self_mem_cycleFull (π := π) (x := x)
  rintro ⟨y, hy⟩ ; ext ; simp_rw [hy, Finset.mem_singleton] at h ⊢ ; rw [h]
· intro hx ; exact ⟨x, hx⟩

lemma pred_card_cycleFull_eq_pred_card_support_cycleOf : (CycleFull π x).card - 1 = (π.cycleOf x).support.card - 1 := by
by_cases h₂ : Function.IsFixedPt π x
· simp_rw [card_cycleFull_eq_one_iff_fixedPt.mpr h₂, π.cycleOf_eq_one_iff.mpr h₂,
    Equiv.Perm.support_one, Finset.card_empty]
· rw [cycleFull_of_not_fixed h₂]

lemma pow_mod_card_cycleFull_self_apply : (π ^ (b % (CycleFull π x).card)) x = (π ^ (b : ℕ)) x := by
by_cases h₂ : Function.IsFixedPt π x
· simp_rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h₂]
· simp_rw [cycleFull_of_not_fixed h₂] ; exact π.pow_mod_card_support_cycleOf_self_apply b x

lemma mem_cycleFull_iff' : y ∈ CycleFull π x ↔ ∃ b, b ≤ (CycleFull π x).card - 1 ∧ (π ^ b) x = y := by
rw [mem_cycleFull_iff] ; refine ⟨?_, ?_⟩
· rintro hb ; rcases (Equiv.Perm.SameCycle.exists_pow_eq π hb) with ⟨b, _, _, rfl⟩
  refine ⟨b % (CycleFull π x).card, Nat.le_pred_of_lt <| Nat.mod_lt _ card_cycleFull_pos, pow_mod_card_cycleFull_self_apply⟩
· rintro ⟨b, _, rfl⟩ ; refine ⟨b, rfl⟩

lemma mem_cycleFull_iff'' : y ∈ CycleFull π x ↔ ∃ b, b < (CycleFull π x).card ∧ (π ^ b) x = y := by
simp_rw [mem_cycleFull_iff', ← Nat.lt_iff_le_pred card_cycleFull_pos]

lemma cycleFull_apply_eq_cycleMin : CycleFull π (π x) = CycleFull π x := by
by_cases h₂ : Function.IsFixedPt π x
· rw [h₂]
· simp_rw [cycleFull_of_not_fixed h₂, cycleFull_of_not_fixed ((EmbeddingLike.apply_eq_iff_eq _).not.mpr h₂),
    Equiv.Perm.cycleOf_self_apply]


def CycleSection (π : Equiv.Perm α) (x : α) (a : ℕ) : Finset α :=
(Finset.Iic a).image fun k => (π ^ k) x

@[simp]
lemma mem_cycleSection_iff : y ∈ CycleSection π x a ↔ ∃ b ≤ a, (π ^ b) x = y := by
simp_rw [CycleSection, Finset.mem_image, Finset.mem_Iic]

lemma self_mem_cycleSection_iff : x ∈ CycleSection π x a := by
simp_rw [mem_cycleSection_iff] ; exact ⟨0, zero_le _, rfl⟩

lemma cycleSection_nonempty : Finset.Nonempty (CycleSection π x a) := ⟨x, self_mem_cycleSection_iff⟩

lemma cycleSection_zero_singleton : CycleSection π x 0 = {x} := by
ext y ; rw [Finset.mem_singleton] ; refine ⟨?_, ?_⟩
· rw [mem_cycleSection_iff]; rintro ⟨_, hb, rfl⟩ ; rw [Nat.le_zero.mp hb] ; rfl
· rintro rfl ; exact self_mem_cycleSection_iff

lemma cycleSection_singleton_of_fixedPt (h : Function.IsFixedPt π x)  :
CycleSection π x a = {x} := by
ext y ; rw [Finset.mem_singleton]
refine ⟨?_, ?_⟩
· rw [mem_cycleSection_iff] ; rintro ⟨_, _, rfl⟩ ; exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self h _
· rintro rfl ; exact self_mem_cycleSection_iff

lemma cycleSection_subset_cycleFull :
CycleSection π x a ⊆ CycleFull π x := by
by_cases h₂ : Function.IsFixedPt π x
· rw [cycleSection_singleton_of_fixedPt h₂, cycleFull_of_fixed h₂]
· intros y h ; rw [mem_cycleSection_iff] at h ; rcases h with ⟨b, _, hb⟩
  rw [cycleFull_of_not_fixed h₂, Equiv.Perm.mem_support_cycleOf_iff' h₂] ; exact ⟨b, hb⟩

lemma cycleSection_mono : Monotone (CycleSection π x)  := by
intros a b hab y h ; rw [mem_cycleSection_iff] at h ⊢; rcases h with ⟨c, hca, hc⟩ ; exact ⟨c, le_trans hca hab, hc⟩

lemma cycleFull_eq_cycleSection_cycleFull_pred :
CycleFull π x = CycleSection π x ((CycleFull π x).card - 1) := by
ext _ ; rw [mem_cycleSection_iff, mem_cycleFull_iff']

lemma cycleFull_eq_cycleSection_ge_cycleFull_pred (ha : (CycleFull π x).card - 1 ≤ a) :
CycleFull π x = CycleSection π x a := by
refine le_antisymm ?_ ?_
· rw [cycleFull_eq_cycleSection_cycleFull_pred] ; exact cycleSection_mono ha
· exact cycleSection_subset_cycleFull

lemma insert_cycleSection : insert ((π ^ (a + 1 : ℕ)) x) (CycleSection π x a) = (CycleSection π x (a + 1)) := by
ext y ; simp_rw [Finset.mem_insert, mem_cycleSection_iff] ; refine ⟨?_, ?_⟩
· rintro (rfl | ⟨b, hb, rfl⟩)
  · exact ⟨a + 1, le_refl _, rfl⟩
  · exact ⟨b, le_trans hb (Nat.le_succ a), rfl⟩
· rintro ⟨b, hb, rfl⟩ ; rw [le_iff_lt_or_eq] at hb ; rcases hb with (hb | rfl)
  · right ; exact ⟨b, Nat.lt_add_one_iff.mp hb, rfl⟩
  · left ; rfl

lemma cycleSection_strict_mono (hf : ¬ Function.IsFixedPt π x) (hab : a + 1 ≤ b) (hb : a + 1 < (π.cycleOf x).support.card) :
CycleSection π x a ⊂ CycleSection π x b := by
rw [Finset.ssubset_iff] ; refine ⟨(π ^ (a + 1 : ℕ)) x, ?_, ?_⟩
· rw [mem_cycleSection_iff] ; push_neg ; intros c hc hac ; rw [← Nat.lt_add_one_iff] at hc ; refine ne_of_lt hc ?_
  rw [← Nat.mod_eq_of_lt (lt_trans hc hb), ← Nat.mod_eq_of_lt hb, ← Nat.ModEq]
  exact (Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply (a := x) (π.isCycleOn_support_cycleOf x)
    <| (π.mem_support_cycleOf_iff' hf).mpr (by rfl)).mp hac
· rw [insert_cycleSection] ; exact cycleSection_mono hab

-- Definition 2.3

def CycleMin [LinearOrder α] (π : Equiv.Perm α) (x : α) : α :=
if h : Function.IsFixedPt π x then x else (π.cycleOf x).support.min' ⟨x, (π.mem_support_cycleOf_iff' h).mpr (by rfl)⟩

section LinearOrder
variable [LinearOrder α]

@[simp]
lemma cycleMin_of_fixed (h : Function.IsFixedPt π x) : CycleMin π x = x := dif_pos h

@[simp]
lemma cycleMin_of_not_fixed (h : ¬ Function.IsFixedPt π x) :
CycleMin π x = (π.cycleOf x).support.min' ⟨x, (π.mem_support_cycleOf_iff' h).mpr (by rfl)⟩ := dif_neg h

lemma cycleMin_eq_min_CycleFull : CycleMin π x = (CycleFull π x).min' cycleFull_nonempty := by
by_cases h : Function.IsFixedPt π x
· simp_rw [cycleMin_of_fixed h, cycleFull_of_fixed h] ; rfl
· simp_rw [cycleMin_of_not_fixed h, cycleFull_of_not_fixed h]

lemma cycleMin_eq_min_cycleSection :
CycleMin π x = (CycleSection π x ((CycleFull π x).card - 1)).min' cycleSection_nonempty := by
rw [cycleMin_eq_min_CycleFull] ; congr ; exact cycleFull_eq_cycleSection_cycleFull_pred

lemma cycleMin_mem_cycleFull (π : Equiv.Perm α) (x : α):
CycleMin π x ∈ CycleFull π x := by
by_cases h : Function.IsFixedPt π x
· simp_rw [cycleMin_of_fixed h, cycleFull_of_fixed h, Finset.mem_singleton]
· simp_rw [cycleMin_of_not_fixed h, cycleFull_of_not_fixed h, Finset.min'_mem]

lemma cycleMin_exists_pow_apply (π : Equiv.Perm α) (x : α):
∃ k : ℤ, (π^k) x = CycleMin π x :=
mem_cycleFull_iff.mp (cycleMin_mem_cycleFull π x)

lemma cycleMin_exists_pow_apply' (π : Equiv.Perm α) (x : α):
∃ k, k ≤ ((CycleFull π x).card - 1) ∧ (π^k) x = CycleMin π x :=
mem_cycleFull_iff'.mp (cycleMin_mem_cycleFull π x)

lemma cycleMin_exists_pow_apply'' (π : Equiv.Perm α) (x : α):
∃ k, k < (CycleFull π x).card ∧ (π^k) x = CycleMin π x :=
mem_cycleFull_iff''.mp (cycleMin_mem_cycleFull π x)

lemma cycleMin_eq_min_cycleSection_ge (ha : (CycleFull π x).card - 1 ≤ a) :
CycleMin π x = (CycleSection π x a).min' cycleSection_nonempty := by
simp_rw [cycleMin_eq_min_CycleFull, cycleFull_eq_cycleSection_ge_cycleFull_pred ha]

lemma cycleMin_le (π : Equiv.Perm α) (x : α) (h : π.SameCycle x y) : CycleMin π x ≤ y := by
rw [cycleMin_eq_min_CycleFull] ; exact Finset.min'_le _ y (mem_cycleFull_iff.mpr h)

lemma cycleMin_le_self : CycleMin π x ≤ x := cycleMin_le π x ⟨0, rfl⟩

@[simp]
lemma cycleMin_bot [OrderBot α] : CycleMin π ⊥ = ⊥ := le_antisymm cycleMin_le_self bot_le

lemma le_cycleMin (h : ∀ y, π.SameCycle x y → z ≤ y) : z ≤ CycleMin π x  := by
simp_rw [cycleMin_eq_min_CycleFull, Finset.le_min'_iff, mem_cycleFull_iff] ; exact h

lemma le_cycleMin_iff : z ≤ CycleMin π x ↔ ∀ y, π.SameCycle x y → z ≤ y := by
simp_rw [cycleMin_eq_min_CycleFull, Finset.le_min'_iff, mem_cycleFull_iff]

def FastCycleMin (n : ℕ) (π : Equiv.Perm α) (x : α) : α :=
  match n with
  | 0 => x
  | (i+1) => min (FastCycleMin i π x) (FastCycleMin i π <| (π ^ (2^i : ℕ)) x)

lemma fastCycleMin_zero_eq : FastCycleMin 0 π x = x := rfl

lemma fastCycleMin_succ_eq :
FastCycleMin (i + 1) π x = min (FastCycleMin i π x) (FastCycleMin i π <| (π ^ (2^i : ℕ)) x) := rfl



-- Theorem 2.4

lemma fastCycleMin_eq_min_cycleSection :
FastCycleMin i π x = (CycleSection π x (2^i - 1)).min' cycleSection_nonempty := by
  induction' i with i hi generalizing x
  · simp_rw [fastCycleMin_zero_eq, Nat.zero_eq, pow_zero, tsub_eq_zero_of_le (le_refl _),
      cycleSection_zero_singleton, Finset.min'_singleton]
  · simp_rw [fastCycleMin_succ_eq, hi, le_antisymm_iff, le_min_iff, Finset.le_min'_iff, min_le_iff,
      mem_cycleSection_iff, Nat.pow_succ', Nat.two_mul, add_tsub_assoc_of_le (i.one_le_two_pow)]
    refine And.intro ?_ (And.intro ?_ ?_)
    · rintro y ⟨b, hb, rfl⟩
      rcases le_or_lt (2^i) b with h | h
      · refine Or.inr <| Finset.min'_le _ _ <| mem_cycleSection_iff.mpr ⟨b - 2^i,
        tsub_le_iff_left.mpr hb, ?_⟩
        simp_rw [← Equiv.Perm.mul_apply, ← pow_add, tsub_add_cancel_of_le h]
      · exact Or.inl <| Finset.min'_le _ _ <| mem_cycleSection_iff.mpr ⟨b, Nat.le_pred_of_lt h, rfl⟩
    · rintro y ⟨b, hb, rfl⟩
      exact Finset.min'_le _ _ <| mem_cycleSection_iff.mpr ⟨b, le_trans hb
        <| (le_add_iff_nonneg_left _).mpr (zero_le _), rfl⟩
    · rintro y ⟨b, hb, rfl⟩
      refine Finset.min'_le _ _ <| mem_cycleSection_iff.mpr ⟨2^i + b, (add_le_add_iff_left _).mpr hb, ?_⟩
      simp_rw [add_comm, pow_add, Equiv.Perm.mul_apply]

-- Theorem 2.5

lemma cycleMin_eq_fastCycleMin (h : (CycleFull π x).card ≤ 2^i) :
FastCycleMin i π x = CycleMin π x := by
rw [fastCycleMin_eq_min_cycleSection, cycleMin_eq_min_cycleSection_ge (tsub_le_tsub_right h _)]

-- Theorem 2.2
lemma cycleMin_eq_cycleMin_apply : CycleMin π x = CycleMin π (π x) := by
by_cases h : Function.IsFixedPt π x
· rw [h]
· simp_rw [cycleMin_of_not_fixed h, cycleMin_of_not_fixed ((EmbeddingLike.apply_eq_iff_eq _).not.mpr h),
    Equiv.Perm.cycleOf_self_apply]

lemma cycleMin_eq_cycleMin_apply_inv : CycleMin π x = CycleMin π (π⁻¹ x) := by
rw [cycleMin_eq_cycleMin_apply (x := (π⁻¹ x)), Equiv.Perm.apply_inv_self]

end LinearOrder

section CanonicallyLinearOrderedMonoid

@[simp]
lemma cycleMin_zero [CanonicallyLinearOrderedAddMonoid α] : CycleMin π 0 = 0 :=
le_antisymm cycleMin_le_self (zero_le _)

end CanonicallyLinearOrderedMonoid

section Fin

@[simp]
lemma Fin.cycleMin_zero {τ : Equiv.Perm (Fin m)} [NeZero m] : CycleMin τ 0 = (0 : Fin m) :=
le_antisymm cycleMin_le_self (Fin.zero_le' _)

end Fin

end CycleMin





def XBackXForth (π : Equiv.Perm (Fin (2^(m + 1)))) := π * (flipBit 0) * π⁻¹ * (flipBit 0)

lemma xBXF_def : XBackXForth π = π * (flipBit 0) * π⁻¹ * (flipBit 0) := rfl

lemma xBXF_inv : (XBackXForth π)⁻¹ = (flipBit 0) * π * (flipBit 0) * π⁻¹ := by
rw [xBXF_def] ; simp only [mul_assoc, mul_inv_rev, flipBit_inv, inv_inv]

lemma xBXF_apply : (XBackXForth π) q = π ((flipBit 0) (π⁻¹ (flipBit 0 q))) := rfl

lemma xBXF_inv_apply : (XBackXForth π)⁻¹ q = (flipBit 0) (π ((flipBit 0) (π⁻¹ q))) := by
rw [xBXF_inv] ; rfl


lemma flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit : flipBit 0 * XBackXForth π =
(XBackXForth π)⁻¹ * flipBit 0 := by simp_rw [xBXF_inv, xBXF_def, mul_assoc]

lemma flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit : XBackXForth π * flipBit 0 =
flipBit 0 * (XBackXForth π)⁻¹ := by rw [eq_mul_inv_iff_mul_eq, mul_assoc,
  flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, mul_inv_cancel_left]

/-
lemma xBXF_eq_xBXF_inv_conj_flipBit : (XBackXForth π) = flipBit 0 * (XBackXForth π)⁻¹ * flipBit 0 := by
rw [← flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit, flipBit_mul_cancel_right]

lemma xBXF_inv_eq_xBXF_conj_flipBit : (XBackXForth π)⁻¹ = flipBit 0 * XBackXForth π * flipBit 0 := by
rw [flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, flipBit_mul_cancel_right]

lemma flipBit_eq_xBXF_mul_flipBit_mul_xBXF : flipBit 0 = (XBackXForth π) * (flipBit 0) *
  (XBackXForth π) := by rw [flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit, inv_mul_cancel_right]

lemma flipBit_eq_xBXF_inv_mul_flipBit_mul_xBXF_inv : flipBit 0 = (XBackXForth π)⁻¹ * (flipBit 0) *
  (XBackXForth π)⁻¹ := by rw [← flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, mul_inv_cancel_right]
-/

@[simp]
lemma xBXF_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF_inv : XBackXForth π (flipBit 0 q) =
flipBit 0 ((XBackXForth π)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_inv_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF : (XBackXForth π)⁻¹ (flipBit 0 q) =
flipBit 0 (XBackXForth π q)
:= by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit, Equiv.Perm.mul_apply]

lemma flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit {k : ℕ} : flipBit 0 * ((XBackXForth π)^k) =
((XBackXForth π)^k)⁻¹ * flipBit 0 := by
induction' k with n hn
· rw [Nat.zero_eq, pow_zero, inv_one, mul_one, one_mul]
· simp_rw [pow_succ', ← mul_assoc, hn, ← pow_succ', pow_succ'', mul_inv_rev, mul_assoc,
    flipBit_mul_xBXF_eq_xBXF_inv_mul_flipBit]

lemma xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow {k : ℕ} : ((XBackXForth π)^k) * flipBit 0 =
flipBit 0 * ((XBackXForth π)^k)⁻¹ := by
rw [eq_mul_inv_iff_mul_eq, mul_assoc, flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit,
  mul_inv_cancel_left]

/-
lemma xBXF_pow_eq_conj_flipBit_xBXF_pow_inv {k : ℕ} :
(XBackXForth π)^k = (flipBit 0) * ((XBackXForth π)^k)⁻¹ * (flipBit 0) := by
rw [← xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow, flipBit_mul_cancel_right]

lemma xBXF_pow_inv_eq_conj_flipBit_xBXF_pow {k : ℕ} :
((XBackXForth π)^k)⁻¹ = (flipBit 0) * (XBackXForth π)^k * (flipBit 0) := by
rw [flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit, flipBit_mul_cancel_right]


lemma flipBit_eq_xBXF_pow_mul_flipBit_mul_xBXF_pow {k : ℕ} :
flipBit 0 = (XBackXForth π)^k * (flipBit 0) * (XBackXForth π)^k := by
rw [xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow, inv_mul_cancel_right]

lemma flipBit_eq_xBXF_pow_inv_mul_flipBit_mul_xBXF_pow_inv {k : ℕ} :
flipBit 0 = ((XBackXForth π)^k)⁻¹ * (flipBit 0) * ((XBackXForth π)^k)⁻¹ := by
rw [← flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit, mul_inv_cancel_right]
-/

@[simp]
lemma xBXF_pow_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF_pow {k : ℕ} : ((XBackXForth π)^k) (flipBit 0 q) =
flipBit 0 (((XBackXForth π)^k)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_pow_inv_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF {k : ℕ} : ((XBackXForth π)^k)⁻¹ (flipBit 0 q)
= flipBit 0 (((XBackXForth π)^k) q)
:= by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit, Equiv.Perm.mul_apply]

lemma xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv {k : ℤ} :
(XBackXForth π)^k * (flipBit 0) = (flipBit 0) * ((XBackXForth π)^k)⁻¹ := by
cases k
· simp only [Int.ofNat_eq_coe, zpow_coe_nat, zpow_neg]
  exact xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow
· simp only [zpow_negSucc, zpow_neg, inv_inv]
  exact flipBit_mul_xBXF_pow_eq_xBXF_pow_inv_mul_flipBit.symm

lemma flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit {k : ℤ} :
(flipBit 0) * (XBackXForth π)^k = ((XBackXForth π)^k)⁻¹ * (flipBit 0) := by
rw [← zpow_neg, xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, zpow_neg, inv_inv]

/-
lemma xBXF_zpow_eq_conj_flipBit_xBXF_zpow_inv {k : ℤ} :
(XBackXForth π)^k = (flipBit 0) * ((XBackXForth π)^k)⁻¹ * (flipBit 0) := by
rw [← xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, flipBit_mul_cancel_right]

lemma xBXF_zpow_neg_eq_conj_flipBit_xBXF_zpow {k : ℤ} :
((XBackXForth π)^k)⁻¹ = (flipBit 0) * (XBackXForth π)^k * (flipBit 0) := by
rw [flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit, flipBit_mul_cancel_right]

lemma flipBit_eq_xBXF_zpow_mul_flipBit_mul_xBXF_zpow {k : ℤ} :
flipBit 0 = (XBackXForth π)^k * (flipBit 0) * (XBackXForth π)^k := by
rw [xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, inv_mul_cancel_right]

lemma flipBit_eq_xBXF_zpow_inv_mul_flipBit_mul_xBXF_zpow_inv {k : ℤ} :
flipBit 0 = ((XBackXForth π)^k)⁻¹ * (flipBit 0) * ((XBackXForth π)^k)⁻¹ := by
rw [← flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit, mul_inv_cancel_right]
-/

-- Theorem 4.3 (a) (ish)

@[simp]
lemma xBXF_zpow_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF_zpow_inv {k : ℤ} :
((XBackXForth π)^k) (flipBit 0 q) = (flipBit 0) (((XBackXForth π)^k)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, Equiv.Perm.mul_apply]

@[simp]
lemma xBXR_zpow_inv_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF_zpow {k : ℤ} :
(((XBackXForth π)^k)⁻¹) (flipBit 0 q) = flipBit 0 (((XBackXForth π)^k) q) := by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_apply_ne_flipBit_eq_mergeBitRes_not_getBit_getRes : (XBackXForth π) q ≠ (flipBit 0) q := by
simp_rw [xBXF_apply, ne_eq, ← Equiv.Perm.eq_inv_iff_eq (y := (flipBit 0) q)]
exact flipBit_ne_self

@[simp]
lemma xBXF_pow_apply_ne_flipBit_eq_mergeBitRes_not_getBit_getRes {k : ℕ} : ((XBackXForth π)^k) q ≠ (flipBit 0) q := by
induction' k using Nat.twoStepInduction with k IH generalizing q
· rw [pow_zero]
  exact (flipBit_ne_self).symm
· rw [pow_one]
  exact xBXF_apply_ne_flipBit_eq_mergeBitRes_not_getBit_getRes
· intros h
  rw [pow_succ'' (n := k.succ), pow_succ' (n := k), Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    ← Equiv.eq_symm_apply (x := flipBit 0 q), ← Equiv.Perm.inv_def,
    xBXF_inv_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF] at h
  exact IH h

@[simp]
lemma xBXF_pow_inv_ne_flipBit {k : ℕ} : (((XBackXForth π)^k)⁻¹) q ≠ flipBit 0 q := by
simp_rw [ne_eq, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
convert (xBXF_pow_apply_ne_flipBit_eq_mergeBitRes_not_getBit_getRes (q := flipBit 0 q)).symm
exact flipBit_flipBit.symm

@[simp]
lemma xBXF_zpow_ne_flipBit {k : ℤ} : ((XBackXForth π)^k) q ≠ flipBit 0 q := by
cases k <;> simp

-- Theorem 4.3 (b)
lemma xBXF_zpow_ne_flipBit_mul_xBXF_zpow {j k : ℤ}  :
((XBackXForth π)^j) q ≠ flipBit 0 (((XBackXForth π)^k) q) := by
rw [← sub_add_cancel j k, zpow_add, Equiv.Perm.mul_apply]
exact xBXF_zpow_ne_flipBit

lemma cycleFull_xBXF_disjoint_image_flipBit {q : Fin (2 ^ (m + 1))} : Disjoint (CycleFull (XBackXForth π) q)
((CycleFull (XBackXForth π) q).image (flipBit 0)) := by
simp_rw [Finset.disjoint_iff_ne, Finset.mem_image, mem_cycleFull_iff]
rintro _ ⟨j, rfl⟩ _ ⟨_, ⟨⟨_, rfl⟩, rfl⟩⟩
exact xBXF_zpow_ne_flipBit_mul_xBXF_zpow

-- Theorem 4.3 (c)
lemma cycleFull_xBXF_card_le_two_pow {q : Fin (2 ^ (m + 1))} :
  (CycleFull (XBackXForth π) q).card ≤ 2^m := by
refine' le_of_mul_le_mul_left _ (zero_lt_two)
rw [two_mul]; nth_rewrite 2 [← Finset.card_image_of_injective _ ((flipBit 0).injective)]
rw [← Nat.pow_succ', ← Finset.card_disjoint_union cycleFull_xBXF_disjoint_image_flipBit]
exact le_of_le_of_eq (Finset.card_le_of_subset (Finset.subset_univ _)) (Finset.card_fin _)

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

-- Theorem 4.4
lemma cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin :
CycleMin (XBackXForth π) (flipBit 0 q) = (flipBit 0) (CycleMin (XBackXForth π) q) := by
rcases cycleMin_exists_pow_apply (XBackXForth π) q with ⟨j, hjq₂⟩
refine' eq_of_le_of_not_lt _ (fun h => _)
· refine' cycleMin_le (XBackXForth π) (flipBit 0 q)  ⟨-j, _⟩
  simp_rw [zpow_neg, xBXR_zpow_inv_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF_zpow, hjq₂]
· rcases cycleMin_exists_pow_apply (XBackXForth π) (flipBit 0 q) with ⟨k, hkq₂⟩
  rw [←hkq₂, ← hjq₂, xBXF_zpow_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF_zpow_inv, ← zpow_neg] at h
  rcases lt_trichotomy ((XBackXForth π ^ (-k)) q) ((XBackXForth π ^ j) q) with H | H | H
  · exact (cycleMin_le (XBackXForth π) q ⟨-k, rfl⟩).not_lt (hjq₂.symm ▸ H)
  · exact False.elim (lt_irrefl _ (H ▸ h))
  · exact xBXF_zpow_ne_flipBit_mul_xBXF_zpow (eq_flipBit_of_lt_of_flipBit_gt H h)

/-
lemma getBit_cycleMin_not_comm_and_getRes_cycleMin_not_eq_getRes_cycleMin :
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (!b) p)) =
  !(getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 b p))) ∧
  (getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (!b) p)) =
  (getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 b p)))) := by
rw [← eq_flipBit_zero_iff, ← flipBit_mergeBitRes]
exact cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin

lemma getBit_cycleMin_not_comm :
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (!b) p)) =
  !(getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 b p))) :=
getBit_cycleMin_not_comm_and_getRes_cycleMin_not_eq_getRes_cycleMin.1

lemma getBit_cycleMin_true_eq_not_getBit_cycleMin_false :
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 true p)) =
  !(getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p))) :=
Bool.not_false ▸ getBit_cycleMin_not_comm

lemma getBit_cycleMin_false_eq_not_getBit_cycleMin_true :
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p)) =
  !(getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 true p))) := by
rw [getBit_cycleMin_true_eq_not_getBit_cycleMin_false, Bool.not_not]

lemma getRes_cycleMin_not_eq_getRes_cycleMin :
(getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (!b) p)) =
  (getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 b p))))  :=
getBit_cycleMin_not_comm_and_getRes_cycleMin_not_eq_getRes_cycleMin.2

lemma getRes_cycleMin_true_eq_getRes_cycleMin_false :
(getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 (true) p)) =
  (getRes 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p))))  :=
Bool.not_false ▸ getRes_cycleMin_not_eq_getRes_cycleMin
-/

abbrev FirstControlBits (π) (p : Fin (2^m)) :=
getBit 0 (CycleMin (XBackXForth π) (mergeBitRes 0 false p))

def FirstControl (π : Equiv.Perm (Fin (2^(m + 1)))) := resCondFlip 0 (FirstControlBits π)

abbrev LastControlBits (π) (p : Fin (2^m)) :=
getBit 0 ((FirstControl π) (π (mergeBitRes 0 false p)))

abbrev LastControl (π : Equiv.Perm (Fin (2^(m + 1)))) := resCondFlip 0 (LastControlBits π)

abbrev MiddlePerm (π : Equiv.Perm (Fin (2^(m + 1)))) := (FirstControl π) * π * (LastControl π)

abbrev flmDecomp (π : Equiv.Perm (Fin (2^((m + 1) )))) :=
(FirstControlBits π, MiddlePerm π, LastControlBits π)

-- Theorem 5.2
lemma firstControlBit_false {π : Equiv.Perm (Fin (2^(m + 1)))} : FirstControlBits π 0 = false := by
simp_rw [FirstControlBits,  getBit_zero, mergeBitRes_apply_false_zero, Fin.cycleMin_zero, Fin.val_zero']

-- Theorem 5.3
lemma getBit_zero_firstControl_apply_eq_getBit_zero_cycleMin :
∀ {q}, getBit 0 (FirstControl π q) = getBit 0 (CycleMin (XBackXForth π) q) := by
simp_rw [forall_iff_forall_mergeBitRes 0, FirstControl, getBit_resCondFlip', getRes_mergeBitRes,
  getBit_mergeBitRes, Bool.xor_false_right, Bool.xor_true, ← Bool.not_false, ← flipBit_mergeBitRes,
  cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin, getBit_flipBit, forall_const]

lemma cycleMin_apply_flipBit_zero_eq_cycleMin_flipBit_zero_apply :
CycleMin (XBackXForth π) (π (flipBit 0 q)) = CycleMin (XBackXForth π) (flipBit 0 (π q)):= by
rw [cycleMin_eq_cycleMin_apply (x := flipBit 0 (π q)), xBXF_apply_flipBit_eq_flipBit_eq_mergeBitRes_not_getBit_getRes_xBXF_inv,
  xBXF_inv_apply, Equiv.Perm.inv_apply_self, flipBit_flipBit]

lemma flipBit_zero_cycleMin_apply_eq_cycleMin_apply_flipBit_zero :
(flipBit 0) (CycleMin (XBackXForth π) (π q)) = CycleMin (XBackXForth π) (π (flipBit 0 q)) := by
rw [cycleMin_apply_flipBit_zero_eq_cycleMin_flipBit_zero_apply,
  cycleMin_flipBit_zero_eq_flipBit_zero_cycleMin]

lemma cycleMin_apply_mergeBitRes_zero_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_not :
CycleMin (XBackXForth π) (π (mergeBitRes 0 b p)) =
  (flipBit 0) (CycleMin (XBackXForth π) (π (mergeBitRes 0 (!b) p))) := by
rw [flipBit_zero_cycleMin_apply_eq_cycleMin_apply_flipBit_zero, flipBit_mergeBitRes, Bool.not_not]

lemma cycleMin_apply_mergeBitRes_zero_true_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_false :
CycleMin (XBackXForth π) (π (mergeBitRes 0 true p)) =
  (flipBit 0) (CycleMin (XBackXForth π) (π (mergeBitRes 0 false p))) :=
Bool.not_true ▸ cycleMin_apply_mergeBitRes_zero_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_not

lemma cycleMin_apply_mergeBitRes_zero_false_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_true :
CycleMin (XBackXForth π) (π (mergeBitRes 0 false p)) =
  (flipBit 0) (CycleMin (XBackXForth π) (π (mergeBitRes 0 true p))) :=
Bool.not_false ▸ cycleMin_apply_mergeBitRes_zero_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_not

-- Theorem 5.4
lemma getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply :
∀ {q}, getBit 0 (LastControl π q) = getBit 0 (FirstControl π (π q)) := by
rw [forall_iff_forall_mergeBitRes 0]
simp_rw [LastControl, getBit_resCondFlip',
  getBit_zero_firstControl_apply_eq_getBit_zero_cycleMin, getRes_mergeBitRes,
  getBit_mergeBitRes, Bool.xor_false_right,
  cycleMin_apply_mergeBitRes_zero_false_eq_flipBit_zero_cycleMin_apply_mergeBitRes_zero_true,
  Bool.xor_true, getBit_flipBit, Bool.not_not, forall_const]

-- Theorem 5.5
lemma MiddlePerm_invar (π : Equiv.Perm (Fin (2^((m + 1) + 1)))) : bitInvar 0 (MiddlePerm π) := by
simp_rw [bitInvar_iff_getBit_apply_eq_getBit, Equiv.Perm.mul_apply,
  ← getBit_zero_lastControl_apply_eq_getBit_zero_firstControl_perm_apply, ← Equiv.Perm.mul_apply,
  resCondFlip_mul_self, Equiv.Perm.coe_one, id_eq, forall_const]

end Reimplementation

@[simps]
def permsResOfBitInvar (i : Fin (m + 1)) (π : Equiv.Perm (Fin (2^(m + 1)))) (h : bitInvar i π) (b : Bool) :
Equiv.Perm (Fin (2^m)) where
  toFun p := getRes i (π (mergeBitRes i b p))
  invFun p := getRes i (π.symm (mergeBitRes i b p))
  left_inv p := by simp_rw [mergeBitRes_getRes_apply_mergeBitRes_eq_apply_mergeBitRes h,
    Equiv.symm_apply_apply, getRes_mergeBitRes]
  right_inv p := by simp_rw [mergeBitRes_getRes_apply_mergeBitRes_eq_apply_mergeBitRes (symm_bitInvar_of_bitInvar h),
                  Equiv.apply_symm_apply, getRes_mergeBitRes]

@[simps]
def permsResToBitInvar (i : Fin (m + 1)) (πe : Equiv.Perm (Fin (2^m))) (πo : Equiv.Perm (Fin (2^m))) :
Equiv.Perm (Fin (2^(m + 1))) where
  toFun q := bif getBit i q then mergeBitRes i true (πo (getRes i q)) else mergeBitRes i false (πe (getRes i q))
  invFun q := bif getBit i q then mergeBitRes i true (πo.symm (getRes i q)) else mergeBitRes i false (πe.symm (getRes i q))
  left_inv q := by rcases(getBit i q).dichotomy with (h | h) <;> simp [h]
  right_inv q := by rcases(getBit i q).dichotomy with (h | h) <;> simp [h]

lemma bitInvarPermsResToBitInvar (i : Fin (m + 1)) (πe : Equiv.Perm (Fin (2^m))) (πo : Equiv.Perm (Fin (2^m)))
: bitInvar i (permsResToBitInvar i πe πo) := by
rw [bitInvar_iff_getBit_apply_eq_getBit]
intros q ; rcases (getBit i q).dichotomy with (h | h) <;>
simp only [permsResToBitInvar_apply, h, cond_false, cond_true, getBit_mergeBitRes]

lemma leftInverse_permsResToBitInvar_permsResOfBitInvar {i : Fin (m + 1)} {π : Equiv.Perm (Fin (2^(m + 1)))}
(hπ : bitInvar i π) : permsResToBitInvar i (permsResOfBitInvar i π hπ false) (permsResOfBitInvar i π hπ true) = π := by
  ext q : 1; rcases (getBit i q).dichotomy with (h | h) <;>
  simp_rw [permsResToBitInvar_apply, permsResOfBitInvar_apply, mergeBitRes_getRes_of_getBit_eq h, h] <;>
  exact mergeBitRes_getRes_of_getBit_eq ((getBit_apply_eq_getBit_of_bitInvar hπ (q := q)).symm ▸ h)

lemma rightInverse_permsResToBitInvar_permsResOfBitInvar_false (i : Fin (m + 1)) (πe : Equiv.Perm (Fin (2^m)))
(πo : Equiv.Perm (Fin (2^m))) : permsResOfBitInvar i _ (bitInvarPermsResToBitInvar i πe πo) false = πe := by
simp_rw [Equiv.ext_iff, permsResOfBitInvar, permsResToBitInvar, Equiv.coe_fn_mk, getBit_mergeBitRes,
  cond_false, getRes_mergeBitRes, forall_const]

lemma rightInverse_permsResToBitInvar_permsResOfBitInvar_true (i : Fin (m + 1)) (πe : Equiv.Perm (Fin (2^m)))
(πo : Equiv.Perm (Fin (2^m))) : permsResOfBitInvar i _ (bitInvarPermsResToBitInvar i πe πo) true = πo := by
simp_rw [Equiv.ext_iff, permsResOfBitInvar, permsResToBitInvar, Equiv.coe_fn_mk, getBit_mergeBitRes,
  cond_true, getRes_mergeBitRes, forall_const]

@[simps]
def equivBitInvar (i : Fin (m + 1)) :
{π : Equiv.Perm (Fin (2^(m + 1))) // bitInvar i π} ≃ Equiv.Perm (Fin (2^m)) × Equiv.Perm (Fin (2^m)) where
  toFun π := (permsResOfBitInvar i π.val π.prop false, permsResOfBitInvar i π.val π.prop true)
  invFun := fun (πe, πo) => ⟨permsResToBitInvar i πe πo, bitInvarPermsResToBitInvar i πe πo⟩
  left_inv π := Subtype.eq (leftInverse_permsResToBitInvar_permsResOfBitInvar π.prop)
  right_inv := fun (πe, πo) => by
    simp_rw [rightInverse_permsResToBitInvar_permsResOfBitInvar_false,
    rightInverse_permsResToBitInvar_permsResOfBitInvar_true]

abbrev ControlBitsLayer (m : ℕ) := Fin (2^m) → Bool

def InductiveControlBits : ℕ → Type
  | 0 => ControlBitsLayer 0
  | (m + 1) => (ControlBitsLayer (m + 1) × (ControlBitsLayer (m + 1))) × ((InductiveControlBits m) × (InductiveControlBits m))

def indCBitsToPerm (cb : InductiveControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
  match m with
  | 0 => resCondFlip 0 cb
  | _ + 1 => (resCondFlip 0 cb.fst.fst) *
      ((equivBitInvar 0).symm (cb.snd.map indCBitsToPerm indCBitsToPerm)) * (resCondFlip 0 cb.fst.snd)

def permToIndCBits (π : Equiv.Perm (Fin (2^(m + 1)))) : InductiveControlBits m :=
  match m with
  | 0 => LastControlBits π
  | _ + 1 => ((FirstControlBits π, LastControlBits π), (equivBitInvar 0 ⟨_, MiddlePerm_invar π⟩).map permToIndCBits permToIndCBits)


def weaveControlBits :  ControlBitsLayer (m + 1) ≃ (ControlBitsLayer m × ControlBitsLayer m) :=
calc
  _ ≃ ((Bool × Fin (2^m)) → Bool) := Equiv.arrowCongr (getBitRes 0) (Equiv.refl _)
  _ ≃ (Fin (2^m) ⊕ Fin (2^m) → Bool) := Equiv.arrowCongr (Equiv.boolProdEquivSum _) (Equiv.refl _)
  _ ≃ _ := (Equiv.sumArrowEquivProdArrow _ _ _)

abbrev LayerTupleControlBits (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

abbrev BitTupleControlBits (m : ℕ) := Fin ((2*m + 1)*(2^m)) → Bool

abbrev PairPairsControlBits (m : ℕ) :=
((ControlBitsLayer (m + 1) × ControlBitsLayer (m + 1)) × (LayerTupleControlBits m × LayerTupleControlBits m))

def bitTupleEquivLayerTuple : BitTupleControlBits m ≃ LayerTupleControlBits m :=
calc
  _ ≃ ((Fin (2*m + 1) × Fin (2^m)) → Bool) := Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl _)
  _ ≃ _ := Equiv.curry _ _ _

def layerTupleSuccEquivPairPairs : LayerTupleControlBits (m + 1) ≃ PairPairsControlBits m :=
calc
  _ ≃ _ := (Equiv.piFinSucc _ _)
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (calc
                                            _ ≃ _ := (finCongr (mul_add 2 m 1)).arrowCongr (Equiv.refl _)
                                            _ ≃ _ := Equiv.piFinSuccAboveEquiv (fun _ => _) (Fin.last _))
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (calc
                                            _ ≃ _ := Equiv.arrowCongr (Equiv.refl _)
                                              (calc
                                                _ ≃ _ := Equiv.arrowCongr (getBitRes 0) (Equiv.refl _)
                                                _ ≃ _ := Equiv.arrowCongr (Equiv.boolProdEquivSum _) (Equiv.refl _)
                                                _ ≃ _ := (Equiv.sumArrowEquivProdArrow _ _ _))
                                            _ ≃ _ := Equiv.arrowProdEquivProdArrow _ _ _)

def layerTupleEquivInductive : LayerTupleControlBits m ≃ InductiveControlBits m :=
  match m with
  | 0 => (Equiv.funUnique (Fin 1) _)
  | (_ + 1) => calc
                _ ≃ _ := layerTupleSuccEquivPairPairs
                _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr layerTupleEquivInductive layerTupleEquivInductive)

def bitTupleEquivInductive : BitTupleControlBits m ≃ InductiveControlBits m :=
bitTupleEquivLayerTuple.trans layerTupleEquivInductive

def permToLayerTuple (π : Equiv.Perm (Fin (2^(m + 1)))) : LayerTupleControlBits m :=
layerTupleEquivInductive.symm (permToIndCBits π)

def permToBitTuple (π : Equiv.Perm (Fin (2^(m + 1)))) : BitTupleControlBits m :=
bitTupleEquivInductive.symm (permToIndCBits π)

def layerTupleToPerm (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
indCBitsToPerm (layerTupleEquivInductive cb)

def bitTupleToPerm (cb : BitTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
indCBitsToPerm (bitTupleEquivInductive cb)

def layerTupleToPerm' (cb : LayerTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => resCondFlip (foldFin k) (cb k))).prod

def bitTupleToPerm' (cb : BitTupleControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => resCondFlip (foldFin k) (bitTupleEquivLayerTuple cb k))).prod

end ControlBits


-- Testing


def myControlBits69 := (![true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false] : BitTupleControlBits 2)


def myControlBits1 : LayerTupleControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def myControlBits2 : LayerTupleControlBits 1 := ![![false, true], ![false, true], ![true, true]]
def myControlBits2a : BitTupleControlBits 1 := ![false, true, false, true, true, true]
def myControlBits3 : LayerTupleControlBits 0 := ![![true]]
def myControlBits4 : LayerTupleControlBits 0 := ![![false]]

#eval bitTupleToPerm <| permToBitTuple (m := 4) (Equiv.refl _)
/--
#eval [0, 1, 2, 3].map (layerTupleToPerm (myControlBits1))
#eval [0, 1, 2, 3].map (layerTupleToPerm' (myControlBits1))
#eval permToLayerTuple <| (layerTupleToPerm (myControlBits1))
#eval permToLayerTuple <| (layerTupleToPerm' (myControlBits1))
#eval permToBitTuple <| (layerTupleToPerm (myControlBits1))
#eval permToBitTuple <| (bitTupleToPerm (myControlBits2a))

#eval [0, 1, 2, 3, 4, 5, 6, 7].map (bitTupleToPerm (m := 2) (myControlBits69))
-/


-- HELL

/-
def ControlBitsEquivInductiveControlBits : LayerTupleControlBits m ≃ InductiveControlBits m :=
  match m with
  | 0 => (Equiv.funUnique (Fin 1) _)
  | _ + 1 => (Equiv.piFinSucc _ _).trans (Equiv.prodCongr (Equiv.refl _) (((Equiv.piFinSuccAboveEquiv (fun _ => _)
                (Fin.last _)).trans ((Equiv.prodComm _ _).trans (Equiv.trans (Equiv.prodCongr
                  ((Equiv.arrowCongr (Equiv.refl _) alternControlBits).trans (Equiv.trans
                    (Equiv.arrowProdEquivProdArrow _ _ _)
                      (Equiv.prodCongr ControlBitsEquivInductiveControlBits ControlBitsEquivInductiveControlBits)))
                        (Equiv.refl _)) (Equiv.prodAssoc _ _ _))))))
-/
/-
lemma tiger_tiger (π : Equiv.Perm (Fin (2^1))) : (π 0 = 0 ∧ π 1 = 1) ∨ (π 0 = 1 ∧ π 1 = 0) := by
  simp_rw [pow_one] at π
  rcases Fin.exists_fin_two.mp ⟨π 0, rfl⟩ with (h₀ | h₀) <;>
  rcases Fin.exists_fin_two.mp ⟨π 1, rfl⟩ with (h₁ | h₁)
  · rw [Function.Injective.eq_iff' π.injective h₀] at h₁ ; simp at h₁
  · exact Or.inl ⟨h₀, h₁⟩
  · exact Or.inr ⟨h₀, h₁⟩
  · exact (π.injective.ne (zero_ne_one).symm (h₀ ▸ h₁)).elim

lemma hippo (π : Equiv.Perm (Fin 2)) :
InductiveControlBitsToPerm (PermToInductiveControlBits (m := 0) ((finCongr rfl).permCongr π)) = π := by
  ext q ;
  rcases (mergeBitRes_surj 0 q) with ⟨b, p, rfl⟩
  simp_rw [Fin.eq_zero p]
  simp only [InductiveControlBitsToPerm, resCondFlip, resCondFlipCore, PermToInductiveControlBits, finCongr,
    Fin.castIso_refl, OrderIso.refl_toEquiv, Equiv.Perm.permCongr_eq_mul, Equiv.Perm.refl_mul, Equiv.Perm.refl_inv,
    mul_one, Equiv.coe_fn_mk, getRes_mergeBitRes, flipBit_mergeBitRes]
  cases b
  · simp [LastControlBits, mergeBitRes_apply_false_zero, FirstControl, getBit_resCondFlip,FirstControlBits, Fin.eq_zero]
    simp [getBit_zero]
    rcases tiger_tiger π with (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    simp_rw [h₀, h₁]
    sorry
  · simp [LastControlBits, mergeBitRes_apply_false_zero, FirstControl, getBit_resCondFlip,FirstControlBits, Fin.eq_zero]
    simp [getBit_zero, finFunctionFinEquiv, finTwoEquiv, coe_mergeBitRes_zero]

lemma in_tiger (π : Equiv.Perm (Fin (2 ^ (m + 1)))): InductiveControlBitsToPerm (PermToInductiveControlBits π) = π := by
induction' m with m IH
· exact hippo π
/-
  ext q ;
  rcases (mergeBitRes_surj 0 q) with ⟨b, p, rfl⟩
  simp_rw [Fin.eq_zero p]
  simp_rw [Nat.zero_eq, InductiveControlBitsToPerm, PermToInductiveControlBits, resCondFlip, Nat.pow_zero,
     getBit_resCondFlip, FirstControlBits, resCondFlipCore]
  simp
  cases b
  · simp [LastControlBits, mergeBitRes_apply_false_zero, FirstControl,  getBit_resCondFlip,FirstControlBits, Fin.eq_zero]
    simp [getBit_zero]
    rcases tiger_tiger π with (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    simp_rw [h₀, h₁]
    sorry
  · simp [LastControlBits, mergeBitRes_apply_false_zero, FirstControl, getBit_resCondFlip,FirstControlBits, Fin.eq_zero]
    simp [getBit_zero, finFunctionFinEquiv, finTwoEquiv, coe_mergeBitRes_zero]
    sorry-/
· simp_rw [ InductiveControlBitsToPerm, PermToInductiveControlBits]
  ext ;
  simp [IH]
  simp_rw [FirstControl, ← Equiv.Perm.mul_apply, mul_assoc]
  simp


#check permToBitTuple (m := 2) (Equiv.Refl _)

-/
def myControlBits5 : LayerTupleControlBits 0 := ![![false]]