import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Combinatorics.Derangements.Basic

section BitResiduum

section GetMerge

def getBitResiduum (i : Fin (m + 1)) : Fin (2^(m + 1)) ≃ Bool × Fin (2^m) :=
(finFunctionFinEquiv.symm.trans ((Equiv.refl _).arrowCongr finTwoEquiv)).trans
<| (Equiv.piFinSuccAboveEquiv _ i).trans
<| (Equiv.refl _).prodCongr
<| ((Equiv.refl _).arrowCongr finTwoEquiv.symm).trans finFunctionFinEquiv

def getBit (i : Fin (m + 1)) : Fin (2^(m + 1)) → Bool := Prod.fst ∘ (getBitResiduum i)

def getResiduum (i : Fin (m + 1)) : Fin (2^(m + 1)) → Fin (2^m) := Prod.snd ∘ (getBitResiduum i)

def mergeBitResiduum (i : Fin (m + 1)) : Bool → Fin (2^m) → Fin (2^(m + 1)) :=
Function.curry (getBitResiduum i).symm

@[simp]
lemma getBitResiduum_apply : getBitResiduum i q = (getBit i q, getResiduum i q) := rfl

@[simp]
lemma getBitResiduum_symm_apply : (getBitResiduum i).symm bp = mergeBitResiduum i bp.fst bp.snd :=
rfl

lemma getBit_def : getBit i q = finTwoEquiv (finFunctionFinEquiv.symm q i) := rfl

lemma getResiduum_def : getResiduum i q =
(finFunctionFinEquiv <| (finTwoEquiv.symm) ∘
(fun j => finTwoEquiv (finFunctionFinEquiv.symm q (Fin.succAbove i j)))) := rfl

lemma mergeBitResiduum_def : mergeBitResiduum i b p =
(finFunctionFinEquiv <| (finTwoEquiv.symm) ∘
(Fin.insertNth i b <| finTwoEquiv ∘ (finFunctionFinEquiv.symm p))) := rfl

@[simp]
lemma getBit_mergeBitResiduum (i : Fin (m + 1)) : getBit i (mergeBitResiduum i b p) = b := by
simp_rw [getBit, mergeBitResiduum, Function.curry_apply, Function.comp_apply, Equiv.apply_symm_apply]

lemma ne_mergeBitResiduum_of_getBit_ne (i : Fin (m + 1)) (h : getBit i q ≠ b) :
q ≠ mergeBitResiduum i b p := by rintro rfl ; exact h (getBit_mergeBitResiduum i)

@[simp]
lemma getResiduum_mergeBitResiduum (i : Fin (m + 1)) : getResiduum i (mergeBitResiduum i b p) = p := by
simp_rw [getResiduum, mergeBitResiduum, Function.curry_apply, Function.comp_apply, Equiv.apply_symm_apply]

lemma ne_mergeBitResiduum_of_getResiduum_ne (i : Fin (m + 1)) (h : getResiduum i q ≠ p) :
q ≠ mergeBitResiduum i b p := by rintro rfl ; exact h (getResiduum_mergeBitResiduum i)

lemma getBit_succAbove_eq_getBit_getResiduum : getBit (j.succAbove i) = getBit i ∘ getResiduum j := by
ext ; simp_rw [Function.comp_apply, getResiduum_def, getBit_def,
        Equiv.symm_apply_apply, Function.comp_apply, Equiv.symm_apply_apply]

lemma getBit_succAbove_eq_getBit_getResiduum_apply : getBit (j.succAbove i) q = getBit i (getResiduum j q) := by
simp_rw [getResiduum_def, getBit_def, Equiv.symm_apply_apply, Function.comp_apply, Equiv.symm_apply_apply]

lemma exists_getBit_eq_getBit_getResiduum {j : Fin (m + 2)} (h : i ≠ j) :
∃ k, j.succAbove k = i ∧ getBit i = getBit k ∘ getResiduum j := by
rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
use k ; exact ⟨rfl, getBit_succAbove_eq_getBit_getResiduum⟩

lemma exists_getBit_eq_getBit_getResiduum_apply {j : Fin (m + 2)} (h : i ≠ j) :
∃ k, j.succAbove k = i ∧ ∀ q, getBit i q = getBit k (getResiduum j q) := by
rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
use k ; exact ⟨rfl, fun _ => getBit_succAbove_eq_getBit_getResiduum_apply⟩

lemma getBit_eq_getBit_succAbove_mergeBitResiduum (j : Fin (m + 2)) :
getBit i p = getBit (j.succAbove i) (mergeBitResiduum j b p) := by
simp [getBit_succAbove_eq_getBit_getResiduum, getResiduum_mergeBitResiduum]

@[simp]
lemma mergeBitResiduum_getBit_getResiduum : mergeBitResiduum i (getBit i q) (getResiduum i q) = q := by
simp_rw [getResiduum, mergeBitResiduum, getBit, Function.comp_apply, Function.curry_apply, Prod.mk.eta, Equiv.symm_apply_apply]

lemma mergeBitResiduum_inv (i : Fin (m + 1)) (h : getBit i q = b) (h₂ : getResiduum i q = p) : mergeBitResiduum i b p = q := by
convert mergeBitResiduum_getBit_getResiduum ; exact h.symm ; exact h₂.symm

lemma mergeBitResiduum_Bool_inj (i : Fin (m + 1)) (h : mergeBitResiduum i b₁ p₁ = mergeBitResiduum i b₂ p₂) : b₁ = b₂ := by
  have h₂ := (congrArg (getBit i) h) ; simp only [getBit_mergeBitResiduum] at h₂ ; exact h₂

lemma mergeBitResiduum_Fin_inj (i : Fin (m + 1)) (h : mergeBitResiduum i b₁ p₁ = mergeBitResiduum i b₂ p₂) : p₁ = p₂ := by
  have h₂ := (congrArg (getResiduum i) h) ; simp_rw [getResiduum_mergeBitResiduum] at h₂ ; exact h₂

lemma mergeBitResiduum_inj (i : Fin (m + 1)) (h : mergeBitResiduum i b₁ p₁ = mergeBitResiduum i b₂ p₂) : b₁ = b₂ ∧ p₁ = p₂ :=
⟨mergeBitResiduum_Bool_inj i h, mergeBitResiduum_Fin_inj i h⟩

lemma mergeBitResiduum_inj_iff (i : Fin (m + 1)) : mergeBitResiduum i b₁ p₁ = mergeBitResiduum i b₂ p₂ ↔ b₁ = b₂ ∧ p₁ = p₂ :=
⟨mergeBitResiduum_inj i, by rintro ⟨rfl, rfl⟩ ; rfl⟩

lemma mergeBitResiduum_surj (i : Fin (m + 1)) (q : Fin (2^(m + 1))) : ∃ b p, mergeBitResiduum i b p = q :=
⟨getBit i q, getResiduum i q, mergeBitResiduum_getBit_getResiduum⟩

lemma getResiduum_inv (i : Fin (m + 1)) (h : mergeBitResiduum i (getBit i q) p = q) : getResiduum i q = p := by
  rcases mergeBitResiduum_surj i q with ⟨b, p', rfl⟩ ; rw [getResiduum_mergeBitResiduum]
  exact (mergeBitResiduum_Fin_inj i h).symm

lemma getBit_inv (i : Fin (m + 1)) (h : mergeBitResiduum i b (getResiduum i q) = q) : getBit i q = b := by
  rcases mergeBitResiduum_surj i q with ⟨b', p', rfl⟩ ; rw [getBit_mergeBitResiduum]
  exact (mergeBitResiduum_Bool_inj i h).symm

lemma forall_iff_forall_mergeBitResiduum (i : Fin (m + 1)) {pr : Fin (2^(m + 1)) → Prop} :
(∀ (q : Fin (2^(m + 1))), pr q) ↔ (∀ p, pr (mergeBitResiduum i false p)) ∧ (∀ p, pr (mergeBitResiduum i true p)) :=
⟨ fun h => ⟨fun _ => h _, fun _ => h _⟩,
  fun h q => by rcases mergeBitResiduum_surj i q with ⟨(h|h), p, rfl⟩
                · exact h.1 _
                · exact h.2 _⟩

lemma exists_iff_exists_mergeBitResiduum (i : Fin (m + 1)) {pr : Fin (2^(m + 1)) → Prop} :
(∃ (q : Fin (2^(m + 1))), pr q) ↔ (∃ b p, pr (mergeBitResiduum i b p)) :=
⟨ fun ⟨q, hq⟩ => ⟨getBit i q, getResiduum i q, mergeBitResiduum_getBit_getResiduum ▸ hq⟩,
  fun ⟨b, p, hbp⟩ => ⟨mergeBitResiduum i b p, hbp⟩⟩

lemma getBit_surj (i : Fin (m + 1)) : ∃ p, mergeBitResiduum i (getBit i q) p = q :=
⟨getResiduum i q, mergeBitResiduum_getBit_getResiduum⟩

lemma getResiduum_surj (i : Fin (m + 1)) : ∃ b, mergeBitResiduum i b (getResiduum i q) = q :=
⟨getBit i q, mergeBitResiduum_getBit_getResiduum⟩

lemma getResiduum_getBit_inj (i : Fin (m + 1)) (h₁ : getBit i q₁ = getBit i q₂) (h₂ : getResiduum i q₁ = getResiduum i q₂) :
q₁ = q₂ := by rw [← mergeBitResiduum_getBit_getResiduum (i := i) (q := q₁), h₁, h₂, mergeBitResiduum_getBit_getResiduum]

lemma getResiduum_getBit_inj_iff (i : Fin (m + 1)) :
getBit i q₁ = getBit i q₂ ∧ getResiduum i q₁ = getResiduum i q₂ ↔ q₁ = q₂ :=
⟨and_imp.mpr (getResiduum_getBit_inj i), by rintro rfl ; exact ⟨rfl, rfl⟩⟩

lemma ne_iff_getBit_ne_or_getResiduum_ne (i : Fin (m + 1)) :
getBit i q₁ ≠ getBit i q₂ ∨ getResiduum i q₁ ≠ getResiduum i q₂ ↔ q₁ ≠ q₂  := by
rw [ne_eq q₁, ← getResiduum_getBit_inj_iff i, not_and_or]

lemma ne_of_getBit_ne (i : Fin (m + 1)) (h : getBit i q₁ ≠ getBit i q₂) :
q₁ ≠ q₂ := (ne_iff_getBit_ne_or_getResiduum_ne i).mp (Or.inl h)

lemma ne_of_getResiduum_ne (i : Fin (m + 1)) (h : getResiduum i q₁ ≠ getResiduum i q₂) :
q₁ ≠ q₂ := (ne_iff_getBit_ne_or_getResiduum_ne i).mp (Or.inr h)

end GetMerge

section Invariants

section bitInvariant

def bitInvariant (i : Fin (m + 1)) (f : Fin (2^(m + 1)) → Fin (2^(m + 1))) : Prop :=
∀ b bp, bp.fst = b → ((getBitResiduum i).conj f bp).fst = b

lemma bitInvariant_iff_getBit_apply_mergeBitResiduum_Bool_cases : bitInvariant i f ↔
(∀ p, getBit i (f (mergeBitResiduum i false p)) = false) ∧ (∀ p, getBit i (f (mergeBitResiduum i true p)) = true) :=
by simp only [bitInvariant, Equiv.conj_apply, getBitResiduum_symm_apply, getBitResiduum_apply, Prod.forall,
  Bool.forall_bool, forall_true_left, IsEmpty.forall_iff, forall_const, and_true, true_and]

lemma bitInvariant_iff_getBit_apply_eq_getBit : bitInvariant i f ↔ ∀ q, getBit i (f q) = getBit i q := by
simp_rw [bitInvariant_iff_getBit_apply_mergeBitResiduum_Bool_cases,
forall_iff_forall_mergeBitResiduum i, getBit_mergeBitResiduum]

lemma bitInvariant_of_getBit_apply_mergeBitResiduum_Bool_cases {f : Fin (2^(m + 1)) → Fin (2^(m + 1))}
(h₁ : ∀ p, getBit i (f (mergeBitResiduum i false p)) = false) (h₂ : ∀ p, getBit i (f (mergeBitResiduum i true p)) = true) :
bitInvariant i f := bitInvariant_iff_getBit_apply_mergeBitResiduum_Bool_cases.mpr ⟨h₁, h₂⟩

lemma bitInvariant_of_getBit_apply_eq_getBit {f : Fin (2^(m + 1)) → Fin (2^(m + 1))}
(h : ∀ q, getBit i (f q) = getBit i q) : bitInvariant i f := bitInvariant_iff_getBit_apply_eq_getBit.mpr h

lemma getBit_apply_mergeBitResiduum_false_eq_false_of_bitInvariant (h : bitInvariant i f) :
getBit i (f (mergeBitResiduum i false p)) = false := (bitInvariant_iff_getBit_apply_mergeBitResiduum_Bool_cases.mp h).1 _

lemma getBit_apply_mergeBitResiduum_true_eq_true_of_bitInvariant (h : bitInvariant i f) :
getBit i (f (mergeBitResiduum i true p)) = true := (bitInvariant_iff_getBit_apply_mergeBitResiduum_Bool_cases.mp h).2 _

lemma getBit_apply_mergeBitResiduum_Bool_eq_Bool_of_bitInvariant (h : bitInvariant i f) :
getBit i (f (mergeBitResiduum i b p)) = b := by
cases b ;
· exact getBit_apply_mergeBitResiduum_false_eq_false_of_bitInvariant h
· exact getBit_apply_mergeBitResiduum_true_eq_true_of_bitInvariant h

lemma getBit_apply_eq_getBit_of_bitInvariant (h : bitInvariant i f) : getBit i (f q) = getBit i q :=
bitInvariant_iff_getBit_apply_eq_getBit.mp h _

lemma symm_bitInvariant_of_bitInvariant {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvariant i π) :
bitInvariant i π.symm := by rw [bitInvariant_iff_getBit_apply_eq_getBit] at h ⊢
                            intros q ; rw [← h (π.symm q), π.apply_symm_apply]

lemma bitInvariant_of_symm_bitInvariant {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvariant i π.symm) :
bitInvariant i π := by rw [← π.symm_symm] ; exact symm_bitInvariant_of_bitInvariant h

lemma inv_bitInvariant_of_bitInvariant {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvariant i π) :
bitInvariant i (π⁻¹ : Equiv.Perm (Fin (2^(m + 1)))) := symm_bitInvariant_of_bitInvariant h

lemma bitInvariant_of_inv_bitInvariant {π : Equiv.Perm (Fin (2^(m + 1)))}
(h : bitInvariant i (π⁻¹ : Equiv.Perm (Fin (2^(m + 1))))) : bitInvariant i π :=
bitInvariant_of_symm_bitInvariant h

lemma id_bitInvariant : bitInvariant i id :=
bitInvariant_of_getBit_apply_eq_getBit (by simp only [id_eq, forall_const])

end bitInvariant

section residuumInvariant

def residuumInvariant (i : Fin (m + 1)) (f : Fin (2^(m + 1)) → Fin (2^(m + 1))) : Prop :=
∀ p bp, bp.snd = p → ((getBitResiduum i).conj f bp).snd = p

lemma residuumInvariant_iff_getResiduum_apply_mergeBitResiduum_Bool_cases : residuumInvariant i f ↔
(∀ p, getResiduum i (f (mergeBitResiduum i false p)) = p) ∧ (∀ p, getResiduum i (f (mergeBitResiduum i true p)) = p) :=
by simp only [residuumInvariant, Equiv.conj_apply, getBitResiduum_symm_apply, getBitResiduum_apply, Prod.forall,
  forall_eq, Bool.forall_bool, forall_and]

lemma residuumInvariant_iff_getResiduum_apply_eq_getResiduum :
residuumInvariant i f ↔ ∀ q, getResiduum i (f q) = getResiduum i q := by
simp_rw [residuumInvariant_iff_getResiduum_apply_mergeBitResiduum_Bool_cases,
forall_iff_forall_mergeBitResiduum i, getResiduum_mergeBitResiduum]

lemma residuumInvariant_of_getResiduum_apply_mergeBitResiduum_Bool_cases {f : Fin (2^(m + 1)) → Fin (2^(m + 1))}
(h₁ : ∀ p, getResiduum i (f (mergeBitResiduum i false p)) = p) (h₂ : ∀ p, getResiduum i (f (mergeBitResiduum i true p)) = p) :
residuumInvariant i f := residuumInvariant_iff_getResiduum_apply_mergeBitResiduum_Bool_cases.mpr ⟨h₁, h₂⟩

lemma residuumInvariant_of_getResiduum_apply_eq_getBit {f : Fin (2^(m + 1)) → Fin (2^(m + 1))}
(h : ∀ q, getResiduum i (f q) = getResiduum i q) : residuumInvariant i f :=
residuumInvariant_iff_getResiduum_apply_eq_getResiduum.mpr h

lemma getResiduum_apply_mergeBitResiduum_false_eq_false_of_residuumInvariant (h : residuumInvariant i f) :
getResiduum i (f (mergeBitResiduum i false p)) = p :=
(residuumInvariant_iff_getResiduum_apply_mergeBitResiduum_Bool_cases.mp h).1 _

lemma getResiduum_apply_mergeBitResiduum_true_eq_true_of_residuumInvariant (h : residuumInvariant i f) :
getResiduum i (f (mergeBitResiduum i true p)) = p :=
(residuumInvariant_iff_getResiduum_apply_mergeBitResiduum_Bool_cases.mp h).2 _

lemma getResiduum_apply_mergeBitResiduum_Bool_eq_Bool_of_residuumInvariant (h : residuumInvariant i f) :
getResiduum i (f (mergeBitResiduum i b p)) = p := by
cases b ;
· exact getResiduum_apply_mergeBitResiduum_false_eq_false_of_residuumInvariant h
· exact getResiduum_apply_mergeBitResiduum_true_eq_true_of_residuumInvariant h

lemma getResiduum_apply_eq_getResiduum_of_residuumInvariant (h : residuumInvariant i f) :
getResiduum i (f q) = getResiduum i q := residuumInvariant_iff_getResiduum_apply_eq_getResiduum.mp h _

lemma symm_residuumInvariant_of_residuumInvariant {π : Equiv.Perm (Fin (2^(m + 1)))} (h : residuumInvariant i π) :
residuumInvariant i π.symm := by  rw [residuumInvariant_iff_getResiduum_apply_eq_getResiduum] at h ⊢ ;
                                  intros q ; rw [← h (π.symm q), π.apply_symm_apply]

lemma residuumInvariant_of_symm_residuumInvariant {π : Equiv.Perm (Fin (2^(m + 1)))} (h : residuumInvariant i π.symm) :
residuumInvariant i π := by rw [← π.symm_symm] ; exact symm_residuumInvariant_of_residuumInvariant h

lemma id_residuumInvariant : residuumInvariant i id :=
residuumInvariant_of_getResiduum_apply_eq_getBit (by simp only [id_eq, forall_const])

end residuumInvariant

lemma id_of_bitInvariant_residuumInvariant (h₁ : bitInvariant i f) (h₂ : residuumInvariant i f) : f = id := by
ext q : 1 ; rw [id_eq]
exact getResiduum_getBit_inj i (getBit_apply_eq_getBit_of_bitInvariant h₁)
  (getResiduum_apply_eq_getResiduum_of_residuumInvariant h₂)

lemma id_iff_bitInvariant_residuumInvariant : (bitInvariant i f) ∧ (residuumInvariant i f) ↔ f = id :=
⟨fun h => id_of_bitInvariant_residuumInvariant h.1 h.2 , fun h => h ▸ ⟨id_bitInvariant, id_residuumInvariant⟩⟩

end Invariants

section FlipBit

def flipBit (i : Fin (m + 1)) : Equiv.Perm (Fin (2^(m + 1))) :=
(getBitResiduum i).symm.permCongr <| (finTwoEquiv.permCongr (finRotate _)).prodCongr (Equiv.refl _)

lemma flipBit_apply :
flipBit i q = mergeBitResiduum i (!(getBit i q)) (getResiduum i q) := by
simp_rw [flipBit, Equiv.permCongr_apply, Equiv.symm_symm, getBitResiduum_apply]
rcases (getBit i q).dichotomy with h | h <;> simp_rw [h] <;> rfl

lemma flipBit_mergeBitResiduum : flipBit i (mergeBitResiduum i b p) = mergeBitResiduum i (!b) p := by
rw [flipBit_apply, getBit_mergeBitResiduum, getResiduum_mergeBitResiduum]

@[simp]
lemma flipBit_mergeBitResiduum_false : flipBit i (mergeBitResiduum i false k) = mergeBitResiduum i true k :=
flipBit_mergeBitResiduum (b := false)

@[simp]
lemma flipBit_mergeBitResiduum_true : flipBit i (mergeBitResiduum i true k) = mergeBitResiduum i false k :=
flipBit_mergeBitResiduum (b := true)

@[simp]
lemma flipBit_flipBit : flipBit i (flipBit i q) = q := by
simp_rw [flipBit_apply, getBit_mergeBitResiduum,
  getResiduum_mergeBitResiduum, Bool.not_not, mergeBitResiduum_getBit_getResiduum]

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
simp_rw [flipBit_apply, getBit_mergeBitResiduum]

@[simp]
lemma getResiduum_flipBit : getResiduum i (flipBit i q) = getResiduum i q := by
rw [flipBit_apply, getResiduum_mergeBitResiduum]

lemma getBit_flipBit_ne {i : Fin (m + 1)} (h : i ≠ j) : getBit i (flipBit j q) = getBit i q := by
cases m
· exact (h (subsingleton_fin_one.elim i j)).elim
· rcases exists_getBit_eq_getBit_getResiduum_apply h with ⟨k, rfl, hk2⟩
  simp_rw [hk2, getResiduum_flipBit]

lemma flipBit_bitInvariant (h : i ≠ j) : bitInvariant i (flipBit j) :=
bitInvariant_of_getBit_apply_eq_getBit (fun _ => (getBit_flipBit_ne h) )

lemma flipBit_residuumInvariant : residuumInvariant i (flipBit i) :=
residuumInvariant_of_getResiduum_apply_eq_getBit (fun _ => getResiduum_flipBit)
end FlipBit

@[simp]
lemma flipBit_apply_ne_self : flipBit i q ≠ q := by
apply ne_of_getBit_ne i
rw [getBit_flipBit, ne_eq, Bool.not_not_eq]

lemma flipBit_mem_derangements {i : Fin (m + 1)} : (flipBit i) ∈ derangements (Fin (2^(m + 1))) :=
fun _ => flipBit_apply_ne_self

@[simp]
lemma flipBit_ne_one : flipBit i ≠ 1 := by
rw [ne_eq, Equiv.ext_iff, not_forall]
exact ⟨0, flipBit_apply_ne_self⟩

@[simp]
lemma one_ne_flipBit : 1 ≠ flipBit i := flipBit_ne_one.symm

section ResiduumCondFlip

def residuumCondFlipCore (i : Fin (m + 1)) (c : Fin (2^m) → Bool) : Fin (2^(m + 1)) → Fin (2^(m + 1)) :=
  fun q => bif c (getResiduum i q) then flipBit i q else q

lemma residuumCondFlipCore_residuumCondFlipCore : residuumCondFlipCore i c (residuumCondFlipCore i c q) = q := by
rcases (c (getResiduum i q)).dichotomy with h | h <;>
simp only [residuumCondFlipCore, h, cond_true, cond_false, getResiduum_flipBit, flipBit_flipBit]

def residuumCondFlip (i : Fin (m + 1)) (c : Fin (2^m) → Bool) : Equiv.Perm (Fin (2^(m + 1))) where
  toFun := residuumCondFlipCore i c
  invFun := residuumCondFlipCore i c
  left_inv _ := residuumCondFlipCore_residuumCondFlipCore
  right_inv _ := residuumCondFlipCore_residuumCondFlipCore

lemma residuumCondFlip_apply_def :
residuumCondFlip i c q = bif c (getResiduum i q) then flipBit i q else q := rfl

lemma residuumCondFlip_eq_mergeBitResiduum_xor_residuum : residuumCondFlip i c q =
mergeBitResiduum i (xor (c (getResiduum i q)) (getBit i q)) (getResiduum i q) := by
rcases (c (getResiduum i q)).dichotomy with h | h <;> rw [residuumCondFlip_apply_def, h]
· rw [cond_false, Bool.xor_false_left, mergeBitResiduum_getBit_getResiduum]
· rw [cond_true, Bool.true_xor, flipBit_apply]

@[simp]
lemma residuumCondFlip_residuumCondFlip : residuumCondFlip i c (residuumCondFlip i c q) = q :=
(residuumCondFlip i c).left_inv q

lemma residuumCondFlip_apply_comm :
residuumCondFlip i c (residuumCondFlip i d q) = residuumCondFlip i d (residuumCondFlip i c q) := by
simp_rw [residuumCondFlip_eq_mergeBitResiduum_xor_residuum, getResiduum_mergeBitResiduum,
  getBit_mergeBitResiduum, Bool.xor_left_comm]

lemma residuumCondFlip_comm :
(residuumCondFlip i c) * (residuumCondFlip i d) = (residuumCondFlip i d) * (residuumCondFlip i c) := by
ext ; simp ; rw [residuumCondFlip_apply_comm]

@[simp]
lemma residuumCondFlip_symm : (residuumCondFlip i c).symm = (residuumCondFlip i c) := rfl

@[simp]
lemma residuumCondFlip_inv : (residuumCondFlip i c)⁻¹ = residuumCondFlip i c := rfl

@[simp]
lemma residuumCondFlip_mul_self : (residuumCondFlip i c) * (residuumCondFlip i c) = 1 := by
ext ; simp_rw [Equiv.Perm.coe_mul, Function.comp_apply, residuumCondFlip_residuumCondFlip, Equiv.Perm.coe_one, id_eq]

lemma residuumCondFlip_flipBit_of_all_true : flipBit i = residuumCondFlip i (Function.const _ true) := by
ext ; rw [residuumCondFlip_apply_def] ; rfl

lemma residuumCondFlip_refl_of_all_false : Equiv.refl _ = residuumCondFlip i (Function.const _ false) :=
rfl

lemma residuumCondFlip_apply_comm_flipBit : residuumCondFlip i c (flipBit i q) = flipBit i (residuumCondFlip i c q) := by
rw [residuumCondFlip_flipBit_of_all_true, residuumCondFlip_apply_comm]

lemma residuumCondFlip_comm_flipBit :
(residuumCondFlip i c) * (flipBit i) = (flipBit i) * (residuumCondFlip i c) := by
rw [residuumCondFlip_flipBit_of_all_true, residuumCondFlip_comm]

lemma residuumCondFlip_apply_flipBit :
residuumCondFlip i c (flipBit i q) = bif c (getResiduum i q) then q else flipBit i q := by
rw [residuumCondFlip_apply_comm_flipBit]
rcases (c (getResiduum i q)).dichotomy with h | h <;> rw [residuumCondFlip_apply_def, h]
· simp_rw [cond_false]
· simp_rw [cond_true, flipBit_flipBit]

@[simp]
lemma getResiduum_residuumCondFlip : getResiduum i (residuumCondFlip i c q) = getResiduum i q := by
rcases (c (getResiduum i q)).dichotomy with h | h  <;> rw [residuumCondFlip_apply_def, h]
· rfl
· rw [cond_true, getResiduum_flipBit]

lemma getBit_residuumCondFlip : getBit i (residuumCondFlip i c q) =
bif c (getResiduum i q) then !(getBit i q) else getBit i q := by
rcases (c (getResiduum i q)).dichotomy with hc | hc <;> simp [residuumCondFlip_apply_def, hc]

lemma getBit_residuumCondFlip' : getBit i (residuumCondFlip i c q) =
xor (c (getResiduum i q)) (getBit i q) := by
rcases (c (getResiduum i q)).dichotomy with hc | hc <;> simp [residuumCondFlip_apply_def, hc]

lemma getBit_residuumCondFlip'' : getBit i (residuumCondFlip i c q) =
bif (getBit i q) then !(c (getResiduum i q)) else c (getResiduum i q) := by
rcases (getBit i q).dichotomy with h | h <;> simp [getBit_residuumCondFlip', h]

lemma residuumCondFlip_mergeBitResiduum : residuumCondFlip i c (mergeBitResiduum i b p) =
bif c p then mergeBitResiduum i (!b) p else mergeBitResiduum i b p := by
rw [residuumCondFlip_apply_def, getResiduum_mergeBitResiduum, flipBit_mergeBitResiduum]

lemma residuumCondFlip_mergeBitResiduum' : residuumCondFlip i c (mergeBitResiduum i b p) =
mergeBitResiduum i (xor (c p) b) p := by
rw [residuumCondFlip_eq_mergeBitResiduum_xor_residuum,getResiduum_mergeBitResiduum, getBit_mergeBitResiduum]

end ResiduumCondFlip

end BitResiduum

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
· simp_rw [cycleFull_of_not_fixed h₂] ; exact π.pow_mod_card_support_cycleOf_self_apply ..

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

lemma cycleMin_apply_eq_cycleMin : CycleMin π (π x) = CycleMin π x := by
by_cases h : Function.IsFixedPt π x
· rw [h]
· simp_rw [cycleMin_of_not_fixed h, cycleMin_of_not_fixed ((EmbeddingLike.apply_eq_iff_eq _).not.mpr h),
    Equiv.Perm.cycleOf_self_apply]

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
lemma xBXF_apply_flipBit_eq_flipBit_apply_xBXF_inv : XBackXForth π (flipBit 0 q) =
flipBit 0 ((XBackXForth π)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, flipBit_mul_xBXF_inv_eq_xBXF_mul_flipBit, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_inv_apply_flipBit_eq_flipBit_apply_xBXF : (XBackXForth π)⁻¹ (flipBit 0 q) =
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
lemma xBXF_pow_apply_flipBit_eq_flipBit_apply_xBXF_pow {k : ℕ} : ((XBackXForth π)^k) (flipBit 0 q) =
flipBit 0 (((XBackXForth π)^k)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, xBXF_pow_mul_flipBit_eq_flipBit_mul_xBXF_pow, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_pow_inv_apply_flipBit_eq_flipBit_apply_xBXF {k : ℕ} : ((XBackXForth π)^k)⁻¹ (flipBit 0 q)
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
lemma xBXF_zpow_apply_flipBit_eq_flipBit_apply_xBXF_zpow_inv {k : ℤ} :
((XBackXForth π)^k) (flipBit 0 q) = (flipBit 0) (((XBackXForth π)^k)⁻¹ q) := by
rw [← Equiv.Perm.mul_apply, xBXF_zpow_mul_flipBit_eq_flipBit_mul_xBXF_zpow_inv, Equiv.Perm.mul_apply]

@[simp]
lemma xBXR_zpow_inv_apply_flipBit_eq_flipBit_apply_xBXF_zpow {k : ℤ} :
(((XBackXForth π)^k)⁻¹) (flipBit 0 q) = flipBit 0 (((XBackXForth π)^k) q) := by
rw [← Equiv.Perm.mul_apply, ← flipBit_mul_xBXF_zpow_eq_xBXR_zpow_inv_mul_flipBit, Equiv.Perm.mul_apply]

@[simp]
lemma xBXF_apply_ne_flipBit_apply : (XBackXForth π) q ≠ (flipBit 0) q := by
simp_rw [xBXF_apply, ne_eq, ← Equiv.Perm.eq_inv_iff_eq (y := (flipBit 0) q)]
exact flipBit_apply_ne_self

@[simp]
lemma xBXF_pow_apply_ne_flipBit_apply {k : ℕ} : ((XBackXForth π)^k) q ≠ (flipBit 0) q := by
induction' k using Nat.twoStepInduction with k IH generalizing q
· rw [pow_zero]
  exact (flipBit_apply_ne_self).symm
· rw [pow_one]
  exact xBXF_apply_ne_flipBit_apply
· intros h
  rw [pow_succ'' (n := k.succ), pow_succ' (n := k), Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    ← Equiv.eq_symm_apply (x := flipBit 0 q), ← Equiv.Perm.inv_def,
    xBXF_inv_apply_flipBit_eq_flipBit_apply_xBXF] at h
  exact IH h

@[simp]
lemma xBXF_pow_inv_ne_flipBit {k : ℕ} : (((XBackXForth π)^k)⁻¹) q ≠ flipBit 0 q := by
simp_rw [ne_eq, Equiv.Perm.inv_def, Equiv.symm_apply_eq]
convert (xBXF_pow_apply_ne_flipBit_apply (q := flipBit 0 q)).symm
exact flipBit_flipBit.symm

@[simp]
lemma xBXF_zpow_ne_flipBit {k : ℤ} : ((XBackXForth π)^k) q ≠ flipBit 0 q := by
cases k <;> simp

-- Theorem 4.3 (b)
lemma xBXF_zpow_ne_flipBit_mul_xBXF_zpow {j k : ℤ}  :
((XBackXForth π)^j) q ≠ flipBit 0 (((XBackXForth π)^k) q) := by
rw [← sub_add_cancel j k, zpow_add, Equiv.Perm.mul_apply]
exact xBXF_zpow_ne_flipBit

lemma cycleFull_xBXF_disjoint_image_flipBit {x: Fin (2 ^ (m + 1))} : Disjoint (CycleFull (XBackXForth π) x)
((CycleFull (XBackXForth π) x).image (flipBit 0)) := by
simp_rw [Finset.disjoint_iff_ne, Finset.mem_image, mem_cycleFull_iff]
rintro _ ⟨j, rfl⟩ _ ⟨_, ⟨⟨_, rfl⟩, rfl⟩⟩
exact xBXF_zpow_ne_flipBit_mul_xBXF_zpow

-- Theorem 4.3 (c)
lemma cycleFull_xBXF_card_le_two_pow {x: Fin (2 ^ (m + 1))} :
  (CycleFull (XBackXForth π) x).card ≤ 2^m := by
refine' le_of_mul_le_mul_left _ (zero_lt_two)
rw [two_mul]; nth_rewrite 2 [← Finset.card_image_of_injective _ ((flipBit 0).injective)]
rw [← Nat.pow_succ', ← Finset.card_disjoint_union cycleFull_xBXF_disjoint_image_flipBit]
exact le_of_le_of_eq (Finset.card_le_of_subset (Finset.subset_univ _)) (Finset.card_fin _)

lemma bar : mergeBitResiduum 0 true p = mergeBitResiduum 0 false p + 1 := by
sorry

lemma foo (h : flipBit 0 q < flipBit 0 q') : q < q' ∨ ((q < flipBit 0 q) ∧ (q' = flipBit 0 q) ) := by
rcases mergeBitResiduum_surj 0 q with ⟨b, p, rfl⟩
rcases mergeBitResiduum_surj 0 q' with ⟨b', p', rfl⟩
cases b <;> cases b' <;> simp  at h ⊢
<;> simp [bar]

-- Theorem 4.4
lemma cycleMin_backForth :
CycleMin (XBackXForth π) (flipBit 0 q) = (flipBit 0) (CycleMin (XBackXForth π) q) := by
rcases cycleMin_exists_pow_apply (XBackXForth π) q with ⟨j, hjq₂⟩
refine' eq_of_le_of_not_lt _ (fun h => _)
· refine' cycleMin_le (XBackXForth π) (flipBit 0 q)  ⟨-j, _⟩
  simp_rw [zpow_neg, xBXR_zpow_inv_apply_flipBit_eq_flipBit_apply_xBXF_zpow, hjq₂]
· rcases cycleMin_exists_pow_apply (XBackXForth π) (flipBit 0 q) with ⟨k, hkq₂⟩
  rw [←hkq₂, ← hjq₂, xBXF_zpow_apply_flipBit_eq_flipBit_apply_xBXF_zpow_inv] at h
  rcases foo h with h | ⟨_, h2⟩
  · apply (cycleMin_le (XBackXForth π) q ⟨-k, rfl⟩).not_lt
    rw [zpow_neg, ← hjq₂]
    exact h
  · exact xBXF_zpow_ne_flipBit_mul_xBXF_zpow ((zpow_neg (XBackXForth π) k).symm ▸ h2)

end Reimplementation



-- DEF

lemma sumCongr_isLeft_invariant {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4}
(ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : ∀ x : α₁ ⊕ β₁, ((Equiv.sumCongr ea eb) x).isLeft = x.isLeft :=
by rintro (x | x) <;> rfl

lemma isLeft_invariant_iff_symm_isLeft_invariant {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂) :
(∀ x, (e x).isLeft = x.isLeft) ↔ (∀ x, (e.symm x).isLeft = x.isLeft) := by
refine ⟨fun h => ?_, fun h => ?_⟩
· intro x ; specialize h (e.symm x) ; rw [Equiv.apply_symm_apply] at h ; rw [h]
· intro x ; specialize h (e x) ; rw [Equiv.symm_apply_apply] at h  ; rw [h]

lemma isLeft_invariant_iff {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂) :
(∀ x, (e x).isLeft = x.isLeft) ↔
((∀ (a : α₁), ∃ y, e (Sum.inl a) = Sum.inl y) ∧ (∀ (b : β₁), ∃ y, e (Sum.inr b) = Sum.inr y)) := by
simp [Sum.isLeft_iff, Sum.isRight_iff]

lemma equiv_isLeft_invariant_iff' {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂) :
(∀ x, (e x).isLeft = x.isLeft) ↔
((∀ (a : α₁), ∃ y, e (Sum.inl a) = Sum.inl y) ∧ (∀ (b : β₁), ∃ y, e (Sum.inr b) = Sum.inr y) ∧
(∀ (a : α₂), ∃ y, e.symm (Sum.inl a) = Sum.inl y) ∧ (∀ (b : β₂), ∃ y, e.symm (Sum.inr b) = Sum.inr y)) := by
rw [← isLeft_invariant_iff, ← and_assoc, ← isLeft_invariant_iff, isLeft_invariant_iff_symm_isLeft_invariant, and_self]

def equivSumInvariantLeft {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂)
(he₁ : (∀ (a : α₁), ∃ y, e (Sum.inl a) = Sum.inl y))
(he₂ : (∀ (a : α₂), ∃ y, e.symm (Sum.inl a) = Sum.inl y)) : (α₁ ≃ α₂) where
  toFun a₁ := (e (Sum.inl a₁)).getLeft.get (by
    rcases he₁ a₁ with ⟨a₂, ha₂⟩ ; rw [ha₂] ; rfl )
  invFun a₂ := (e.symm (Sum.inl a₂)).getLeft.get (by
    rcases he₂ a₂ with ⟨a₁, ha₁⟩ ; rw [ha₁] ; rfl
  )
  left_inv a₁ := (by
    rcases he₁ a₁ with ⟨a₂, ha₂⟩ ; rcases he₂ a₂ with ⟨na₁, hna₁⟩ ;
    simp_rw [ha₂, Sum.getLeft_inl, Option.get_some, hna₁]
    simp_rw [← ha₂, Equiv.symm_apply_apply, Sum.inl.injEq] at hna₁ ; exact hna₁.symm
  )
  right_inv a₂ := (by
    rcases he₂ a₂ with ⟨a₁, ha₁⟩ ; rcases he₁ a₁ with ⟨na₂, hna₂⟩ ;
    simp_rw [ha₁, Sum.getLeft_inl, Option.get_some, hna₂]
    simp_rw [← ha₁, Equiv.apply_symm_apply, Sum.inl.injEq] at hna₂ ; exact hna₂.symm
  )

def equivSumInvariantRight {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂)
(he₁ : (∀ (b : β₁), ∃ y, e (Sum.inr b) = Sum.inr y))
(he₂ : (∀ (b : β₂), ∃ y, e.symm (Sum.inr b) = Sum.inr y)) : (β₁ ≃ β₂) where
  toFun b₁ := (e (Sum.inr b₁)).getRight.get (by
    rcases he₁ b₁ with ⟨b₂, hb₂⟩ ; rw [hb₂] ; rfl )
  invFun b₂ := (e.symm (Sum.inr b₂)).getRight.get (by
    rcases he₂ b₂ with ⟨b₁, hb₁⟩ ; rw [hb₁] ; rfl)
  left_inv b₁ := (by
    rcases he₁ b₁ with ⟨b₂, hb₂⟩ ; rcases he₂ b₂ with ⟨nb₁, hnb₁⟩ ;
    simp_rw [hb₂, Sum.getRight_inr, Option.get_some, hnb₁]
    simp_rw [← hb₂, Equiv.symm_apply_apply, Sum.inr.injEq] at hnb₁ ; exact hnb₁.symm)
  right_inv b₂ := (by
    rcases he₂ b₂ with ⟨b₁, hb₁⟩ ; rcases he₁ b₁ with ⟨nb₂, hnb₂⟩ ;
    simp_rw [hb₁, Sum.getRight_inr, Option.get_some, hnb₂]
    simp_rw [← hb₁, Equiv.apply_symm_apply, Sum.inr.injEq] at hnb₂ ; exact hnb₂.symm)

def equivSumInvariant {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂)
(h : ∀ x, (e x).isLeft = x.isLeft) : (α₁ ≃ α₂) × (β₁ ≃ β₂) :=
(equivSumInvariantLeft e ((equiv_isLeft_invariant_iff' e).mp h).1 ((equiv_isLeft_invariant_iff' e).mp h).2.2.1,
equivSumInvariantRight e ((equiv_isLeft_invariant_iff' e).mp h).2.1 ((equiv_isLeft_invariant_iff' e).mp h).2.2.2)

def equivSubInvariantSubtype : {e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ // ∀ x, (e x).isLeft = x.isLeft} ≃
(α₁ ≃ α₂) × (β₁ ≃ β₂) where
  toFun := fun ⟨e, he⟩ => equivSumInvariant e he
  invFun := fun ⟨ea, eb⟩ => ⟨Equiv.sumCongr ea eb, sumCongr_isLeft_invariant ea eb⟩
  left_inv := fun ⟨e, he⟩ => (by
    ext x ;
    simp only [equivSumInvariant, equivSumInvariantLeft, equivSumInvariantRight, Equiv.sumCongr_apply, Equiv.coe_fn_mk]
    rcases x with (a₁ | b₁) <;> rw [equiv_isLeft_invariant_iff'] at he
    · rcases he.1 a₁ with ⟨a₂, ha₂⟩ ;
      simp only [Sum.map_inl, ha₂, Sum.getLeft_inl, Option.get_some]
    · rcases he.2.1 b₁ with ⟨b₂, hb₂⟩ ;
      simp only [Sum.map_inr, hb₂, Sum.getRight_inr, Option.get_some])
  right_inv := fun ⟨ea, eb⟩ => (by
    ext x ;
    · simp only [equivSumInvariant, equivSumInvariantLeft, Equiv.sumCongr_apply, Sum.map_inl, Sum.getLeft_inl,
      Option.get_some, Equiv.sumCongr_symm, equivSumInvariantRight, Sum.map_inr, Sum.getRight_inr, Equiv.coe_fn_mk]
    · simp only [equivSumInvariant, equivSumInvariantLeft, Equiv.sumCongr_apply, Sum.map_inl, Sum.getLeft_inl,
      Option.get_some, Equiv.sumCongr_symm, equivSumInvariantRight, Sum.map_inr, Sum.getRight_inr, Equiv.coe_fn_mk]
  )


lemma foo {i : Fin (m + 1)} : ∀ (a : Equiv.Perm (Fin (2 ^ (m + 1)))),
  bitInvariant i a ↔ ∀ (x : Fin (2 ^ m) ⊕ Fin (2 ^ m)),
      Sum.isLeft (((Equiv.permCongr ((getBitResiduum i).trans (Equiv.boolProdEquivSum (Fin (2 ^ m))))) a) x) =
        Sum.isLeft x := by (
          simp_rw [isLeft_invariant_iff] ; intros π
          refine ⟨fun H => ⟨fun p => ?_, fun p => ?_⟩, fun ⟨H1, H2⟩ => ?_⟩
          · use (getResiduum i (π (mergeBitResiduum i false p)))
            simp only [Equiv.permCongr_apply, Equiv.symm_trans_apply, Equiv.boolProdEquivSum_symm_apply, Sum.elim_inl,
              getBitResiduum_symm_apply, Equiv.trans_apply, getBitResiduum_apply,
              getBit_apply_mergeBitResiduum_false_eq_false_of_bitInvariant H, Equiv.boolProdEquivSum_apply, cond_false]
          · use (getResiduum i (π (mergeBitResiduum i true p)))
            simp only [Equiv.permCongr_apply, Equiv.symm_trans_apply, Equiv.boolProdEquivSum_symm_apply, Sum.elim_inr,
              getBitResiduum_symm_apply, Equiv.trans_apply, getBitResiduum_apply,
              getBit_apply_mergeBitResiduum_true_eq_true_of_bitInvariant H, Equiv.boolProdEquivSum_apply, cond_true]
          · rw [bitInvariant_iff_getBit_apply_eq_getBit, forall_iff_forall_mergeBitResiduum i]
            refine ⟨fun p => ?_, fun p => ?_⟩
            · specialize H1 p ; simp only [Equiv.permCongr_apply, Equiv.symm_trans_apply,
              Equiv.boolProdEquivSum_symm_apply, Sum.elim_inl, getBitResiduum_symm_apply, Equiv.trans_apply,
              getBitResiduum_apply, Equiv.boolProdEquivSum_apply] at H1
              rcases (getBit i (π (mergeBitResiduum i false p))).dichotomy with h | h
              · rw [h, getBit_mergeBitResiduum]
              · rw [h] at H1 ; simp only [cond_true, exists_false] at H1
            · specialize H2 p ; simp only [Equiv.permCongr_apply, Equiv.symm_trans_apply,
              Equiv.boolProdEquivSum_symm_apply, Sum.elim_inr, getBitResiduum_symm_apply, Equiv.trans_apply,
              getBitResiduum_apply, Equiv.boolProdEquivSum_apply] at H2
              rcases (getBit i (π (mergeBitResiduum i true p))).dichotomy with h | h
              · rw [h] at H2 ; simp only [cond_false, exists_false] at H2
              · rw [h, getBit_mergeBitResiduum])

example {i : Fin (m + 1)} : Equiv.Perm (Fin (2^(m + 1))) ≃
((Fin (2^m) ⊕ Fin (2^m)) ≃ (Fin (2^m) ⊕ Fin (2^m))) :=
Equiv.permCongr ((getBitResiduum i).trans (Equiv.boolProdEquivSum _))

def foobar : {π : Equiv.Perm (Fin (2^(m + 1))) // bitInvariant i π } ≃
{e : Equiv.Perm (Fin (2^m) ⊕ Fin (2^m))  // ∀ x, (e x).isLeft = x.isLeft} :=
Equiv.subtypeEquiv (Equiv.permCongr ((getBitResiduum i).trans (Equiv.boolProdEquivSum _))) foo

def foobarbar : {π : Equiv.Perm (Fin (2^(m + 1))) // bitInvariant i π } ≃ Equiv.Perm (Fin (2^m)) × Equiv.Perm (Fin (2^m)) :=
foobar.trans equivSubInvariantSubtype


def myfoo (i : Fin (m + 1))  : Equiv.Perm (Fin (2^m)) × Equiv.Perm (Fin (2^m)) → {π : Equiv.Perm (Fin (2^(m + 1))) // bitInvariant i π } :=
foobarbar.symm

def evenPerm {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvariant 0 π) := (foobarbar ⟨π, h⟩).1
def oddPerm {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvariant 0 π) := (foobarbar ⟨π, h⟩).2

def toBitInvariant (i : Fin (m + 1)) {π : Equiv.Perm (Fin (2^m))} : Equiv.Perm (Fin (2^(m + 1))) :=
(getBitResiduum i).symm.permCongr (Equiv.prodCongr (Equiv.refl _) π)

--Equiv.boolProdEquivSum


def ControlBitsLayer (m : ℕ) := Fin (2^m) → Bool
def ControlBits (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

def inductiveControl : ControlBits (m + 1) ≃ (ControlBitsLayer (m + 1) × ControlBits m × ControlBits m × ControlBitsLayer (m + 1)) :=
((Equiv.piFinSucc _ _).trans ((Equiv.refl _).prodCongr (((finCongr (mul_add _ _ _)).arrowCongr (Equiv.refl _)).trans
((Equiv.piFinSuccAboveEquiv (fun _ => _) (Fin.last _)).trans (Equiv.prodComm _ _))))).trans (Equiv.prodCongr (Equiv.refl _)
(Equiv.trans (Equiv.prodCongr ((((Equiv.refl _).arrowCongr (((((getBitResiduum 0).trans (Equiv.boolProdEquivSum _)).arrowCongr
  (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)))).trans
  (Equiv.arrowProdEquivProdArrow _ _ _))) (Equiv.refl _)) ((Equiv.prodAssoc _ _ _))))


namespace ControlBits

def ControlBitsToPerm (cb : ControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => residuumCondFlip (foldFin k) (cb k))).prod

def ControlBitsToPerm' (cb : ControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
  match m with
  | 0 => residuumCondFlip 0 (cb 0)
  | _ + 1 => (residuumCondFlip 0 (cb 0)) *
    (myfoo 0 (ControlBitsToPerm' ((inductiveControl cb).2.1), ControlBitsToPerm' (inductiveControl cb).2.2.1)).1 *
            (residuumCondFlip 0 (cb (Fin.last _)))

end ControlBits

def XIf (c : Fin (2^m) → Bool) : Equiv.Perm (Fin (2^(m + 1))) := residuumCondFlip 0 c
def FirstControlBits (π) (p : Fin (2^m)) := getBit 0 (CycleMin (XBackXForth π) (mergeBitResiduum 0 false p))
def FirstControl (π : Equiv.Perm (Fin (2^(m + 1)))) := XIf (FirstControlBits π)

def LastControlBits (π) (p : Fin (2^m)) := getBit 0 (((FirstControl π) * π) (mergeBitResiduum 0 false p))

def LastControl (π : Equiv.Perm (Fin (2^(m + 1)))) := XIf (LastControlBits π)

def MiddlePerm (π : Equiv.Perm (Fin (2^(m + 1)))) := (FirstControl π) * π * (LastControl π)

def flmDecomp (π : Equiv.Perm (Fin (2^((m + 1) )))) := (FirstControlBits π, MiddlePerm π, LastControlBits π)

lemma MiddlePerm_invar (π : Equiv.Perm (Fin (2^((m + 1) + 1)))) :
bitInvariant 0 (MiddlePerm π) := sorry


def PermToControlBits (π : Equiv.Perm (Fin (2^(m + 1)))) : ControlBits m :=
  match m with
  | 0 => ![LastControlBits π]
  | _ + 1 => inductiveControl.symm (FirstControlBits π,
                                    PermToControlBits (evenPerm (MiddlePerm_invar π)),
                                    PermToControlBits (oddPerm (MiddlePerm_invar π)),
                                    LastControlBits π)

end ControlBits


-- Testing

def myControlBits1 : ControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def myControlBits2 : ControlBits 1 := ![![false, true], ![false, true], ![true, true]]
def myControlBits3 : ControlBits 0 := ![![true]]
def myControlBits4 : ControlBits 0 := ![![false]]

#eval [0, 1, 2, 3].map (ControlBits.ControlBitsToPerm (myControlBits1))
#eval [0, 1, 2, 3].map (residuumCondFlip 0 (myControlBits2 0))
#eval [0, 1, 2, 3].map (myfoo 0 (residuumCondFlip 0 (myControlBits4 0), residuumCondFlip 0 (myControlBits3 0))).1
#eval [0, 1, 2, 3].map (residuumCondFlip 0 (myControlBits2 2))
#eval [0, 1, 2, 3].map (((residuumCondFlip 0 (myControlBits2 0))) *
  ((myfoo 0 (residuumCondFlip 0 (myControlBits4 0), residuumCondFlip 0 (myControlBits3 0))).1) * ((residuumCondFlip 0 (myControlBits2 2))))

#eval PermToControlBits (ControlBits.ControlBitsToPerm' (myControlBits1))

#eval PermToControlBits (ControlBits.ControlBitsToPerm (myControlBits1))