import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.GroupTheory.Perm.Cycle.Basic

section BitResiduum

section GetMerge

def getBitResiduum (i : Fin (m + 1)) : Fin (2^(m + 1)) ≃ Bool × Fin (2^m) :=
(finFunctionFinEquiv.symm.trans ((Equiv.refl _).arrowCongr finTwoEquiv)).trans
<| (Equiv.piFinSuccAboveEquiv _ i).trans
<| (Equiv.refl _).prodCongr
<| ((Equiv.refl _).arrowCongr finTwoEquiv.symm).trans finFunctionFinEquiv

def getBit (i : Fin (m + 1)) : Fin (2^(m + 1)) → Bool := Prod.fst ∘ (getBitResiduum i)

def getResiduum (i : Fin (m + 1)) : Fin (2^(m + 1)) → Fin (2^m) := Prod.snd ∘ (getBitResiduum i)

def mergeBitResiduum (i : Fin (m + 1)) : Bool → Fin (2^m) → Fin (2^(m + 1)) := Function.curry (getBitResiduum i).symm

@[simp]
lemma getBitResiduum_apply : getBitResiduum i q = (getBit i q, getResiduum i q) := rfl

@[simp]
lemma getBitResiduum_symm_apply : (getBitResiduum i).symm bp = mergeBitResiduum i bp.fst bp.snd := rfl

lemma getBit_def : getBit i q = finTwoEquiv (finFunctionFinEquiv.symm q i) := rfl

lemma getResiduum_def : getResiduum i q =
(finFunctionFinEquiv <| (finTwoEquiv.symm) ∘ (fun j => finTwoEquiv (finFunctionFinEquiv.symm q (Fin.succAbove i j)))) := rfl

lemma mergeBitResiduum_def : mergeBitResiduum i b p =
(finFunctionFinEquiv <| (finTwoEquiv.symm) ∘ (Fin.insertNth i b <| finTwoEquiv ∘ (finFunctionFinEquiv.symm p))) := rfl

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
ext ; simp_rw [Function.comp_apply, getResiduum_def, getBit_def, Equiv.symm_apply_apply, Function.comp_apply, Equiv.symm_apply_apply]

lemma getBit_succAbove_eq_getBit_getResiduum_apply : getBit (j.succAbove i) q = getBit i (getResiduum j q) := by
simp_rw [getResiduum_def, getBit_def, Equiv.symm_apply_apply, Function.comp_apply, Equiv.symm_apply_apply]

lemma exists_getBit_eq_getBit_getResiduum {j : Fin (m + 2)} (h : i ≠ j) : ∃ k, j.succAbove k = i ∧ getBit i = getBit k ∘ getResiduum j := by
rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
use k ; exact ⟨rfl, getBit_succAbove_eq_getBit_getResiduum⟩

lemma exists_getBit_eq_getBit_getResiduum_apply {j : Fin (m + 2)} (h : i ≠ j) : ∃ k, j.succAbove k = i ∧ ∀ q, getBit i q = getBit k (getResiduum j q) := by
rcases Fin.exists_succAbove_eq h with ⟨k, rfl⟩
use k ; exact ⟨rfl, fun _ => getBit_succAbove_eq_getBit_getResiduum_apply⟩

lemma getBit_eq_getBit_succAbove_mergeBitResiduum (j : Fin (m + 2)) : getBit i p = getBit (j.succAbove i) (mergeBitResiduum j b p) := by
simp [getBit_succAbove_eq_getBit_getResiduum, getResiduum_mergeBitResiduum]

@[simp]
lemma mergeBitResiduum_getBit_getResiduum : mergeBitResiduum i (getBit i q) (getResiduum i q) = q := by
simp_rw [getResiduum, mergeBitResiduum, getBit, Function.comp_apply, Function.curry_apply, Prod.mk.eta, Equiv.symm_apply_apply]

lemma getBit_inv (i : Fin (m + 1)) (h : getBit i q = b) : mergeBitResiduum i b (getResiduum i q) = q := by
convert mergeBitResiduum_getBit_getResiduum ; exact h.symm

lemma getResiduum_inv (i : Fin (m + 1)) (h : getResiduum i q = p) : mergeBitResiduum i (getBit i q) p = q := by
convert mergeBitResiduum_getBit_getResiduum ; exact h.symm

lemma mergeBitResiduum_Bool_inj (i : Fin (m + 1)) (h : mergeBitResiduum i b₁ p₁ = mergeBitResiduum i b₂ p₂) : b₁ = b₂ := by
  have h₂ := (congrArg (getBit i) h) ; simp only [getBit_mergeBitResiduum] at h₂ ; exact h₂

lemma mergeBitResiduum_Fin_inj (i : Fin (m + 1)) (h : mergeBitResiduum i b₁ p₁ = mergeBitResiduum i b₂ p₂) : p₁ = p₂ := by
  have h₂ := (congrArg (getResiduum i) h) ; simp_rw [getResiduum_mergeBitResiduum] at h₂ ; exact h₂

lemma mergeBitResiduum_inj (i : Fin (m + 1)) (h : mergeBitResiduum i b₁ p₁ = mergeBitResiduum i b₂ p₂) : b₁ = b₂ ∧ p₁ = p₂ :=
⟨mergeBitResiduum_Bool_inj i h, mergeBitResiduum_Fin_inj i h⟩

lemma mergeBitResiduum_inj_iff (i : Fin (m + 1)) : mergeBitResiduum i b₁ p₁ = mergeBitResiduum i b₂ p₂ ↔ b₁ = b₂ ∧ p₁ = p₂ :=
⟨mergeBitResiduum_inj i, by rintro ⟨rfl, rfl⟩ ; rfl⟩

lemma mergeBitResiduum_surj (i : Fin (m + 1)) (q : Fin (2^(m + 1))): ∃ b p, mergeBitResiduum i b p = q :=
⟨getBit i q, getResiduum i q, mergeBitResiduum_getBit_getResiduum⟩

lemma forall_iff_forall_mergeBitResiduum (i : Fin (m + 1)) {pr : Fin (2^(m + 1)) → Prop} :
(∀ (q : Fin (2^(m + 1))), pr q) ↔ (∀ p, pr (mergeBitResiduum i false p)) ∧ (∀ p, pr (mergeBitResiduum i true p)) :=
⟨ fun h => ⟨fun _ => h _, fun _ => h _⟩,
  fun h q => by rcases mergeBitResiduum_surj i q with ⟨(h|h), p, rfl⟩
                · exact h.1 _
                · exact h.2 _⟩

lemma getBit_surj (i : Fin (m + 1)) : ∃ p, mergeBitResiduum i (getBit i q) p = q :=
⟨getResiduum i q, mergeBitResiduum_getBit_getResiduum⟩

lemma getResiduum_surj (i : Fin (m + 1)) : ∃ b, mergeBitResiduum i b (getResiduum i q) = q :=
⟨getBit i q, mergeBitResiduum_getBit_getResiduum⟩

lemma getResiduum_getBit_inj (i : Fin (m + 1)) (h₁ : getBit i q₁ = getBit i q₂) (h₂ : getResiduum i q₁ = getResiduum i q₂) :
q₁ = q₂ := by rw [← mergeBitResiduum_getBit_getResiduum (i := i) (q := q₁), h₁, h₂, mergeBitResiduum_getBit_getResiduum]

lemma getResiduum_getBit_inj_iff (i : Fin (m + 1)) :
getBit i q₁ = getBit i q₂ ∧ getResiduum i q₁ = getResiduum i q₂ ↔ q₁ = q₂ :=
⟨and_imp.mpr (getResiduum_getBit_inj i), by rintro rfl ; exact ⟨rfl, rfl⟩⟩

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

lemma flipBit_eq_mergeBitResiduum_not_getBit_getResiduum : flipBit i q = mergeBitResiduum i (!(getBit i q)) (getResiduum i q) := by
simp_rw [flipBit, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.trans_apply, getBitResiduum_apply]
rcases (getBit i q).dichotomy with h | h <;> simp_rw [h] <;> rfl

lemma flipBit_mergeBitResiduum : flipBit i (mergeBitResiduum i b p) = mergeBitResiduum i (!b) p := by
rw [flipBit_eq_mergeBitResiduum_not_getBit_getResiduum, getBit_mergeBitResiduum, getResiduum_mergeBitResiduum]

@[simp]
lemma flipBit_mergeBitResiduum_false : flipBit i (mergeBitResiduum i false k) = mergeBitResiduum i true k := flipBit_mergeBitResiduum (b := false)

@[simp]
lemma flipBit_mergeBitResiduum_true : flipBit i (mergeBitResiduum i true k) = mergeBitResiduum i false k := flipBit_mergeBitResiduum (b := true)

@[simp]
lemma flipBit_flipBit : flipBit i (flipBit i q) = q := by
simp_rw [flipBit_eq_mergeBitResiduum_not_getBit_getResiduum, getBit_mergeBitResiduum, getResiduum_mergeBitResiduum, Bool.not_not, mergeBitResiduum_getBit_getResiduum]

@[simp]
lemma getBit_flipBit : getBit i (flipBit i q) = !(getBit i q) := by
simp_rw [flipBit_eq_mergeBitResiduum_not_getBit_getResiduum, getBit_mergeBitResiduum]

@[simp]
lemma getResiduum_flipBit : getResiduum i (flipBit i q) = getResiduum i q := by
rw [flipBit_eq_mergeBitResiduum_not_getBit_getResiduum, getResiduum_mergeBitResiduum]

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

section ResiduumCondFlip

def residuumCondFlipCore (c : Fin (2^m) → Bool) (i : Fin (m + 1)) : Fin (2^(m + 1)) → Fin (2^(m + 1)) :=
  fun q => bif c (getResiduum i q) then flipBit i q else q

lemma residuumCondFlipCore_false (h : c (getResiduum i q) = false) : residuumCondFlipCore c i q = q := by
unfold residuumCondFlipCore ; simp only [h, cond_false]

lemma residuumCondFlipCore_true (h : c (getResiduum i q) = true) : residuumCondFlipCore c i q = flipBit i q := by
unfold residuumCondFlipCore ; simp only [h, cond_true]

lemma residuumCondFlipCore_flipBit : residuumCondFlipCore c i (flipBit i q) =
  bif c (getResiduum i q) then q else flipBit i q := by
unfold residuumCondFlipCore ; simp only [getResiduum_flipBit, flipBit_flipBit]

lemma residuumCondFlipCore_residuumCondFlipCore : residuumCondFlipCore c i (residuumCondFlipCore c i q) = q := by
rcases (c (getResiduum i q)).dichotomy with h | h
· simp only [h, residuumCondFlipCore_false]
· simp only [h, residuumCondFlipCore_true, getResiduum_flipBit, flipBit_flipBit]

def residuumCondFlip (c : Fin (2^m) → Bool) (i : Fin (m + 1)) : Equiv.Perm (Fin (2^(m + 1))) where
  toFun := residuumCondFlipCore c i
  invFun := residuumCondFlipCore c i
  left_inv _ := residuumCondFlipCore_residuumCondFlipCore
  right_inv _ := residuumCondFlipCore_residuumCondFlipCore

lemma residuumCondFlip_apply_def : residuumCondFlip c i q = bif c (getResiduum i q) then flipBit i q else q := rfl

@[simp]
lemma residuumCondFlip_apply_def_false (h : c (getResiduum i q) = false) :
residuumCondFlip c i q = q := residuumCondFlipCore_false h

@[simp]
lemma residuumCondFlip_apply_def_true (h : c (getResiduum i q) = true) :
residuumCondFlip c i q = flipBit i q := residuumCondFlipCore_true h

@[simp]
lemma residuumCondFlip_refl_of_all_false (h : ∀ p, c p = false) : residuumCondFlip c i = Equiv.refl _ :=
Equiv.ext fun _ =>  residuumCondFlip_apply_def_false (h _)

@[simp]
lemma residuumCondFlip_refl_of_all_true (h : ∀ p, c p = true) : residuumCondFlip c i = flipBit i :=
Equiv.ext fun _ => residuumCondFlip_apply_def_true (h _)

lemma residuumCondFlip_apply_flipBit :
residuumCondFlip c i (flipBit i q) = bif c (getResiduum i q) then q else flipBit i q := residuumCondFlipCore_flipBit

@[simp]
lemma residuumCondFlip_apply_flipBit_false (h : c (getResiduum i q) = false) : residuumCondFlip c i (flipBit i q) = (flipBit i q) :=
by simp only [getResiduum_flipBit, h, residuumCondFlip_apply_def_false]

@[simp]
lemma residuumCondFlip_apply_flipBit_true (h : c (getResiduum i q) = true) : residuumCondFlip c i (flipBit i q) = q :=
by simp only [getResiduum_flipBit, h, residuumCondFlip_apply_def_true, flipBit_flipBit]

@[simp]
lemma residuumCondFlip_residuumCondFlip :
(residuumCondFlip c i).trans (residuumCondFlip c i) = Equiv.refl _ :=
  Equiv.ext fun _ => residuumCondFlipCore_residuumCondFlipCore

@[simp]
lemma symm_residuumCondFlip : (residuumCondFlip c i).symm = (residuumCondFlip c i) := rfl

@[simp]
lemma residuumCondFlip_inv : (residuumCondFlip c i)⁻¹ = residuumCondFlip c i := rfl

@[simp]
lemma residuumCondFlip_mul_self : (residuumCondFlip c i) * (residuumCondFlip c i) = 1 := residuumCondFlip_residuumCondFlip

lemma getResiduum_residuumCondFlip : getResiduum i (residuumCondFlip c i q) = getResiduum i q := by
rcases (c (getResiduum i q)).dichotomy with h | h
· simp only [h, residuumCondFlip_apply_def_false]
· simp only [h, residuumCondFlip_apply_def_true, getResiduum_flipBit]

lemma getBit_residuumCondFlip : getBit i (residuumCondFlip c i q) =
bif c (getResiduum i q) then !(getBit i q) else getBit i q := by
rcases (c (getResiduum i q)).dichotomy with h | h
· simp only [h, residuumCondFlip_apply_def_false, cond_false]
· simp only [h, residuumCondFlip_apply_def_true, getBit_flipBit, cond_true]

@[simp]
lemma getBit_residuumCondFlip_false (h : c (getResiduum i q) = false) :
getBit i (residuumCondFlip c i q) = getBit i q := by rw [getBit_residuumCondFlip, h, cond_false]

@[simp]
lemma getBit_residuumCondFlip_true (h : c (getResiduum i q) = true) :
getBit i (residuumCondFlip c i q) = !(getBit i q) := by rw [getBit_residuumCondFlip, h, cond_true]

lemma residuumCondFlip_mergeBitResiduum :
residuumCondFlip c i (mergeBitResiduum i b p) = bif c p then mergeBitResiduum i (!b) p else mergeBitResiduum i b p := by
rw [residuumCondFlip_apply_def, getResiduum_mergeBitResiduum, flipBit_mergeBitResiduum]

@[simp]
lemma residuumCondFlip_mergeBitResiduum_false (h : c p = false) : residuumCondFlip c i (mergeBitResiduum i b p) = mergeBitResiduum i b p := by
simp only [getResiduum_mergeBitResiduum, h, residuumCondFlip_apply_def_false]

@[simp]
lemma residuumCondFlip_mergeBitResiduum_true (h : c p = true) : residuumCondFlip c i (mergeBitResiduum i b p) = mergeBitResiduum i (!b) p := by
simp only [getResiduum_mergeBitResiduum, h, residuumCondFlip_apply_def_true, flipBit_mergeBitResiduum]

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

def ControlBitsLayer (m : ℕ) := Fin (2^m) → Bool
def ControlBits (m : ℕ) := Fin (2*m + 1) → ControlBitsLayer m

namespace ControlBits

def controlBitsPerm (cb : ControlBits m) : Equiv.Perm (Fin (2^(m + 1))) :=
(List.ofFn (fun k => residuumCondFlip (cb k) (foldFin k))).prod

end ControlBits

def myControlBits1 : ControlBits 1 := ![![true, false], ![true, false], ![false, false]]
def myControlBits2 : ControlBits 1 := ![![true, false], ![true, true], ![true, false]]
def myControlBits3 : ControlBits 0 := ![![true]]
def myControlBits4 : ControlBits 0 := ![![false]]

#eval [0, 1, 2, 3].map (ControlBits.controlBitsPerm ((fun (i : Fin (2*100 + 1)) (p : Fin (2^100)) => false) : ControlBits 100))

-- DEF

def firstEquiv {α : Type u} (a : α) (β : Type v) : { ab : α × β // ab.fst = a } ≃ β where
  toFun ab := ab.1.2
  invFun b := ⟨(_, b), rfl⟩
  left_inv ab := by rcases ab with ⟨_, rfl⟩ ; rfl
  right_inv b := rfl

def secondEquiv (α : Type u) {β : Type v} (b : β) : { ab : α × β // ab.snd = b } ≃ α where
  toFun ab := ab.1.1
  invFun a := ⟨(a, _), rfl⟩
  left_inv ab := by rcases ab with ⟨_, rfl⟩ ; rfl
  right_inv b := rfl

def invariantFunctionFirst (f : (α × β) → (α × β)) (a : α) (h : ∀ a ab, ab.fst = a → (f ab).fst = a) : β → β :=
(firstEquiv a β).conj (Subtype.map f (h _))

def invariantFunctionSecond (f : (α × β) → (α × β)) (b : β) (h : ∀ b ab, ab.snd = b → (f ab).snd = b) : α → α :=
(secondEquiv α b).conj (Subtype.map f (h _))


def EquivAlongFirst (e : Equiv.Perm (α × β)) (a : α) (h : ∀ a ab, ab.fst = a → (e ab).fst = a) : Equiv.Perm β :=
(firstEquiv a β).permCongr (e.subtypePerm (fun _ => ⟨h _ _, fun h₂ => (h₂.symm.trans (h _ _ rfl)).symm⟩))

def EquivAlongSecond (e : Equiv.Perm (α × β)) (b : β) (h : ∀ b (ab : α × β), ab.snd = b → (e ab).snd = b) : Equiv.Perm α :=
(secondEquiv α b).permCongr (e.subtypePerm (fun _ => ⟨h _ _, fun h₂ => (h₂.symm.trans (h _ _ rfl)).symm⟩))

def inductiveControl : ControlBits (m + 1) ≃ (ControlBitsLayer (m + 1) × ControlBits m × ControlBits m × ControlBitsLayer (m + 1)) :=
((Equiv.piFinSucc _ _).trans ((Equiv.refl _).prodCongr (((finCongr (mul_add _ _ _)).arrowCongr (Equiv.refl _)).trans
((Equiv.piFinSuccAboveEquiv (fun _ => _) (Fin.last _)).trans (Equiv.prodComm _ _))))).trans (Equiv.prodCongr (Equiv.refl _)
(Equiv.trans (Equiv.prodCongr ((((Equiv.refl _).arrowCongr (((((getBitResiduum 0).trans (Equiv.boolProdEquivSum _)).arrowCongr
  (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)))).trans
  (Equiv.arrowProdEquivProdArrow _ _ _))) (Equiv.refl _)) ((Equiv.prodAssoc _ _ _))))

def permOthers {π : Equiv.Perm (Fin (2^(m + 1)))} {i : Fin (m + 1)} (b : Bool) (h : bitInvariant i π)
: Equiv.Perm (Fin (2^m)) := EquivAlongFirst ((getBitResiduum i).permCongr π) b h

def evenPerm {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvariant 0 π) := permOthers false h
def oddPerm {π : Equiv.Perm (Fin (2^(m + 1)))} (h : bitInvariant 0 π) := permOthers true h


--Equiv.boolProdEquivSum

def xIf : ControlBitsLayer m → Equiv.Perm (Fin (2^(m + 1))) := (residuumCondFlip · 0)

def piBar (π : Equiv.Perm (Fin (2^(m + 1)))) := (π.permCongr (flipBit 0)).trans (flipBit 0)

def flmDecomp (π : Equiv.Perm (Fin (2^((m + 1) + 1)))) :
ControlBitsLayer (m + 1) × Equiv.Perm (Fin (2^((m + 1) + 1))) × ControlBitsLayer (m + 1)
:= sorry

lemma flmDecomp_invar (π : Equiv.Perm (Fin (2^((m + 1) + 1)))) :
bitInvariant 0 (flmDecomp π).2.1 := sorry


def ControlBitsBase (π : Equiv.Perm (Fin (2^(0 + 1)))) : ControlBits 0 := ![![π 0 == 1]]
def ControlBitsCheat (π : Equiv.Perm (Fin (2^(m + 1)))) : ControlBits m := sorry

def ControlBitsInductive' (π : Equiv.Perm (Fin (2^((m + 1) + 1)))) :
ControlBits (m + 1)
:= inductiveControl.symm ((flmDecomp π).1, ControlBitsCheat (evenPerm (flmDecomp_invar π)),
ControlBitsCheat (oddPerm (flmDecomp_invar π)), (flmDecomp π).2.2)


end ControlBits
 /-
 def permOthers' {π : Equiv.Perm (Fin (2^(m + 1)))} {i : Fin (m + 1)} (h : bitInvariant i π) (b : Bool) : Equiv.Perm (Fin (2^m)) where
  toFun := Prod.snd ∘ ((getBitResiduum i).permCongr π) ∘ (Prod.mk b)
  invFun := Prod.snd ∘ ((getBitResiduum i).permCongr π.symm) ∘ (Prod.mk b)
  left_inv := fun x => by simp only [Function.comp_apply, Equiv.permCongr_apply, getBitResiduum_symm_apply,
    getBitResiduum_apply, mergeBitResiduum_getResiduum_perm_mergeBitResiduum_of_bitInvariant h, Equiv.symm_apply_apply, getBit_mergeBitResiduum,
    getResiduum_mergeBitResiduum]
  right_inv := fun x => by simp only [Function.comp_apply, Equiv.permCongr_apply, getBitResiduum_symm_apply,
    getBitResiduum_apply, mergeBitResiduum_getResiduum_perm_mergeBitResiduum_of_bitInvariant (Equiv.Perm.symm_bitInvariant h),
    Equiv.apply_symm_apply, getBit_mergeBitResiduum, getResiduum_mergeBitResiduum]


def bitvecEquiv {m : ℕ} : Fin (2^m) ≃ (Fin m → Bool) :=
(finFunctionFinEquiv.symm.trans ((Equiv.refl _).arrowCongr finTwoEquiv))

-- DEF

def getBitResiduum' (i : Fin (m + 1)) : Fin (2^(m + 1)) ≃ Bool × Fin (2^m) :=
Equiv.trans bitvecEquiv (Equiv.trans (Equiv.piFinSuccAboveEquiv _ i) ((Equiv.refl _).prodCongr bitvecEquiv.symm))

 -/