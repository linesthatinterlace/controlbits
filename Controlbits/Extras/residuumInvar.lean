/-
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

lemma mergeBitRes_getBit_apply_mergeBitRes_eq_apply_mergeBitRes (h : residuumInvar i f) :
mergeBitRes i (getBit i (f (mergeBitRes i b p))) p = f (mergeBitRes i b p) := by
rcases getRes_surj i (f (mergeBitRes i b p)) with ⟨c, hc⟩
rw [getRes_apply_mergeBitRes_Bool_eq_Bool_of_residuumInvar h] at hc
rw [← hc, getBit_mergeBitRes]

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
-/

/-

lemma flipBit_residuumInvar : residuumInvar i (flipBit i) :=
residuumInvar_of_getRes_apply_eq_getBit (fun _ => getRes_flipBit)

-/
