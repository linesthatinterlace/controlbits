import Mathlib.Data.Fin.Tuple.Basic

variable {n : ℕ} {α : Type*}

open Fin

def piFinSuccCastSucc : (Fin (n + 2) → α) ≃ (α × α) × (Fin n → α) :=
calc
  _ ≃ _ := (Fin.consEquiv _).symm
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) ((Fin.insertNthEquiv _ (last _)).symm )
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm

lemma piFinSuccCastSucc_apply (v : (Fin (n + 2) → α)) : piFinSuccCastSucc v =
    ((v 0, v (last _)), v ∘ (fun i => i.castSucc.succ)) := by
  simp_rw [Prod.ext_iff, funext_iff]
  refine ⟨⟨rfl, rfl⟩, fun _ => ?_⟩
  unfold piFinSuccCastSucc
  simp only [insertNthEquiv_last, Equiv.trans_def, Equiv.trans_apply, consEquiv_symm_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, snocEquiv_symm_apply,
    Equiv.prodAssoc_symm_apply, Function.comp_apply]
  rfl

@[simp]
lemma piFinSuccCastSucc_apply_fst_fst (v : (Fin (n + 2) → α)) : (piFinSuccCastSucc v).1.1 =
    v 0 := by simp_rw [piFinSuccCastSucc_apply]

@[simp]
lemma piFinSuccCastSucc_apply_fst_snd (v : (Fin (n + 2) → α)) : (piFinSuccCastSucc v).1.2 =
    v (last _) := by simp_rw [piFinSuccCastSucc_apply]

@[simp]
lemma piFinSuccCastSucc_apply_snd (v : (Fin (n + 2) → α)) : (piFinSuccCastSucc v).2 =
    v ∘ (fun i => i.castSucc.succ) := by simp only [piFinSuccCastSucc_apply]

@[simp]
lemma piFinSuccCastSucc_symm_apply_castSucc_succ (a b : α) (v : (Fin n → α)) (i : Fin n) :
      piFinSuccCastSucc.symm ((a, b), v) (i.castSucc.succ) = v i := by
  unfold piFinSuccCastSucc
  simp only [insertNthEquiv_last, Equiv.trans_def, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.prodAssoc_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq, consEquiv_apply, cons_succ, snocEquiv_apply,
    snoc_castSucc]

@[simp]
lemma piFinSuccCastSucc_symm_apply_succ_castSucc (a b : α) (v : (Fin n → α)) (i : Fin n) :
      piFinSuccCastSucc.symm ((a, b), v) (i.succ.castSucc) = v i := by
  rw [<- succ_castSucc, piFinSuccCastSucc_symm_apply_castSucc_succ]

@[simp]
lemma piFinSuccCastSucc_symm_apply_zero (a b : α) (v : (Fin n → α)) :
      piFinSuccCastSucc.symm ((a, b), v) 0 = a := rfl

@[simp]
lemma piFinSuccCastSucc_symm_apply_last (a b : α) (v : (Fin n → α)) :
      piFinSuccCastSucc.symm ((a, b), v) (last _) = b := by
  unfold piFinSuccCastSucc
  simp only [insertNthEquiv_last, Equiv.trans_def, ← succ_last, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.prodAssoc_apply, Equiv.prodCongr_symm, Equiv.refl_symm,
    Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, consEquiv_apply, cons_succ,
    snocEquiv_apply, snoc_last]

@[simp]
lemma finTwoEquiv_apply : ∀ j, finTwoEquiv j = decide (j = 1) := (Fin.forall_fin_two).mpr ⟨rfl, rfl⟩

@[simp]
lemma finTwoEquiv_symm_apply : ∀ j, finTwoEquiv.symm j = bif j then 1 else 0 :=
  (Bool.forall_bool).mpr ⟨rfl, rfl⟩

@[simps!]
def boolInversion : Equiv.Perm Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not
