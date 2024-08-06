import Mathlib.Logic.Equiv.Fin

open Fin

def piFinSuccCastSucc : (Fin (n + 2) → α) ≃ (α × α) × (Fin n → α) :=
calc
  _ ≃ _ := Equiv.piFinSucc _ _
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (Equiv.piFinSuccAbove _ (last _))
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm

lemma piFinSuccCastSucc_apply (v : (Fin (n + 2) → α)) : piFinSuccCastSucc v =
    ((v 0, v (last _)), v ∘ (fun i => i.castSucc.succ)) := by
  simp_rw [Prod.ext_iff, Function.funext_iff]
  refine ⟨⟨rfl, rfl⟩, fun _ => ?_⟩
  simp_rw [piFinSuccCastSucc, Equiv.instTrans_trans, Equiv.trans_apply, Equiv.prodCongr_apply,
  Equiv.piFinSuccAbove_apply, Fin.removeNth_last]
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
  simp only [piFinSuccCastSucc, Equiv.instTrans_trans, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.prodAssoc_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply,
    Equiv.coe_refl, Equiv.piFinSuccAbove_symm_apply, insertNth_last', Prod.map_apply, id_eq,
    Equiv.piFinSucc_symm_apply, cons_succ, snoc_castSucc]

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
  simp_rw [piFinSuccCastSucc, Equiv.instTrans_trans, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.prodAssoc_apply, Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply,
    Equiv.coe_refl, Equiv.piFinSuccAbove_symm_apply, insertNth_last', Prod.map_apply, id_eq,
    Equiv.piFinSucc_symm_apply, cons_snoc_eq_snoc_cons, snoc_last]

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
