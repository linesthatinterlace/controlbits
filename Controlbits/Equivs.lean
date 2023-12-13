import Mathlib.Logic.Equiv.Fin

@[simps!]
def splitOffFirstLast : (Fin (2*(n + 1) + 1) → α) ≃ (α × α) × (Fin (2*n + 1) → α) :=
calc
  _ ≃ _ := Equiv.piFinSucc _ _
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (Equiv.piFinSuccAboveEquiv _ (Fin.last _))
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm

lemma splitOffFirstLast_apply_fst (cb : (Fin (2*(n + 1) + 1) → α)) :
  (splitOffFirstLast cb).1 = (cb 0, cb (Fin.last _)) := rfl

lemma splitOffFirstLast_apply_snd (cb : (Fin (2*(n + 1) + 1) → α)) :
  (splitOffFirstLast cb).2 = fun j => cb (j.castSucc.succ) := by
  simp_rw [splitOffFirstLast_apply]

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
