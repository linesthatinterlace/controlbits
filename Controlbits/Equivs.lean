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
