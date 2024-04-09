import Mathlib.Logic.Equiv.Fin

@[simps!]
def piFinSuccCastSucc : (Fin (n + 2) → α) ≃ (α × α) × (Fin n → α) :=
calc
  _ ≃ _ := Equiv.piFinSucc _ _
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (Equiv.piFinSuccAbove _ (Fin.last _))
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm

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
