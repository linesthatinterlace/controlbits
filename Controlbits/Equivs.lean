import Mathlib.Logic.Equiv.Fin

def finArrowFinEquiv : (Fin a → Fin b → α) ≃ (Fin (a*b) → α) :=
(Equiv.curry _ _ _).symm.trans (finProdFinEquiv.arrowCongr <| Equiv.refl _)

def splitOffFirstLast : (Fin (2*(n + 1) + 1) → α) ≃ (α × α) × (Fin (2*n + 1) → α) :=
calc
  _ ≃ _ := Equiv.piFinSucc _ _
  _ ≃ _ := Equiv.prodCongr (Equiv.refl _) (Equiv.piFinSuccAboveEquiv _ (Fin.last _))
  _ ≃ _ := (Equiv.prodAssoc _ _ _).symm

def prodArrowEquivCongr {α β γ δ : Type*} (e : α ≃ β) : γ × (δ → α) ≃ γ × (δ → β) :=
(Equiv.refl _).prodCongr ((Equiv.refl _).arrowCongr e)
