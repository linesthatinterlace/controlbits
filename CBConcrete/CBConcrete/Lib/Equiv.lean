import Mathlib.Logic.Equiv.Defs

@[simp, grind =]
lemma finTwoEquiv_apply {j} : finTwoEquiv j = decide (j = 1) := rfl

@[simp, grind =]
lemma finTwoEquiv_symm_apply {j} : finTwoEquiv.symm j = bif j then 1 else 0 := rfl

@[simps!]
def boolInversion : Equiv.Perm Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not
