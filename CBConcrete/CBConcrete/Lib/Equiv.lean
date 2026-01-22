import Mathlib.Logic.Equiv.Defs

@[simp, grind =]
lemma finTwoEquiv_apply {j} : finTwoEquiv j = decide (j = 1) := rfl

@[simp, grind =]
lemma finTwoEquiv_symm_apply {j} : finTwoEquiv.symm j = bif j then 1 else 0 := rfl
