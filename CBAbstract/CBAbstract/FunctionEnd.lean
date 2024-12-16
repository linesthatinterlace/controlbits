import Mathlib.Algebra.Group.Action.End

universe u

instance Function.End.instFunLikeEnd {α : Type u} : FunLike (Function.End α) α α where
  coe := id
  coe_injective' := injective_id

@[ext] lemma Function.End.ext {α : Type u} {f : Function.End α} {g : Function.End α}
(H : ∀ (x : α), f x = g x) : f = g := DFunLike.ext _ _ H
