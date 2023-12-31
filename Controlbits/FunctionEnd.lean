import Mathlib.GroupTheory.GroupAction.Defs

instance Function.End.instFunLikeEnd {α : Type u} : FunLike (Function.End α) α (fun _ => α) where
  coe := id
  coe_injective' := injective_id

@[ext] lemma Function.End.ext {α : Type u} {f : Function.End α} {g : Function.End α}
(H : ∀ (x : α), f x = g x) : f = g := FunLike.ext _ _ H

lemma Function.End.ext_iff {α : Type u} {f : Function.End α} {g : Function.End α}
: f = g ↔ ∀ (x : α), f x = g x := FunLike.ext_iff
