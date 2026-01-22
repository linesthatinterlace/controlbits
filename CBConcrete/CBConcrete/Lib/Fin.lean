namespace Fin

variable {n : Nat}

@[simp, grind =]
theorem coe_xor {i j : Fin n} : (i ^^^ j).val = (i.val ^^^ j.val) % n := rfl

theorem surj_of_inj (f : Fin n → Fin n) (hf : ∀ x y, f x = f y → x = y) : ∀ y, ∃ x, f x = y := by
  induction n with | zero => exact (·.elim0) | succ n IH
  have H (g : Fin (n + 1) → Fin (n + 1)) (hg' : g (last n) = last n)
    (hg' : ∀ (x y : Fin (n + 1)), g x = g y → x = y) : ∀ y, ∃ x, g x = y := lastCases (by grind)
    (fun i => by specialize IH (⟨g ⟨·, by grind⟩, by grind⟩) (by grind) i; grind)
  intro y; specialize H (fun i => if i = last n then last n else
    if f i = last n then f (last n) else f i) (by grind) (by grind)
    (if y = f (last n) then last n else if y = last n then f (last n) else y); grind

theorem inj_of_surj (g : Fin n → Fin n) (hg : ∀ y, ∃ x, g x = y) : ∀ x y, g x = g y → x = y := by
  have hf x y (hxy : (hg ·|>.choose) x = (hg ·|>.choose) y) : x = y :=
    (Exists.choose_spec <| hg _).symm.trans <| (congrArg g hxy).trans <| Exists.choose_spec <| hg _
  intro x y hxy; have := And.intro (surj_of_inj _ hf x) (surj_of_inj _ hf y); grind

theorem surjective_of_injective : (f : Fin n → Fin n) → f.Injective → f.Surjective := surj_of_inj

theorem injective_of_surjective : (f : Fin n → Fin n) → f.Surjective → f.Injective := inj_of_surj

theorem injective_iff_surjective (f : Fin n → Fin n) : f.Injective ↔ f.Surjective :=
  ⟨surjective_of_injective f, injective_of_surjective f⟩

end Fin
