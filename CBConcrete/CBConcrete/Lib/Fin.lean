namespace Fin

variable {n : Nat}

@[simp, grind =]
theorem coe_xor {i j : Fin n} : (i ^^^ j).val = (i.val ^^^ j.val) % n := rfl

theorem surj_of_inj (f : Fin n → Fin n) (hf : ∀ x y, f x = f y → x = y) : ∀ y, ∃ x, f x = y := by
  induction n with | zero => exact (·.elim0) | succ n IH =>
  let g i := if i = f (last n) then last n else if i = last n then f (last n) else i
  suffices ∀ y, ∃ x, (g ∘ f) x = y from (by grind [this <| g ·])
  specialize IH (⟨(g ∘ f) ⟨·, by grind⟩, by grind⟩) (by grind)
  exact lastCases (⟨last n, by grind⟩) (by grind [IH ·])

theorem inj_of_surj (g : Fin n → Fin n) (hg : ∀ y, ∃ x, g x = y) : ∀ x y, g x = g y → x = y := by
  have hf (x y) (hxy : (hg x).choose = (hg y).choose) : x = y := by grind
  exact (by grind [surj_of_inj _ hf ·, surj_of_inj _ hf ·])

theorem surjective_of_injective : (f : Fin n → Fin n) → f.Injective → f.Surjective := surj_of_inj

theorem injective_of_surjective : (f : Fin n → Fin n) → f.Surjective → f.Injective := inj_of_surj

theorem injective_iff_surjective (f : Fin n → Fin n) : f.Injective ↔ f.Surjective :=
  ⟨surjective_of_injective f, injective_of_surjective f⟩

end Fin
