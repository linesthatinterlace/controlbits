namespace Fin

variable {n : Nat}

@[simp, grind =]
theorem coe_xor {i j : Fin n} : (i ^^^ j).val = (i.val ^^^ j.val) % n := rfl

/-
@[grind =]
theorem coe_succAbove {i : Fin n} {p : Fin (n + 1)} :
    (p.succAbove i : ℕ) = if p.val ≤ i.val then i.val + 1 else i.val := by
  grind [succAbove, val_castSucc]

@[grind =]
theorem coe_predAbove {p : Fin n} {i : Fin (n + 1)} :
    (p.predAbove i : ℕ) = if p.val < i.val then i.val - 1 else i.val := by
  grind [predAbove, val_castSucc, coe_castPred]
-/

theorem surj_of_inj (f : Fin n → Fin n) (hf : ∀ x y, f x = f y → x = y) (y : Fin n) :
     ∃ x, f x = y := by
  induction n with | zero | succ n IH
  · grind [cases Fin]
  · have H (g : Fin (n + 1) → Fin (n + 1)) (hg' : g (last n) = last n)
      (hg' : ∀ (x y : Fin (n + 1)), g x = g y → x = y) (y : Fin (n + 1)) : ∃ x, g x = y :=
      y.lastCases (by grind)
        fun i => have := IH (fun i => ⟨g ⟨i, by grind⟩, by grind⟩) (by grind) i; by grind
    specialize H (fun i => if i = last n then last n else
      if f i = last n then f (last n) else f i) (by grind) (by grind)
      (if y = f (last n) then last n else if y = last n then f (last n) else y)
    grind

theorem inj_of_surj (g : Fin n → Fin n) (hg : ∀ y, ∃ x, g x = y) (x y : Fin n) :
    g x = g y → x = y := by
  have hf : ∀ x y, (hg ·|>.choose) x = (hg ·|>.choose) y → x = y :=
    fun x y hxy => have := congrArg g hxy; by grind
  have Hx := surj_of_inj _ hf x; have Hy := surj_of_inj _ hf y; grind

open Function in
theorem surjective_of_injective (f : Fin n → Fin n) : Injective f → Surjective f := surj_of_inj f

open Function in
theorem injective_of_surjective (f : Fin n → Fin n) : Surjective f → Injective f := inj_of_surj f

open Function in
theorem injective_iff_surjective (f : Fin n → Fin n) : Injective f ↔ Surjective f :=
  ⟨surjective_of_injective f, injective_of_surjective f⟩


end Fin
