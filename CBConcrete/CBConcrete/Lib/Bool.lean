namespace Bool

theorem and_inj_left : ∀ {a b b'}, (a && b) = (a && b') ↔ (a = false) ∨ (b = b') := by decide
theorem and_inj_right : ∀ {a b b'}, (b && a) = (b' && a) ↔ (a = false) ∨ (b = b') := by decide
theorem or_inj_left : ∀ {a b b'}, (a || b) = (a || b') ↔ (a = true) ∨ (b = b') := by decide
theorem or_inj_right : ∀ {a b b'}, (b || a) = (b' || a) ↔ (a = true) ∨ (b = b') := by decide

@[grind =]
theorem toNat_decide {P : Prop} [Decidable P] : toNat P = if P then 1 else 0 := cond_decide _ _ _

@[simp]
theorem toNat_pos {P : Prop} [Decidable P] (p : P) : toNat P = 1 := by grind

@[simp]
theorem toNat_neg {P : Prop} [Decidable P] (p : ¬P) : toNat P = 0 := by grind

theorem toNat_not {b} : (!b).toNat = 1 - b.toNat := by grind [cases Bool]

theorem toNat_not_add_toNat {b} : (!b).toNat + b.toNat = 1 := by grind [cases Bool]

theorem toNat_add_toNat_not {b} : b.toNat + (!b).toNat = 1 := by grind [cases Bool]

theorem toNat_True : toNat True = 1 := by grind

theorem toNat_False : toNat False = 0 := by grind

theorem decide_toNat_eq_one {b} : (b.toNat = 1 : Bool) = b := by grind [cases Bool]

theorem toNat_injective : Function.Injective toNat := by grind [Function.Injective, cases Bool]

theorem toNat_inj {b b'} : toNat b = toNat b' ↔ b = b' := by grind [cases Bool]

@[simp]
theorem decide_mod_two_eq_one_toNat {p} : (p % 2 = 1 : Bool).toNat = p % 2 := by grind

@[simp]
theorem decide_toNat_mod_two_eq_one {b} : (b.toNat % 2 = 1 : Bool) = b := toNat_injective <| by
  grind [cases Bool]

theorem eq_iff_iff' {a b} : a = b ↔ (a = false ↔ b = false) := by grind

theorem decide_and_eq_decide_and {b b'} {P : Prop} [Decidable P] :
    (decide P && b) = (decide P && b') ↔ P → b = b' := by grind

theorem apply_apply_apply_not_of_comm {α β} {f : β → β → α}
    (hf : ∀ x y, f x y = f y x) (b b' : Bool) (g : Bool → β)  :
    f (g b) (g b.not) = f (g b') (g b'.not) := by grind [cases Bool]

theorem apply_false_apply_true_of_comm {α β} {f : β → β → α}
    (hf : ∀ x y, f x y = f y x) (b : Bool) (g : Bool → β) :
    f (g false) (g true) = f (g b) (g b.not) := by grind [cases Bool]

theorem apply_true_apply_false_of_comm {α β} {f : β → β → α}
    (hf : ∀ x y, f x y = f y x) (b : Bool) (g : Bool → β)  :
    f (g true) (g false) = f (g b) (g b.not) := by grind [cases Bool]

end Bool
