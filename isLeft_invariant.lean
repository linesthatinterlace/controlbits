import Mathlib.Logic.Equiv.Defs

lemma sumCongr_isLeft_invariant {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4}
(ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : ∀ x : α₁ ⊕ β₁, ((Equiv.sumCongr ea eb) x).isLeft = x.isLeft :=
by rintro (x | x) <;> rfl

lemma isLeft_invariant_iff_symm_isLeft_invariant {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂) :
(∀ x, (e x).isLeft = x.isLeft) ↔ (∀ x, (e.symm x).isLeft = x.isLeft) := by
refine ⟨fun h => ?_, fun h => ?_⟩
· intro x ; specialize h (e.symm x) ; rw [Equiv.apply_symm_apply] at h ; rw [h]
· intro x ; specialize h (e x) ; rw [Equiv.symm_apply_apply] at h  ; rw [h]

lemma isLeft_invariant_iff {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂) :
(∀ x, (e x).isLeft = x.isLeft) ↔
((∀ (a : α₁), ∃ y, e (Sum.inl a) = Sum.inl y) ∧ (∀ (b : β₁), ∃ y, e (Sum.inr b) = Sum.inr y)) := by
simp [Sum.isLeft_iff, Sum.isRight_iff]

lemma equiv_isLeft_invariant_iff' {α₁ : Type u_1} {α₂ : Type u_2} {β₁ : Type u_3} {β₂ : Type u_4} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂) :
(∀ x, (e x).isLeft = x.isLeft) ↔
((∀ (a : α₁), ∃ y, e (Sum.inl a) = Sum.inl y) ∧ (∀ (b : β₁), ∃ y, e (Sum.inr b) = Sum.inr y) ∧
(∀ (a : α₂), ∃ y, e.symm (Sum.inl a) = Sum.inl y) ∧ (∀ (b : β₂), ∃ y, e.symm (Sum.inr b) = Sum.inr y)) := by
rw [← isLeft_invariant_iff, ← and_assoc, ← isLeft_invariant_iff, isLeft_invariant_iff_symm_isLeft_invariant, and_self]

def equivSumInvariantLeft {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂)
(he₁ : (∀ (a : α₁), ∃ y, e (Sum.inl a) = Sum.inl y))
(he₂ : (∀ (a : α₂), ∃ y, e.symm (Sum.inl a) = Sum.inl y)) : (α₁ ≃ α₂) where
  toFun a₁ := (e (Sum.inl a₁)).getLeft.get (by
    rcases he₁ a₁ with ⟨a₂, ha₂⟩ ; rw [ha₂] ; rfl )
  invFun a₂ := (e.symm (Sum.inl a₂)).getLeft.get (by
    rcases he₂ a₂ with ⟨a₁, ha₁⟩ ; rw [ha₁] ; rfl
  )
  left_inv a₁ := (by
    rcases he₁ a₁ with ⟨a₂, ha₂⟩ ; rcases he₂ a₂ with ⟨na₁, hna₁⟩ ;
    simp_rw [ha₂, Sum.getLeft_inl, Option.get_some, hna₁]
    simp_rw [← ha₂, Equiv.symm_apply_apply, Sum.inl.injEq] at hna₁ ; exact hna₁.symm
  )
  right_inv a₂ := (by
    rcases he₂ a₂ with ⟨a₁, ha₁⟩ ; rcases he₁ a₁ with ⟨na₂, hna₂⟩ ;
    simp_rw [ha₁, Sum.getLeft_inl, Option.get_some, hna₂]
    simp_rw [← ha₁, Equiv.apply_symm_apply, Sum.inl.injEq] at hna₂ ; exact hna₂.symm
  )

def equivSumInvariantRight {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂)
(he₁ : (∀ (b : β₁), ∃ y, e (Sum.inr b) = Sum.inr y))
(he₂ : (∀ (b : β₂), ∃ y, e.symm (Sum.inr b) = Sum.inr y)) : (β₁ ≃ β₂) where
  toFun b₁ := (e (Sum.inr b₁)).getRight.get (by
    rcases he₁ b₁ with ⟨b₂, hb₂⟩ ; rw [hb₂] ; rfl )
  invFun b₂ := (e.symm (Sum.inr b₂)).getRight.get (by
    rcases he₂ b₂ with ⟨b₁, hb₁⟩ ; rw [hb₁] ; rfl)
  left_inv b₁ := (by
    rcases he₁ b₁ with ⟨b₂, hb₂⟩ ; rcases he₂ b₂ with ⟨nb₁, hnb₁⟩ ;
    simp_rw [hb₂, Sum.getRight_inr, Option.get_some, hnb₁]
    simp_rw [← hb₂, Equiv.symm_apply_apply, Sum.inr.injEq] at hnb₁ ; exact hnb₁.symm)
  right_inv b₂ := (by
    rcases he₂ b₂ with ⟨b₁, hb₁⟩ ; rcases he₁ b₁ with ⟨nb₂, hnb₂⟩ ;
    simp_rw [hb₁, Sum.getRight_inr, Option.get_some, hnb₂]
    simp_rw [← hb₁, Equiv.apply_symm_apply, Sum.inr.injEq] at hnb₂ ; exact hnb₂.symm)

def equivSumInvariant {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂)
(h : ∀ x, (e x).isLeft = x.isLeft) : (α₁ ≃ α₂) × (β₁ ≃ β₂) :=
(equivSumInvariantLeft e ((equiv_isLeft_invariant_iff' e).mp h).1 ((equiv_isLeft_invariant_iff' e).mp h).2.2.1,
equivSumInvariantRight e ((equiv_isLeft_invariant_iff' e).mp h).2.1 ((equiv_isLeft_invariant_iff' e).mp h).2.2.2)

def equivSubInvariantSubtype : {e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ // ∀ x, (e x).isLeft = x.isLeft} ≃
(α₁ ≃ α₂) × (β₁ ≃ β₂) where
  toFun := fun ⟨e, he⟩ => equivSumInvariant e he
  invFun := fun ⟨ea, eb⟩ => ⟨Equiv.sumCongr ea eb, sumCongr_isLeft_invariant ea eb⟩
  left_inv := fun ⟨e, he⟩ => (by
    ext x ;
    simp only [equivSumInvariant, equivSumInvariantLeft, equivSumInvariantRight, Equiv.sumCongr_apply, Equiv.coe_fn_mk]
    rcases x with (a₁ | b₁) <;> rw [equiv_isLeft_invariant_iff'] at he
    · rcases he.1 a₁ with ⟨a₂, ha₂⟩ ;
      simp only [Sum.map_inl, ha₂, Sum.getLeft_inl, Option.get_some]
    · rcases he.2.1 b₁ with ⟨b₂, hb₂⟩ ;
      simp only [Sum.map_inr, hb₂, Sum.getRight_inr, Option.get_some])
  right_inv := fun ⟨ea, eb⟩ => (by
    ext x ;
    · simp only [equivSumInvariant, equivSumInvariantLeft, Equiv.sumCongr_apply, Sum.map_inl, Sum.getLeft_inl,
      Option.get_some, Equiv.sumCongr_symm, equivSumInvariantRight, Sum.map_inr, Sum.getRight_inr, Equiv.coe_fn_mk]
    · simp only [equivSumInvariant, equivSumInvariantLeft, Equiv.sumCongr_apply, Sum.map_inl, Sum.getLeft_inl,
      Option.get_some, Equiv.sumCongr_symm, equivSumInvariantRight, Sum.map_inr, Sum.getRight_inr, Equiv.coe_fn_mk]
  )