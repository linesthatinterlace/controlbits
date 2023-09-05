import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.PropInstances
import Mathlib.GroupTheory.Perm.Basic

namespace Sum
variable {α : Type u} {β: Type v}

/-- Get the data from a sum type given a proof that it is of the left constructor. -/
def getLeft! : (ab : α ⊕ β) → ab.isLeft → α | inl a, _ => a

@[simp]
lemma left_getLeft! : ∀ (ab : α ⊕ β) (h : ab.isLeft), inl (ab.getLeft! h) = ab | inl _, _ => rfl

@[simp]
lemma getLeft!_left (a : α) (h : (inl a : α ⊕ β).isLeft) : (inl a).getLeft! h = a := rfl

lemma eq_left_iff_getLeft!_eq {ab : α ⊕ β} {a : α} : ab = inl a ↔ ∃ h, ab.getLeft! h = a := by
  cases ab <;> simp

lemma eq_left_of_isLeft : ∀ {ab : α ⊕ β} (h : ab.isLeft), ab = inl (ab.getLeft! h)
  | inl _, _ => rfl

/-- Get the data from a sum type given a proof that it is of the right constructor. -/
def getRight! : (ab : α ⊕ β) → ab.isRight → β | inr b, _ => b

@[simp]
lemma right_getRight! : ∀ (ab : α ⊕ β) (h : ab.isRight), inr (ab.getRight! h) = ab | inr _, _ => rfl

@[simp]
lemma getRight!_right (b : β) (h : (inr b : α ⊕ β).isRight) : (inr b).getRight! h = b := rfl

lemma eq_right_iff_getRight!_eq {ab : α ⊕ β} {b : β} : ab = inr b ↔ ∃ h, ab.getRight! h = b := by
  cases ab <;> simp

lemma eq_right_of_isRight : ∀ {ab : α ⊕ β} (h : ab.isRight), ab = inr (ab.getRight! h)
  | inr _, _ => rfl

@[simp]
lemma isLeft_eq_of_liftRel_inl_right (h : LiftRel ra rb ab (inl c)) : ab.isLeft  := by
  cases h ; simp

@[simp]
lemma isLeft_eq_of_liftRel_inl_left (h : LiftRel ra rb (inl a) cd) : cd.isLeft := by
  cases h ; simp

lemma isLeft_eq_of_liftRel (h : LiftRel ra rb ab cd) : ab.isLeft = cd.isLeft := by
  cases h <;> simp

lemma isRight_eq_of_liftRel (h : LiftRel ra rb ab cd) : ab.isRight = cd.isRight := by
  cases h <;> simp

@[simp]
lemma isRight_eq_of_liftRel_inr_left (h : LiftRel ra rb (inr b) cd) : cd.isRight := by
  cases h ; simp

@[simp]
lemma isRight_eq_of_liftRel_inr_right (h : LiftRel ra rb ab (inr d)) : ab.isRight := by
  cases h ; simp

lemma liftRel_equiv_left_iff_symm_right {e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂} :
(∀ ab, LiftRel ra rb (e ab) ab) ↔ ∀ cd, LiftRel ra rb cd (e.symm cd) :=
⟨fun H cd => by convert (H (e.symm cd)) ; exact (e.apply_symm_apply _).symm,
fun H ab => by convert (H (e ab)) ; exact (e.symm_apply_apply _).symm⟩

lemma liftRel_equiv_right_iff_symm_left {e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂} :
(∀ ab, LiftRel ra rb ab (e ab)) ↔ ∀ cd, LiftRel ra rb (e.symm cd) cd :=
by convert liftRel_equiv_left_iff_symm_right.symm ; exact e.symm_symm

def shouldExistLeft (α β) : {x : Sum α β // x.isLeft} ≃ α where
  toFun := fun ⟨x, hx⟩ => x.getLeft! hx
  invFun := fun x => ⟨Sum.inl x, rfl⟩
  left_inv := by intro _; ext ; dsimp ; exact left_getLeft! _ _
  right_inv := fun x => rfl

def shouldExistRight (α β): {x : Sum α β // x.isRight} ≃ β where
  toFun := fun ⟨x, hx⟩ => x.getRight! hx
  invFun := fun x => ⟨Sum.inr x, rfl⟩
  left_inv := by intro _; ext ; dsimp ; exact right_getRight! _ _
  right_inv := fun x => rfl

end Sum

open Sum

variable {e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂} {ra : α₂ → α₁ → Prop} {rb : β₂ → β₁ → Prop}
{ea : α₁ ≃ α₂} {eb : β₁ ≃ β₂}


/-- Given an equiv is compatible with the lifted relation, induce an equivalence between first
types of a sum type. -/
@[simps]
def equivOfLiftRelToEquivLeft (he : ∀ ab, LiftRel ra rb (e ab) ab) : α₁ ≃ α₂ where
  toFun := fun a₁ => (e (inl a₁)).getLeft! (
    isLeft_eq_of_liftRel_inl_right (he (inl _)))
  invFun := fun a₂ => (e.symm (inl a₂)).getLeft! (by
    rw [liftRel_equiv_left_iff_symm_right] at he ;
    exact isLeft_eq_of_liftRel_inl_left (he (inl a₂)))
  left_inv := fun a₁ => (by simp_rw [left_getLeft!, Equiv.symm_apply_apply, getLeft!_left])
  right_inv := fun a₂ => (by simp_rw [left_getLeft!, Equiv.apply_symm_apply, getLeft!_left])

/-- Given an equiv is compatible with the lifted relation, induce an equivalence between second
types of a sum type. -/
@[simps]
def equivOfLiftRelToEquivRight (he : ∀ ab, LiftRel ra rb (e ab) ab) : β₁ ≃ β₂ where
  toFun := fun b₁ => (e (inr b₁)).getRight! (
    isRight_eq_of_liftRel_inr_right (he (inr _)))
  invFun := fun b₂ => (e.symm (inr b₂)).getRight! (by
    rw [liftRel_equiv_left_iff_symm_right] at he ;
    exact isRight_eq_of_liftRel_inr_left (he (inr b₂)))
  left_inv := fun b₁ => (by simp_rw [right_getRight!, Equiv.symm_apply_apply, getRight!_right])
  right_inv := fun b₂ => (by simp_rw [right_getRight!, Equiv.apply_symm_apply, getRight!_right])

lemma equivOfLiftRelToEquivLeft_rel_left {he : ∀ ab, LiftRel ra rb (e ab) ab} (a : α₁) :
ra (equivOfLiftRelToEquivLeft he a) a := by
  simp only [equivOfLiftRelToEquivLeft_apply, ← liftRel_inl_inl (r := ra) (s := rb),
    left_getLeft!, he]

lemma equivOfLiftRelToEquivRight_rel_right {he : ∀ ab, LiftRel ra rb (e ab) ab} (b : β₁):
rb (equivOfLiftRelToEquivRight he b) b := by
  simp only [equivOfLiftRelToEquivRight_apply, ← liftRel_inr_inr (r := ra) (s := rb),
    right_getRight!, he]

lemma liftRelSumCongr_of_rel_left_rel_right (hea : ∀ a, ra (ea a) a) (heb : ∀ b, rb (eb b) b) (ab) :
LiftRel ra rb (ea.sumCongr eb ab) ab := by
  cases ab <;> simp [hea, heb]

lemma sumCongrEquivLiftRelLeftRight_eq_self (he : ∀ ab, LiftRel ra rb (e ab) ab) :
(equivOfLiftRelToEquivLeft he).sumCongr (equivOfLiftRelToEquivRight he) = e := by
  ext ab ; cases ab <;> simp [he]

/-- There is an equivalence between the subtype of equivalences between sum types compatible
with the lifted relations and the product of equivalences compatible with each relation. -/

@[simps]
def equivLiftRelSum (ra : α₂ → α₁ → Prop) (rb : β₂ → β₁ → Prop) :
    {e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ // ∀ x, LiftRel ra rb (e x) x} ≃
    {ea : α₁ ≃ α₂ // ∀ x, ra (ea x) x} × {eb : β₁ ≃ β₂ // ∀ x, rb (eb x) x} where
    toFun :=  fun ⟨e, he⟩ =>
  ⟨⟨equivOfLiftRelToEquivLeft he, equivOfLiftRelToEquivLeft_rel_left⟩,
  ⟨equivOfLiftRelToEquivRight he, equivOfLiftRelToEquivRight_rel_right⟩⟩
    invFun :=  fun ⟨⟨ea, hea⟩, ⟨_, heb⟩⟩ => ⟨ea.sumCongr _, liftRelSumCongr_of_rel_left_rel_right hea heb⟩
    left_inv := fun ⟨_, he⟩ => by simp_rw [Subtype.mk.injEq] ; exact sumCongrEquivLiftRelLeftRight_eq_self he
    right_inv := fun ⟨⟨_, hea⟩, ⟨_, heb⟩⟩ => rfl

--

lemma equivIsLeftInvariant_iff_liftRel_top_top (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂) :
(∀ ab, isLeft (e ab) = isLeft ab) ↔ ∀ ab, LiftRel ⊤ ⊤ (e ab) ab := by
  simp_rw  [Sum.forall, isLeft_inl, isLeft_inr, isLeft_eq_false, isLeft_iff, isRight_iff]
  exact ⟨fun ⟨hA, hB⟩ => ⟨fun a => (hA a).elim (fun _ h => h ▸ LiftRel.inl (trivial)),
                          fun b => (hB b).elim (fun _ h => h ▸ LiftRel.inr (trivial))⟩,
          fun ⟨hA, hB⟩ => ⟨fun a => isLeft_iff.mp (isLeft_eq_of_liftRel (hA a)),
                          fun b => isRight_iff.mp (isRight_eq_of_liftRel (hB b))⟩⟩

lemma equivIsRightInvariant_iff_liftRel_top_top (e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂) :
(∀ ab, isRight (e ab) = isRight ab) ↔
∀ ab, LiftRel ⊤ ⊤ (e ab) ab := by
  rw [← equivIsLeftInvariant_iff_liftRel_top_top] ;
  simp_rw [Sum.forall]
  simp_rw  [isRight_inl, isRight_eq_false, isRight_inr, isLeft_inl, isLeft_inr, isLeft_eq_false]

/-- There is an equivalence between the subtype of equivalences between sum types which
preserve chiarality and the product of equivalences compatible with each relation. -/
@[simps!]
def equivIsChiralInvariantProdEquiv : {e : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ // ∀ x, (e x).isLeft = x.isLeft} ≃
(α₁ ≃ α₂) × (β₁ ≃ β₂) :=
(Equiv.subtypeEquivRight equivIsLeftInvariant_iff_liftRel_top_top).trans
  <| (equivLiftRelSum ⊤ ⊤).trans
    <| (Equiv.subtypeUnivEquiv (fun _ _ => trivial)).prodCongr
        <| Equiv.subtypeUnivEquiv (fun _ _ => trivial)