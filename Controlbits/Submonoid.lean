import Mathlib.Algebra.Group.Submonoid.Units

namespace MulEquiv

def piUnits {β : α → Type*} [∀ a, Monoid (β a)] : (∀ a, β a)ˣ ≃* (∀ a, (β a)ˣ) where
  toFun f a := ⟨f.val a, f.inv a, congr_fun f.mul_inv a, congr_fun f.inv_mul a⟩
  invFun f := ⟨(f ·), (f⁻¹ ·), funext (f · |>.mul_inv), funext (f · |>.inv_mul)⟩
  left_inv _ := Units.ext <| funext fun _ => rfl
  right_inv _ := funext fun _ => Units.ext rfl
  map_mul' _ _ := funext fun _ => Units.ext rfl

def subtypeMulEquiv {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] (e : M₁ ≃* M₂)
  {S : Submonoid M₁} {T : Submonoid M₂} (h : ∀ s, s ∈ S ↔ (e s) ∈ T) : S ≃* T where
  toEquiv := e.subtypeEquiv h
  map_mul' := by simp_rw [toEquiv_eq_coe, Equiv.toFun_as_coe, Equiv.subtypeEquiv_apply,
    Submonoid.coe_mul, coe_toEquiv, map_mul, Submonoid.mk_mul_mk, Subtype.forall, implies_true]

lemma mem_iff_map_mem_units_of_mem_iff_map_mem {G M : Type*} [Group G] [Monoid M] (e : G ≃* Mˣ)
  {S : Subgroup G} {T : Submonoid M} (h : ∀ s, s ∈ S ↔ (e s : M) ∈ T) (s : G) :
  s ∈ S ↔ e s ∈ T.units := by
  simp_rw [Submonoid.mem_units_iff, ← e.map_inv, ← h, iff_self_and, inv_mem_iff, imp_self]

def subgroupMulEquivUnits {G M : Type*} [Group G] [Monoid M] (e : G ≃* Mˣ)
  {S : Subgroup G} {T : Submonoid M} (h : ∀ s, s ∈ S ↔ (e s : M) ∈ T) : S ≃* T.units :=
  e.subtypeMulEquiv (e.mem_iff_map_mem_units_of_mem_iff_map_mem h)

def subgroupMulEquivUnitsType {G M : Type*} [Group G] [Monoid M] (e : G ≃* Mˣ)
  {S : Subgroup G} {T : Submonoid M} (h : ∀ s, s ∈ S ↔ (e s : M) ∈ T) : S ≃* Tˣ :=
  (e.subgroupMulEquivUnits h).trans T.unitsEquivUnitsType

end MulEquiv
