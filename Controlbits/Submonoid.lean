import Mathlib.GroupTheory.Submonoid.Operations
import Mathlib.GroupTheory.Submonoid.Pointwise
import Mathlib.GroupTheory.Subgroup.Basic

/-!
# Submonoid of units
Given a submonoid `S` of a monoid `M`, we define the submonoid `S.units` as the units of `S` as a
subgroup of `Mˣ`. That is to say, `S.units` contains all members of `S` which have a
two-sided inverse within `S`, as terms of type `Mˣ`.
This is multiplicatively equivalent to `Sˣ` and also to `IsUnit.submonoid S`,
but it is as a `Subgroup Mˣ` rather than as a type in and of itself or a `Submonoid S`.
-/

variable {M : Type*}

variable [Monoid M]

open Pointwise in
/-- The units of `S`, packaged as a subgroup of `Mˣ`.  -/
@[to_additive " The additive units of `S`, packaged as an additive subgroup of `AddUnits M`. "]
def Submonoid.units (S : Submonoid M) : Subgroup Mˣ where
  toSubmonoid := S.comap (Units.coeHom M) ⊓ (S.comap (Units.coeHom M))⁻¹
  inv_mem' ha := ⟨ha.2, ha.1⟩

/-- A subgroup of units represented as a submonoid of `M`.  -/
@[to_additive " A additive subgroup of additive units represented as a additive submonoid of `M`. "]
def Subgroup.ofUnits (S : Subgroup Mˣ) : Submonoid M := S.toSubmonoid.map (Units.coeHom M)

@[to_additive]
lemma Submonoid.units_mono : Monotone (Submonoid.units (M := M)) :=
fun _ _ hST _ ⟨h₁, h₂⟩ => ⟨hST h₁, hST h₂⟩

@[to_additive (attr := simp)]
lemma Submonoid.ofunits_units_le (S : Submonoid M) : S.units.ofUnits ≤ S :=
fun  _ ⟨_, hm, he⟩ => he ▸ hm.1

@[to_additive]
lemma Subgroup.ofUnits_mono : Monotone (Subgroup.ofUnits (M := M)) :=
fun _ _ hST _ ⟨x, hx, hy⟩ => ⟨x, hST hx, hy⟩

@[to_additive (attr := simp)]
lemma Subgroup.ofUnits_units_eq (S : Subgroup Mˣ) : S.ofUnits.units = S := Subgroup.ext (fun _ =>
  ⟨fun ⟨⟨_, hm, he⟩, _⟩ => (Units.ext he) ▸ hm, fun hm => ⟨⟨_, hm, rfl⟩, ⟨_, S.inv_mem hm, rfl⟩⟩⟩)

/-- A Galois coinsertion exists between the coercion from a subgroup of units to a submonoid and
the reduction from a submonoid to its unit group. -/
@[to_additive " A Galois coinsertion exists between the coercion from an additive subgroup of
additive units to an additive submonoid and the reduction from an additive submonoid to its unit
group. " ]
def ofUnits_units_gci : GaloisCoinsertion (Subgroup.ofUnits) (Submonoid.units (M := M)) :=
  GaloisCoinsertion.monotoneIntro Submonoid.units_mono Subgroup.ofUnits_mono
  Submonoid.ofunits_units_le Subgroup.ofUnits_units_eq

@[to_additive]
lemma ofUnits_units_gc : GaloisConnection (Subgroup.ofUnits) (Submonoid.units (M := M)) :=
ofUnits_units_gci.gc

namespace Submonoid

section Units

@[to_additive (attr := simp)]
lemma mem_units_iff (S : Submonoid M) (x : Mˣ) : x ∈ S.units ↔
    ((x : M) ∈ S ∧ ((x⁻¹ : Mˣ) : M) ∈ S) := Iff.rfl

@[to_additive]
lemma mem_units_of_coe_mem_coe_inv_mem (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) ∈ S)
    (h₂ : ((x⁻¹ : Mˣ) : M) ∈ S) : x ∈ S.units := ⟨h₁, h₂⟩

@[to_additive]
lemma coe_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : (x : M) ∈ S := h.1

@[to_additive]
lemma coe_inv_mem_of_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    ((x⁻¹ : Mˣ) : M) ∈ S := h.2

@[to_additive]
lemma coe_coe_inv_mul_coe_coe (S : Submonoid M) {x : Sˣ} :
    ((x⁻¹ : Sˣ) : M) * ((x : Sˣ) : M) = 1 := congrArg ((↑) : S → M) (Units.inv_mul _)

@[to_additive]
lemma coe_coe_mul_coe_coe_inv (S : Submonoid M) {x : Sˣ} :
    ((x : Sˣ) : M) * ((x⁻¹ : Sˣ) : M) = 1 := congrArg ((↑) : S → M) (Units.mul_inv _)

@[to_additive]
lemma mk_inv_mul_mk_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.2⟩ : S) * ⟨_, h.1⟩ = 1 := Subtype.ext (Units.inv_mul _)

@[to_additive]
lemma mk_mul_mk_inv_eq_one (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) :
    (⟨_, h.1⟩ : S) * ⟨_, h.2⟩ = 1 := Subtype.ext (Units.mul_inv _)

@[to_additive]
lemma mul_mem_units (S : Submonoid M) {x y : Mˣ} (h₁ : x ∈ S.units) (h₂ : y ∈ S.units):
    x * y ∈ S.units := mul_mem h₁ h₂

@[to_additive]
lemma inv_mem_units (S : Submonoid M) {x : Mˣ} (h : x ∈ S.units) : x⁻¹ ∈ S.units := inv_mem h

@[to_additive]
lemma inv_mem_units_iff (S : Submonoid M) {x : Mˣ} : x⁻¹ ∈ S.units ↔ x ∈ S.units := inv_mem_iff

/-- The equivalence between the subgroup of units of `S` and the type of units of `S`. -/
@[to_additive (attr := simps!) " The equivalence between the additive subgroup of additive units of
`S` and the type of additive units of `S`. "]
def unitsEquivUnitsType (S : Submonoid M) : S.units ≃* Sˣ where
  toFun := fun x => ⟨⟨_, x.2.1⟩, ⟨_, x.2.2⟩, S.mk_mul_mk_inv_eq_one x.2, S.mk_inv_mul_mk_eq_one x.2⟩
  invFun := fun x => ⟨⟨_, _, S.coe_coe_mul_coe_coe_inv, S.coe_coe_inv_mul_coe_coe⟩, ⟨x.1.2, x.2.2⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_mul' := fun _ _ => rfl

@[to_additive]
lemma ge_ofUnits_iff_units_ge (S : Submonoid M) (H : Subgroup Mˣ) :
    H.ofUnits ≤ S ↔ H ≤ S.units := ofUnits_units_gc _ _

@[to_additive (attr := simp)]
lemma units_top : (⊤ : Submonoid M).units = ⊤ := ofUnits_units_gc.u_top

@[to_additive (attr := simp)]
lemma units_inf (S T : Submonoid M): (S ⊓ T).units = S.units ⊓ T.units :=
ofUnits_units_gc.u_inf

@[to_additive]
lemma units_sInf {s: Set (Submonoid M)} : (sInf s).units = ⨅ S ∈ s, S.units :=
ofUnits_units_gc.u_sInf

@[to_additive]
lemma units_iInf {ι : Sort*} {f : ι → Submonoid M} : (iInf f).units = ⨅ (i : ι), (f i).units :=
ofUnits_units_gc.u_iInf

@[to_additive]
lemma units_iInf₂ {ι : Sort*} {κ : ι → Sort*} {f : (i : ι) → κ i → Submonoid M} :
    (⨅ (i : ι), ⨅ (j : κ i), f i j).units = ⨅ (i : ι), ⨅ (j : κ i), (f i j).units :=
    ofUnits_units_gc.u_iInf₂

@[to_additive (attr := simp)]
lemma units_bot : (⊥ : Submonoid M).units = ⊥ := ofUnits_units_gci.u_bot

@[to_additive]
lemma units_surjective : Function.Surjective (Submonoid.units (M := M)) :=
ofUnits_units_gci.u_surjective

@[to_additive]
lemma units_left_inverse :
    Function.LeftInverse (Submonoid.units (M := M)) (Subgroup.ofUnits (M := M)) :=
    ofUnits_units_gci.u_l_leftInverse

/-- The multiplicative equivalence between the type of units of `M` and the submonoid of unit
elements of `M`. -/
@[to_additive (attr := simps!) " The additive equivalence between the type of additive units of `M`
  and the additive submonoid whose elements are the additive units of `M`. "]
noncomputable def unitsTypeEquivIsUnitSubmonoid :
  Mˣ ≃* IsUnit.submonoid M where
  toFun x := ⟨x, Units.isUnit x⟩
  invFun x := x.prop.unit
  left_inv x := IsUnit.unit_of_val_units _
  right_inv x := by simp_rw [IsUnit.unit_spec]
  map_mul' x y := by simp_rw [Units.val_mul]; rfl

/-- The equivalence between the subgroup of units of `S` and the submonoid of unit
elements of `S`. -/
@[to_additive (attr := simps!) " The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`.  "]
noncomputable def unitsEquivIsUnitSubmonoid (S : Submonoid M) : S.units ≃* IsUnit.submonoid S :=
S.unitsEquivUnitsType.trans unitsTypeEquivIsUnitSubmonoid

/-- The unit group of a unit group is equivalent to the same group. -/
@[to_additive " The additive unit group of an additive unit group is equivalent to the same
group. " ]
def unitsTypeUnitsTypeEquivUnitsType : Mˣˣ ≃* Mˣ := toUnits.symm

end Units

end Submonoid

namespace Subgroup

@[to_additive (attr := simp)]
lemma mem_ofUnits_iff (S : Subgroup Mˣ) (x : M) : x ∈ S.ofUnits ↔ ∃ y ∈ S, y = x := Iff.rfl

@[to_additive]
lemma mem_ofUnits (S : Subgroup Mˣ) {x : M} {y : Mˣ} (h₁ : y ∈ S) (h₂ : y = x) : x ∈ S.ofUnits :=
  ⟨_, h₁, h₂⟩

@[to_additive]
lemma exists_unit_coe_eq_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    ∃ y ∈ S, y = x := h

@[to_additive]
lemma mem_of_mem_coe_ofUnits (S : Subgroup Mˣ) {y : Mˣ} : (y : M) ∈ S.ofUnits → y ∈ S :=
  fun ⟨_, hm, he⟩ => (Units.ext he) ▸ hm

@[to_additive]
lemma isUnit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} : x ∈ S.ofUnits → IsUnit x :=
fun ⟨_, _, h⟩ => ⟨_, h⟩

/-- Given some `x : M` which is a member of the submonoid of unit elements corresponding to a
  subgroup of units, produce a unit of `M` whose coercion is equal to `x`. `-/
@[to_additive " Given some `x : M` which is a member of the additive submonoid of additive unit
elements corresponding to a subgroup of units, produce a unit of `M` whose coercion is equal to
`x`. "]
noncomputable def unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) : Mˣ :=
(Classical.choose h).copy x (Classical.choose_spec h).2.symm _ rfl

@[to_additive]
lemma unit_of_mem_ofUnits_spec_eq_of_coe_mem (S : Subgroup Mˣ) {x : Mˣ} (h : (x : M) ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := Units.ext <| rfl

@[to_additive]
lemma unit_of_mem_ofUnits_spec_coe_eq_of_mem (S : Subgroup Mˣ) {x : M} (h : x ∈ S.ofUnits) :
    S.unit_of_mem_ofUnits h = x := rfl

@[to_additive]
lemma unit_of_mem_ofUnits_spec_mem (S : Subgroup Mˣ) {x : M} {h : x ∈ S.ofUnits} :
    S.unit_of_mem_ofUnits h ∈ S := S.mem_of_mem_coe_ofUnits h

@[to_additive]
lemma unit_eq_unit_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : x ∈ S.ofUnits) : h₁.unit = S.unit_of_mem_ofUnits h₂ := Units.ext <| rfl

@[to_additive]
lemma unit_mem_of_mem_ofUnits (S : Subgroup Mˣ) {x : M} {h₁ : IsUnit x}
    (h₂ : x ∈ S.ofUnits) : h₁.unit ∈ S :=
    S.unit_eq_unit_of_mem_ofUnits h₁ h₂ ▸ (S.unit_of_mem_ofUnits_spec_mem)

@[to_additive]
lemma mem_ofUnits_of_isUnit_of_unit_mem (S : Subgroup Mˣ) {x : M} (h₁ : IsUnit x)
    (h₂ : h₁.unit ∈ S) : x ∈ S.ofUnits := S.mem_ofUnits h₂ h₁.unit_spec

@[to_additive]
lemma mem_ofUnits_iff_exists_isUnit (S : Subgroup Mˣ) (x : M) :
    x ∈ S.ofUnits ↔ ∃ h : IsUnit x, h.unit ∈ S :=
    ⟨fun h => ⟨S.isUnit_of_mem_ofUnits h, S.unit_mem_of_mem_ofUnits h⟩,
    fun ⟨hm, he⟩ => S.mem_ofUnits_of_isUnit_of_unit_mem hm he⟩

/-- The equivalence between the coercion of a subgroup `S` of `Mˣ` to a submonoid of `M` and
the subgroup itself as a type. -/
@[to_additive (attr := simps!) " The equivalence between the coercion of an additive subgroup `S` of
`Mˣ` to an additive submonoid of `M` and the additive subgroup itself as a type. "]
noncomputable def ofUnitsEquivType (S : Subgroup Mˣ) : S.ofUnits ≃* S where
  toFun := fun x => ⟨S.unit_of_mem_ofUnits x.2, S.unit_of_mem_ofUnits_spec_mem⟩
  invFun := fun x => ⟨x.1, ⟨x.1, x.2, rfl⟩⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => Subtype.ext <| Units.ext <| rfl
  map_mul' := fun _ _ => Subtype.ext <| Units.ext <| rfl

@[to_additive]
lemma ofUnits_le_iff_le_units (H : Subgroup Mˣ) (S : Submonoid M) :
    H.ofUnits ≤ S ↔ H ≤ S.units := S.ge_ofUnits_iff_units_ge H

@[to_additive (attr := simp)]
lemma ofUnits_bot : (⊥ : Subgroup Mˣ).ofUnits = ⊥ := ofUnits_units_gc.l_bot

@[to_additive (attr := simp)]
lemma ofUnits_inf (S T : Subgroup Mˣ): (S ⊔ T).ofUnits = S.ofUnits ⊔ T.ofUnits :=
ofUnits_units_gc.l_sup

@[to_additive]
lemma ofUnits_sSup {s: Set (Subgroup Mˣ)} : (sSup s).ofUnits = ⨆ S ∈ s, S.ofUnits :=
ofUnits_units_gc.l_sSup

@[to_additive]
lemma ofUnits_iSup {ι : Sort*} {f : ι → Subgroup Mˣ} :
    (iSup f).ofUnits = ⨆ (i : ι), (f i).ofUnits := ofUnits_units_gc.l_iSup

@[to_additive]
lemma ofUnits_iSup₂ {ι : Sort*} {κ : ι → Sort*} {f : (i : ι) → κ i → Subgroup Mˣ} :
    (⨆ (i : ι), ⨆ (j : κ i), f i j).ofUnits = ⨆ (i : ι), ⨆ (j : κ i), (f i j).ofUnits :=
    ofUnits_units_gc.l_iSup₂

@[to_additive]
lemma Submonoid.ofUnits_surjective : Function.Injective (Subgroup.ofUnits (M := M)) :=
ofUnits_units_gci.l_injective

@[to_additive (attr := simp)]
lemma ofUnits_sup_units (S T : Subgroup Mˣ): (S.ofUnits ⊔ T.ofUnits).units = S ⊔ T :=
ofUnits_units_gci.u_sup_l _ _

@[to_additive]
lemma ofUnits_right_inverse :
    Function.RightInverse (Subgroup.ofUnits (M := M)) (Submonoid.units (M := M)) :=
    Submonoid.units_left_inverse

@[to_additive]
lemma ofUnits_strictMono : StrictMono (Subgroup.ofUnits (M := M)) := ofUnits_units_gci.strictMono_l

/-- The equivalence between the top subgroup of `Mˣ` coerced to a submonoid `M` and the
units of `M`. -/
@[to_additive (attr := simps!) " The equivalence between the additive subgroup of additive units of
`S` and the additive submonoid of additive unit elements of `S`.  "]
noncomputable def ofUnitsTopEquiv : (⊤ : Subgroup Mˣ).ofUnits ≃* Mˣ :=
(⊤ : Subgroup Mˣ).ofUnitsEquivType.trans topEquiv

variable {G : Type*}  [Group G]

@[to_additive]
lemma mem_units_iff_coe_mem (T : Subgroup G) (x : Gˣ): x ∈ T.units ↔ (x : G) ∈ T := by
    simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, Units.val_inv_eq_inv_val, inv_mem_iff,
    and_self]

@[to_additive]
lemma mem_iff_toUnits_mem_units (T : Subgroup G) (x : G) : x ∈ T ↔ toUnits x ∈ T.units := by
    simp_rw [Submonoid.mem_units_iff, mem_toSubmonoid, Units.val_inv_eq_inv_val, inv_mem_iff,
    and_self, coe_toUnits]


/-- The equivalence between the greatest subgroup of units contained within `T` and `T` itself. -/
@[to_additive " The equivalence between the greatest subgroup of additive units
contained within `T` and `T` itself. "]
def unitsEquivSelf (T : Subgroup G) : T.units ≃* T :=
T.unitsEquivUnitsType.trans (toUnits).symm

end Subgroup

@[to_additive (attr := simp)]
lemma toUnits_symm_eq_coe {G : Type*} [Group G] (x : Gˣ) : toUnits.symm x = x := rfl

@[to_additive (attr := simp)]
lemma toUnits_coe {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x := by
  simp_rw [MulEquiv.apply_eq_iff_symm_apply, toUnits_symm_eq_coe]

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
