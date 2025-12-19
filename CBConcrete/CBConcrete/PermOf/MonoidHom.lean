import CBConcrete.PermOf.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib
namespace Equiv

variable {α β : Type*}

end Equiv

namespace Equiv.Perm

variable {α : Type*}

@[irreducible]
def FixGENat (n : ℕ) : Subgroup (Perm ℕ) where
  carrier e := ∀ i, n ≤ i → e i = i
  mul_mem' {a} {b} ha hb i hi := (ha (b i) ((hb i hi).symm ▸ hi)).trans (hb i hi)
  one_mem' i hi := by simp_rw [Perm.coe_one, id_eq]
  inv_mem' {a} ha i hi := EquivLike.inv_apply_eq.mpr (ha i hi).symm

section FixGENat

variable {e : Perm ℕ} {n m i : ℕ}

theorem apply_eq_of_ge_of_mem_fixGENat {e : Perm ℕ} (he : e ∈ FixGENat n)
    (hi : n ≤ i) : e i = i := by
  unfold FixGENat at he
  exact he _ hi

theorem inv_apply_eq_of_ge_of_mem_fixGENat {e : Perm ℕ} (he : e ∈ FixGENat n)
    (hi : n ≤ i) : e⁻¹ i = i := apply_eq_of_ge_of_mem_fixGENat (inv_mem he) hi

theorem apply_lt_of_lt_of_mem_fixGENat {e : Perm ℕ} (he : e ∈ FixGENat n) (hi : i < n) :
    e i < n := by
  contrapose hi
  simp_rw [not_lt] at hi ⊢
  exact hi.trans_eq <| (inv_apply_eq_of_ge_of_mem_fixGENat he hi).symm.trans
    (Equiv.symm_apply_apply _ _)

theorem inv_apply_lt_of_lt_of_mem_fixGENat {e : Perm ℕ} (he : e ∈ FixGENat n) (hi : i < n) :
    e⁻¹ i < n := apply_lt_of_lt_of_mem_fixGENat (inv_mem he) hi

theorem lt_iff_apply_lt_of_mem_fixGENat {e : Perm ℕ} (he : e ∈ FixGENat n) :
    ∀ i, i < n ↔ e i < n :=
  fun _ => ⟨apply_lt_of_lt_of_mem_fixGENat he,
    fun hi => (inv_apply_lt_of_lt_of_mem_fixGENat he hi).trans_eq' (Equiv.symm_apply_apply _ _)⟩

theorem mem_fixGENat_of_ge_imp_apply_eq {e : Perm ℕ} (he : ∀ i, n ≤ i → e i = i) :
    e ∈ FixGENat n := by
  unfold FixGENat
  exact he

theorem mem_fixGENat_of_ge_imp_inv_apply {e : Perm ℕ} (he : ∀ i, n ≤ i → e i = i) :
    e ∈ FixGENat n := by
  unfold FixGENat
  exact he

theorem fixGENat_mono (hnm : n ≤ m) : FixGENat n ≤ FixGENat m :=
  fun _ he => mem_fixGENat_of_ge_imp_apply_eq
    fun _ hi => apply_eq_of_ge_of_mem_fixGENat he (hnm.trans hi)

theorem directed_fixGENat : Directed (· ≤ ·) (FixGENat) := fun _ _ =>
  ⟨_, fixGENat_mono (le_max_left _ _), fixGENat_mono (le_max_right _ _)⟩

end FixGENat

def FinitePermNat : Subgroup (Perm ℕ) := ⨆ (n : ℕ), FixGENat n

section FinitePermNat

variable {e : Perm ℕ} {n : ℕ}

@[simp] theorem mem_finitePermNat_iff : e ∈ FinitePermNat ↔ ∃ n, e ∈ FixGENat n :=
  Subgroup.mem_iSup_of_directed directed_fixGENat

theorem exists_mem_fixGENat_of_mem_finitePermNat (he : e ∈ FinitePermNat) :
    ∃ n, e ∈ FixGENat n := mem_finitePermNat_iff.mp he

theorem fixGENat_le_finitePermNat :
    FixGENat n ≤ FinitePermNat := fun _ he => mem_finitePermNat_iff.mpr ⟨_, he⟩

theorem mem_finitePermNat_of_mem_fixGENat (he : e ∈ FixGENat n) :
    e ∈ FinitePermNat := fixGENat_le_finitePermNat he

end FinitePermNat

end Equiv.Perm

namespace PermOf

open Equiv Perm Function

@[irreducible] def IsCongr {n m : ℕ} (a : PermOf n) (b : PermOf m) : Prop :=
  ∀ {i}, i < max m n → a • i = b • i

section IsCongr

variable {n m l i : ℕ} {a : PermOf n} {b : PermOf m} {c : PermOf l}

theorem isCongr_iff_smul_eq_of_lt :
    a.IsCongr b ↔ ∀ {i}, i < max m n → a • i = b • i := by
  unfold IsCongr
  exact Iff.rfl

instance {a : PermOf n} {b : PermOf m} : Decidable (a.IsCongr b) :=
  decidable_of_decidable_of_iff isCongr_iff_smul_eq_of_lt.symm

theorem isCongr_iff_smul_eq : a.IsCongr b ↔ ∀ {i : ℕ}, a • i = b • i :=
  ⟨fun h i => (lt_or_ge i (max m n)).elim (isCongr_iff_smul_eq_of_lt.mp h)
    (fun hmn => (a.smul_of_ge (le_of_max_le_right hmn)).trans
    (b.smul_of_ge (le_of_max_le_left hmn)).symm),
    fun h => isCongr_iff_smul_eq_of_lt.mpr (fun _ => h)⟩

theorem isCongr_iff_getElem_eq_getElem_and_getElem_eq_of_le (hnm : n ≤ m) :
    a.IsCongr b ↔ (∀ {i} (hi : i < n), a[i] = b[i]) ∧
    (∀ {i}, n ≤ i → ∀ (hi' : i < m), b[i] = i) := by
  simp_rw [isCongr_iff_smul_eq_of_lt, max_eq_left hnm, smul_eq_dite]
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · intro i hi
    have H :=  dif_pos hi ▸ dif_pos (hi.trans_le hnm) ▸ h (hi.trans_le hnm)
    exact H
  · intro i hi hi'
    have H := dif_neg hi.not_gt ▸ dif_pos hi' ▸ h hi'
    exact H.symm
  · intro i hi'
    simp_rw [hi', dite_true]
    split_ifs with hi
    · exact h.1 _
    · exact (h.2 (le_of_not_gt hi) _).symm

theorem IsCongr.smul_eq (hab : a.IsCongr b) : ∀ {i : ℕ}, a • i = b • i :=
  isCongr_iff_smul_eq.mp hab

@[simp] theorem isCongr_refl (a : PermOf n) : a.IsCongr a := by
  simp_rw [isCongr_iff_smul_eq, implies_true]

theorem isCongr_rfl : a.IsCongr a := isCongr_refl a

theorem IsCongr.symm : a.IsCongr b → b.IsCongr a := by
  simp_rw [isCongr_iff_smul_eq, eq_comm, imp_self]

theorem isCongr_comm : a.IsCongr b ↔ b.IsCongr a :=
  ⟨IsCongr.symm, IsCongr.symm⟩

theorem isCongr_iff_getElem_eq_getElem_and_getElem_eq_of_ge (hmn : m ≤ n) :
    a.IsCongr b ↔ (∀ {i} (hi : i < m), a[i] = b[i]) ∧
    (∀ {i}, m ≤ i → ∀ (hi' : i < n), a[i] = i) := by
  refine isCongr_comm.trans
    ((isCongr_iff_getElem_eq_getElem_and_getElem_eq_of_le hmn).trans ?_)
  simp_rw [and_congr_left_iff]
  exact fun _ => ⟨fun h _ _ => (h _).symm, fun h _ _ => (h _).symm⟩

theorem IsCongr.trans : a.IsCongr b → b.IsCongr c → a.IsCongr c := by
  simp_rw [isCongr_iff_smul_eq]
  intro h₁ h₂
  exact (h₁.trans h₂)

@[simp] theorem isCongr_one_iff_eq_one : a.IsCongr (1 : PermOf m) ↔ a = 1 := by
  simp_rw [isCongr_iff_smul_eq, one_smul, smul_eq_iff_eq_one]

@[simp] theorem one_isCongr_iff_eq_one : (1 : PermOf m).IsCongr a ↔ a = 1 := by
  simp_rw [isCongr_comm, isCongr_one_iff_eq_one]

theorem isCongr_one_one : (1 : PermOf n).IsCongr (1 : PermOf m) := by
  simp_rw [isCongr_one_iff_eq_one]

theorem IsCongr.inv_inv (hab : a.IsCongr b) : a⁻¹.IsCongr b⁻¹ := by
  simp_rw [isCongr_iff_smul_eq, eq_inv_smul_iff, hab.symm.smul_eq,
    smul_inv_smul, implies_true]

theorem IsCongr.inv_right (hab : a.IsCongr b⁻¹) : a⁻¹.IsCongr b := hab.inv_inv

theorem IsCongr.inv_left (hab : a⁻¹.IsCongr b) : a.IsCongr b⁻¹ := hab.inv_inv

theorem inv_isCongr_iff_isCongr_inv : a⁻¹.IsCongr b ↔ a.IsCongr b⁻¹ :=
  ⟨fun hab => hab.inv_left, fun hab => hab.inv_right⟩

@[simp] theorem inv_isCongr_inv_iff : a⁻¹.IsCongr b⁻¹ ↔ a.IsCongr b :=
  ⟨fun hab => hab.inv_inv, fun hab => hab.inv_inv⟩

theorem IsCongr.mul_mul {a' : PermOf n} {b' : PermOf m} (hab : a.IsCongr b)
    (hab' : a'.IsCongr b') : (a*a').IsCongr (b*b') := by
  simp_rw [isCongr_iff_smul_eq, mul_smul, hab.smul_eq, hab'.smul_eq, implies_true]

theorem IsCongr.eq {a' : PermOf n} (h : a.IsCongr a') : a = a' := by
  ext i hi
  simp_rw [← smul_of_lt hi, h.smul_eq]

@[simp] theorem isCongr_iff_eq {a' : PermOf n} : a.IsCongr a' ↔ a = a' :=
  ⟨IsCongr.eq, fun h => h ▸ isCongr_rfl⟩

@[simps!]
def IsCongrSubgroup (n m : ℕ) : Subgroup (PermOf n × PermOf m) where
  carrier a := a.1.IsCongr a.2
  mul_mem' := IsCongr.mul_mul
  one_mem' := isCongr_one_one
  inv_mem' := IsCongr.inv_inv

@[simp] theorem mem_IsCongrSubgroup_iff (ab : PermOf n × PermOf m) :
    ab ∈ IsCongrSubgroup n m ↔ ab.1.IsCongr ab.2 := Iff.rfl

end IsCongr

section Cast

variable {m n o : ℕ}

/--
`PermOf.cast` re-interprets an `PermOf n` as an `PermOf m`, where `n = m`.
-/
@[inline] protected def cast (hnm : n = m) (a : PermOf n) : PermOf m where
  toVector := a.toVector.cast hnm
  invVector := a.invVector.cast hnm
  getElem_invVector_getElem_toVector := by simp_rw [Vector.getElem_cast]; grind

@[simp]
theorem getElem_cast (hnm : n = m) (a : PermOf n) {i : ℕ} (hi : i < m):
    (a.cast hnm)[i] = a[i] := rfl

@[simp]
theorem getElem_inv_cast (hnm : n = m) (a : PermOf n) {i : ℕ} (hi : i < m):
    (a.cast hnm)⁻¹[i] = a⁻¹[i] := rfl

@[simp] theorem cast_rfl (a : PermOf n) : a.cast rfl = a := rfl

@[simp]
theorem cast_smul (hnm : n = m) (a : PermOf n) (i : ℕ) :
    (a.cast hnm) • i = a • i := by simp_rw [smul_eq_dite, hnm, getElem_cast]

@[simp] theorem cast_one (hnm : n = m) : (1 : PermOf n).cast hnm = 1 := by
  ext
  simp_rw [getElem_cast, getElem_one]

theorem cast_eq_iff (hnm : n = m) {a : PermOf n} {b : PermOf m} :
    a.cast hnm = b ↔ a = b.cast hnm.symm := by
  simp_rw [PermOf.ext_iff, getElem_cast, hnm]

theorem cast_eq_one_iff (hnm : n = m) (a : PermOf n) : a.cast hnm = 1 ↔ a = 1 := by
  simp_rw [cast_eq_iff, cast_one]

@[simp]
theorem cast_inv (hnm : n = m) (a : PermOf n) :
    a⁻¹.cast hnm = (a.cast hnm)⁻¹ := rfl

@[simp]
theorem cast_mul (hnm : n = m) (a b : PermOf n) :
    a.cast hnm * b.cast hnm = (a * b).cast hnm := ext <| fun _ hi => by
  simp only [getElem_cast, getElem_mul]

theorem cast_eq_cast (hnm : n = m) (a : PermOf n) :
    hnm ▸ a = a.cast hnm := by cases hnm ; rfl

@[simp] theorem cast_symm {hnm : n = m} {hmb : m = n} (a : PermOf n) :
    (a.cast hnm).cast hmb = a := rfl

@[simp] theorem cast_trans {hnm : n = m} {hmo : m = o} (a : PermOf n) :
    (a.cast hnm).cast hmo = a.cast (hnm.trans hmo) := rfl

@[simp]
theorem cast_inj {a b : PermOf n} {hnm : n = m} : a.cast hnm = b.cast hnm ↔ a = b := by
  refine ⟨?_, fun H => H ▸ rfl⟩
  simp_rw [PermOf.ext_iff, getElem_cast]
  refine fun H _ hi => ?_
  exact H _ (hnm ▸ hi)

theorem cast_injective (h : n = m) : Function.Injective (PermOf.cast h) := fun _ _ => cast_inj.mp

theorem cast_surjective (h : n = m) : Function.Surjective (PermOf.cast h) :=
  fun a => ⟨a.cast h.symm, a.cast_symm⟩

@[simp] theorem cast_left_isCongr {n' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n = m} :
    (a.cast hnm).IsCongr b ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, cast_smul]

@[simp] theorem cast_right_isCongr {n' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n' = m} :
    a.IsCongr (b.cast hnm) ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, cast_smul]

theorem cast_isCongr_cast_iff_isCongr {n' m' : ℕ} {a : PermOf n}
    {b : PermOf n'} {hnm : n = m} {hnm' : n' = m'} :
    (a.cast hnm).IsCongr (b.cast hnm') ↔ a.IsCongr b := by
  simp_rw [cast_left_isCongr, cast_right_isCongr]

theorem cast_isCongr_cast {k : ℕ}  {a : PermOf n} {hnm : n = m} {hnk : n = k} :
    (a.cast hnk).IsCongr (a.cast hnm) := by
  simp_rw [cast_isCongr_cast_iff_isCongr, isCongr_iff_eq]

/--
When `n = m`, `PermOf n` is multiplicatively congruent to `PermOf m`.
-/

@[simps! apply symm_apply]
def castMulEquiv (hnm : n = m) : PermOf n ≃* PermOf m where
  toFun := PermOf.cast hnm
  invFun := PermOf.cast hnm.symm
  left_inv a := a.cast_symm
  right_inv a := a.cast_symm
  map_mul' _ _ := (cast_mul hnm _ _).symm

end Cast

def pushEq {n : ℕ} (a : PermOf n) : PermOf (n + 1) where
  toVector := a.toVector.push n
  invVector := a.invVector.push n
  getElem_invVector_getElem_toVector := by grind

section PushEq

variable {n m k i : ℕ} {a : PermOf n}

@[grind =]
theorem getElem_pushEq {i : ℕ} {hi : i < n + 1} :
    (a.pushEq)[i] = if hi : i < n then a[i] else n := by grind [pushEq]

@[simp]
theorem getElem_pushEq_of_lt {i : ℕ} (hi : i < n) :
    (a.pushEq)[i] = a[i] := by grind

@[simp]
theorem getElem_pushEq_of_eq : (a.pushEq)[n] = n := by grind

@[simp]
theorem pushEq_inv :
    a⁻¹.pushEq = (a.pushEq)⁻¹ := rfl

@[grind =]
theorem getElem_inv_pushEq {i : ℕ} {hi : i < n + 1} :
    (a.pushEq)⁻¹[i] = if hi : i < n then a⁻¹[i] else n := by grind [pushEq]

@[simp]
theorem pushEq_one : (1 : PermOf n).pushEq = 1 := by grind

@[simp]
theorem pushEq_mul {a b : PermOf n} :
    (a * b).pushEq = a.pushEq * b.pushEq := by grind

@[simp, grind =]
theorem pushEq_smul {i : ℕ} :
    a.pushEq • i = a • i := by grind

theorem pushEq_injective : Function.Injective (pushEq (n := n)) := fun a b hab => by
  simp_rw [PermOf.ext_iff, getElem_pushEq] at hab
  grind

@[simp, grind =]
theorem pushEq_inj {a b : PermOf n} : a.pushEq = b.pushEq ↔ a = b := pushEq_injective.eq_iff

@[simp] theorem pushEq_isCongr {b : PermOf m} :
    a.pushEq.IsCongr b ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, pushEq_smul]

@[simp] theorem isCongr_pushEq {b : PermOf m} : a.IsCongr b.pushEq ↔ a.IsCongr b := by
  simp_rw [isCongr_comm (a := a), pushEq_isCongr]

@[simps! apply]
def pushEqHom : PermOf n →* PermOf (n + 1) where
  toFun a := a.pushEq
  map_mul' _ _ := pushEq_mul
  map_one' := pushEq_one

theorem pushEqHom_injective :
    Function.Injective (pushEqHom (n := n)) := fun _ _ h => pushEq_injective h

end PushEq

def popOfEq {n : ℕ} (a : PermOf (n + 1)) (ha : a[n] = n) : PermOf n where
  toVector := a.toVector.pop
  invVector := a.invVector.pop
  getElem_invVector_getElem_toVector := by grind

section PopOfEq

variable {n m i k : ℕ} (a : PermOf (n + 1)) (ha : a[n] = n)

@[simp, grind =] theorem getElem_popOfEq (him : i < n) :
    (a.popOfEq ha)[i] = a[i] := Vector.getElem_pop _

@[simp]
theorem popOfEq_smul : a.popOfEq ha • i = a • i := by grind

@[simp] theorem popOfEq_inv {ha : a⁻¹[n] = n} : a⁻¹.popOfEq ha =
    (a.popOfEq ((a.getElem_inv_eq_iff _ _).mp ha).symm)⁻¹ := rfl

@[simp, grind =]
theorem getElem_inv_popOfEq (hi : i < n) :
    (a.popOfEq ha)⁻¹[i] = a⁻¹[i] := Vector.getElem_pop _

@[simp]
theorem popOfEq_one :
    ((1 : PermOf (n + 1)).popOfEq (getElem_one _)) = (1 : PermOf n) := by
  ext
  simp_rw [getElem_popOfEq, getElem_one]

theorem popOfEq_mul {a b : PermOf (n + 1)} (ha : a[n] = n) (hb : b[n] = n) :
    (a * b).popOfEq (by simp_rw [getElem_mul, hb, ha]) = a.popOfEq ha * b.popOfEq hb := by grind

@[simp] theorem popOfEq_pushEq {a : PermOf n} :
    a.pushEq.popOfEq getElem_pushEq_of_eq = a := by grind

@[simp]
theorem pushEq_popOfEq :
    (a.popOfEq ha).pushEq = a := by grind

theorem getElem_pushEq_popOfEq_of_lt (hi : i < n) :
    ((a.popOfEq ha).pushEq)[i] = a[i] := by grind

@[simp, grind =]
theorem popOfEq_inj {a b : PermOf (n + 1)} {ha hb} : a.popOfEq ha = b.popOfEq hb ↔ a = b := by
  simp_rw [eq_iff_smul_eq_smul, popOfEq_smul]

theorem popOfEq_surjective (b : PermOf n) :
    ∃ (a : PermOf (n + 1)), ∃ (ha : a[n] = n), a.popOfEq ha = b :=
  ⟨_, _, b.popOfEq_pushEq⟩

@[simp] theorem popOfEq_isCongr {b : PermOf m} :
    (a.popOfEq ha).IsCongr b ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, popOfEq_smul]

@[simp] theorem isCongr_popOfEq {b : PermOf m} :
    b.IsCongr (a.popOfEq ha) ↔ b.IsCongr a := by
  simp_rw [isCongr_comm (a := b), popOfEq_isCongr]

theorem popOfEq_cast {hnm : n + 1 = m + 1} {ha : (a.cast hnm)[m] = m} :
    (a.cast hnm).popOfEq ha =
    (a.popOfEq (by rw [getElem_cast] at ha ; simp_rw [Nat.succ_injective hnm, ha])).cast
    (Nat.succ_injective hnm) := by
  ext
  simp_rw [getElem_cast, getElem_popOfEq, getElem_cast]

theorem exists_pushEq_apply {a : PermOf (n + 1)} :
    (∃ b : PermOf n, b.pushEq = a) ↔ a[n] = n :=
  ⟨fun ⟨_, hb⟩ => hb ▸ getElem_pushEq_of_eq,
    fun ha => ⟨a.popOfEq ha, a.pushEq_popOfEq ha⟩⟩

theorem range_pushEq :
    Set.range (pushEq (n := n)) = {a : PermOf (n + 1) | a[n] = n} := Set.ext <| fun _ => by
  simp_rw [Set.mem_range, exists_pushEq_apply, Set.mem_setOf_eq]

theorem coe_range_pushEqHom :
    (pushEqHom (n := n)).range = {a : PermOf (n + 1) | a[n] = n} := range_pushEq

end PopOfEq

def push {n : ℕ} (i : Fin (n + 1)) : PermOf n → PermOf (n + 1) :=
  i.lastCases pushEq (fun i a => a.pushEq.swap a⁻¹[i.1] n (by grind))

def pop {n : ℕ} (a : PermOf (n + 1)) : PermOf n := (a.swap a⁻¹[n] n).popOfEq (by grind)

section PushPop

variable {n : ℕ} {i : Fin (n + 1)}

@[grind =]
theorem getElem_push {a : PermOf n} {k} {hk : k < n + 1} :
    (a.push i)[k] = if i < n then
    if hk : k < n then if a[k] = i then n else a[k] else i
    else if hk : k < n then a[k] else n := by
  unfold push
  cases i using Fin.lastCases <;>
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc] <;> grind

@[grind =]
theorem getElem_inv_push {a : PermOf n} {k} {hk : k < n + 1} :
    (a.push i)⁻¹[k] = if hi : i < n then
    (if hk : k < n then if k = i then n else a⁻¹[k] else a⁻¹[i])
    else if hk : k < n then a⁻¹[k] else n := by
  unfold push
  cases i using Fin.lastCases <;>
    simp only [Fin.lastCases_last, Fin.lastCases_castSucc] <;> grind

@[grind =]
theorem getElem_pop {a : PermOf (n + 1)} {k} {hk : k < n} :
    (a.pop)[k] = if a[k] = n then a[a[k]] else if k = n then n else a[k] := by grind [pop]

@[grind =]
theorem getElem_inv_pop {a : PermOf (n + 1)} {k} {hk : k < n} :
    (a.pop)⁻¹[k] = if a⁻¹[k] = n then a⁻¹[a⁻¹[k]] else if k = n then n else a⁻¹[k] := by
  grind [pop]

@[simp, grind =]
theorem push_pop_getElem_last {a : PermOf (n + 1)} :
    a.pop.push ⟨a[n], a.getElem_lt⟩ = a := by grind

@[simp, grind =]
theorem pop_push {a : PermOf n} : (a.push i).pop = a := by grind

@[simp, grind =]
theorem getElem_last_push {a : PermOf n} : (a.push i)[n] = i := by grind

end PushPop

def decomposeFin {n : ℕ} : PermOf (n + 1) ≃ Fin (n + 1) × PermOf n where
  toFun a := (⟨a[n], a.getElem_lt⟩, a.pop)
  invFun ia := ia.2.push ia.1
  left_inv a := by grind
  right_inv ia := by grind

@[simp]
theorem card_permOf {n : ℕ} : Nat.card (PermOf n) = n.factorial := by
  induction n with | zero | succ n IH
  · exact Nat.card_eq_of_equiv_fin zeroEquivFinOne
  · rw [Nat.card_congr decomposeFin, Nat.card_prod, IH, Nat.card_fin, Nat.factorial_succ]

@[simp]
theorem card_permOf_of_fintype {n : ℕ} [Fintype (PermOf n)] :
    Fintype.card (PermOf n) = n.factorial := by
  rw [← Nat.card_eq_fintype_card, card_permOf]

def castAdd {n : ℕ} (a : PermOf n) : (k : ℕ) → PermOf (n + k)
  | 0 => a
  | k + 1 => (a.castAdd k).pushEq

section CastAdd

variable {n m k k' : ℕ} {a : PermOf n}

@[simp]
theorem castAdd_zero : a.castAdd 0 = a := rfl

@[simp]
theorem castAdd_of_eq_zero (h : k = 0) : a.castAdd k = a.cast (h ▸ rfl) := by
  cases h
  exact castAdd_zero

@[simp]
theorem one_castAdd : a.castAdd 1 = a.pushEq := rfl

@[simp]
theorem castAdd_succ :
    a.castAdd (k + 1) = (a.castAdd k).pushEq := rfl

@[simp]
theorem castAdd_smul {i : ℕ} :
    a.castAdd k • i = a • i := by
  induction k with | zero => _ | succ k IH => _
  · rfl
  · simp_rw [castAdd_succ, pushEq_smul, IH]

@[simp]
theorem castAdd_succ_eq_cast_castAdd_pushEq :
    a.castAdd (k + 1) = (a.pushEq.castAdd k).cast (Nat.add_right_comm _ _ _) := by
  simp_rw [eq_iff_smul_eq_smul, cast_smul, castAdd_smul, pushEq_smul, implies_true]

theorem castAdd_inv : a⁻¹.castAdd k = (a.castAdd k)⁻¹ := by
  induction k with | zero => _ | succ k IH => _
  · rfl
  · simp_rw [castAdd_succ, IH, pushEq_inv]

@[simp]
theorem castAdd_one : (1 : PermOf n).castAdd k = 1 := by
  induction k with | zero => _ | succ k IH => _
  · rfl
  · simp_rw [castAdd_succ, IH, pushEq_one]

@[simp]
theorem castAdd_mul {a b : PermOf n} :
    (a * b).castAdd k = a.castAdd k * b.castAdd k := by
  induction k with | zero => _ | succ k IH => _
  · rfl
  · simp_rw [castAdd_succ, IH, pushEq_mul]

@[simp]
theorem castAdd_inj {a b : PermOf n} : a.castAdd k = b.castAdd k ↔ a = b := by
  induction k with | zero => _ | succ k IH => _
  · rfl
  · simp_rw [castAdd_succ, pushEq_inj, IH]

theorem castAdd_injective : Function.Injective (castAdd (n := n) (k := k)) :=
  fun _ _ => castAdd_inj.mp

@[simp]
theorem getElem_castAdd {i : ℕ} (hi : i < n + k) :
    (a.castAdd k)[i] = a • i := (smul_of_lt _).symm.trans castAdd_smul

@[simp] theorem castAdd_isCongr {b : PermOf m} :
    (a.castAdd k).IsCongr b ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, castAdd_smul]

@[simp] theorem isCongr_castAdd {b : PermOf m} : a.IsCongr (b.castAdd k) ↔ a.IsCongr b := by
  simp_rw [isCongr_comm (a := a), castAdd_isCongr]

theorem castAdd_comm : (a.castAdd k).castAdd k' =
    ((a.castAdd k').castAdd k).cast (Nat.add_right_comm _ _ _) := by
  simp_rw [eq_iff_smul_eq_smul, cast_smul, castAdd_smul, implies_true]

theorem castAdd_assoc : (a.castAdd k).castAdd k' =
    (a.castAdd (k + k')).cast (add_assoc _ _ _).symm := by
  simp_rw [eq_iff_smul_eq_smul, cast_smul, castAdd_smul, implies_true]

@[simps! apply]
def castAddHom (k : ℕ) : PermOf n →* PermOf (n + k) where
  toFun a := a.castAdd k
  map_mul' _ _ := castAdd_mul
  map_one' := castAdd_one

theorem castAddHom_injective :
    Function.Injective (castAddHom (n := n) k) := fun _ _ h => castAdd_injective h

end CastAdd

def castGE {m n : ℕ} (hnm : n ≤ m) (a : PermOf n) : PermOf m :=
  (a.castAdd _).cast (Nat.add_sub_cancel' hnm)

section CastGE

variable {n m k i : ℕ} {a : PermOf n}

@[simp]
theorem castGE_smul {hnm : n ≤ m} :
    a.castGE hnm • i = a • i := by
  unfold castGE
  simp_rw [cast_smul, castAdd_smul]

theorem castGE_of_eq (hnm : n = m) :
    a.castGE hnm.le = a.cast hnm := by
  simp_rw [eq_iff_smul_eq_smul, castGE_smul, cast_smul, implies_true]

@[simp] theorem castGE_rfl  :
    a.castGE le_rfl = a := by simp_rw [castGE_of_eq rfl, cast_rfl]

@[simp]
theorem succ_self_castGE : a.castGE (Nat.le_succ _) = a.pushEq := by
  simp_rw [eq_iff_smul_eq_smul, castGE_smul, pushEq_smul, implies_true]

theorem castGE_inv (hnm : n ≤ m) : a⁻¹.castGE hnm = (a.castGE hnm)⁻¹ := by
  unfold castGE
  simp_rw [castAdd_inv, cast_inv]

@[simp]
theorem castGE_one (hnm : n ≤ m) : (1 : PermOf n).castGE hnm = 1 := by
  unfold castGE
  simp_rw [castAdd_one, cast_one]

@[simp]
theorem castGE_mul {a b : PermOf n} (hnm : n ≤ m) :
    (a * b).castGE hnm = a.castGE hnm * b.castGE hnm := by
  unfold castGE
  simp_rw [castAdd_mul, cast_mul]

@[simp]
theorem castGE_inj {a b : PermOf n} {hnm : n ≤ m} : a.castGE hnm = b.castGE hnm ↔ a = b := by
  unfold castGE
  simp_rw [cast_inj, castAdd_inj]

theorem castGE_injective (hnm : n ≤ m) : Function.Injective (castGE hnm) :=
  fun _ _ => castGE_inj.mp

@[simp]
theorem getElem_castGE {i : ℕ} (hnm : n ≤ m) (hi : i < m) :
    (a.castGE hnm)[i] = a • i := (smul_of_lt _).symm.trans castGE_smul

@[simp] theorem castGE_isCongr {b : PermOf k} {hnm : n ≤ m} :
    (a.castGE hnm).IsCongr b ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, castGE_smul]

@[simp] theorem isCongr_castGE {b : PermOf k} {hnm : k ≤ m} :
    a.IsCongr (b.castGE hnm) ↔ a.IsCongr b := by
  simp_rw [isCongr_comm (a := a), castGE_isCongr]

@[simp] theorem castGE_trans {hnm : n ≤ m} {hmk : m ≤ k} :
    (a.castGE hnm).castGE hmk = a.castGE (hnm.trans hmk) := by
  simp_rw [eq_iff_smul_eq_smul, castGE_smul, implies_true]

theorem isCongr_iff_eq_castGE_of_le {b : PermOf m} (hnm : n ≤ m) :
    a.IsCongr b ↔ b = a.castGE hnm := by
  simp_rw [eq_iff_smul_eq_smul, castGE_smul, isCongr_iff_smul_eq, eq_comm]

theorem isCongr_iff_eq_castGE_of_ge {b : PermOf m} (hmn : m ≤ n) :
    a.IsCongr b ↔ a = b.castGE hmn := by
  rw [isCongr_comm, isCongr_iff_eq_castGE_of_le hmn]

@[simp] theorem pushEq_pushEq :
    a.pushEq.pushEq = a.castGE (by omega) := by
  simp_rw [eq_iff_smul_eq_smul, castGE_smul, pushEq_smul, implies_true]

@[simp] theorem castGE_pushEq (h : n ≤ m) :
    (a.castGE h).pushEq = a.castGE (h.trans (Nat.le_succ _)) := by
  simp_rw [eq_iff_smul_eq_smul, pushEq_smul, castGE_smul, implies_true]

@[simp] theorem pushEq_castGE (h : n + 1 ≤ m) :
    a.pushEq.castGE h = a.castGE ((Nat.le_succ _).trans h) := by
  simp_rw [eq_iff_smul_eq_smul, castGE_smul, pushEq_smul, implies_true]

@[simps! apply]
def castGEHom (hnm : n ≤ m) : PermOf n →* PermOf m where
  toFun a := a.castGE hnm
  map_mul' _ _ := castGE_mul hnm
  map_one' := castGE_one hnm

theorem castGEHom_injective {hnm : n ≤ m} :
    (⇑(castGEHom hnm)).Injective :=
  fun _ _ h => castGE_injective hnm h

end CastGE

def ofFixGENat {n : ℕ} : FixGENat n →* PermOf n where
  toFun := fun ⟨e, he⟩ => ofFn (fun i => e i) (fun i => e⁻¹ i)
    (fun _ => apply_lt_of_lt_of_mem_fixGENat he (Fin.isLt _))
    (fun _ => symm_apply_apply _ _)
  map_one' := PermOf.ext <| fun _ _ => by
    simp_rw [getElem_ofFn, getElem_one, one_apply]
  map_mul' := fun _ _ => PermOf.ext <| fun _ _ => by
    simp_rw [getElem_mul, getElem_ofFn, mul_apply]

section OfFixGENat

variable {n : ℕ}

theorem getElem_ofFixGENat_apply (e : FixGENat n)
    {i : ℕ} (hi : i < n) : (ofFixGENat e)[i] = e.1 i := by
  unfold ofFixGENat
  simp_rw [MonoidHom.coe_mk, OneHom.coe_mk, getElem_ofFn]

theorem getElem_inv_ofFixGENat_apply_mk  (e : FixGENat n)
    {i : ℕ} (hi : i < n) : (ofFixGENat e)⁻¹[i] = e⁻¹.1 i := by
  unfold ofFixGENat
  simp_rw [MonoidHom.coe_mk, OneHom.coe_mk, InvMemClass.coe_inv, getElem_inv_ofFn]

@[simp]
theorem ofFixGENat_smul (e : FixGENat n) {i : ℕ} :
    ofFixGENat e • i = e.1 i := by
  simp_rw [smul_eq_dite, getElem_ofFixGENat_apply, dite_eq_left_iff, not_lt]
  exact fun hi => (apply_eq_of_ge_of_mem_fixGENat e.2 hi).symm

theorem ofFixGENat_injective : Injective (ofFixGENat (n := n)) :=
    fun ⟨_, _⟩ ⟨_, _⟩ h => Subtype.ext <| Equiv.ext <| fun _ => by
  simp_rw [eq_iff_smul_eq_smul, ofFixGENat_smul] at h
  exact h

end OfFixGENat


/--
`natPerm` is the monoid homomorphism from `PermOf n` to `Perm ℕ`.
-/

@[simps!]
def natPerm {n : ℕ} : PermOf n →* Perm ℕ := MulAction.toPermHom (PermOf n) ℕ

section NatPerm

variable {n : ℕ}

theorem natPerm_injective : Function.Injective (natPerm (n := n)) :=
  MulAction.toPerm_injective

theorem natPerm_inj {a b : PermOf n} : natPerm a = natPerm b ↔ a = b :=
  natPerm_injective.eq_iff

theorem natPerm_mem_fixGENat {a : PermOf n} : natPerm a ∈ FixGENat n :=
  mem_fixGENat_of_ge_imp_apply_eq (fun _ => smul_of_ge)

@[simp]
theorem ofFixGENat_natPerm {a : PermOf n} :
    ofFixGENat ⟨a.natPerm, natPerm_mem_fixGENat⟩ = a :=
  FaithfulSMul.eq_of_smul_eq_smul <| fun (_ : ℕ) => by
  simp_rw [ofFixGENat_smul, natPerm_apply_apply]

@[simp]
theorem natPerm_ofFixGENat {e : FixGENat n} :
    natPerm (ofFixGENat e) = e.1 := Equiv.ext <| fun _ => by
  simp_rw [natPerm_apply_apply, ofFixGENat_smul]

theorem exists_natPerm_apply_iff_mem_finitePermNat {e : Perm ℕ} :
    (∃ a : PermOf n, natPerm a = e) ↔ e ∈ FixGENat n := by
  refine ⟨?_, fun he => ?_⟩
  · rintro ⟨a, rfl⟩
    exact natPerm_mem_fixGENat
  · exact ⟨ofFixGENat ⟨e, he⟩, natPerm_ofFixGENat⟩

theorem range_natPerm : natPerm (n := n).range = FixGENat n := SetLike.ext <| fun _ => by
  simp_rw [MonoidHom.mem_range, exists_natPerm_apply_iff_mem_finitePermNat]

theorem ofFixGENat_surjective : Surjective (ofFixGENat (n := n)) := fun _ =>
  ⟨⟨_, natPerm_mem_fixGENat⟩, ofFixGENat_natPerm⟩

theorem natPerm_lt_iff_lt (a : PermOf n) {i : ℕ} : natPerm a i < n ↔ i < n := by
  rw [natPerm_apply_apply, smul_lt_iff_lt]

@[simp]
theorem natPerm_eq_iff_isCongr {a : PermOf n} {m : ℕ} {b : PermOf m} :
    a.natPerm = b.natPerm ↔ a.IsCongr b := by
  simp_rw [Equiv.ext_iff, natPerm_apply_apply, isCongr_iff_smul_eq]

theorem IsCongr.natPerm_eq {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.IsCongr b) : a.natPerm = b.natPerm := natPerm_eq_iff_isCongr.mpr hab

theorem natPerm_swap (a : PermOf n) {i j hi hj} :
    natPerm (swap a i j hi hj) = natPerm a * Equiv.swap i j := by
  ext : 1
  simp_rw [Perm.mul_apply, natPerm_apply_apply, swap_smul_eq_smul_swap]

@[simp]
theorem natPerm_one_swap {i j hi hj} :
    natPerm (n := n) (swap 1 i j hi hj) = Equiv.swap i j := by
  simp_rw [natPerm_swap, map_one, one_mul]

end NatPerm


open Perm in
@[simps! apply_coe symm_apply]
def natPermEquiv {n : ℕ} : PermOf n ≃* FixGENat n :=
  MonoidHom.toMulEquiv (MonoidHom.codRestrict natPerm _ fun _ => natPerm_mem_fixGENat) ofFixGENat
  (MonoidHom.ext <| fun _ => ofFixGENat_natPerm)
  (MonoidHom.ext <| fun _ => by simp_rw [MonoidHom.comp_apply,
    MonoidHom.codRestrict_apply, MonoidHom.id_apply, natPerm_ofFixGENat])

section NatPermEquiv

variable {n m : ℕ}

@[simp]
theorem natPermEquiv_apply_coe_apply {a : PermOf n} {i : ℕ} :
    (natPermEquiv a).1 i = a • i := rfl

@[simp]
theorem natPermEquiv_apply_coe_symm_apply {a : PermOf n} {i : ℕ} :
    (natPermEquiv a).1.symm i = a⁻¹ • i := rfl

@[simp]
theorem natPermEquiv_symm_apply_smul {e : FixGENat n} {i : ℕ} :
    (natPermEquiv.symm e) • i = e.1 i := ofFixGENat_smul _

theorem natPermEquiv_castGE {a : PermOf n} (hnm : n ≤ m) :
    (natPermEquiv (a.castGE hnm)) =
    Subgroup.inclusion (fixGENat_mono hnm) (natPermEquiv a) :=
    Subtype.ext <| Equiv.ext <| fun _ => by
  simp_rw [Subgroup.coe_inclusion, natPermEquiv_apply_coe_apply, castGE_smul]

end NatPermEquiv

def minLen {n : ℕ} (a : PermOf n) : ℕ := match n with
  | 0 => 0
  | (n + 1) => if ha : a[n] = n then (a.popOfEq ha).minLen else n + 1

section MinLen

variable {n : ℕ}

@[simp] theorem minLen_zero {a : PermOf 0} : a.minLen = 0 := rfl

theorem minLen_succ {a : PermOf (n + 1)} :
    a.minLen = if ha : a[n] = n then (a.popOfEq ha).minLen else n + 1 := rfl

theorem minLen_succ_of_getElem_eq {a : PermOf (n + 1)} (ha : a[n] = n) :
    a.minLen = (a.popOfEq ha).minLen := by
  simp_rw [minLen_succ, ha, dite_true]

theorem minLen_succ_of_getElem_ne {a : PermOf (n + 1)} (ha : a[n] ≠ n) :
    a.minLen = n + 1 := by
  simp_rw [minLen_succ, ha, dite_false]

@[simp] theorem minLen_le {a : PermOf n} : a.minLen ≤ n := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero, le_rfl]
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha]
      exact IH.trans (Nat.le_succ _)
    · simp_rw [minLen_succ_of_getElem_ne ha, le_rfl]

@[simp] theorem minLen_eq_iff {a : PermOf n} : a.minLen = n ↔ ∀ (hn : n ≠ 0),
    a[n - 1]'(Nat.pred_lt hn) ≠ n - 1 := by
  simp_rw [← minLen_le.ge_iff_eq]
  cases n with | zero => _ | succ n => _
  · simp_rw [minLen_zero, le_rfl, ne_eq, not_true_eq_false, IsEmpty.forall_iff]
  · simp_rw [Nat.add_sub_cancel, ne_eq, Nat.succ_ne_zero, not_false_eq_true, forall_true_left]
    by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha, ha, not_true_eq_false, iff_false, not_le,
        Nat.lt_succ_iff]
      exact minLen_le
    · simp_rw [minLen_succ_of_getElem_ne ha, le_rfl, ha, not_false_eq_true]

@[simp] theorem succ_minLen_le_of_getElem_eq {a : PermOf (n + 1)} (ha : a[n] = n) :
    a.minLen ≤ n := by simp_rw [minLen_succ_of_getElem_eq ha, minLen_le]

theorem minLen_one : (1 : PermOf n).minLen = 0 := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · rw [minLen_succ_of_getElem_eq (getElem_one _), popOfEq_one, IH]

theorem eq_one_of_minLen_eq_zero {a : PermOf n} (ha : a.minLen = 0) : a = 1 := by
  induction n with | zero => _ | succ n IH => _
  · exact Subsingleton.elim _ _
  · by_cases ha' : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha'] at ha
      have ha := IH ha
      simp_rw [PermOf.ext_iff, getElem_one, getElem_popOfEq] at ha
      simp_rw [PermOf.ext_iff, getElem_one, Nat.lt_succ_iff, le_iff_lt_or_eq]
      exact fun _ hi => hi.elim (ha _) (fun hi => hi ▸ ha')
    · simp_rw [minLen_succ_of_getElem_ne ha', Nat.succ_ne_zero] at ha

@[simp] theorem minLen_eq_zero_iff_eq_one {a : PermOf n} : a.minLen = 0 ↔ a = 1 :=
  ⟨eq_one_of_minLen_eq_zero, fun h => h ▸ minLen_one⟩

@[simp] theorem minLen_inv {a : PermOf n} : a⁻¹.minLen = a.minLen := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha,
        minLen_succ_of_getElem_eq (getElem_inv_eq_self_of_getElem_eq_self ha), popOfEq_inv, IH]
    · simp_rw [minLen_succ_of_getElem_ne ha,
        minLen_succ_of_getElem_ne (getElem_inv_ne_self_of_getElem_ne_self ha)]

@[simp] theorem minLen_cast {m : ℕ} {a : PermOf n} {hnm : n = m} :
    (a.cast hnm).minLen = a.minLen := by
  cases hnm
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minLen_zero]
  · simp_rw [minLen_succ, getElem_cast, popOfEq_cast, IH]

theorem minLen_popOfEq {a : PermOf (n + 1)} {ha : a[n] = n} :
    (a.popOfEq ha).minLen = a.minLen := (minLen_succ_of_getElem_eq _).symm

theorem minLen_pushEq {a : PermOf n} :
    a.pushEq.minLen = a.minLen := by
  rw [minLen_succ_of_getElem_eq (getElem_pushEq_of_eq), popOfEq_pushEq]

@[simp] theorem minLen_castGE {m : ℕ} {a : PermOf n} {hnm : n ≤ m} :
    (a.castGE hnm).minLen = a.minLen := by
  induction m generalizing n with | zero => _ | succ m IH => _
  · simp_rw [Nat.le_zero] at hnm
    cases hnm
    simp_rw [minLen_zero]
  · rcases hnm.eq_or_lt with rfl | hnm
    · simp_rw [castGE_of_eq, minLen_cast]
    · simp_rw [Nat.lt_succ_iff] at hnm
      simp_rw [← castGE_pushEq hnm, minLen_pushEq, IH]

@[simp] theorem getElem_of_ge_minLen {a : PermOf n} {i : ℕ} (hi : a.minLen ≤ i) {hi' : i < n} :
    a[i] = i := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [Nat.not_lt_zero] at hi'
  · by_cases ha : a[n] = n
    · simp_rw [minLen_succ_of_getElem_eq ha] at hi
      simp_rw [Nat.lt_succ_iff, le_iff_lt_or_eq] at hi'
      rcases hi' with hi' | rfl
      · exact ((a.getElem_popOfEq ha hi').symm).trans (IH hi)
      · exact ha
    · simp_rw [minLen_succ_of_getElem_ne ha] at hi
      exact (hi'.not_ge hi).elim

@[simp] theorem smul_of_ge_minLen {a : PermOf n} {i : ℕ} (hi : a.minLen ≤ i) : a • i = i := by
  simp_rw [smul_eq_dite, dite_eq_right_iff]
  exact fun _ => getElem_of_ge_minLen hi

theorem IsCongr.minLen_eq {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.IsCongr b) : a.minLen = b.minLen := by
  rcases Nat.le_or_le m n with hmn | hnm
  · simp_rw [isCongr_iff_eq_castGE_of_ge hmn] at hab
    simp_rw [hab, minLen_castGE]
  · simp_rw [isCongr_iff_eq_castGE_of_le hnm] at hab
    simp_rw [hab, minLen_castGE]

theorem IsCongr.minLen_le {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.IsCongr b) : a.minLen ≤ m := hab.minLen_eq ▸ b.minLen_le

theorem IsCongr.minLen_le_min {a : PermOf n} {m : ℕ} {b : PermOf m}
    (hab : a.IsCongr b) : a.minLen ≤ n ⊓ m := le_inf a.minLen_le hab.minLen_le

end MinLen

def minPerm {n : ℕ} (a : PermOf n) : PermOf a.minLen := match n with
  | 0 => 1
  | (n + 1) =>
    if ha : a[n] = n
    then (a.popOfEq ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm
    else a.cast (minLen_succ_of_getElem_ne ha).symm

section MinPerm

variable {n m : ℕ}

@[simp] theorem minPerm_zero {a : PermOf 0} : a.minPerm = 1 := rfl

theorem minPerm_succ {a : PermOf (n + 1)} :
    a.minPerm = if ha : a[n] = n
    then (a.popOfEq ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm
    else a.cast (minLen_succ_of_getElem_ne ha).symm := rfl

@[simp] theorem minPerm_succ_of_getElem_eq {a : PermOf (n + 1)}  (ha : a[n] = n) :
    a.minPerm = (a.popOfEq ha).minPerm.cast (minLen_succ_of_getElem_eq _).symm := by
  simp_rw [minPerm_succ, ha, dite_true]

@[simp] theorem minPerm_succ_of_getElem_ne {a : PermOf (n + 1)} (ha : a[n] ≠ n) :
    a.minPerm = a.cast (minLen_succ_of_getElem_ne ha).symm := by
  simp_rw [minPerm_succ, ha, dite_false]

theorem minPerm_smul {a : PermOf n} {i : ℕ} : a.minPerm • i = a • i := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minPerm_zero, Unique.eq_default, default_eq]
  · simp_rw [minPerm_succ]
    split_ifs
    · simp_rw [cast_smul, IH, popOfEq_smul]
    · simp_rw [cast_smul]

@[simp] theorem getElem_minPerm {a : PermOf n} {i : ℕ} (hi : i < a.minLen) :
    (a.minPerm)[i] = a[i]'(hi.trans_le minLen_le) :=
  (smul_of_lt _).symm.trans (minPerm_smul.trans (smul_of_lt _))

@[simp] theorem getElem_inv_minPerm {a : PermOf n} {i : ℕ} (hi : i < a.minLen) :
    (a.minPerm)⁻¹[i] = a⁻¹[i]'(hi.trans_le minLen_le) := by
  simp_rw [← smul_of_lt, inv_smul_eq_iff, minPerm_smul, smul_inv_smul]

@[simp]
theorem castGE_minPerm_minLen_le {a : PermOf n} : a.minPerm.castGE minLen_le = a := by
  simp_rw [eq_iff_smul_eq_smul, castGE_smul, minPerm_smul, implies_true]


theorem isCongr_minPerm_left {a : PermOf n} {b : PermOf m} :
    a.minPerm.IsCongr b ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, minPerm_smul]

theorem isCongr_minPerm_right {a : PermOf n} {b : PermOf m} :
    a.IsCongr b.minPerm ↔ a.IsCongr b := by
  simp_rw [isCongr_iff_smul_eq, minPerm_smul]

@[simp] theorem minPerm_isCongr {a : PermOf n} : a.minPerm.IsCongr a := by
  simp_rw [isCongr_minPerm_left, isCongr_rfl]

@[simp] theorem isCongr_minPerm {a : PermOf n} : a.IsCongr a.minPerm := minPerm_isCongr.symm

theorem natPerm_minPerm {a : PermOf n} : natPerm a.minPerm = natPerm a := by
  simp_rw [natPerm_eq_iff_isCongr, minPerm_isCongr]

@[simp] theorem isCongr_minPerm_minPerm {a : PermOf n} {b : PermOf m} :
    a.minPerm.IsCongr b.minPerm ↔ a.IsCongr b := by
  simp_rw [isCongr_minPerm_right, isCongr_minPerm_left]

theorem IsCongr.minPerm_left {a : PermOf n} {b : PermOf m}
    (hab : a.IsCongr b) : a.minPerm.IsCongr b :=
  isCongr_minPerm_left.mpr hab

theorem IsCongr.minPerm_right {a : PermOf n} {b : PermOf m}
    (hab : a.IsCongr b) : a.IsCongr b.minPerm :=
  isCongr_minPerm_right.mpr hab

theorem IsCongr.minPerm_minPerm {a : PermOf n} {b : PermOf m}
    (hab : a.IsCongr b) : a.minPerm.IsCongr b.minPerm :=
  isCongr_minPerm_minPerm.mpr hab

theorem isCongr_minPerm_inv_inv_minPerm {a : PermOf n} : a⁻¹.minPerm.IsCongr (a.minPerm)⁻¹ := by
  simp_rw [isCongr_minPerm_left, inv_isCongr_inv_iff, isCongr_minPerm_right, isCongr_iff_eq]

@[simp] theorem minPerm_one : (1 : PermOf n).minPerm = 1 := by
  ext
  simp_rw [getElem_minPerm, getElem_one]

@[simp] theorem minPerm_inv {a : PermOf n} :
    a⁻¹.minPerm = a.minPerm⁻¹.cast minLen_inv.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_inv_minPerm]

@[simp] theorem minPerm_cast {m : ℕ} {a : PermOf n} (hnm : n = m) :
    (a.cast hnm).minPerm = a.minPerm.cast minLen_cast.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_minPerm]

@[simp] theorem minPerm_popOfEq {a : PermOf (n + 1)} {ha : a[n] = n} :
    (a.popOfEq ha).minPerm = a.minPerm.cast (minLen_succ_of_getElem_eq _) := by
  ext
  simp_rw [getElem_minPerm, getElem_popOfEq, getElem_cast, getElem_minPerm]

theorem minPerm_pushEq {a : PermOf n} :
    a.pushEq.minPerm = a.minPerm.cast minLen_pushEq.symm := by
  simp_rw [eq_iff_smul_eq_smul, cast_smul, minPerm_smul, pushEq_smul, implies_true]

@[simp] theorem minPerm_castGE {m : ℕ} {a : PermOf n} (hnm : n ≤ m) :
    (a.castGE hnm).minPerm = a.minPerm.cast minLen_castGE.symm := by
  simp_rw [eq_iff_smul_eq_smul, cast_smul, minPerm_smul, castGE_smul, implies_true]

theorem eq_one_of_minPerm_eq_one {a : PermOf n} (ha : a.minPerm = 1) : a = 1 := by
  induction n with | zero => _ | succ n IH => _
  · exact Subsingleton.elim _ _
  · by_cases ha' : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha', cast_eq_one_iff] at ha
      have ha := IH ha
      simp_rw [PermOf.ext_iff, getElem_one, getElem_popOfEq] at ha
      simp_rw [PermOf.ext_iff, getElem_one, Nat.lt_succ_iff, le_iff_lt_or_eq]
      exact fun _ hi => hi.elim (ha _) (fun hi => hi ▸ ha')
    · simp_rw [minPerm_succ_of_getElem_ne ha', cast_eq_one_iff] at ha
      exact ha

@[simp]
theorem minPerm_eq_one_iff_eq_one {a : PermOf n} : a.minPerm = 1 ↔ a = 1 :=
  ⟨eq_one_of_minPerm_eq_one, fun h => h ▸ minPerm_one⟩

@[simp] theorem minLen_minPerm {a : PermOf n} : a.minPerm.minLen = a.minLen := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [minPerm_zero, Unique.eq_default, Unique.default_eq (1 : PermOf 0)]
  · by_cases ha : a[n] = n
    · simp_rw [minPerm_succ_of_getElem_eq ha, minLen_cast, IH, minLen_popOfEq]
    · simp_rw [minPerm_succ_of_getElem_ne ha, minLen_cast]

@[simp] theorem minPerm_minPerm {a : PermOf n} :
    a.minPerm.minPerm = a.minPerm.cast minLen_minPerm.symm := by
  ext
  simp_rw [getElem_minPerm, getElem_cast, getElem_minPerm]

end MinPerm

end PermOf

structure FinitePerm where
  len : ℕ
  toPermOf : PermOf len
  toPermOf_minLen : toPermOf.minLen = len
  deriving DecidableEq

namespace FinitePerm

open PermOf Equiv Equiv.Perm

variable {n m : ℕ} {a : FinitePerm}

@[ext] theorem ext {b : FinitePerm} (hab : a.toPermOf.IsCongr b.toPermOf) : a = b := by
  cases a with | mk n a hna => _
  cases b with | mk m b hmb => _
  simp_rw [FinitePerm.mk.injEq]
  have hnm : n = m := hna.symm.trans (hab.minLen_eq.trans hmb)
  subst hnm
  simp_rw [isCongr_iff_eq] at hab
  simp_rw [heq_eq_eq, true_and, hab]

instance : SMul FinitePerm ℕ where smul a i := a.toPermOf • i

theorem smul_eq_dite (i : ℕ) :
    a • i = if h : i < a.len then a.toPermOf[i] else i := PermOf.smul_eq_dite _

theorem smul_of_lt {i : ℕ} (h : i < a.len) :
    a • i = a.toPermOf[i] := PermOf.smul_of_lt _

theorem smul_of_ge {i : ℕ} : a.len ≤ i → a • i = i := PermOf.smul_of_ge

@[simp]
theorem toPermOf_smul {i : ℕ} : a.toPermOf • i = a • i := rfl

@[simp]
theorem mk_smul {a : PermOf n} (ha : a.minLen = n) {i : ℕ} :
    (⟨n, a, ha⟩ : FinitePerm) • i = a • i := rfl

theorem eq_iff_smul_eq_smul {b : FinitePerm} :
    a = b ↔ ∀ {i : ℕ}, a • i = b • i := by
  simp_rw [FinitePerm.ext_iff, isCongr_iff_smul_eq, toPermOf_smul]

instance : FaithfulSMul FinitePerm ℕ where
  eq_of_smul_eq_smul := by
    simp_rw [eq_iff_smul_eq_smul, imp_self, implies_true]

instance : One FinitePerm := ⟨⟨0, 1, minLen_zero⟩⟩

theorem one_len : (1 : FinitePerm).len = 0 := rfl

@[simp]
theorem one_toPermOf : (1 : FinitePerm).toPermOf = 1 := rfl

instance mul : Mul FinitePerm where
  mul a b :=
  let ab := ((a.toPermOf.castGE (le_max_left a.len b.len)) *
    (b.toPermOf.castGE (le_max_right a.len b.len)))
  ⟨ab.minLen, ab.minPerm, minLen_minPerm⟩

theorem mul_len (b : FinitePerm): (a * b).len =
      (a.toPermOf.castGE (le_max_left a.len b.len) * b.toPermOf.castGE
      (le_max_right a.len b.len)).minLen := rfl

theorem mul_toPermOf (b : FinitePerm): (a * b).toPermOf =
      ( a.toPermOf.castGE (le_max_left a.len b.len) * b.toPermOf.castGE
      (le_max_right a.len b.len)).minPerm := rfl

instance : Inv FinitePerm where
  inv a := ⟨a.len, a.toPermOf⁻¹, minLen_inv.trans a.toPermOf_minLen⟩

theorem inv_len (a : FinitePerm): (a⁻¹).len = a.len := rfl

theorem inv_toPermOf : (a⁻¹).toPermOf = a.toPermOf⁻¹ := rfl

instance : Group FinitePerm where
  mul_assoc a b c := by
    ext
    simp_rw [mul_toPermOf, isCongr_minPerm_minPerm, isCongr_iff_smul_eq]
    simp only [minPerm_isCongr.smul_eq, mul_smul, castGE_smul, implies_true]
  mul_one a := by
    ext
    simp_rw [mul_toPermOf, one_toPermOf, isCongr_minPerm_left,
      castGE_one, mul_one, castGE_isCongr, isCongr_rfl]
  one_mul a := by
    ext
    simp_rw [mul_toPermOf, one_toPermOf,  isCongr_minPerm_left,
      castGE_one, one_mul, castGE_isCongr, isCongr_rfl]
  inv_mul_cancel a := by
    ext
    simp_rw [mul_toPermOf, one_toPermOf, inv_toPermOf, isCongr_one_iff_eq_one]
    exact minPerm_eq_one_iff_eq_one.mpr (by simp_rw [castGE_inv, inv_mul_cancel])

instance : MulAction FinitePerm ℕ where
  one_smul := by
    simp_rw [← toPermOf_smul, one_toPermOf, one_smul, implies_true]
  mul_smul := by
    simp_rw [← toPermOf_smul, mul_toPermOf, minPerm_isCongr.smul_eq,
      mul_smul, castGE_smul, implies_true]

end FinitePerm

namespace PermOf

variable {n m : ℕ}

@[simps! apply_toPermOf]
def ofPermOf : PermOf n →* FinitePerm where
  toFun a := ⟨a.minLen, a.minPerm, minLen_minPerm⟩
  map_one' := by
    ext
    simp_rw [minPerm_one,  one_isCongr_iff_eq_one, FinitePerm.one_toPermOf]
  map_mul' a b := by
    ext
    simp_rw [FinitePerm.mul_toPermOf, isCongr_minPerm_left, isCongr_minPerm_right,
      isCongr_iff_smul_eq, mul_smul, castGE_smul, minPerm_smul, implies_true]

section OfPermOf

variable {a : PermOf n} {b : PermOf m} {i : ℕ}

@[simp]
theorem smul_ofPermOf : a.ofPermOf • i = a • i := minPerm_smul

@[simp]
theorem toPermOf_ofPermOf {a : FinitePerm} : a.toPermOf.ofPermOf = a := by
  ext
  simp_rw [ofPermOf_apply_toPermOf, minPerm_isCongr]

theorem ofPermOf_len_le : a.ofPermOf.len ≤ n := minLen_le

theorem IsCongr.ofPermOf (hab : a.IsCongr b) : a.ofPermOf = b.ofPermOf := by
  ext
  exact hab.minPerm_minPerm

theorem ofPermOf_eq_iff_isCongr : a.ofPermOf = b.ofPermOf ↔ a.IsCongr b :=
  ⟨by simp_rw [FinitePerm.ext_iff, ofPermOf_apply_toPermOf, isCongr_minPerm_minPerm,
    imp_self], IsCongr.ofPermOf⟩

theorem ofPermOf_inj {b : PermOf n} : a.ofPermOf = b.ofPermOf ↔ a = b := by
  simp_rw [ofPermOf_eq_iff_isCongr, isCongr_iff_eq]

theorem ofPermOf_injective : Function.Injective (ofPermOf (n := n)) := fun a b => by
  simp_rw [ofPermOf_inj, imp_self]

@[simp]
theorem castGE_ofPermOf (hnm : n ≤ m) : (a.castGE hnm).ofPermOf = a.ofPermOf := by
  simp_rw [ofPermOf_eq_iff_isCongr, castGE_isCongr, isCongr_rfl]

end OfPermOf

end PermOf

namespace FinitePerm

open PermOf Equiv Equiv.Perm

variable {n m : ℕ} {a : FinitePerm}

@[simps!]
def natPerm : FinitePerm →* Perm ℕ := MulAction.toPermHom FinitePerm ℕ

section NatPerm

theorem natPerm_injective : Function.Injective natPerm := MulAction.toPerm_injective

theorem natPerm_inj {b : FinitePerm} : natPerm a = natPerm b ↔ a = b :=
  natPerm_injective.eq_iff

@[simp]
theorem natPerm_toPermOf :
    a.toPermOf.natPerm = a.natPerm := Equiv.ext <| fun _ => by
  simp_rw [natPerm_apply_apply, PermOf.natPerm_apply_apply, toPermOf_smul]

@[simp]
theorem natPerm_ofPermOf {a : PermOf n} : a.ofPermOf.natPerm = a.natPerm := Equiv.ext <| fun _ => by
  simp_rw [FinitePerm.natPerm_apply_apply, smul_ofPermOf, PermOf.natPerm_apply_apply]

theorem natPerm_eq_ofPermOf_comp_natPerm :
    PermOf.natPerm (n := n) = FinitePerm.natPerm.comp ofPermOf := MonoidHom.ext <| fun _ => by
  simp_rw [MonoidHom.comp_apply, natPerm_ofPermOf]

theorem natPerm_mem_fixGENat : a.natPerm ∈ FixGENat a.len := by
  apply mem_fixGENat_of_ge_imp_apply_eq
  simp_rw [natPerm_apply_apply]
  exact fun _ => smul_of_ge

theorem natPerm_mem_finitePermNat : a.natPerm ∈ FinitePermNat :=
  fixGENat_le_finitePermNat natPerm_mem_fixGENat

theorem exists_natPerm_apply_iff_mem_finitePermNat {e : Perm ℕ} :
    (∃ a : FinitePerm, natPerm a = e) ↔ e ∈ FinitePermNat := by
  refine ⟨?_, fun he => ?_⟩
  · rintro ⟨a, rfl⟩
    exact natPerm_mem_finitePermNat
  · simp_rw [mem_finitePermNat_iff] at he
    rcases he with ⟨n, he⟩
    refine ⟨(ofFixGENat ⟨e, he⟩).ofPermOf, ?_⟩
    simp_rw [natPerm_ofPermOf, natPerm_ofFixGENat]

theorem range_natPerm : natPerm.range = FinitePermNat := SetLike.ext <| fun _ => by
  simp_rw [MonoidHom.mem_range, exists_natPerm_apply_iff_mem_finitePermNat]

end NatPerm

@[simps! apply_coe_apply apply_coe_symm_apply]
noncomputable def mulEquivFinitePermNat : FinitePerm ≃* FinitePermNat :=
    MulEquiv.ofBijective (natPerm.codRestrict _ (fun _ => natPerm_mem_finitePermNat))
    ⟨(MonoidHom.injective_codRestrict _ _ _).mpr natPerm_injective, fun _ => by
    simp_rw [MonoidHom.codRestrict_apply, Subtype.ext_iff,
    exists_natPerm_apply_iff_mem_finitePermNat, SetLike.coe_mem]⟩

@[simp]
theorem mulEquivFinitePermNat_symm_apply_smul (e : FinitePermNat) {i : ℕ} :
    mulEquivFinitePermNat.symm e • i = e.1 i := by
  rcases e with ⟨e, he⟩
  simp_rw [mem_finitePermNat_iff] at he
  rcases he with ⟨n, he'⟩
  have H : (⟨e, he⟩ : FinitePermNat) =
    ⟨mulEquivFinitePermNat (natPermEquiv.symm ⟨e, he'⟩).ofPermOf, SetLike.coe_mem _⟩ :=
    Subtype.ext <| Equiv.ext <| fun _ => by
    simp_rw [mulEquivFinitePermNat_apply_coe_apply, smul_ofPermOf,
      natPermEquiv_symm_apply_smul]
  simp_rw [H, Subtype.coe_eta, MulEquiv.symm_apply_apply, smul_ofPermOf,
    natPermEquiv_symm_apply_smul]

end FinitePerm
