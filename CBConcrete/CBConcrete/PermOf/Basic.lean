import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Finite.Prod


namespace Equiv

variable {α β : Type*} [DecidableEq α]

theorem swap_smul {R : Type*} [Group R] [MulAction R α] {i j k : α} {r : R} :
    swap (r • i) (r • j) (r • k) = r • swap i j k :=
  (MulAction.injective r).swap_apply _ _ _

theorem swap_prop (p : α → Prop) {i j k : α} (hk : k ≠ i → k ≠ j → p k)
    (hi : k = j → p i) (hj : k = i → p j) : p (swap i j k) := by
  rcases eq_or_ne k i with rfl | hik
  · simp_rw [swap_apply_left, hj]
  · rcases eq_or_ne k j with rfl | hjk
    · simp_rw [swap_apply_right, hi]
    · simp_rw [swap_apply_of_ne_of_ne hik hjk, hk hik hjk]

theorem swap_prop_const (p : α → Prop) {i j k : α} (hk : p k)
    (hi : p i) (hj : p j) : p (swap i j k) :=
  swap_prop _ (fun _ _ => hk) (fun _ => hi) (fun _ => hj)

end Equiv

namespace Vector

open Function

variable {α β γ : Type*} {n m k i j : ℕ} {v : Vector α n}

theorem getElem_swap_eq_getElem_swap_apply
    (hi : i < n) (hj : j < n) (k : ℕ) (hk : k < n) :
    (v.swap i j)[k] =
    v[Equiv.swap i j k]'(Equiv.swap_prop_const (· < n) hk hi hj) := by
  simp_rw [getElem_swap, Equiv.swap_apply_def]
  split_ifs <;> rfl

def Nodup (v : Vector α n) : Prop := ∀ {i} (hi : i < n) {j} (hj : j < n), v[i] = v[j] → i = j

section Nodup

theorem Nodup.getElem_inj_iff {i j : ℕ} {hi : i < n} {hj : j < n}
    (hv : v.Nodup) : v[i] = v[j] ↔ i = j := ⟨hv _ _, fun h => h ▸ rfl⟩

theorem Nodup.getElem_ne_iff {i j : ℕ} {hi : i < n} {hj : j < n}
    (hv : v.Nodup) : v[i] ≠ v[j] ↔ i ≠ j := by simp_rw [ne_eq, hv.getElem_inj_iff]

theorem nodup_iff_getElem?_ne_getElem? :
    v.Nodup ↔ ∀ {i j}, (hij : i < j) → (hj : j < n) → v[i] ≠ v[j] := by
  refine ⟨fun hv => by simp_rw [hv.getElem_ne_iff] ; exact fun hij _ => hij.ne,
    fun hv i hi j hj => Function.mtr fun hij => ?_⟩
  rcases Ne.lt_or_gt hij with (hij | hij)
  exacts [hv hij _, (hv hij _).symm]

theorem nodup_iff_injective_getElem : v.Nodup ↔ Injective (fun (i : Fin n) => v[(i : ℕ)]) := by
  unfold Injective Nodup
  simp_rw [Fin.ext_iff, Fin.forall_iff]

theorem nodup_iff_injective_get : v.Nodup ↔ Injective v.get := by
  simp_rw [nodup_iff_injective_getElem]
  exact Iff.rfl

theorem toList_nodup_iff_nodup : v.toList.Nodup ↔ v.Nodup := by
    simp_rw [List.nodup_iff_injective_get, nodup_iff_injective_getElem,
      Function.Injective, Fin.ext_iff, Fin.forall_iff, length_toList,
        List.get_eq_getElem, getElem_toList]

instance nodupDecidable [DecidableEq α] : Decidable v.Nodup :=
  decidable_of_decidable_of_iff toList_nodup_iff_nodup

end Nodup

end Vector

/--
A `PermOf n` is a permutation on `n` elements represented by two vectors, which we can
think of as an array of values and a corresponding array of indexes which are inverse to
one another. (One can flip the interpretation of indexes and values, and this is essentially
the inversion operation.)
It is designed to be a more performant version of `Equiv.Perm`.
-/
structure PermOf (n : ℕ) where
  /--
  Gives the `PermOf` as an vector of size `n`.
  -/
  protected toVector : Vector ℕ n
  /--
  Gives the inverse of the `PermOf` as a vector of size `n`.
  -/
  protected invVector : Vector ℕ n
  getElem_toVector_lt (i : ℕ) (hi : i < n := by get_elem_tactic) : toVector[i] < n := by decide
  getElem_invVector_getElem_toVector (i : ℕ) (hi : i < n := by get_elem_tactic) :
      invVector[toVector[i]]'(getElem_toVector_lt i hi) = i := by decide
  deriving DecidableEq

namespace PermOf

open Function Equiv

variable {n m i j : ℕ} {a b : PermOf n}

instance : GetElem (PermOf n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.toVector[i]

section GetElem

@[simp]
theorem getElem_mk (a b : Vector ℕ n) {ha hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk a b ha hab)[i] = a[i] := rfl

@[simp]
theorem getElem_lt {i : ℕ} (hi : i < n := by get_elem_tactic) : a[i] < n :=
  a.getElem_toVector_lt _

@[simp]
theorem getElem_toVector {i : ℕ} (hi : i < n := by get_elem_tactic) :
  a.toVector[i] = a[i] := rfl

theorem getElem_injective (hi : i < n) (hj : j < n)
    (hij : a[i] = a[j]) : i = j := by
  rw [← a.getElem_invVector_getElem_toVector i, ← a.getElem_invVector_getElem_toVector j]
  congr 1

@[simp] theorem getElem_inj (hi : i < n) (hj : j < n) :
    a[i] = a[j] ↔ i = j := ⟨a.getElem_injective hi hj, fun h => h ▸ rfl⟩

theorem getElem_ne_iff {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := (a.getElem_inj hi hj).not

theorem getElem_surjective (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i := by
  have h_inj : Injective (⟨a[·.val], a.getElem_lt⟩ : Fin n → Fin n) :=
    fun _ _ hij => Fin.ext (a.getElem_injective _ _ (Fin.val_eq_of_eq hij))
  have h_surj := h_inj.surjective_of_fintype (Equiv.refl (Fin n)) ⟨i, hi⟩
  grind

end GetElem

@[ext]
theorem ext (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by
    rcases a ; rcases b ; simp_rw [mk.injEq] ; exact h
  simp_rw [Vector.ext_iff]
  refine ⟨h, fun i hi => ?_⟩
  rcases a.getElem_surjective hi with ⟨j, hj, rfl⟩
  trans j
  · exact a.getElem_invVector_getElem_toVector j
  · simp_rw [h]
    symm
    exact b.getElem_invVector_getElem_toVector j

section Ext

instance : Subsingleton (PermOf 0) where
  allEq a b := by simp_rw [PermOf.ext_iff, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true]

instance : Subsingleton (PermOf 1) where
  allEq a b := by
    simp_rw [PermOf.ext_iff]
    intro _ hi
    have ha := a.getElem_lt (hi := hi)
    have hb := b.getElem_lt (hi := hi)
    rw [Nat.lt_one_iff] at ha hb
    exact ha.trans hb.symm

instance : Finite (PermOf n) := Finite.of_injective
  (fun a => (⟨a[·], a.getElem_lt⟩ : Fin n → Fin n)) <| fun a b => by
    simp_rw [funext_iff, Fin.ext_iff, PermOf.ext_iff, Fin.forall_iff,
      Fin.getElem_fin, imp_self]

end Ext

instance : One (PermOf n) where
  one := PermOf.mk (Vector.range n) (Vector.range n)
    (fun _ => by simp_rw [Vector.getElem_range, imp_self])
    (by simp_rw [Vector.getElem_range, implies_true])

section One

@[simp]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : PermOf n)[i] = i := Vector.getElem_range _

instance : Inhabited (PermOf n) := ⟨1⟩

@[simp]
theorem default_eq : (default : PermOf n) = 1 := rfl

instance : Unique (PermOf 0) := Unique.mk' _

instance : Unique (PermOf 1) := Unique.mk' _

end One

instance : Inv (PermOf n) where
  inv a := PermOf.mk
    (toVector := a.invVector)
    (invVector := a.toVector)
    (getElem_toVector_lt := fun i hi => by
      rcases a.getElem_surjective hi with ⟨j, hj, rfl⟩
      exact hj.trans_eq' (a.getElem_invVector_getElem_toVector _))
    (getElem_invVector_getElem_toVector := fun i hi => by
      rcases a.getElem_surjective hi with ⟨j, hj, rfl⟩
      congr 1
      exact a.getElem_invVector_getElem_toVector _)

section Inv

@[simp]
theorem getElem_inv_mk (a b : Vector ℕ n) {ha hab} (hi : i < n) :
  (PermOf.mk a b ha hab)⁻¹[i] = b[i] := rfl

@[simp]
theorem getElem_invVector (hi : i < n) :
  a.invVector[i] = a⁻¹[i] := rfl

@[simp]
theorem getElem_inv_getElem (hi : i < n) :
    a⁻¹[a[i]] = i := a.getElem_invVector_getElem_toVector _

@[simp]
theorem getElem_getElem_inv (hi : i < n) :
  a[a⁻¹[i]] = i := (a⁻¹).getElem_invVector_getElem_toVector _

theorem eq_getElem_inv_iff (hi : i < n) (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by
  rw [← (a⁻¹).getElem_inj (a.getElem_lt) hj, getElem_inv_getElem]

theorem ne_getElem_inv_iff (hi : i < n) (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := (a.eq_getElem_inv_iff _ _).ne

theorem getElem_inv_eq_iff (hi : i < n) (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by
  rw [← a.getElem_inj (a⁻¹.getElem_lt) hj, getElem_getElem_inv]

theorem getElem_inv_ne_iff (hi : i < n) (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := (a.getElem_inv_eq_iff _ _).ne

end Inv

instance : Mul (PermOf n) where
  mul a b := {
    toVector := Vector.ofFn (fun i => a.toVector[b[(i : ℕ)]])
    invVector := Vector.ofFn (fun i => b⁻¹.toVector[a⁻¹[(i : ℕ)]])
    getElem_toVector_lt := fun {i} hi => by
      simp_rw [Vector.getElem_ofFn, getElem_toVector, getElem_lt]
    getElem_invVector_getElem_toVector := fun {i} hi => by
      simp_rw [Vector.getElem_ofFn, getElem_toVector, getElem_inv_getElem]}

section Mul

@[simp]
theorem getElem_mul {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]] := Vector.getElem_ofFn _

end Mul

instance : Group (PermOf n) := Group.ofLeftAxioms
  (fun _ _ _ => ext <| fun i hi => by simp_rw [getElem_mul])
  (fun _ => ext <| fun i hi => by simp_rw [getElem_mul, getElem_one])
  (fun _ => ext <| fun i hi => by simp_rw [getElem_mul, getElem_one, getElem_inv_getElem])

section Group

theorem getElem_pow_eq_self_of_getElem_eq_self {k : ℕ} (hi : i < n := by get_elem_tactic)
  (hia : a[i] = i) : (a^k)[i] = i := by
  induction k with | zero => _ | succ k IH => _
  · simp_rw [pow_zero, getElem_one]
  · simp_rw [pow_succ, getElem_mul, hia, IH]

theorem getElem_inv_eq_self_of_getElem_eq_self (hi : i < n := by get_elem_tactic) :
  a[i] = i → (a⁻¹)[i] = i := by simp_rw [getElem_inv_eq_iff _ hi, eq_comm, imp_self]

theorem getElem_inv_ne_self_of_getElem_ne_self (hi : i < n := by get_elem_tactic):
  a[i] ≠ i → (a⁻¹)[i] ≠ i := by simp_rw [ne_eq, getElem_inv_eq_iff _ hi, eq_comm, imp_self]

theorem getElem_zpow_eq_self_of_getElem_eq_self {k : ℤ} (hi : i < n := by get_elem_tactic)
    (hia : a[i] = i) : (a^k)[i] = i := by
  cases k
  · exact getElem_pow_eq_self_of_getElem_eq_self _ hia
  · simp_rw [zpow_negSucc]
    exact (getElem_inv_eq_self_of_getElem_eq_self _ (getElem_pow_eq_self_of_getElem_eq_self _ hia))

@[simp]
theorem getElem_pow_add {i x y : ℕ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [pow_add, getElem_mul]

@[simp]
theorem getElem_zpow_add {i : ℕ} {x y : ℤ} (hi : i < n) :
    (a^x)[(a^y)[i]] = (a^(x + y))[i] := by simp_rw [zpow_add, getElem_mul]

end Group

instance : SMul (PermOf n) ℕ where
  smul a i := a[i]?.getD i

section SMul

theorem smul_eq_dite (i : ℕ) :
    a • i = if h : i < n then a[i]'h else i :=
  apply_dite (fun (o : Option ℕ) => o.getD i) _ _ _

theorem smul_of_lt {i : ℕ} (h : i < n) : a • i = a[i] := by
  simp_rw [smul_eq_dite, dif_pos h]

theorem smul_of_ge {i : ℕ} (h : n ≤ i) : a • i = i := by
  simp_rw [smul_eq_dite, dif_neg h.not_gt]

@[simp] theorem smul_fin {i : Fin n} : a • i = a[i.1] := a.smul_of_lt i.isLt

@[simp]
theorem smul_getElem {i : ℕ} (h : i < n) : a • b[i] = a[b[i]] :=
  a.smul_of_lt _

theorem smul_eq_iff {i j : ℕ} :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by
  rcases lt_or_ge i n with hi | hi
  · simp_rw [a.smul_of_lt hi, hi, hi.not_ge, false_implies, forall_true_left, and_true]
  · simp_rw [a.smul_of_ge hi, hi, hi.not_gt, IsEmpty.forall_iff, forall_true_left, true_and]

theorem eq_smul_iff {i j : ℕ} :
    i = a • j ↔ (∀ (hj : j < n), i = a[j]) ∧ (n ≤ j → i = j) := by
  simp_rw [eq_comm (a := i), smul_eq_iff]

theorem smul_eq_self_iff {i : ℕ} :
    a • i = i ↔ ∀ (hi : i < n), a[i] = i := by
  simp_rw [smul_eq_iff, implies_true, and_true]

theorem self_eq_smul_iff {i : ℕ} :
    i = a • i ↔ ∀ (hi : i < n), i = a[i] := by
  simp_rw [eq_comm (a := i), smul_eq_self_iff]

@[simp]
theorem smul_lt_iff_lt {i : ℕ} : a • i < n ↔ i < n := by
  rcases lt_or_ge i n with h | h
  · simp_rw [h, iff_true, a.smul_of_lt h, getElem_lt]
  · simp_rw [h.not_gt, iff_false, not_lt, a.smul_of_ge h, h]

theorem smul_lt_of_lt {i : ℕ} (h : i < n) : a • i < n := a.smul_lt_iff_lt.mpr h

theorem lt_of_smul_lt {i : ℕ} (h : a • i < n) : i < n := a.smul_lt_iff_lt.mp h

theorem smul_fin_lt {i : Fin n} : a • i < n := a.smul_lt_of_lt i.isLt

theorem smul_eq_smul_same_iff {i : ℕ} :
  a • i = b • i ↔ {hi : i < n} → a[i] = b[i] := by
  rcases lt_or_ge i n with hi | hi
  · simp_rw [smul_of_lt hi, hi, forall_true_left]
  · simp_rw [smul_of_ge hi, hi.not_gt, IsEmpty.forall_iff]

theorem smul_right_inj {i j : ℕ} : a • i = a • j ↔ i = j := by
  rcases lt_or_ge i n with hi | hi <;>
  rcases lt_or_ge j n with hj | hj
  · simp_rw [a.smul_of_lt hi, a.smul_of_lt hj, a.getElem_inj]
  · simp_rw [a.smul_of_lt hi, a.smul_of_ge hj, (hi.trans_le hj).ne, iff_false]
    exact ne_of_lt (hj.trans_lt' a.getElem_lt)
  · simp_rw [a.smul_of_ge hi, a.smul_of_lt hj, (hj.trans_le hi).ne', iff_false]
    exact ne_of_gt (hi.trans_lt' a.getElem_lt)
  · simp_rw [a.smul_of_ge hi, a.smul_of_ge hj]

theorem smul_right_surj {i : ℕ} : ∃ j, a • j = i := by
  rcases lt_or_ge i n with hi | hi
  · rcases a.getElem_surjective hi with ⟨j, hj, rfl⟩
    exact ⟨j, smul_of_lt _⟩
  · exact ⟨i, smul_of_ge hi⟩

theorem eq_iff_smul_eq_smul_lt : a = b ↔ ∀ {i : ℕ}, i < n → a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, PermOf.ext_iff, imp_forall_iff_forall]

theorem eq_iff_smul_eq_smul :
    a = b ↔ ∀ {i : ℕ}, a • i = b • i := by
  simp_rw [smul_eq_smul_same_iff, PermOf.ext_iff]

instance : FaithfulSMul (PermOf n) ℕ where
  eq_of_smul_eq_smul := by
    simp_rw [eq_iff_smul_eq_smul, imp_self, implies_true]

instance : MulAction (PermOf n) ℕ where
  one_smul k := by
    rcases lt_or_ge k n with hkn | hkn
    · simp_rw [smul_of_lt hkn, getElem_one]
    · simp_rw [smul_of_ge hkn]
  mul_smul a b k := by
    rcases lt_or_ge k n with hkn | hkn
    · simp_rw [smul_of_lt hkn, smul_of_lt (getElem_lt _), getElem_mul]
    · simp_rw [smul_of_ge hkn]

section MulAction

theorem smul_eq_iff_eq_one : (∀ {i : ℕ}, a • i = i) ↔ a = 1 := by
  simp_rw [eq_iff_smul_eq_smul, one_smul]

theorem smul_eq_id_iff_eq_one : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  simp_rw [funext_iff, id_eq, smul_eq_iff_eq_one]

end MulAction

end SMul

def ofVector (a : Vector ℕ n) (hx : ∀ x (hx : x < n), a[x] < n := by decide)
  (ha : a.toList.Nodup := by decide) : PermOf n where
  toVector := a
  invVector := (Vector.range n).map a.toList.idxOf
  getElem_toVector_lt := hx
  getElem_invVector_getElem_toVector := fun {i} hi => by
    simp_rw [Vector.getElem_map, Vector.getElem_range]
    exact a.toList.idxOf_getElem ha _ _

section OfVector

@[simp]
theorem getElem_ofVector {a : Vector ℕ n} {hx : ∀ x (hx : x < n), a[x] < n}
    {ha : a.toList.Nodup} {i : ℕ} (hi : i < n) : (ofVector a hx ha)[i] = a[i] := rfl

theorem toVector_Nodup : a.toVector.Nodup := by
  simp_rw [Vector.nodup_iff_injective_getElem, Injective, getElem_toVector,
    getElem_inj, Fin.ext_iff, imp_self, implies_true]

theorem toVector_toList_Nodup : a.toVector.toList.Nodup := by
  simp_rw [Vector.toList_nodup_iff_nodup, toVector_Nodup]

@[simp] theorem ofVector_toVector :
    ofVector a.toVector (fun i _ => a.getElem_toVector_lt i) a.toVector_toList_Nodup = a :=
  ext <| fun _ _ => by simp_rw [getElem_ofVector, getElem_toVector]

@[simp] theorem ofVector_invVector :
    ofVector a.invVector (fun i _ => a⁻¹.getElem_toVector_lt i) a⁻¹.toVector_toList_Nodup = a⁻¹ :=
  ext <| fun _ _ => by simp_rw [getElem_ofVector, getElem_invVector]

end OfVector

def ofFn (f g : Fin n → ℕ) (hf : ∀ i, f i < n)
    (hfg : ∀ i, g ⟨f i, hf _⟩ = i) : PermOf n where
  toVector := Vector.ofFn f
  invVector := Vector.ofFn g
  getElem_toVector_lt := fun _ _ => by simp_rw [Vector.getElem_ofFn, hf]
  getElem_invVector_getElem_toVector := fun _ _ => by simp_rw [Vector.getElem_ofFn, hfg]

section OfFn

@[simp]
theorem getElem_ofFn {f g : Fin n → ℕ} {hf : ∀ i, f i < n}
    {hfg : ∀ i, g ⟨f i, hf _⟩ = i} {i : ℕ} (hi : i < n) :
    (ofFn f g hf hfg)[i] = f ⟨i, hi⟩ := by
  unfold ofFn
  simp_rw [getElem_mk, Vector.getElem_ofFn]

@[simp]
theorem getElem_inv_ofFn {f g : Fin n → ℕ} {hf : ∀ i, f i < n}
    {hfg : ∀ i, g ⟨f i, hf _⟩ = i} {i : ℕ} (hi : i < n) :
    (ofFn f g hf hfg)⁻¹[i] = g ⟨i, hi⟩ := by
  unfold ofFn
  simp_rw [getElem_inv_mk, Vector.getElem_ofFn]

@[simp] theorem ofFn_getElem :
    ofFn (fun i => a[i.1]) (fun i => a⁻¹[i.1])
    (fun _ => a.getElem_lt) (fun _ => a.getElem_inv_getElem _) = a :=
  ext <| fun _ _ => by simp_rw [getElem_ofFn]

@[simp] theorem ofFn_getElem_inv :
    ofFn (fun i => a⁻¹[i.1]) (fun i => a[i.1])
    (fun _ => a⁻¹.getElem_lt) (fun _ => a.getElem_getElem_inv _) = a⁻¹ :=
  ext <| fun _ _ => by simp_rw [getElem_ofFn]

end OfFn

/--
For `a` an `PermOf n`, `a.swap i j hi hj` is the permutation which is the same except for switching
the `i`th and `j`th values, which corresponds to multiplying on the right by a transposition.
-/
def swap (a : PermOf n) (i j : ℕ)
    (hi : i < n := by get_elem_tactic) (hj : j < n := by get_elem_tactic) : PermOf n where
  toVector := a.toVector.swap i j
  invVector := a.invVector.map (fun k => Equiv.swap i j k)
  getElem_toVector_lt := fun _ _ => by
    simp_rw [Vector.getElem_swap_eq_getElem_swap_apply, getElem_toVector, getElem_lt]
  getElem_invVector_getElem_toVector := fun _ _ => by
    simp_rw [Vector.getElem_map, getElem_invVector, Vector.getElem_swap_eq_getElem_swap_apply,
      getElem_toVector, getElem_inv_getElem, swap_apply_self]

section Swap

variable {i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n)

@[simp]
theorem getElem_swap :
    (a.swap i j)[k] = a[Equiv.swap i j k]'(swap_prop_const (· < n) hk hi hj) :=
  Vector.getElem_swap_eq_getElem_swap_apply hi hj _ _

@[simp]
theorem getElem_inv_swap :
    (a.swap i j hi hj)⁻¹[k] = Equiv.swap i j a⁻¹[k] := a.invVector.getElem_map _ _

theorem swap_smul_eq_smul_swap :
    (a.swap i j hi hj) • k = a • (Equiv.swap i j k) := by
  rcases lt_or_ge k n with hk | hk
  · simp_rw [smul_of_lt (swap_prop_const (· < n) hk hi hj), smul_of_lt hk, getElem_swap]
  · simp_rw [Equiv.swap_apply_of_ne_of_ne (hk.trans_lt' hi).ne' (hk.trans_lt' hj).ne',
      smul_of_ge hk]

theorem swap_inv_eq_swap_apply_inv_smul :
  (a.swap i j hi hj)⁻¹ • k = Equiv.swap i j (a⁻¹ • k) := by
  simp_rw [inv_smul_eq_iff, swap_smul_eq_smul_swap,
  ← swap_smul, smul_inv_smul, swap_apply_self]

theorem swap_smul_eq_swap_apply_smul :
    (a.swap i j hi hj) • k = Equiv.swap (a • i) (a • j) (a • k) := by
  rw [swap_smul, swap_smul_eq_smul_swap]

theorem swap_inv_smul_eq_inv_smul_swap : (a.swap i j hi hj)⁻¹ • k =
    a⁻¹ • (Equiv.swap (a • i) (a • j) k) := by
  simp_rw [swap_inv_eq_swap_apply_inv_smul, ← Equiv.swap_smul, inv_smul_smul]

theorem swap_smul_left :
    (a.swap i j hi hj) • i = a • j := by rw [swap_smul_eq_smul_swap, swap_apply_left]

theorem swap_smul_right :
  (a.swap i j hi hj) • j = a • i := by rw [swap_smul_eq_smul_swap, swap_apply_right]

theorem swap_smul_of_ne_of_ne {k} :
  k ≠ i → k ≠ j → (a.swap i j hi hj) • k = a • k := by
  rw [swap_smul_eq_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

theorem swap_inv_smul_left :
    (a.swap i j hi hj)⁻¹ • (a • i) = j := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_left, inv_smul_smul]

theorem swap_inv_smul_right :
    (a.swap i j hi hj)⁻¹ • (a • j) = i := by
  rw [swap_inv_smul_eq_inv_smul_swap, swap_apply_right, inv_smul_smul]

theorem swap_inv_smul_of_ne_of_ne {k} :
  k ≠ a • i → k ≠ a • j → (a.swap i j hi hj)⁻¹ • k = a⁻¹ • k := by
  rw [swap_inv_smul_eq_inv_smul_swap, smul_left_cancel_iff]
  exact swap_apply_of_ne_of_ne

@[simp]
theorem swap_self (i : ℕ) (hi hi' : i < n) : a.swap i i hi hi' = a := by
  ext : 1
  simp_rw [getElem_swap, Equiv.swap_self, Equiv.refl_apply]

@[simp]
theorem swap_swap (i j : ℕ) (hi hi' : i < n) (hj hj' : j < n) :
    (a.swap i j hi hj).swap i j hi' hj' = a := by
  ext : 1
  simp_rw [getElem_swap, swap_apply_self]

theorem getElem_one_swap : (swap 1 i j hi hj)[k] = Equiv.swap i j k := by
  rw [getElem_swap, getElem_one]

theorem getElem_inv_one_swap : (swap 1 i j hi hj)⁻¹[k] = Equiv.swap i j k := by
  simp_rw [getElem_inv_swap, inv_one, getElem_one]

theorem one_swap_smul : (swap 1 i j hi hj) • k = Equiv.swap i j k := by
  rw [swap_smul_eq_smul_swap, one_smul]

theorem one_swap_inv_smul : (swap 1 i j hi hj)⁻¹ • k = Equiv.swap i j k := by
  simp_rw [swap_inv_smul_eq_inv_smul_swap, one_smul, inv_one, one_smul]

theorem one_swap_mul_self : swap 1 i j hi hj * swap 1 i j hi hj = 1 := by
  ext : 1
  simp_rw [getElem_mul, getElem_one_swap, swap_apply_self, getElem_one]

theorem one_swap_inverse : (swap 1 i j hi hj)⁻¹ = swap 1 i j hi hj := by
  ext : 1
  rw [getElem_one_swap, getElem_inv_one_swap]

theorem swap_eq_mul_one_swap : a.swap i j hi hj = a * swap 1 i j hi hj := by
  ext : 1
  simp only [getElem_swap, getElem_mul, getElem_one]

theorem swap_eq_one_swap_mul (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    a.swap i j hi hj = swap 1 _ _ hi' hj' * a := by
  rw [eq_iff_smul_eq_smul_lt]
  simp_rw [mul_smul, one_swap_smul, swap_smul_eq_smul_swap, swap_smul, implies_true]

theorem swap_inv_eq_one_swap_mul :
    (a.swap i j hi hj)⁻¹ = swap 1 i j hi hj * a⁻¹ := by
  rw [swap_eq_mul_one_swap, mul_inv_rev, one_swap_inverse]

theorem swap_inv_eq_mul_one_swap (hi' : a • i < n := a.smul_lt_iff_lt.mpr hi)
    (hj' : a • j < n := a.smul_lt_iff_lt.mpr hj) :
    (a.swap i j hi hj)⁻¹ = a⁻¹ * swap 1 _ _ hi' hj' := by
  rw [swap_eq_one_swap_mul, mul_inv_rev, mul_right_inj, one_swap_inverse]

end Swap

end PermOf

namespace Vector

open PermOf

variable {n : ℕ} {a b : PermOf n} {α : Type*} {v : Vector α n}

def shuffle {α : Type*} (a : PermOf n) (v : Vector α n) : Vector α n :=
  Vector.ofFn (fun i => v[a[i]])

section Shuffle

@[simp] theorem getElem_shuffle {i : ℕ} (hi : i < n) :
    (v.shuffle a)[i] = v[a[i]] := Vector.getElem_ofFn _

theorem mem_of_mem_shuffle {x : α}
    (hx : x ∈ v.shuffle a) : x ∈ v := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_shuffle] at hx
  rcases hx with ⟨i, hi, hix⟩
  exact ⟨a[i], a.getElem_lt, hix⟩

theorem mem_shuffle_of_mem {x : α}
    (hx : x ∈ v) : x ∈ v.shuffle a := by
  simp_rw [Vector.mem_iff_getElem] at hx ⊢
  simp_rw [getElem_shuffle]
  rcases hx with ⟨i, hi, hix⟩
  refine ⟨a⁻¹[i], getElem_lt _, ?_⟩
  simp_rw [getElem_getElem_inv, hix]

theorem mem_onIndices_iff {x : α} :
    x ∈ v.shuffle a ↔ x ∈ v := ⟨v.mem_of_mem_shuffle, v.mem_shuffle_of_mem⟩

@[simp]
theorem shuffle_range :
    (Vector.range n).shuffle a = a.toVector := by
  simp_rw [Vector.ext_iff, getElem_shuffle, Vector.getElem_range,
    getElem_toVector, implies_true]

@[simp] theorem one_shuffle {α : Type*} (v : Vector α n) :
    v.shuffle (1 : (PermOf n)) = v := by
  simp_rw [Vector.ext_iff, getElem_shuffle, getElem_one, implies_true]

@[simp] theorem shuffle_shuffle_inv :
    (v.shuffle a⁻¹).shuffle a = v := by
  simp_rw [Vector.ext_iff, getElem_shuffle, getElem_inv_getElem, implies_true]

@[simp] theorem shuffle_inv_shuffle : (v.shuffle a).shuffle a⁻¹ = v := by
  simp_rw [Vector.ext_iff, getElem_shuffle, getElem_getElem_inv, implies_true]

theorem inv_shuffle_range :
    (Vector.range n).shuffle a⁻¹ = a.invVector := by
  simp_rw [shuffle_range] ; rfl

@[simp] theorem mul_shuffle {α : Type*} (v : Vector α n) :
    v.shuffle (a * b) = (v.shuffle a).shuffle b := by
  simp_rw [Vector.ext_iff, getElem_shuffle, a.getElem_mul, implies_true]

theorem shuffle_toVector :
    a.toVector.shuffle b = (a * b).toVector := by
  simp_rw [Vector.ext_iff, getElem_shuffle, getElem_toVector, a.getElem_mul, implies_true]

instance {α : Type*} : SMul (PermOf n)ᵐᵒᵖ (Vector α n) where
  smul a v := v.shuffle a.unop

section SMulOp

variable {α : Type*}

@[simp] theorem op_smul (v : Vector α n) :
    (MulOpposite.op a) • v = v.shuffle a := rfl

@[simp] theorem unop_shuffle (a : (PermOf n)ᵐᵒᵖ) (v : Vector α n) :
    v.shuffle a.unop = a • v := rfl

end SMulOp

end Shuffle

end Vector
