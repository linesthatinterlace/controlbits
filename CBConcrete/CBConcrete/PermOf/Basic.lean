import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Data.Finite.Prod

namespace Equiv

variable {α β : Type*} [DecidableEq α]

theorem swap_smul {R : Type*} [Group R] [MulAction R α] {i j k : α} {r : R} :
    swap (r • i) (r • j) (r • k) = r • swap i j k :=
  (MulAction.injective r).swap_apply _ _ _

theorem swap_prop (p : α → Prop) {i j k : α} (hk : k ≠ i → k ≠ j → p k)
    (hi : k = j → p i) (hj : k = i → p j) : p (swap i j k) := by grind

theorem swap_prop_const (p : α → Prop) {i j k : α} (hk : p k)
    (hi : p i) (hj : p j) : p (swap i j k) := by grind

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

@[grind =]
theorem Nodup.getElem_inj_iff {i j : ℕ} {hi : i < n} {hj : j < n}
    (hv : v.Nodup) : v[i] = v[j] ↔ i = j := ⟨hv _ _, fun h => h ▸ rfl⟩

theorem Nodup.getElem_ne_iff {i j : ℕ} {hi : i < n} {hj : j < n}
    (hv : v.Nodup) : v[i] ≠ v[j] ↔ i ≠ j := by simp_rw [ne_eq, hv.getElem_inj_iff]

@[grind =]
theorem nodup_iff_getElem_ne_getElem :
    v.Nodup ↔ ∀ {i j}, (hij : i < j) → (hj : j < n) → v[i] ≠ v[j] :=
  ⟨by grind, fun _ _ _ _ _ => Function.mtr <| by grind⟩

theorem nodup_iff_injective_getElem : v.Nodup ↔ Injective (fun (i : Fin n) => v[(i : ℕ)]) := by
  unfold Injective Nodup
  simp_rw [Fin.ext_iff, Fin.forall_iff]

theorem nodup_iff_injective_get : v.Nodup ↔ Injective v.get := by
  simp_rw [nodup_iff_injective_getElem]
  exact Iff.rfl

theorem toList_nodup_iff_nodup : v.toList.Nodup ↔ v.Nodup := by
  grind [List.nodup_iff_getElem?_ne_getElem?]

theorem Nodup.nodup_toList (hv : v.Nodup) : v.toList.Nodup := toList_nodup_iff_nodup.mpr hv

theorem _root_.List.Nodup.nodup_of_nodup_toList (hv : v.toList.Nodup) : v.Nodup :=
  toList_nodup_iff_nodup.mp hv

instance nodupDecidable [DecidableEq α] : Decidable v.Nodup :=
  decidable_of_decidable_of_iff toList_nodup_iff_nodup

end Nodup

theorem getElem_getElem_flip {a b : Vector ℕ n}
    (H : ∀ {i} {hi : i < n}, ∃ (hi' : a[i] < n), b[a[i]] = i) {i hi} :
    (∃ (hi' : b[i] < n), a[b[i]'(hi : i < n)] = i) := by
  have := (Finite.surjective_of_injective (α := Fin n) (f := (⟨a[·.val], by grind⟩)) <|
    fun i j hij => by have := congrArg (b[·.val]) hij; grind) <| Fin.mk _ hi
  grind

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
  getElem_invVector_getElem_toVector {i : ℕ} {hi : i < n} :
      ∃ (hi' : toVector[i] < n), invVector[toVector[i]] = i := by decide

namespace PermOf

theorem getElem_toVector_getElem_invVector {n : ℕ} (a : PermOf n) {i : ℕ} {hi : i < n} :
    ∃ (hi' : a.invVector[i] < n), a.toVector[a.invVector[i]] = i :=
  Vector.getElem_getElem_flip a.getElem_invVector_getElem_toVector

open Function Equiv

variable {n m i j : ℕ} {a b : PermOf n}

instance : GetElem (PermOf n) ℕ ℕ fun _ i => i < n where
  getElem a i h := a.toVector[i]

section GetElem

@[simp, grind =]
theorem getElem_mk (a b : Vector ℕ n) {hab} {i : ℕ} (hi : i < n) :
  (PermOf.mk a b hab)[i]'hi = a[i]'hi := rfl

@[simp, grind =]
theorem getElem_toVector {i : ℕ} {hi : i < n} :
  a.toVector[i] = a[i] := rfl

@[simp]
theorem getElem_lt (a : PermOf n) {i : ℕ} {hi : i < n} : a[i] < n :=
  a.getElem_invVector_getElem_toVector.1

grind_pattern getElem_lt => a[i]

theorem getElem_ne (a : PermOf n) {i : ℕ} {hi : i < n} : a[i] ≠ n := by grind

grind_pattern getElem_ne => a[i]

theorem getElem_injective (hi : i < n) (hj : j < n)
    (hij : a[i] = a[j]) : i = j := by
  grind [=_ getElem_toVector, getElem_invVector_getElem_toVector]

@[simp, grind =] theorem getElem_inj (hi : i < n) (hj : j < n) :
    a[i] = a[j] ↔ i = j := by grind [getElem_injective]

theorem getElem_ne_iff {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n) :
    a[i] ≠ a[j] ↔ i ≠ j := by grind

theorem getElem_surjective (hi : i < n) :
    ∃ (j : ℕ) (hj : j < n), a[j] = i :=
  ⟨a.invVector[i], by grind [getElem_toVector_getElem_invVector]⟩

end GetElem

instance : Inv (PermOf n) where
  inv a := PermOf.mk a.invVector a.toVector a.getElem_toVector_getElem_invVector

section Inv

@[simp, grind =]
theorem inv_mk (a b : Vector ℕ n) {hab} :
  (PermOf.mk a b hab)⁻¹ = PermOf.mk b a (a.getElem_getElem_flip hab) := rfl

theorem getElem_inv_mk (a b : Vector ℕ n) {hab} (hi : i < n) :
  (PermOf.mk a b hab)⁻¹[i] = b[i] := by grind

@[simp, grind =]
theorem getElem_invVector (hi : i < n) : a.invVector[i] = a⁻¹[i] := rfl

@[simp, grind =]
theorem getElem_inv_getElem (hi : i < n) :
    a⁻¹[a[i]] = i := a.getElem_invVector_getElem_toVector.2

@[simp, grind =]
theorem getElem_getElem_inv (hi : i < n) :
  a[a⁻¹[i]] = i := a.getElem_toVector_getElem_invVector.2

theorem eq_getElem_inv_iff (hi : i < n) (hj : j < n) :
    i = a⁻¹[j] ↔ a[i] = j := by grind

theorem ne_getElem_inv_iff (hi : i < n) (hj : j < n) :
    i ≠ a⁻¹[j] ↔ a[i] ≠ j := by grind

theorem getElem_inv_eq_iff (hi : i < n) (hj : j < n) :
    a⁻¹[i] = j ↔ i = a[j] := by grind

theorem getElem_inv_ne_iff (hi : i < n) (hj : j < n) :
    a⁻¹[i] ≠ j ↔ i ≠ a[j] := by grind

end Inv

theorem mem_toVector_of_lt : ∀ i < n, i ∈ a.toVector :=
    fun i hi => Vector.mem_of_getElem (h := by grind) (i := a⁻¹[i]) (by grind)

theorem mem_invVector_of_lt : ∀ i < n, i ∈ a.invVector :=
    fun i hi => Vector.mem_of_getElem (h := by grind) (i := a[i]) (by grind)

theorem lt_of_mem_toVector : ∀ i ∈ a.toVector, i < n := by
  grind [Vector.mem_iff_getElem]

theorem lt_of_mem_invVector : ∀ i ∈ a.invVector, i < n := by
  grind [Vector.mem_iff_getElem]

@[grind =]
theorem mem_toVector_iff_lt {i : ℕ} : i ∈ a.toVector ↔ i < n := by
  grind [mem_toVector_of_lt, lt_of_mem_toVector]

@[grind =]
theorem mem_invVector_iff_lt {i : ℕ} : i ∈ a.invVector ↔ i < n := by
  grind [mem_invVector_of_lt, lt_of_mem_invVector]

theorem toVector_nodup : a.toVector.Nodup := by grind

theorem invVector_nodup : a.invVector.Nodup := by grind

@[ext, grind ext]
theorem ext (h : ∀ (i : ℕ) (hi : i < n), a[i] = b[i]) : a = b := by
  suffices h : a.toVector = b.toVector ∧ a.invVector = b.invVector by grind [cases PermOf]
  grind

section Ext

instance : DecidableEq (PermOf n) := fun _ _ => decidable_of_decidable_of_iff PermOf.ext_iff.symm

instance : Subsingleton (PermOf 0) where
  allEq a b := by simp_rw [PermOf.ext_iff, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true]

instance : Subsingleton (PermOf 1) where
  allEq a b := by grind

instance : Finite (PermOf n) := Finite.of_injective
  (fun a => (⟨a[·], a.getElem_lt⟩ : Fin n → Fin n)) <|
    fun a b hab => PermOf.ext <| fun _ hi => by have H := congrFun hab ⟨_, hi⟩; grind

end Ext

instance : One (PermOf n) where
  one := PermOf.mk (Vector.range n) (Vector.range n) (by grind)

section One

@[simp, grind =]
theorem getElem_one {i : ℕ} (hi : i < n) : (1 : PermOf n)[i] = i := Vector.getElem_range _

instance : Inhabited (PermOf n) := ⟨1⟩

@[simp]
theorem default_eq : (default : PermOf n) = 1 := rfl

theorem unique_zero : ∀ a : PermOf 0, a = 1 := by grind

theorem unique_one : ∀ a : PermOf 1, a = 1 := by grind

instance : Unique (PermOf 0) := Unique.mk' _

instance : Unique (PermOf 1) := Unique.mk' _

def zeroEquivFinOne : PermOf 0 ≃ Fin 1 := Equiv.ofUnique _ _
def oneEquivFinOne : PermOf 1 ≃ Fin 1 := Equiv.ofUnique _ _

end One


instance : Mul (PermOf n) where
  mul a b := {
    toVector := Vector.ofFn (fun i => a.toVector[b[(i : ℕ)]])
    invVector := Vector.ofFn (fun i => b⁻¹.toVector[a⁻¹[(i : ℕ)]])
    getElem_invVector_getElem_toVector := by grind }

section Mul

@[simp, grind =]
theorem getElem_mul {i : ℕ} (hi : i < n) :
    (a * b)[i] = a[b[i]] := Vector.getElem_ofFn _

end Mul

instance : Group (PermOf n) := Group.ofLeftAxioms (by grind) (by grind) (by grind)

section Group

theorem getElem_pow_eq_self_of_getElem_eq_self {k : ℕ} {hi : i < n}
  (hia : a[i] = i) : (a^k)[i] = i := by
  induction k with | zero => _ | succ k IH => _
  · simp_rw [pow_zero, getElem_one]
  · simp_rw [pow_succ, getElem_mul, hia, IH]

theorem getElem_inv_eq_self_of_getElem_eq_self {hi : i < n} :
  a[i] = i → (a⁻¹)[i] = i := by simp_rw [getElem_inv_eq_iff _ hi, eq_comm, imp_self]

theorem getElem_inv_ne_self_of_getElem_ne_self {hi : i < n}:
  a[i] ≠ i → (a⁻¹)[i] ≠ i := by simp_rw [ne_eq, getElem_inv_eq_iff _ hi, eq_comm, imp_self]

theorem getElem_zpow_eq_self_of_getElem_eq_self {k : ℤ} {hi : i < n}
    (hia : a[i] = i) : (a^k)[i] = i := by
  cases k
  · exact getElem_pow_eq_self_of_getElem_eq_self hia
  · simp_rw [zpow_negSucc]
    exact (getElem_inv_eq_self_of_getElem_eq_self (getElem_pow_eq_self_of_getElem_eq_self hia))

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

@[grind =]
theorem smul_def (i : ℕ) : a • i = a[i]?.getD i := rfl

instance : MulAction (PermOf n) ℕ where
  one_smul := by grind
  mul_smul := by grind

theorem getElem_eq_of_smul_eq (hab : a • i = b • i) {hi : i < n} : a[i] = b[i] := by grind

instance : FaithfulSMul (PermOf n) ℕ where eq_of_smul_eq_smul := by grind [getElem_eq_of_smul_eq]

theorem smul_eq_dite (i : ℕ) : a • i = if h : i < n then a[i]'h else i := by grind

theorem smul_of_lt {i : ℕ} (h : i < n) : a • i = a[i] := by grind

theorem smul_of_ge {i : ℕ} (h : n ≤ i) : a • i = i := by grind

@[simp] theorem smul_fin {i : Fin n} : a • i = a[i.1] := by grind

@[simp]
theorem smul_getElem {i : ℕ} (h : i < n) : a • b[i] = a[b[i]] :=
  a.smul_of_lt _

theorem smul_eq_iff {i j : ℕ} :
    a • i = j ↔ (∀ (hi : i < n), a[i] = j) ∧ (n ≤ i → i = j) := by grind
theorem eq_smul_iff {i j : ℕ} :
    i = a • j ↔ (∀ (hj : j < n), i = a[j]) ∧ (n ≤ j → i = j) := by grind

theorem smul_eq_self_iff {i : ℕ} :
    a • i = i ↔ ∀ (hi : i < n), a[i] = i := by grind

theorem self_eq_smul_iff {i : ℕ} :
    i = a • i ↔ ∀ (hi : i < n), i = a[i] := by grind

@[simp]
theorem smul_lt_iff_lt {i : ℕ} : a • i < n ↔ i < n := by grind

theorem smul_lt_of_lt {i : ℕ} (h : i < n) : a • i < n := by grind

theorem lt_of_smul_lt {i : ℕ} (h : a • i < n) : i < n := by grind

theorem smul_fin_lt {i : Fin n} : a • i < n := by grind


theorem smul_eq_smul_same_iff {i : ℕ} :
  a • i = b • i ↔ ∀ {hi : i < n}, a[i] = b[i] := by grind

theorem smul_right_inj {i j : ℕ} : a • i = a • j ↔ i = j := by grind

theorem smul_right_surj {i : ℕ} : ∃ j, a • j = i := ⟨a⁻¹ • i, by grind⟩

theorem eq_iff_smul_eq_smul_lt : a = b ↔ ∀ {i : ℕ}, i < n → a • i = b • i := by grind

theorem eq_iff_smul_eq_smul :
    a = b ↔ ∀ {i : ℕ}, a • i = b • i := by grind [getElem_eq_of_smul_eq]

theorem smul_eq_iff_eq_one : (∀ {i : ℕ}, a • i = i) ↔ a = 1 := by grind [getElem_eq_of_smul_eq]

theorem smul_eq_id_iff_eq_one : ((a • ·) : ℕ → ℕ) = id ↔ a = 1 := by
  grind [Function.id_def, getElem_eq_of_smul_eq]

end SMul

def ofFn (f g : Fin n → ℕ) (hf : ∀ i, f i < n) (hfg : ∀ i, g ⟨f i, hf _⟩ = i) : PermOf n :=
  PermOf.mk (Vector.ofFn f) (Vector.ofFn g) (by grind)

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
  invVector := a.invVector.swap a[i] a[j]
  getElem_invVector_getElem_toVector := by grind

section Swap

variable {i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n)

@[simp, grind =]
theorem getElem_swap : (a.swap i j)[k] = if k = i then a[j] else if k = j then a[i] else a[k] := by
  dsimp [swap]; grind

@[simp, grind =]
theorem getElem_inv_swap :
    (a.swap i j hi hj)⁻¹[k] = if k = a[i] then j else if k = a[j] then i else a⁻¹[k] := by
  dsimp [swap]; grind

theorem swap_smul_eq_smul_swap :
    (a.swap i j hi hj) • k = a • (Equiv.swap i j k) := by grind

theorem swap_inv_eq_swap_apply_inv_smul :
  (a.swap i j hi hj)⁻¹ • k = Equiv.swap i j (a⁻¹ • k) := by grind

theorem swap_smul_eq_swap_apply_smul :
    (a.swap i j hi hj) • k = Equiv.swap (a • i) (a • j) (a • k) := by grind

theorem swap_inv_smul_eq_inv_smul_swap : (a.swap i j hi hj)⁻¹ • k =
    a⁻¹ • (Equiv.swap (a • i) (a • j) k) := by grind

theorem swap_smul_left :
    (a.swap i j hi hj) • i = a • j := by grind

theorem swap_smul_right :
  (a.swap i j hi hj) • j = a • i := by grind

theorem swap_smul_of_ne_of_ne {k} :
  k ≠ i → k ≠ j → (a.swap i j hi hj) • k = a • k := by grind

theorem swap_inv_smul_left :
    (a.swap i j hi hj)⁻¹ • (a • i) = j := by grind

theorem swap_inv_smul_right :
    (a.swap i j hi hj)⁻¹ • (a • j) = i := by grind

theorem swap_inv_smul_of_ne_of_ne {k} :
  k ≠ a • i → k ≠ a • j → (a.swap i j hi hj)⁻¹ • k = a⁻¹ • k := by grind

@[simp]
theorem swap_self (i : ℕ) (hi hi' : i < n) : a.swap i i hi hi' = a := by grind

@[simp]
theorem swap_swap (i j : ℕ) (hi hi' : i < n) (hj hj' : j < n) :
    (a.swap i j hi hj).swap i j hi' hj' = a := by grind

theorem getElem_one_swap : (swap 1 i j hi hj)[k] = Equiv.swap i j k := by grind

theorem getElem_inv_one_swap : (swap 1 i j hi hj)⁻¹[k] = Equiv.swap i j k := by grind [inv_one]

theorem one_swap_smul : (swap 1 i j hi hj) • k = Equiv.swap i j k := by grind

theorem one_swap_inv_smul : (swap 1 i j hi hj)⁻¹ • k = Equiv.swap i j k := by grind [inv_one]

theorem one_swap_mul_self : swap 1 i j hi hj * swap 1 i j hi hj = 1 := by grind

theorem one_swap_inverse : (swap 1 i j hi hj)⁻¹ = swap 1 i j hi hj := by
  ext : 1
  rw [getElem_one_swap, getElem_inv_one_swap]

theorem swap_eq_mul_one_swap : a.swap i j hi hj = a * swap 1 i j hi hj := by grind

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

variable {n : ℕ} {a b : PermOf n}

open PermOf

def toPermOf (a : Vector ℕ n) (ha : ∀ x < n, x ∈ a := by decide) : PermOf n :=
  ⟨(Vector.range n).map a.toList.idxOf, a, fun {i hi} => by
    have H : List.idxOf i a.toList < a.toList.length := by grind [Vector.mem_toArray_iff]
    have H2 := List.getElem_idxOf H; grind⟩⁻¹

section ToPermOf

@[simp, grind =]
theorem getElem_toPermOf {a : Vector ℕ n} {ha : ∀ x < n, x ∈ a} {i : ℕ} (hi : i < n) :
    (toPermOf a ha)[i] = a[i] := rfl

@[simp] theorem toPermOf_toVector : toPermOf a.toVector (by grind) = a := by grind

@[simp] theorem toPermOf_invVector : toPermOf a.invVector (by grind) = a⁻¹ := by grind

def permOfEquiv : PermOf n ≃ Subtype (α := Vector ℕ n) (∀ x < n, x ∈ ·) where
  toFun a := ⟨a.toVector, mem_toVector_of_lt⟩
  invFun a := toPermOf a.1 a.2
  left_inv _ := toPermOf_toVector
  right_inv _ := Subtype.ext rfl

end ToPermOf

def shuffle {α : Type*} (a : PermOf n) (v : Vector α n) : Vector α n :=
  Vector.ofFn (fun i => v[a[i.1]])

section Shuffle

variable {α : Type*} {v : Vector α n}

@[simp, grind =] theorem getElem_shuffle {i : ℕ} (hi : i < n) :
    (v.shuffle a)[i] = v[a[i]] := Vector.getElem_ofFn _

@[simp, grind =] theorem getElem?_shuffle {i : ℕ} :
    (v.shuffle a)[i]? = if h : i < n then some v[a[i]] else none := Vector.getElem?_ofFn

@[simp, grind =]
theorem toList_shuffle : (v.shuffle a).toList = List.ofFn (fun i => v[a[i.1]]) :=
    List.ext_getElem? <| by grind

theorem mem_shuffle_iff {x : α} :
    x ∈ v.shuffle a ↔ x ∈ v := by
  simp_rw [Vector.mem_iff_getElem, getElem_shuffle]
  exact ⟨fun ⟨i, hi, hia⟩ => ⟨a[i], a.getElem_lt, by simpa using hia⟩,
    fun ⟨i, hi, hia⟩ => ⟨a⁻¹[i], a⁻¹.getElem_lt, by simpa using hia⟩⟩

theorem mem_of_mem_shuffle {x : α}
    (hx : x ∈ v.shuffle a) : x ∈ v := mem_shuffle_iff.mp hx
theorem mem_shuffle_of_mem {x : α}
    (hx : x ∈ v) : x ∈ v.shuffle a := mem_shuffle_iff.mpr hx

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

instance {α : Type*} : MulAction (PermOf n)ᵐᵒᵖ (Vector α n) where
  smul a v := v.shuffle a.unop
  one_smul := one_shuffle
  mul_smul _ _ := mul_shuffle

section SMulOp

variable {α : Type*}

@[simp] theorem op_smul (v : Vector α n) :
    (MulOpposite.op a) • v = v.shuffle a := rfl

@[simp] theorem unop_shuffle (a : (PermOf n)ᵐᵒᵖ) (v : Vector α n) :
    v.shuffle a.unop = a • v := rfl

end SMulOp

end Shuffle

end Vector
