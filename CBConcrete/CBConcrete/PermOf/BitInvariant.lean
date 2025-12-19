import CBConcrete.PermOf.Basic
import CBConcrete.Lib.Nat
import CBConcrete.Lib.Bool

namespace PermOf

section BitInvariant

variable {n i k x l : ℕ}

theorem getElem_testBit_of_ge (a : PermOf n) {k : ℕ} (h : n ≤ 2^k) {i : ℕ} (hi : i < n) :
    a[i].testBit k = false :=
  Nat.testBit_lt_two_pow <| a.getElem_lt.trans_le h

open Nat

def BitInvariant (i : ℕ) (a : PermOf n) : Prop :=
  a.toVector.map (testBit · i) = (Vector.range n).map (testBit · i)

variable {a b : PermOf n}

theorem one_bitInvariant : BitInvariant i (1 : PermOf n) := rfl

theorem bitInvariant_iff_testBit_getElem_eq_testBit : a.BitInvariant i ↔
    ∀ {x} (h : x < n), a[x].testBit i = x.testBit i := by
  unfold BitInvariant
  simp_rw [Vector.ext_iff, Vector.getElem_map, getElem_toVector, Vector.getElem_range]

theorem bitInvariant_of_ge (h : n ≤ 2^i) : a.BitInvariant i := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit, a.getElem_testBit_of_ge h]
  exact fun (hx : _ < n) => (Nat.testBit_lt_two_pow (hx.trans_le h)).symm

theorem bitInvariant_of_ge_of_ge (h : n ≤ 2^i) (hk : i ≤ k) : a.BitInvariant k :=
  bitInvariant_of_ge (h.trans (Nat.pow_le_pow_right Nat.zero_lt_two hk))

theorem bitInvariant_lt_of_lt_iff_testBit_getElem_eq_testBit_of_lt : (∀ k < i, a.BitInvariant k) ↔
    (∀ {x : ℕ} (h : x < n), ∀ k < i, a[x].testBit k = x.testBit k) := by
  simp_rw [bitInvariant_iff_testBit_getElem_eq_testBit]
  exact forall₂_swap

theorem bitInvariant_lt_of_lt_iff_getElem_mod_two_pow_eq_mod_two_pow : (∀ k < i, a.BitInvariant k) ↔
    ∀ {x} (h : x < n), a[x] % 2^i = x % 2^i := by
  simp_rw [Nat.testBit_eq_iff, testBit_mod_two_pow,
    bitInvariant_lt_of_lt_iff_testBit_getElem_eq_testBit_of_lt,
    Bool.and_inj_left, decide_eq_false_iff_not, imp_iff_not_or]

theorem forall_lt_bitInvariant_iff_eq_one_of_ge (hin : n ≤ 2^i) :
    (∀ k < i, a.BitInvariant k) ↔ a = 1 := by
  simp_rw [bitInvariant_lt_of_lt_iff_getElem_mod_two_pow_eq_mod_two_pow,
    PermOf.ext_iff, getElem_one, Nat.mod_eq_of_lt <| a.getElem_lt.trans_le hin]
  exact forall₂_congr (fun k hk => (Nat.mod_eq_of_lt <| hk.trans_le hin).congr_right)

@[simp]
theorem BitInvariant.testBit_getElem_eq_testBit (ha : a.BitInvariant i) {x : ℕ}
    (h : x < n) : a[x].testBit i = x.testBit i :=
  bitInvariant_iff_testBit_getElem_eq_testBit.mp ha h

theorem bitInvariant_of_testBit_getElem_eq_testBit (h : ∀ {x} (h : x < n),
    a[x].testBit i = x.testBit i) : a.BitInvariant i :=
  bitInvariant_iff_testBit_getElem_eq_testBit.mpr h

@[simp]
theorem BitInvariant.inv (ha : a.BitInvariant i) :
    BitInvariant i a⁻¹ := bitInvariant_of_testBit_getElem_eq_testBit <| fun hi => by
  rw [← ha.testBit_getElem_eq_testBit (getElem_lt _), getElem_getElem_inv]

theorem BitInvariant.of_inv (ha : a⁻¹.BitInvariant i) : BitInvariant i a := ha.inv

theorem bitInvariant_iff_bitInvariant_inv : a⁻¹.BitInvariant i ↔ a.BitInvariant i :=
  ⟨fun h => h.inv, fun h => h.inv⟩

theorem BitInvariant.mul (ha : a.BitInvariant i) (hb : b.BitInvariant i) :
    BitInvariant i (a * b) := bitInvariant_of_testBit_getElem_eq_testBit <| by
  simp_rw [getElem_mul, ha.testBit_getElem_eq_testBit,
  hb.testBit_getElem_eq_testBit, implies_true]

theorem BitInvariant.pow (ha : a.BitInvariant i) (p : ℕ) : (a ^ p).BitInvariant i := by
  induction p with | zero | succ p IH
  · exact one_bitInvariant
  · rw [pow_succ]
    exact BitInvariant.mul IH ha

theorem BitInvariant.zpow (ha : a.BitInvariant i) (p : ℤ) : (a ^ p).BitInvariant i := by
  cases p
  · simp_rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact ha.pow _
  · simp only [zpow_negSucc]
    exact (ha.pow _).inv

theorem self_le_getElem_of_forall_bitInvariant_lt_of_lt (ha : ∀ k < i, a.BitInvariant k)
    (hx : x < 2^i) (hin : 2^i ≤ n) : ∀ k, x ≤ (a^k)[x] := fun k =>
  ((Nat.mod_eq_of_lt hx).symm.trans
  ((bitInvariant_lt_of_lt_iff_getElem_mod_two_pow_eq_mod_two_pow.mp
    (fun _ hk => (ha _ hk).pow k) _).symm)).trans_le (Nat.mod_le _ (2^i))

end BitInvariant

end PermOf
