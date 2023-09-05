import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.ZMod.Basic

open Nat

def foldFin (i : Fin (2*m + 1)) : Fin (m + 1) := m - (dist i m)

lemma le_bit0 : m ≤ 2*m := le_mul_of_pos_left zero_lt_two

lemma lt_bit1 : m < 2*m + 1 := lt_succ_of_le le_bit0

lemma foldFinCast_of_le (hn : n ≤ m) : foldFin (n : Fin (2*m + 1)) = n := by
rw [foldFin, Fin.coe_ofNat_eq_mod, mod_eq_of_lt (lt_of_le_of_lt hn lt_bit1), Nat.dist_eq_sub_of_le hn]
rw [cast_sub (R := Fin (m + 1)) hn, sub_sub_cancel]

lemma foldFinZero : foldFin 0 = (0 : Fin (2*m + 1)) := foldFinCast_of_le (Nat.zero_le _)

lemma foldFinCast_of_ge (hn₁ : m ≤ n) (hn₂ : n < 2*m + 1) : foldFin (n : Fin (2*m + 1)) = 2*m - n := by
rw [foldFin, Fin.coe_ofNat_eq_mod, mod_eq_of_lt hn₂, Nat.dist_eq_sub_of_le_right hn₁, cast_sub hn₁]
ring

lemma foldFin2M: foldFin (2*m : ℕ) = (0 : Fin (m + 1)) := by
rw [foldFinCast_of_ge le_bit0 (lt_succ_self _), cast_mul, cast_two, sub_self]

lemma foldFinM : foldFin (m : ℕ) = (m : Fin (m + 1)) := foldFinCast_of_le (le_refl _)