import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.ZMod.Basic

open Nat



def foldFin (m : ℕ) (i : Fin (2*m + 1)) : Fin (m + 1) :=
if h : (i : ℕ) < m + 1 then i.castLT h else
((finCongr (by simp_rw [two_mul, add_assoc, add_comm]) i).subNat m
  (Nat.lt_of_succ_le (le_of_not_lt h)).le).rev

#eval foldFin (m := 9)

lemma le_bit0 : m ≤ 2*m := le_mul_of_pos_left zero_lt_two

lemma lt_bit1 : m < 2*m + 1 := lt_succ_of_le le_bit0

lemma le_bit1 : m + 1 ≤ 2*m + 1 := Nat.succ_le_succ le_bit0

lemma coe_foldFinLE {i : Fin (2*m + 1)} (h : (i : ℕ) ≤ m) : (foldFin m i : ℕ) = i := by
  simp_rw [foldFin, Nat.lt_succ_of_le h, dite_true, Fin.coe_castLT]

lemma coe_foldFinEQ {i : Fin (2*m + 1)} (h : (i : ℕ) = m) :
  (foldFin m i : ℕ) = i := coe_foldFinLE h.le

lemma coe_foldFinLT {i : Fin (2*m + 1)} (h : (i : ℕ) < m) :
  (foldFin m i : ℕ) = i := coe_foldFinLE h.le

lemma foldFinCastLE (i : Fin (m + 1)) : foldFin m (i.castLE le_bit1) = i := by
  rw [Fin.ext_iff, coe_foldFinLE (Nat.le_of_lt_succ i.isLt), Fin.coe_castLE]

lemma foldFinCastLELast : foldFin m ((Fin.last m).castLE le_bit1) = Fin.last m := foldFinCastLE _

lemma foldFinCastLT (i : Fin m) : foldFin m (i.castLT (i.isLt.trans lt_bit1)) = i.castSucc := by
  rw [Fin.ext_iff, coe_foldFinLT i.isLt, Fin.coe_castLT, Fin.coe_castSucc]

lemma foldFin_zero : foldFin m 0 = 0 := Fin.castLE_zero _ ▸ foldFinCastLE _


/-




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
-/
