import Mathlib.Data.Fin.SuccPred

namespace Fin

variable {n : ℕ}

@[simp, grind =]
theorem coe_xor {i j : Fin n} : (i ^^^ j).val = (i.val ^^^ j.val) % n := rfl

@[grind =]
theorem coe_succAbove {i : Fin n} {p : Fin (n + 1)} :
    (p.succAbove i : ℕ) = if p.val ≤ i.val then i.val + 1 else i.val := by
  grind [succAbove, coe_castSucc, val_succ]

@[grind =]
theorem coe_predAbove {p : Fin n} {i : Fin (n + 1)} :
    (p.predAbove i : ℕ) = if p.val < i.val then i.val - 1 else i.val := by
  grind [predAbove, coe_castSucc, coe_pred, coe_castPred]

def newPredAbove (p i : Fin (n + 1)) (hip : i ≠ p) : Fin n :=
  if h : p < i then i.pred <| p.ne_zero_of_lt h
  else i.castPred <| i.ne_last_of_lt ((i.lt_or_lt_of_ne hip).resolve_right h)

@[simp, grind =]
theorem coe_newPredAbove {p i : Fin (n + 1)} {hip : i ≠ p} :
    (p.newPredAbove i hip  : ℕ) = if p.val < i.val then i.val - 1 else i.val := by
  grind [newPredAbove, coe_pred, coe_castPred]

theorem predAbove_eq_newPredAbove_succAbove (p : Fin n) (i : Fin (n + 1)) :
    p.predAbove i = newPredAbove (i.succAbove p) i (ne_succAbove _ _) := Fin.ext <| by grind

theorem newPredAbove_eq_dite_castPred_predAbove {p i : Fin (n + 1)} {hip : i ≠ p} :
    p.newPredAbove i hip = if h : p = last n then
    i.castPred (h ▸ hip) else (p.castPred h).predAbove i := Fin.ext <| by
  grind [val_last, coe_castPred]

end Fin
