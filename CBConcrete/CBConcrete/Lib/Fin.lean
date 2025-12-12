import Mathlib.Data.Fin.SuccPred

namespace Fin

variable {m : ℕ}

theorem coe_succAbove {i : Fin m} {j : Fin (m + 1)} :
    (j.succAbove i : ℕ) = i.val + if j.val ≤ i.val then 1 else 0 := by
  grind [succAbove, coe_castSucc, val_succ]

theorem coe_predAbove {i : Fin m} {j : Fin (m + 1)} :
    (i.predAbove j : ℕ) = j.val - (if i.val < j.val then 1 else 0) := by
  grind [predAbove, coe_castSucc, coe_pred, coe_castPred]

@[simp]
theorem coe_xor {i j : Fin m} : (i ^^^ j).val = (i.val ^^^ j.val) % m := rfl

end Fin
