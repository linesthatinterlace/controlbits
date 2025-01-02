import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.SimpRw

namespace Nat

universe u

theorem fold_succ_zero {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    fold (n + 1) f init = (fold n (fun i h => f (i + 1) (by omega)) (f 0 (by omega) init)) := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [fold_succ, fold_zero]
  · rw [fold_succ, IH, fold_succ]

theorem foldRev_succ_zero {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n + 1 → α → α) (init : α) :
    foldRev (n + 1) f init = f 0 (by omega)
    (foldRev n (fun i hi => f (i + 1) (by omega)) init) := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_succ, foldRev_zero]
  · rw [foldRev_succ, IH, foldRev_succ]

theorem foldRev_eq_fold_of_apply_eq_apply_pred_sub' {α : Type u} (n : Nat)
    (f g : (i : Nat) → i < n → α → α)
    (hfg : ∀ i (hi : i < n) , f i hi = g ((n - i) - 1) (by omega)) (init : α) :
    foldRev n f init = fold n g init := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_zero, fold_zero]
  · simp_rw [foldRev_succ_zero, fold_succ, hfg 0, Nat.sub_zero, Nat.add_one_sub_one]
    exact congrArg _ (IH _ _ (fun i hi => (hfg (i + 1) (Nat.succ_lt_succ hi)).trans
      (funext (fun _ => by simp_rw [Nat.add_sub_add_right]))) _)

theorem foldRev_eq_fold_of_apply_eq_apply_pred_sub {α : Type u} (n : Nat)
    (f g : (i : Nat) → i < n → α → α)
    (hfg : ∀ i j (hi : i < n) (hj : j < n), i + j = n - 1 → f i hi = g j hj) (init : α) :
    foldRev n f init = fold n g init := by
  induction n generalizing init with | zero => _ | succ n IH => _
  · simp_rw [foldRev_zero, fold_zero]
  · rw [foldRev_succ_zero, fold_succ, hfg 0 n (by omega) (by omega) (by omega)]
    congr
    refine IH _ _ (fun x y hx hy hxy => hfg _ _ _ _ ?_) _
    omega

theorem foldRev_eq_fold {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n → α → α) (init : α) :
    foldRev n f init = fold n (fun i (hi : i < n) => f ((n - 1) - i) (by omega)) init := by
  refine foldRev_eq_fold_of_apply_eq_apply_pred_sub _ _ _ (fun i j hi hj hij => ?_) _
  conv =>
    lhs
    congr
    rw [Nat.eq_sub_of_add_eq hij]

theorem fold_eq_foldRev {α : Type u} (n : Nat)
    (f : (i : Nat) → i < n → α → α) (init : α) :
    fold n f init = foldRev n (fun i (hi : i < n) => f ((n - 1) - i) (by omega)) init := by
  refine (foldRev_eq_fold_of_apply_eq_apply_pred_sub _ _ _ (fun i j hi hj hij => ?_) _).symm
  conv =>
    rhs
    congr
    rw [Nat.eq_sub_of_add_eq' hij]

end Nat
