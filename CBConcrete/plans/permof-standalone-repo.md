# Notes: PermOf Standalone Repo / Mathlib Contribution

## Goal
Extract `PermOf` into a standalone repo, polish for Mathlib contribution.

## Value Over `Equiv.Perm (Fin n)`
- Both store inverses (O(1) lookup either direction)
- `PermOf` uses real arrays (`Vector`) rather than opaque functions — in practice this can be faster for computation-heavy proofs and `#eval`
- `finPermEquiv` proves equivalence, so theorems transfer freely
- The control bit decomposition is a good showcase of array-indexed permutation work

## Pre-Mathlib Checklist
- Revisit structure axiom (existential bundling, improvement #1) — reviewers will flag
- Add `Fintype` instance (improvement #7)
- Add `Repr`/`ToString` instances
- Consider `Decidable` for `BitInvariant` (improvement #3)
- Split `MonoidHom.lean` (improvement #9, plan exists)
- Cycle type, sign — prove by transfer via `finPermEquiv` rather than duplicating Mathlib proofs
- Position as "computational frontend to `Equiv.Perm`", not a competitor

## Strategy
- Use `finPermEquiv` as the canonical bridge
- Transfer theorems from `Equiv.Perm` where possible
- Keep native proofs only where the array representation genuinely helps (e.g., control bits, grind-based automation)
