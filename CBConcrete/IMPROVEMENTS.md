# Improvement Suggestions

## 1. Existential bundling in `PermOf` axiom — COMPLETED

The structure axiom bundled the bound proof with the inverse property in a single existential `∃ (hi' : toVector[i] < n), invVector[toVector[i]] = i`. Splitting into two separate fields makes projections definitional instead of requiring `.1`/`.2`.

## 2. `finPermEquiv : PermOf n ≃* Equiv.Perm (Fin n)` — COMPLETED

Added `finPerm`, `ofFinPerm`, and `finPermEquiv` providing a direct `MulEquiv` between `PermOf n` and `Equiv.Perm (Fin n)`, with simp lemmas. Also replaced `import Mathlib` with minimal imports in `MonoidHom.lean`.

## 3. `Decidable` instance for `BitInvariant`

`BitInvariant` is defined as equality of vectors, which is decidable when the element type has `DecidableEq`. But no `Decidable` instance is provided. Adding one would allow `#eval` and `decide` to work with `BitInvariant`:

```lean
instance : Decidable (a.BitInvariant i) := inferInstanceAs (Decidable (_ = _))
```

## 4. `Subgroup` instance for `BitInvariant`

You have `one_bitInvariant`, `BitInvariant.mul`, `BitInvariant.inv`, so `{a : PermOf n | a.BitInvariant i}` forms a subgroup. Registering this as a `Subgroup (PermOf n)` would let you use Mathlib's subgroup infrastructure (quotients, index, etc.):

```lean
def bitInvariantSubgroup (i : ℕ) : Subgroup (PermOf n) where
  carrier a := a.BitInvariant i
  mul_mem' := BitInvariant.mul
  one_mem' := one_bitInvariant
  inv_mem' := BitInvariant.inv
```

Similarly, for the intersection `∀ k < i, a.BitInvariant k`.

## 5. `smul_right_inj` as `@[simp]`

`smul_right_inj` (`Basic.lean:278`) is `a • i = a • j ↔ i = j`, which is a natural simp lemma but is not tagged. Similarly, `smul_eq_iff_eq_one` (`Basic.lean:287`) could be `@[simp]`.

## 6. Order / `orderOf` connection

`MulAction.lean` proves `isOfFinOrder` and `orderOf_pos` but doesn't connect `orderOf` to the cycle structure. A theorem like:

```lean
theorem orderOf_eq_lcm_period (a : PermOf n) :
    orderOf a = (Finset.range n).lcm (MulAction.period a ·)
```

would tie the group-theoretic order to the combinatorial cycle data.

## 7. `Fintype` instance

There's `Finite (PermOf n)` and `card_permOf_of_fintype` assumes `[Fintype (PermOf n)]`, but no `Fintype` instance is actually provided. The `decomposeFin` equivalence gives a natural path:

```lean
instance : Fintype (PermOf n) := Fintype.ofEquiv _ decomposeFin.symm
```

## 8. `pushEq` / `popOfEq` names

These names don't convey the mathematical content. `pushEq` embeds `PermOf n` into `PermOf (n+1)` by fixing the last element; `popOfEq` is the inverse when the last element is already fixed. Consider names like `fixLast` / `unfixLast`, or `embedSucc` / `restrictSucc`. The "Eq" in the name refers to `a[n] = n`, which isn't obvious.

## 9. File splitting

`MonoidHom.lean` is large and contains several logically distinct sections: `IsCongr`, `Cast`, `pushEq`/`popOfEq`, `push`/`pop`, `decomposeFin`, `castAdd`, `castGE`, `natPerm`/`natPermEquiv`, `finPermEquiv`, `minLen`/`minPerm`, `FinitePerm`, and `ofPermOf`. Splitting into separate files (e.g., `PermOf/Congr.lean`, `PermOf/Embed.lean`, `PermOf/MinPerm.lean`, `PermOf/FinitePerm.lean`) would make navigation easier and reduce build times when only part of the API changes.

**Plan:** [plans/09-split-monoidhom.md](plans/09-split-monoidhom.md)

## 10. `CycleMinVectorAux` naming

The `Aux` suffix is a Lean convention for helper definitions, but `CycleMinVectorAux` returns a `PermOf n × Vector ℕ n` where the first component tracks `a^(2^i)`. The pairing is an implementation detail of the doubling algorithm. Consider making it `private` or `protected` if it's not meant to be part of the public API.

## 11. `castAdd` recursive definition

`castAdd` is defined by recursion on `k`, applying `pushEq` one step at a time. For large `k`, this creates deeply nested terms. A direct definition via `castGE` (which already exists and has the right API) could replace it:

```lean
def castAdd (a : PermOf n) (k : ℕ) : PermOf (n + k) := a.castGE (Nat.le_add_right n k)
```

Currently `castGE` is defined *in terms of* `castAdd`, so the dependency would need to be reversed, but the resulting API would be simpler.

## 12. `grind` vs more targeted tactics

Many straightforward proofs use `grind` where `simp` or `exact` would suffice. While `grind` works, it can be slower than targeted tactics and may be fragile if `grind` behavior changes across Lean versions. For stability, consider reserving `grind` for genuinely hard goals. That said, if build time is acceptable, this is a stylistic preference.

## 13. Cycle type / sign

The `cycleOf` finset is defined, but there's no `cycleType` (as a multiset of cycle lengths) or `sign` function. These are natural next steps and would connect to `Equiv.Perm.cycleType` and `Equiv.Perm.sign` in Mathlib via `natPerm`.

## 14. `condFlipBit` as a primitive

The layer decomposition in `Controlbits.lean` uses `flipBitCommutator` and `CycleMinVector` to extract layers. A dedicated `condFlipBit : Vector Bool (2^n) → PermOf (2^(n+1))` constructor that directly builds the conditional bit-flip permutation from a boolean vector would make the decomposition statement cleaner and could serve as the building block for both analysis and synthesis of the control bit representation.
