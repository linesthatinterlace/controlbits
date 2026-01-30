# Plan: Split MonoidHom.lean (Improvement #9)

## Current State

`MonoidHom.lean` is ~1420 lines containing 10+ logically distinct sections. It currently lives at `PermOf/MonoidHom.lean` and is imported by `CBConcrete.lean`.

## Proposed Split

### File 1: `PermOf/Congr.lean` (~200 lines)
- **Imports:** `PermOf.Basic`
- **Contains:** `IsCongr`, `IsCongrSubgroup`
- Lines 92-196

### File 2: `PermOf/Cast.lean` (~100 lines)
- **Imports:** `PermOf.Congr`
- **Contains:** `Cast`, `castMulEquiv`
- Lines 198-295

### File 3: `PermOf/Embed.lean` (~200 lines)
- **Imports:** `PermOf.Cast`
- **Contains:** `pushEq`, `pushEqHom`, `popOfEq`, `push`, `pop`, `decomposeFin`, `card_permOf`
- Lines 297-512
- Note: `exists_pushEq_apply`, `range_pushEq`, `coe_range_pushEqHom` need `Mathlib.Algebra.Group.Subgroup.Ker` for `MonoidHom.range`

### File 4: `PermOf/CastGE.lean` (~190 lines)
- **Imports:** `PermOf.Embed` (needs `castAdd` which uses `pushEq`)
- **Contains:** `castAdd`, `castAddHom`, `castGE`, `castGEHom`
- Lines 513-698

### File 5: `PermOf/PermEquiv.lean` (~230 lines)
- **Imports:** `PermOf.CastGE`, Mathlib group action/subgroup imports
- **Contains:** `Equiv.Perm.FixGENat`, `FinitePermNat` (currently in `Equiv.Perm` namespace, lines 7-90), `ofFixGENat`, `natPerm`, `natPermEquiv`, `finPerm`, `ofFinPerm`, `finPermEquiv`
- The `Equiv.Perm` namespace block (lines 7-90) moves here since it's only used by `natPerm`

### File 6: `PermOf/MinPerm.lean` (~270 lines)
- **Imports:** `PermOf.PermEquiv`
- **Contains:** `minLen`, `minPerm`
- Lines 925-1192

### File 7: `PermOf/FinitePerm.lean` (~230 lines)
- **Imports:** `PermOf.MinPerm`
- **Contains:** `FinitePerm` structure, its `Group`/`MulAction` instances, `ofPermOf`, `FinitePerm.natPerm`, `mulEquivFinitePermNat`
- Lines 1194-1421

## Dependency Chain

```
PermOf.Basic
  -> PermOf.Congr       (IsCongr)
    -> PermOf.Cast       (cast, castMulEquiv)
      -> PermOf.Embed    (pushEq, popOfEq, push, pop, decomposeFin)
        -> PermOf.CastGE (castAdd, castGE)
          -> PermOf.PermEquiv (FixGENat, natPerm, finPerm, natPermEquiv, finPermEquiv)
            -> PermOf.MinPerm (minLen, minPerm)
              -> PermOf.FinitePerm (FinitePerm, ofPermOf)
```

## Execution Steps

1. Create files bottom-up (starting with `Congr.lean`), moving code section by section
2. Each file gets only the Mathlib imports it needs (use `#min_imports` to verify)
3. Update `CBConcrete.lean` to import `PermOf.FinitePerm` (the leaf) instead of `PermOf.MonoidHom`
4. Delete `MonoidHom.lean`
5. Run `lake build` — must succeed with no errors or warnings
6. Verify no other files import `PermOf.MonoidHom` (currently none do, only `CBConcrete.lean`)

## Risks

- **Section variable scoping:** Some theorems (e.g., `exists_pushEq_apply`) pick up section variables. Moving them to new sections/files may change their signatures. Test carefully.
- **`Equiv.Perm` namespace:** The `FixGENat`/`FinitePermNat` block (lines 7-90) is in `Equiv.Perm` namespace but only used by `natPerm` and `FinitePerm.natPerm`. It could stay in `PermEquiv.lean` or get its own file.
- **Import minimality:** Each new file should use `#min_imports` to ensure no unnecessary Mathlib transitive imports creep in.
