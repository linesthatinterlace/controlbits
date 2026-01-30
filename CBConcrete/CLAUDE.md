# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

This is a Lean 4 project using Lake as the build system.

- **Build:** `lake build`
- **Clean build:** `lake clean && lake build`
- **Update dependencies:** `lake update`
- **Lean toolchain:** `leanprover/lean4:v4.28.0-rc1` (see `lean-toolchain`)

There are no separate test or lint commands. Lean's type checker serves as verification — if `lake build` succeeds with no errors or warnings, all proofs are valid. Lint warnings (whitespace, empty lines, unused simp args) must also be fixed.

## Project Overview

CBConcrete is a Lean 4 formalization of control bit decomposition for permutations, built on top of Mathlib. The central result is decomposing permutations on `2^(n+1)` elements into layers of conditional bit flips.

## Architecture

### Core Data Structure

**`PermOf n`** (`PermOf/Basic.lean`) — A permutation on `n` elements represented by paired vectors (`toVector` and `invVector`) that are inverse to each other. This is a more performant alternative to Mathlib's `Equiv.Perm`, with custom `GetElem` indexing so `a[i]` gives the image of `i`.

### Module Dependency Chain

```
CBConcrete.lean
└── Controlbits        — Layer decomposition (leftLayer, rightLayer)
    └── Flipbit         — flipBit, flipBitCommutator, CycleMinVector on PermOf
        └── RemoveInsert — Bit-level removeBit/insertBit on ℕ
        └── PermOf.BitInvariant — BitInvariant predicate on PermOf
            └── PermOf.MulAction  — Group action of PermOf on ℕ
                └── PermOf.MonoidHom — Monoid/group homomorphisms to Equiv.Perm
                    └── PermOf.Basic  — Core PermOf structure and group operations
```

### Lib/ Directory

Extensions to Mathlib types (`Array`, `Vector`, `Nat`, `Bool`, `Fin`, `List`, `Finset`, `MulAction`, `Logic`, `Equiv`) providing lemmas not yet in Mathlib that the main development needs.

### Key Bit Operations (on `ℕ`)

- **`removeBit q i`** — Erase the `(i+1)`-th least significant bit from `q`
- **`insertBit b p i`** — Insert bit `b` as the `(i+1)`-th least significant bit of `p`
- **`flipBit q i`** — Toggle bit `i` of `q` (defined as `q ^^^ 1 <<< i`)

### Key PermOf Operations

- **`flipBitCommutator i`** — Conjugation-style commutator involving bit flip at position `i`
- **`CycleMinVector k`** — Vector of cycle minimums under iterated application
- **`BitInvariant j`** — Predicate: permutation preserves bit `j` of every element
- **`leftLayer` / `rightLayer`** — The layer decomposition of a permutation

## Lean Configuration

From `lakefile.toml`:
- `relaxedAutoImplicit = false` — all implicit arguments must be declared explicitly
- `pp.unicode.fun = true` — pretty-prints `fun a ↦ b`
- Mathlib linter enabled (`weak.linter.mathlibStandardSet = true`)

## Proof Style Conventions

- Heavy use of the `grind` tactic and `@[grind =]` annotations for automated equational reasoning
- Extensive `@[simp]` lemma tagging (250+ lemmas) for rewriting
- Bit-level theorems follow an inductive pattern: `_zero` base case, `_succ` step case
- `grind_pattern` declarations guide the `grind` tactic's matching
