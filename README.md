# GoldbachPsido — a Lean 4 + Mathlib formalization

Formalization of the definitions and lemmas of the paper
*"The Goldbach conjecture from the pseudodifferential calculus on the torus"*
(original Spanish title: *«La conjetura de Goldbach desde el cálculo pseudodiferencial en el toro»*).

> **Status.** The project builds with `lake build` without errors (Lean `v4.37.0-rc1`,
> Mathlib `master` as of 2026-11-22). 15 main theorems are fully proved and checked with
> `#print axioms` (only `propext`, `Classical.choice`, `Quot.sound`); 5 statements remain as `sorry`.
> See `STATUS.md` for details.
>
> Nothing here proves Goldbach: `BinaryGoldbach` is only a definition (a `Prop`).

## How to build

```bash
lake update                                   # fetch Mathlib (latest version)
cp .lake/packages/mathlib/lean-toolchain .    # use exactly Mathlib's Lean version
lake exe cache get                            # download precompiled Mathlib binaries
lake build
```

`lean-toolchain` is currently `v4.37.0-rc1` (Mathlib master of 2026-11-22; see `STATUS.md`).
The `cp` step replaces it with the one required by whichever Mathlib version you download.
To reproduce the exact checked build, skip `lake update` and use the committed `lake-manifest.json`.

To list the remaining `sorry`s:

```bash
grep -rn "^\s*sorry" GoldbachPsido/
```

## Layout

| File | Contents |
|---|---|
| `GoldbachPsido/Basic.lean` | `IsGoldbach`, `BinaryGoldbach`, `r N`, its parity, exceptional set `E X`, examples |
| `GoldbachPsido/FiniteCircle.lean` | root of unity `ζ M`, orthogonality, finite (proved) and continuous (`sorry`) circle method |
| `GoldbachPsido/Symbols.lean` | differences `Δ`, classes `S^m_{ρ,0}`, `𝟙_𝒫 ∈ S^0_{0,0}`, `𝟙_𝒫 ∉ S^m_{ρ,0}` (ρ>0) |
| `GoldbachPsido/Reflection.lean` | reflection operator `U_N`, exact Egorov, trace = `r N` |
| `GoldbachPsido/Ramanujan.lean` | Ramanujan sums, expansion, orthogonality (all `sorry`) |

## Suggested next steps

1. `circle_method` (continuous version): the plan is in the docstring (linearity of
   `fourierCoeff` + orthonormality of the Fourier basis).
2. Ramanujan sums: Kluyver's formula first; the other two identities build on it.
3. `cramer_mem_S010`: iterated mean value theorem plus derivative bounds for `1/log t`.
