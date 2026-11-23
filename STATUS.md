# Formalization status

**Last check:** 2026-11-22 — `lake build` finishes **without errors** (only `sorry` warnings
and the informational "imports `Mathlib` … module system" notice, which has no effect).

## Environment

| | |
|---|---|
| Lean | `leanprover/lean4:v4.37.0-rc1` (commit `0b77e12952ad39077d80d8bd6b66d601f225c321`) |
| Mathlib | `master`, commit `7dde1da6462d490beca415534c082b4f0435c9a9` (2026-11-22), via `lake exe cache get` |
| `lean-toolchain` | replaced with Mathlib master's (previously `v4.33.1`) |

Legend:

- **checked**: compiles without `sorry` and `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.
- **sorry**: statement only; the proof is pending (there is a plan in the docstring).

| # | Lean name | Statement | Status | Paper |
|---|---|---|---|---|
| 1 | `isGoldbach_iff_r_pos` | Goldbach(N) ⇔ r(N) > 0 | checked | §2.2 |
| 2 | `r_eq_sum` | r(N) = Σ_{n≤N} a(n)a(N−n) | checked | Prop. 3.3 |
| 3 | `refl_mem`, `refl_refl` | n ↦ N−n is an involution of the Goldbach set | checked | Prop. 3.3 |
| 4 | `r_mod_two` | r(N) odd ⇔ N = 2p, p prime | **checked (new)** | Rem. 3.4 |
| 5 | `binaryGoldbach_iff_E_zero` | binary Goldbach ⇔ E(X) = 0 ∀X | checked | §2.2 |
| — | examples `IsGoldbach 4, 100, 1000, 10^6` | explicit witnesses via `norm_num` | compile | — |
| 6 | `sum_root_pow` | Σ_{j<M} ζ^{jk} = M·[M∣k] | checked | Prop. 3.1 |
| 7 | `finite_circle` (+ `dvd_iff_eq_sub`) | exact finite circle method (M > 2N) | **checked (new)** | Prop. 3.1 |
| 8 | `circle_method` | N-th Fourier coefficient of S² = convolution | sorry | Prop. 3.1 |
| 9 | `abs_iterate_Δ_le` | \|σ\| ≤ B ⇒ \|Δ^kσ\| ≤ 2^k B | checked | Prop. 3.8 |
| 10 | `primeInd_mem_S00` | 𝟙_𝒫 ∈ S^0_{0,0} | checked | Prop. 3.8(a) |
| 11 | `primeInd_not_mem` (+ `iterate_Δ_int`, `Δ_eq_zero_of_Δ_Δ`, `Δ_eq_zero_of_iterate`) | ρ > 0 ⇒ 𝟙_𝒫 ∉ S^m_{ρ,0} | **checked (new)** | Prop. 3.8(b) |
| 12 | `cramer_mem_S010` | 1/log ξ ∈ S^0_{1,0} | sorry | Prop. 3.8(c) |
| 13 | `U_invol` | U_N² = I | checked | Prop. 3.5 |
| 14 | `egorov` | U_N Op(σ) U_N = Op(σ∘κ_N) | checked | Prop. 3.5 |
| 15 | `mult_mult` | Op(σ)Op(τ) = Op(στ) | checked | Prop. 3.5 |
| 16 | `trace_eq_r` | sum of the symbol of Π_𝒫U_NΠ_𝒫U_N = r(N) (ℕ version) | checked | Cor. 3.6 |
| 17 | `ramanujan_kluyver` | c_q(n) = Σ_{d∣(q,n)} μ(q/d)d | sorry | Prop. 3.10 |
| 18 | `ramanujan_expansion_coprime` | Σ_{r∣q} μ(r)/φ(r) c_r(n) = q/φ(q)·[(n,q)=1] | sorry | Prop. 3.10 |
| 19 | `ramanujan_orthogonality` | orthogonality of c_q over one period | sorry | Prop. 3.10 |

**Summary:** 15 main theorems checked (12 that were already written + 3 new ones), plus 4 new auxiliary
lemmas. **5 `sorry`s remain**: `circle_method`, `cramer_mem_S010` and the 3 in `Ramanujan.lean`.
No written proof failed: none had to be turned into `sorry`.
Nothing here proves Goldbach: `BinaryGoldbach` is only a definition (a `Prop`).

## Changes per file

- **`lean-toolchain`**: `v4.33.1` → `v4.37.0-rc1` (Mathlib master's).
- **`Basic.lean`**: proof of `r_mod_two` (previously `sorry`). Split `goldbachSet N` into
  `{2p < N} ∪ {2p = N} ∪ {2p > N}`; `Finset.card_nbij'` with the reflection between the first and the
  third; the middle one is `{N/2}` or `∅`. Statement unchanged.
- **`FiniteCircle.lean`**:
  - Proof of `finite_circle` (previously `sorry`) following the 4-step plan, with the new lemma
    `dvd_iff_eq_sub` (step 3). Statement unchanged.
  - `circle_method` (still `sorry`): `fourierCoeff` → `AddCircle.fourierCoeff` and `fourier` →
    `AddCircle.fourier` (the old names are deprecated; same definitions). Removed the hypothesis
    `[Fact ((0 : ℝ) < 1)]` because Mathlib already provides that global instance (the linter asked for
    it); the **meaning is unchanged**.
- **`Symbols.lean`**: proof of `primeInd_not_mem` (previously `sorry`), with 3 new lemmas:
  `iterate_Δ_int` (differences of an integer-valued function are integers), `Δ_eq_zero_of_Δ_Δ`
  (h bounded and Δ²h = 0 on [ξ₀,∞) ⇒ Δh = 0 there) and `Δ_eq_zero_of_iterate` (same for Δ^{j+1}).
  This replaces "Newton's formula + a bounded polynomial is constant": we get Δ𝟙_𝒫 = 0 on [ξ₀,∞),
  contradicting 𝟙_𝒫(p) = 1, 𝟙_𝒫(p+1) = 0 for an odd prime p ≥ ξ₀. Added `open Filter`.
  Statement unchanged.
- **`Reflection.lean`**, **`Ramanujan.lean`**: no code changes (they compiled on the first try).
- All comments and docstrings were translated from Spanish to English (no code changes).

No `axiom`, `native_decide`, `unsafe` or `set_option` was used.

## `#print axioms` output

(`circle_method` and `cramer_mem_S010` are included as a control: they show `sorryAx`.)

```
'GoldbachPsido.isGoldbach_iff_r_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.r_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.refl_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.refl_refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.r_mod_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.binaryGoldbach_iff_E_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.sum_root_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.dvd_iff_eq_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.finite_circle' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.abs_iterate_Δ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.primeInd_mem_S00' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.iterate_Δ_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.Δ_eq_zero_of_Δ_Δ' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.Δ_eq_zero_of_iterate' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.primeInd_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.U_invol' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.egorov' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.mult_mult' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.trace_eq_r' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachPsido.circle_method' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'GoldbachPsido.cramer_mem_S010' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

**Not formalized** (beyond reasonable reach with current Mathlib): L²(𝕋) spaces with trace-class
operators, S^m_{ρ,δ} classes with x-dependence, the Montgomery–Vaughan theorem (large sieve),
Vinogradov bounds, Bessel's inequality for minor arcs, the equidistribution theorem
(Theorem 3.12, which needs an upper-bound sieve of Brun/Selberg type).
