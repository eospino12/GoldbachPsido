# Estado de la formalización

**Última verificación:** 2026-11-22 — `lake build` termina **sin errores** (solo advertencias de `sorry`
y el aviso informativo «imports `Mathlib` … module system», que no afecta a nada).

## Entorno usado

| | |
|---|---|
| Lean | `leanprover/lean4:v4.37.0-rc1` (commit `0b77e12952ad39077d80d8bd6b66d601f225c321`) |
| Mathlib | `master`, commit `7dde1da6462d490beca415534c082b4f0435c9a9` (2026-11-22), vía `lake exe cache get` |
| `lean-toolchain` | reemplazado por el de Mathlib master (antes `v4.33.1`) |

Leyenda:

- **verificada**: compila sin `sorry` y `#print axioms` muestra solo `propext`, `Classical.choice`, `Quot.sound`.
- **sorry**: solo el enunciado; la prueba queda pendiente (hay un plan en el docstring).

| # | Nombre en Lean | Enunciado | Estado | Artículo |
|---|---|---|---|---|
| 1 | `isGoldbach_iff_r_pos` | Goldbach(N) ⇔ r(N) > 0 | verificada | §2.2 |
| 2 | `r_eq_sum` | r(N) = Σ_{n≤N} a(n)a(N−n) | verificada | Prop. 3.3 |
| 3 | `refl_mem`, `refl_refl` | n ↦ N−n es involución del conjunto de Goldbach | verificada | Prop. 3.3 |
| 4 | `r_mod_two` | r(N) impar ⇔ N = 2p, p primo | **verificada (nueva)** | Obs. 3.4 |
| 5 | `binaryGoldbach_iff_E_zero` | Goldbach binaria ⇔ E(X) = 0 ∀X | verificada | §2.2 |
| — | ejemplos `IsGoldbach 4, 100, 1000, 10^6` | testigos explícitos con `norm_num` | compilan | — |
| 6 | `sum_root_pow` | Σ_{j<M} ζ^{jk} = M·[M∣k] | verificada | Prop. 3.1 |
| 7 | `finite_circle` (+ `dvd_iff_eq_sub`) | método del círculo finito exacto (M > 2N) | **verificada (nueva)** | Prop. 3.1 |
| 8 | `circle_method` | coeficiente de Fourier N de S² = convolución | sorry | Prop. 3.1 |
| 9 | `abs_iterate_Δ_le` | \|σ\| ≤ B ⇒ \|Δ^kσ\| ≤ 2^k B | verificada | Prop. 3.8 |
| 10 | `primeInd_mem_S00` | 𝟙_𝒫 ∈ S^0_{0,0} | verificada | Prop. 3.8(a) |
| 11 | `primeInd_not_mem` (+ `iterate_Δ_int`, `Δ_eq_zero_of_Δ_Δ`, `Δ_eq_zero_of_iterate`) | ρ > 0 ⇒ 𝟙_𝒫 ∉ S^m_{ρ,0} | **verificada (nueva)** | Prop. 3.8(b) |
| 12 | `cramer_mem_S010` | 1/log ξ ∈ S^0_{1,0} | sorry | Prop. 3.8(c) |
| 13 | `U_invol` | U_N² = I | verificada | Prop. 3.5 |
| 14 | `egorov` | U_N Op(σ) U_N = Op(σ∘κ_N) | verificada | Prop. 3.5 |
| 15 | `mult_mult` | Op(σ)Op(τ) = Op(στ) | verificada | Prop. 3.5 |
| 16 | `trace_eq_r` | Σ del símbolo de Π_𝒫U_NΠ_𝒫U_N = r(N) (versión en ℕ) | verificada | Cor. 3.6 |
| 17 | `ramanujan_kluyver` | c_q(n) = Σ_{d∣(q,n)} μ(q/d)d | sorry | Prop. 3.10 |
| 18 | `ramanujan_expansion_coprime` | Σ_{r∣q} μ(r)/φ(r) c_r(n) = q/φ(q)·[(n,q)=1] | sorry | Prop. 3.10 |
| 19 | `ramanujan_orthogonality` | ortogonalidad de c_q en un periodo | sorry | Prop. 3.10 |

**Resumen:** 15 teoremas principales verificados (12 que ya estaban escritos + 3 nuevos), más 4 sub-lemas
auxiliares nuevos. Quedan **5 `sorry`**: `circle_method`, `cramer_mem_S010` y los 3 de `Ramanujan.lean`.
Ninguna prueba escrita falló: no hubo que convertir ninguna en `sorry`.
Nada de esto demuestra Goldbach: `BinaryGoldbach` es solo una definición (`Prop`).

## Cambios por archivo

- **`lean-toolchain`**: `v4.33.1` → `v4.37.0-rc1` (el de Mathlib master).
- **`Basic.lean`**: prueba de `r_mod_two` (antes `sorry`). Partición de `goldbachSet N` en
  `{2p < N} ∪ {2p = N} ∪ {2p > N}`; `Finset.card_nbij'` con la reflexión entre el primero y el tercero;
  el del medio es `{N/2}` o `∅`. Enunciado sin cambios.
- **`FiniteCircle.lean`**:
  - Prueba de `finite_circle` (antes `sorry`) siguiendo el plan de 4 pasos, con el sub-lema nuevo
    `dvd_iff_eq_sub` (paso 3). Enunciado sin cambios.
  - `circle_method` (sigue en `sorry`): `fourierCoeff` → `AddCircle.fourierCoeff` y `fourier` →
    `AddCircle.fourier` (los nombres viejos están deprecados; son las mismas definiciones). Se quitó la
    hipótesis `[Fact ((0 : ℝ) < 1)]` porque Mathlib ya trae esa instancia global (el linter lo pedía);
    el **significado no cambia**.
- **`Symbols.lean`**: prueba de `primeInd_not_mem` (antes `sorry`), con 3 sub-lemas nuevos:
  `iterate_Δ_int` (diferencias de una función entera son enteras), `Δ_eq_zero_of_Δ_Δ`
  (h acotada y Δ²h = 0 en [ξ₀,∞) ⇒ Δh = 0 allí) y `Δ_eq_zero_of_iterate` (lo mismo para Δ^{j+1}).
  Esto sustituye a «Newton + polinomio acotado ⇒ constante»: se obtiene Δ𝟙_𝒫 = 0 en [ξ₀,∞), lo que
  contradice 𝟙_𝒫(p) = 1, 𝟙_𝒫(p+1) = 0 para un primo impar p ≥ ξ₀. Se añadió `open Filter`.
  Enunciado sin cambios.
- **`Reflection.lean`**, **`Ramanujan.lean`**: sin cambios (compilaron a la primera).

No se usó `axiom`, `native_decide`, `unsafe` ni `set_option`.

## Salida de `#print axioms`

(`circle_method` y `cramer_mem_S010` se incluyen como control: muestran `sorryAx`.)

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

**No formalizado** (fuera de alcance razonable con Mathlib actual): espacios L²(𝕋) con operadores
de traza, clases S^m_{ρ,δ} con dependencia en x, teorema de Montgomery–Vaughan (criba grande),
cotas de Vinogradov, desigualdad de Bessel para arcos menores, el teorema de equidistribución
(Teorema 3.12, necesita una criba superior de Brun/Selberg).
