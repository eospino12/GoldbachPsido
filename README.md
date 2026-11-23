# GoldbachPsido — formalización en Lean 4 + Mathlib

Formalización de las definiciones y lemas del artículo
*«La conjetura de Goldbach desde el cálculo pseudodiferencial en el toro»*.

> **Aviso importante.** Este proyecto se escribió en un entorno **sin Lean instalado**.
> **Ningún archivo se compiló.** Las pruebas marcadas «escrita» son pruebas completas
> (sin `sorry`), pero pueden fallar por nombres de lemas de Mathlib que cambiaron
> o por detalles de tácticas. Lo primero que hay que hacer es `lake build` y anotar los errores.
> Ver `STATUS.md`.

## Cómo compilar

```bash
cd lean
lake update                                   # descarga Mathlib (última versión)
cp .lake/packages/mathlib/lean-toolchain .    # usa exactamente la versión de Lean de Mathlib
lake exe cache get                            # binarios precompilados de Mathlib
lake build
```

El archivo `lean-toolchain` ahora es `v4.37.0-rc1` (Mathlib master del 2026-11-22; ver STATUS.md). El paso `cp`
lo reemplaza por el que exige la versión de Mathlib que descargues.

Para contar los `sorry` que quedan:

```bash
grep -rn "sorry" GoldbachPsido/ | grep -v "^.*--"
```

## Estructura

| Archivo | Contenido |
|---|---|
| `GoldbachPsido/Basic.lean` | `IsGoldbach`, `BinaryGoldbach`, `r N`, conjunto excepcional `E X`, ejemplos |
| `GoldbachPsido/FiniteCircle.lean` | raíz de la unidad `ζ M`, ortogonalidad, método del círculo finito y continuo |
| `GoldbachPsido/Symbols.lean` | diferencias `Δ`, clases `S^m_{ρ,0}`, `𝟙_𝒫 ∈ S^0_{0,0}`, `𝟙_𝒫 ∉ S^m_{ρ,0}` (ρ>0) |
| `GoldbachPsido/Reflection.lean` | operador de reflexión `U_N`, Egorov exacto, traza = `r N` |
| `GoldbachPsido/Ramanujan.lean` | sumas de Ramanujan, expansión, ortogonalidad (todo `sorry`) |

## Siguiente paso sugerido

1. Compilar y corregir los nombres de lemas que fallen (es trabajo mecánico).
2. Demostrar `finite_circle` (el plan de 4 pasos está en el docstring).
3. Demostrar `primeInd_not_mem`: es el resultado «nuevo» más limpio del artículo y
   su prueba es elemental (fórmula de Newton para diferencias finitas).
4. `r_mod_two` (paridad por involución): conecta con tu ruta de involuciones tipo Zagier.
