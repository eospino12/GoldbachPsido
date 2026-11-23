/-
  GoldbachPsido/Reflection.lean
  El operador de reflexión U_N f(x) = e(Nx) f(-x) en 𝕋, escrito del lado de las frecuencias:
  (U_N g)(ξ) = g(N - ξ). Es una involución que cuantiza la aplicación canónica
  κ_N(x, ξ) = (-x, N - ξ), y conjuga multiplicadores de forma EXACTA (Egorov sin resto).
-/
import Mathlib
import GoldbachPsido.Basic

open Finset

namespace GoldbachPsido

/-- Reflexión en frecuencias: `(U_N g)(ξ) = g(N - ξ)`. -/
def U (N : ℤ) (g : ℤ → ℂ) : ℤ → ℂ := fun ξ => g (N - ξ)

/-- Multiplicador de Fourier `Op(σ)` visto en frecuencias: multiplicación por `σ`. -/
def mult (σ : ℤ → ℂ) (g : ℤ → ℂ) : ℤ → ℂ := fun ξ => σ ξ * g ξ

/-- **Lema 8.** `U_N` es una involución. -/
theorem U_invol (N : ℤ) (g : ℤ → ℂ) : U N (U N g) = g := by
  funext ξ
  simp [U]

/-- **Lema 9 (Egorov exacto).** `U_N ∘ Op(σ) ∘ U_N = Op(σ ∘ κ_N)`, con `σ ∘ κ_N (ξ) = σ(N - ξ)`. -/
theorem egorov (N : ℤ) (σ g : ℤ → ℂ) :
    U N (mult σ (U N g)) = mult (fun ξ => σ (N - ξ)) g := by
  funext ξ
  simp [U, mult]

/-- Composición de multiplicadores: `Op(σ) Op(τ) = Op(στ)`. -/
theorem mult_mult (σ τ g : ℤ → ℂ) : mult σ (mult τ g) = mult (fun ξ => σ ξ * τ ξ) g := by
  funext ξ
  simp [mult, mul_assoc]

/-- **Corolario (versión en ℕ).** Por `egorov` y `mult_mult`, `Π_𝒫 · U_N Π_𝒫 U_N` es el
multiplicador de símbolo `𝟙_𝒫(ξ) 𝟙_𝒫(N - ξ)`, un proyector de rango finito; su traza es la
suma del símbolo, que es `r N`. Aquí solo se formaliza la igualdad de sumas (trivial a partir
de `r_eq_sum`). La afirmación de operadores en `L²(𝕋)` (traza, rango) NO está formalizada. -/
theorem trace_eq_r (N : ℕ) :
    (∑ n ∈ range (N + 1), (a n * a (N - n) : ℕ)) = r N := by
  rw [r_eq_sum]

end GoldbachPsido
