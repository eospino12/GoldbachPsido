/-
  GoldbachPsido/Reflection.lean
  The reflection operator U_N f(x) = e(Nx) f(-x) on 𝕋, written on the frequency side:
  (U_N g)(ξ) = g(N - ξ). It is an involution that quantizes the canonical map
  κ_N(x, ξ) = (-x, N - ξ), and it conjugates multipliers EXACTLY (Egorov with no remainder).
-/
import Mathlib
import GoldbachPsido.Basic

open Finset

namespace GoldbachPsido

/-- Reflection on frequencies: `(U_N g)(ξ) = g(N - ξ)`. -/
def U (N : ℤ) (g : ℤ → ℂ) : ℤ → ℂ := fun ξ => g (N - ξ)

/-- Fourier multiplier `Op(σ)` seen on frequencies: multiplication by `σ`. -/
def mult (σ : ℤ → ℂ) (g : ℤ → ℂ) : ℤ → ℂ := fun ξ => σ ξ * g ξ

/-- **Lemma 8.** `U_N` is an involution. -/
theorem U_invol (N : ℤ) (g : ℤ → ℂ) : U N (U N g) = g := by
  funext ξ
  simp [U]

/-- **Lemma 9 (exact Egorov).** `U_N ∘ Op(σ) ∘ U_N = Op(σ ∘ κ_N)`, with `σ ∘ κ_N (ξ) = σ(N - ξ)`. -/
theorem egorov (N : ℤ) (σ g : ℤ → ℂ) :
    U N (mult σ (U N g)) = mult (fun ξ => σ (N - ξ)) g := by
  funext ξ
  simp [U, mult]

/-- Composition of multipliers: `Op(σ) Op(τ) = Op(στ)`. -/
theorem mult_mult (σ τ g : ℤ → ℂ) : mult σ (mult τ g) = mult (fun ξ => σ ξ * τ ξ) g := by
  funext ξ
  simp [mult, mul_assoc]

/-- **Corollary (ℕ version).** By `egorov` and `mult_mult`, `Π_𝒫 · U_N Π_𝒫 U_N` is the
multiplier with symbol `𝟙_𝒫(ξ) 𝟙_𝒫(N - ξ)`, a finite-rank projector; its trace is the
sum of the symbol, which is `r N`. Only the equality of sums is formalized here (trivial from
`r_eq_sum`). The operator statement on `L²(𝕋)` (trace, rank) is NOT formalized. -/
theorem trace_eq_r (N : ℕ) :
    (∑ n ∈ range (N + 1), (a n * a (N - n) : ℕ)) = r N := by
  rw [r_eq_sum]

end GoldbachPsido
