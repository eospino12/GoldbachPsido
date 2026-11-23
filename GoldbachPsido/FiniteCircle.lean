/-
  GoldbachPsido/FiniteCircle.lean
  El método del círculo "finito": en el grupo cíclico ℤ/M, con M > 2N, la identidad
  R(N) = (1/M) ∑_j S(j/M)^2 e(-N j/M) es EXACTA. Es la versión discreta de
  R(N) = ∫_𝕋 S(α)^2 e(-Nα) dα, y es la que usan los cálculos del artículo.
-/
import Mathlib

open Finset

namespace GoldbachPsido

/-- Raíz primitiva `M`-ésima de la unidad `ζ_M = e(1/M) = exp(2πi/M)`. -/
noncomputable def ζ (M : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (M : ℂ))

theorem ζ_isPrimitiveRoot (M : ℕ) (hM : 0 < M) : IsPrimitiveRoot (ζ M) M :=
  Complex.isPrimitiveRoot_exp M (by omega)

/-- **Lema 6 (ortogonalidad de caracteres de ℤ/M).**
`∑_{j<M} ζ^{jk} = M` si `M ∣ k`, y `0` en otro caso. -/
theorem sum_root_pow (M : ℕ) (hM : 0 < M) (k : ℕ) :
    ∑ j ∈ range M, (ζ M) ^ (j * k) = if M ∣ k then (M : ℂ) else 0 := by
  have hprim := ζ_isPrimitiveRoot M hM
  have hpow : ∀ j : ℕ, (ζ M) ^ (j * k) = ((ζ M) ^ k) ^ j := fun j => by
    rw [← pow_mul, mul_comm]
  simp_rw [hpow]
  split_ifs with hdvd
  · have h1 : (ζ M) ^ k = 1 := (hprim.pow_eq_one_iff_dvd k).mpr hdvd
    simp [h1]
  · have hne : (ζ M) ^ k ≠ 1 := fun h => hdvd ((hprim.pow_eq_one_iff_dvd k).mp h)
    rw [geom_sum_eq hne]
    have h2 : ((ζ M) ^ k) ^ M = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    simp [h2]

/-- Suma exponencial en la malla `j/M`: `S(j) = ∑_{n ≤ N} c(n) ζ^{jn}`. -/
noncomputable def Sgrid (c : ℕ → ℂ) (N M j : ℕ) : ℂ :=
  ∑ n ∈ range (N + 1), c n * (ζ M) ^ (j * n)

/-- Paso 3 del plan: si `2N < M` y `n, m ≤ N`, entonces `M ∣ n + m + (M - N) ↔ m = N - n`
(porque `0 < M - N ≤ n + m + (M - N) < 2M`). -/
theorem dvd_iff_eq_sub {N M n m : ℕ} (hM : 2 * N < M) (hn : n < N + 1) (hm : m < N + 1) :
    M ∣ n + m + (M - N) ↔ m = N - n := by
  constructor
  · rintro ⟨q, hq⟩
    have hlt : M * q < M * 2 := by rw [← hq]; omega
    have hq2 : q < 2 := Nat.lt_of_mul_lt_mul_left hlt
    interval_cases q <;> omega
  · intro h
    exact ⟨1, by omega⟩

/-- **Proposición (método del círculo finito).**
Si `2N < M`, entonces `M · ∑_{n ≤ N} c(n) c(N-n) = ∑_{j<M} S(j)^2 ζ^{j(M-N)}`.
(El factor `ζ^{j(M-N)} = ζ^{-jN}` evita exponentes negativos.)

Plan de prueba:
1. Expandir `S(j)^2 = ∑_{n,m ≤ N} c n c m ζ^{j(n+m)}` (`Finset.sum_mul_sum`, `sq`).
2. Intercambiar sumas (`Finset.sum_comm`) y usar `sum_root_pow` con `k = n + m + M - N`.
3. Como `0 ≤ n + m ≤ 2N < M` y `N < M`, se tiene `M - N ≤ k < 2M`; luego `M ∣ k ↔ n + m = N`.
4. La suma doble colapsa a `M ∑_{n} c n c (N - n)` (`Finset.sum_ite_eq`). -/
theorem finite_circle (c : ℕ → ℂ) (N M : ℕ) (hM : 2 * N < M) :
    (M : ℂ) * ∑ n ∈ range (N + 1), c n * c (N - n) =
      ∑ j ∈ range M, (Sgrid c N M j) ^ 2 * (ζ M) ^ (j * (M - N)) := by
  have hM0 : 0 < M := by omega
  have expand : ∀ j, (Sgrid c N M j) ^ 2 * (ζ M) ^ (j * (M - N)) =
      ∑ n ∈ range (N + 1), ∑ m ∈ range (N + 1),
        c n * c m * (ζ M) ^ (j * (n + m + (M - N))) := by
    intro j
    rw [Sgrid, sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine sum_congr rfl fun n _ => ?_
    rw [Finset.sum_mul]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_add, mul_add, pow_add, pow_add]
    ring
  symm
  calc ∑ j ∈ range M, (Sgrid c N M j) ^ 2 * (ζ M) ^ (j * (M - N))
      = ∑ j ∈ range M, ∑ n ∈ range (N + 1), ∑ m ∈ range (N + 1),
          c n * c m * (ζ M) ^ (j * (n + m + (M - N))) := sum_congr rfl fun j _ => expand j
    _ = ∑ n ∈ range (N + 1), ∑ m ∈ range (N + 1), ∑ j ∈ range M,
          c n * c m * (ζ M) ^ (j * (n + m + (M - N))) := by
        rw [sum_comm]
        refine sum_congr rfl fun n _ => ?_
        rw [sum_comm]
    _ = ∑ n ∈ range (N + 1), ∑ m ∈ range (N + 1),
          c n * c m * (if M ∣ n + m + (M - N) then (M : ℂ) else 0) := by
        refine sum_congr rfl fun n _ => sum_congr rfl fun m _ => ?_
        rw [← mul_sum, sum_root_pow M hM0]
    _ = ∑ n ∈ range (N + 1), ∑ m ∈ range (N + 1),
          (if N - n = m then c n * c m * (M : ℂ) else 0) := by
        refine sum_congr rfl fun n hn => sum_congr rfl fun m hm => ?_
        rw [mem_range] at hn hm
        rw [mul_ite, mul_zero]
        exact if_congr ((dvd_iff_eq_sub hM hn hm).trans eq_comm) rfl rfl
    _ = ∑ n ∈ range (N + 1), c n * c (N - n) * (M : ℂ) := by
        refine sum_congr rfl fun n hn => ?_
        rw [sum_ite_eq]
        simp [show N - n < N + 1 by omega]
    _ = (M : ℂ) * ∑ n ∈ range (N + 1), c n * c (N - n) := by
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by ring

/-- **Proposición (método del círculo continuo, SIN DEMOSTRAR AÚN).**
El coeficiente de Fourier `N`-ésimo de `S^2` en `AddCircle 1` es la convolución.
Plan: `fourierCoeff` es lineal, `fourier m * fourier n = fourier (m+n)` y
`fourierCoeff (fourier m) n = if m = n then 1 else 0` (ortonormalidad, `orthonormal_fourier`).
(Se quitó la hipótesis `[Fact ((0 : ℝ) < 1)]`: Mathlib ya tiene esa instancia global.) -/
theorem circle_method (c : ℕ → ℂ) (N : ℕ) :
    AddCircle.fourierCoeff (T := 1)
        (fun x => (∑ n ∈ range (N + 1), c n * AddCircle.fourier (n : ℤ) x) ^ 2) (N : ℤ)
      = ∑ n ∈ range (N + 1), c n * c (N - n) := by
  sorry

end GoldbachPsido
