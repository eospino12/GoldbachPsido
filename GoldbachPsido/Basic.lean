/-
  GoldbachPsido/Basic.lean
  Definiciones aritméticas básicas: enunciado de Goldbach, la función de conteo r(N),
  su forma de "suma de productos" (correlación en reflexión) y el conjunto excepcional.

  Estado (ver STATUS.md): las pruebas de este archivo están escritas pero NO se compilaron
  en la sesión en que se generaron (no había Lean instalado). Ejecuta `lake build`.
-/
import Mathlib

open Finset

namespace GoldbachPsido

/-- `N` es suma de dos primos. -/
def IsGoldbach (N : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N

/-- La conjetura binaria de Goldbach (enunciado; obviamente NO se demuestra aquí). -/
def BinaryGoldbach : Prop := ∀ N : ℕ, 4 ≤ N → Even N → IsGoldbach N

/-- El conjunto de Goldbach de `N`: los `p ≤ N` con `p` y `N - p` primos. -/
def goldbachSet (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)

/-- `r N` = número de pares ordenados `(p, N - p)` de primos. -/
def r (N : ℕ) : ℕ := (goldbachSet N).card

/-- Indicador de los primos con valores en `ℕ`. -/
def a (n : ℕ) : ℕ := if n.Prime then 1 else 0

/-- **Lema 1.** Goldbach en `N` equivale a `r N > 0`. -/
theorem isGoldbach_iff_r_pos (N : ℕ) : IsGoldbach N ↔ 0 < r N := by
  unfold IsGoldbach r goldbachSet
  rw [Finset.card_pos]
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨p, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, hp, ?_⟩
    have h : p + q - p = q := by omega
    rw [h]; exact hq
  · rintro ⟨p, hp⟩
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨p, N - p, hp.2.1, hp.2.2, by omega⟩

/-- **Lema 2.** `r N = ∑_{n ≤ N} a(n) a(N - n)`: Goldbach es una correlación
del indicador de los primos con su reflejado `n ↦ N - n`. -/
theorem r_eq_sum (N : ℕ) : r N = ∑ n ∈ range (N + 1), a n * a (N - n) := by
  unfold r goldbachSet a
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h1 : n.Prime <;> by_cases h2 : (N - n).Prime <;> simp [h1, h2]

/-- **Lema 3.** La reflexión `p ↦ N - p` preserva el conjunto de Goldbach. -/
theorem refl_mem {N p : ℕ} (hp : p ∈ goldbachSet N) : N - p ∈ goldbachSet N := by
  simp only [goldbachSet, Finset.mem_filter, Finset.mem_range] at hp ⊢
  refine ⟨by omega, hp.2.2, ?_⟩
  have h : N - (N - p) = p := by omega
  rw [h]; exact hp.2.1

/-- La reflexión es una involución en el conjunto de Goldbach. -/
theorem refl_refl {N p : ℕ} (hp : p ∈ goldbachSet N) : N - (N - p) = p := by
  simp only [goldbachSet, Finset.mem_filter, Finset.mem_range] at hp
  omega

/-- **Lema 4 (paridad).** `r N` es impar exactamente cuando `N = 2p` con `p` primo:
la involución `p ↦ N - p` empareja los puntos no fijos, y el único punto fijo posible es `N/2`.
Prueba: se parte `goldbachSet N` en `{2p < N}`, `{2p = N}` y `{2p > N}`; la reflexión es una
biyección entre el primero y el tercero (`refl_mem`, `refl_refl`), y el segundo es `{N/2}` o `∅`. -/
theorem r_mod_two (N : ℕ) :
    r N % 2 = if (Even N ∧ (N / 2).Prime) then 1 else 0 := by
  set s := goldbachSet N with hs
  have hle : ∀ p ∈ s, p ≤ N := fun p hp => by have := refl_refl hp; omega
  have h1 := card_filter_add_card_filter_not (s := s) (fun p => 2 * p < N)
  have h2 := card_filter_add_card_filter_not
    (s := s.filter (fun p => ¬ 2 * p < N)) (fun p => 2 * p = N)
  -- la reflexión empareja `2p < N` con `2p > N`
  have hLG : (s.filter (fun p => 2 * p < N)).card =
      ((s.filter (fun p => ¬ 2 * p < N)).filter (fun p => ¬ 2 * p = N)).card := by
    apply card_nbij' (fun p => N - p) (fun p => N - p)
    · intro p hp
      simp only [mem_coe, mem_filter] at hp ⊢
      have := hle p hp.1
      exact ⟨⟨refl_mem hp.1, by omega⟩, by omega⟩
    · intro p hp
      simp only [mem_coe, mem_filter] at hp ⊢
      have := hle p hp.1.1
      exact ⟨refl_mem hp.1.1, by omega⟩
    · intro p hp
      simp only [mem_coe, mem_filter] at hp
      exact refl_refl hp.1
    · intro p hp
      simp only [mem_coe, mem_filter] at hp
      exact refl_refl hp.1.1
  -- el único punto fijo posible es `N/2`
  have hF : ((s.filter (fun p => ¬ 2 * p < N)).filter (fun p => 2 * p = N)).card =
      if (Even N ∧ (N / 2).Prime) then 1 else 0 := by
    split_ifs with h
    · rw [card_eq_one]
      refine ⟨N / 2, ?_⟩
      obtain ⟨k, hk⟩ := h.1
      ext p
      simp only [hs, goldbachSet, mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨_, h2⟩; omega
      · rintro rfl
        have e : N - N / 2 = N / 2 := by omega
        exact ⟨⟨⟨by omega, h.2, by rw [e]; exact h.2⟩, by omega⟩, by omega⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro p hp hpN
      apply h
      simp only [hs, goldbachSet, mem_filter, mem_range] at hp
      have e : N / 2 = p := by omega
      exact ⟨⟨p, by omega⟩, by rw [e]; exact hp.1.2.1⟩
  have hr : r N = s.card := rfl
  split_ifs at hF ⊢ <;> omega

/-- Conjunto excepcional: `E X = #{N ≤ X : N ≥ 4 par, r N = 0}`. -/
def E (X : ℕ) : ℕ := ((range (X + 1)).filter (fun N => 4 ≤ N ∧ Even N ∧ r N = 0)).card

/-- **Lema 5.** La conjetura binaria equivale a `E X = 0` para todo `X`. -/
theorem binaryGoldbach_iff_E_zero : BinaryGoldbach ↔ ∀ X, E X = 0 := by
  constructor
  · intro h X
    unfold E
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro N _ hN
    obtain ⟨h4, hev, h0⟩ := hN
    have hpos := (isGoldbach_iff_r_pos N).mp (h N h4 hev)
    omega
  · intro h N h4 hev
    rw [isGoldbach_iff_r_pos]
    by_contra hr
    have hE := h N
    unfold E at hE
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hE
    exact hE (Finset.mem_range.mpr (Nat.lt_succ_self N)) ⟨h4, hev, by omega⟩

/-! ### Ejemplos con testigos explícitos -/

example : IsGoldbach 4 := ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
example : IsGoldbach 100 := ⟨3, 97, by norm_num, by norm_num, rfl⟩
example : IsGoldbach 1000 := ⟨3, 997, by norm_num, by norm_num, rfl⟩
example : IsGoldbach 1000000 := ⟨17, 999983, by norm_num, by norm_num, rfl⟩

end GoldbachPsido
