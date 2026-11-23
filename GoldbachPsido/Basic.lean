/-
  GoldbachPsido/Basic.lean
  Basic arithmetic definitions: the Goldbach statement, the counting function r(N),
  its "sum of products" form (a correlation under reflection) and the exceptional set.
-/
import Mathlib

open Finset

namespace GoldbachPsido

/-- `N` is a sum of two primes. -/
def IsGoldbach (N : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = N

/-- The binary Goldbach conjecture (statement only; obviously NOT proved here). -/
def BinaryGoldbach : Prop := ∀ N : ℕ, 4 ≤ N → Even N → IsGoldbach N

/-- The Goldbach set of `N`: the `p ≤ N` such that both `p` and `N - p` are prime. -/
def goldbachSet (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p => p.Prime ∧ (N - p).Prime)

/-- `r N` = number of ordered pairs `(p, N - p)` of primes. -/
def r (N : ℕ) : ℕ := (goldbachSet N).card

/-- Indicator function of the primes, with values in `ℕ`. -/
def a (n : ℕ) : ℕ := if n.Prime then 1 else 0

/-- **Lemma 1.** Goldbach at `N` is equivalent to `r N > 0`. -/
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

/-- **Lemma 2.** `r N = ∑_{n ≤ N} a(n) a(N - n)`: Goldbach is a correlation of the
prime indicator with its reflection `n ↦ N - n`. -/
theorem r_eq_sum (N : ℕ) : r N = ∑ n ∈ range (N + 1), a n * a (N - n) := by
  unfold r goldbachSet a
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases h1 : n.Prime <;> by_cases h2 : (N - n).Prime <;> simp [h1, h2]

/-- **Lemma 3.** The reflection `p ↦ N - p` preserves the Goldbach set. -/
theorem refl_mem {N p : ℕ} (hp : p ∈ goldbachSet N) : N - p ∈ goldbachSet N := by
  simp only [goldbachSet, Finset.mem_filter, Finset.mem_range] at hp ⊢
  refine ⟨by omega, hp.2.2, ?_⟩
  have h : N - (N - p) = p := by omega
  rw [h]; exact hp.2.1

/-- The reflection is an involution on the Goldbach set. -/
theorem refl_refl {N p : ℕ} (hp : p ∈ goldbachSet N) : N - (N - p) = p := by
  simp only [goldbachSet, Finset.mem_filter, Finset.mem_range] at hp
  omega

/-- **Lemma 4 (parity).** `r N` is odd exactly when `N = 2p` with `p` prime:
the involution `p ↦ N - p` pairs up the non-fixed points, and the only possible fixed point is `N/2`.
Proof: split `goldbachSet N` into `{2p < N}`, `{2p = N}` and `{2p > N}`; the reflection is a
bijection between the first and the third (`refl_mem`, `refl_refl`), and the second is `{N/2}` or `∅`. -/
theorem r_mod_two (N : ℕ) :
    r N % 2 = if (Even N ∧ (N / 2).Prime) then 1 else 0 := by
  set s := goldbachSet N with hs
  have hle : ∀ p ∈ s, p ≤ N := fun p hp => by have := refl_refl hp; omega
  have h1 := card_filter_add_card_filter_not (s := s) (fun p => 2 * p < N)
  have h2 := card_filter_add_card_filter_not
    (s := s.filter (fun p => ¬ 2 * p < N)) (fun p => 2 * p = N)
  -- the reflection pairs `2p < N` with `2p > N`
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
  -- the only possible fixed point is `N/2`
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

/-- Exceptional set: `E X = #{N ≤ X : N ≥ 4 even, r N = 0}`. -/
def E (X : ℕ) : ℕ := ((range (X + 1)).filter (fun N => 4 ≤ N ∧ Even N ∧ r N = 0)).card

/-- **Lemma 5.** The binary conjecture is equivalent to `E X = 0` for all `X`. -/
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

/-! ### Examples with explicit witnesses -/

example : IsGoldbach 4 := ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
example : IsGoldbach 100 := ⟨3, 97, by norm_num, by norm_num, rfl⟩
example : IsGoldbach 1000 := ⟨3, 997, by norm_num, by norm_num, rfl⟩
example : IsGoldbach 1000000 := ⟨17, 999983, by norm_num, by norm_num, rfl⟩

end GoldbachPsido
