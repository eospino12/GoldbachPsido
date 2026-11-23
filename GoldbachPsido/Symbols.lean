/-
  GoldbachPsido/Symbols.lean
  Toroidal symbol classes S^m_{ρ,0}(𝕋 × ℤ) for Fourier multipliers
  (symbols that do not depend on x), defined with the forward difference
  Δσ(ξ) = σ(ξ+1) - σ(ξ), as in Ruzhansky–Turunen and in the undergraduate thesis.

  Main result (Prop. 3.5 of the paper):
    * the indicator of the primes lies in S^0_{0,0}       (proved below);
    * it does NOT lie in S^m_{ρ,0} for any ρ > 0          (proved below).
-/
import Mathlib

namespace GoldbachPsido

open Filter

/-- Forward difference on `ℤ`. -/
def Δ (σ : ℤ → ℝ) : ℤ → ℝ := fun ξ => σ (ξ + 1) - σ ξ

/-- `σ ∈ S^m_{ρ,0}`: for every `k` there is `C` with `|Δ^k σ(ξ)| ≤ C ⟨ξ⟩^{m - ρ k}`,
where `⟨ξ⟩ = (1 + ξ²)^{1/2}`. -/
def InS (m ρ : ℝ) (σ : ℤ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, ∀ ξ : ℤ,
    |(Δ^[k] σ) ξ| ≤ C * (1 + (ξ : ℝ) ^ 2) ^ ((m - ρ * k) / 2)

/-- **Lemma 7.** If `|σ| ≤ B`, then `|Δ^k σ| ≤ 2^k B`. -/
theorem abs_iterate_Δ_le (σ : ℤ → ℝ) (B : ℝ) (hB : ∀ ξ, |σ ξ| ≤ B) :
    ∀ k : ℕ, ∀ ξ, |(Δ^[k] σ) ξ| ≤ 2 ^ k * B := by
  intro k
  induction k with
  | zero => intro ξ; simpa using hB ξ
  | succ k ih =>
    intro ξ
    rw [Function.iterate_succ_apply']
    have h1 := ih (ξ + 1)
    have h2 := ih ξ
    show |(Δ^[k] σ) (ξ + 1) - (Δ^[k] σ) ξ| ≤ 2 ^ (k + 1) * B
    rw [abs_le] at h1 h2 ⊢
    rw [pow_succ]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Indicator of the primes as a symbol on `ℤ` (equal to `0` for `ξ ≤ 0`). -/
noncomputable def primeInd (ξ : ℤ) : ℝ := if 0 < ξ ∧ ξ.natAbs.Prime then 1 else 0

theorem abs_primeInd_le (ξ : ℤ) : |primeInd ξ| ≤ 1 := by
  unfold primeInd
  split_ifs <;> simp

/-- **Proposition 3.5(a).** `𝟙_𝒫 ∈ S^0_{0,0}`. -/
theorem primeInd_mem_S00 : InS 0 0 primeInd := by
  intro k
  refine ⟨2 ^ k, fun ξ => ?_⟩
  have h := abs_iterate_Δ_le primeInd 1 abs_primeInd_le k ξ
  simpa using h

/-- Iterated differences of an integer-valued function are integers. -/
theorem iterate_Δ_int (f : ℤ → ℝ) (hf : ∀ ξ, ∃ z : ℤ, f ξ = z) :
    ∀ k ξ, ∃ z : ℤ, (Δ^[k] f) ξ = z := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    intro ξ
    obtain ⟨a, ha⟩ := ih (ξ + 1)
    obtain ⟨b, hb⟩ := ih ξ
    refine ⟨a - b, ?_⟩
    rw [Function.iterate_succ_apply']
    show (Δ^[k] f) (ξ + 1) - (Δ^[k] f) ξ = _
    rw [ha, hb]; push_cast; ring

/-- If `h` is bounded and `Δ(Δh) = 0` on `[ξ₀, ∞)`, then `Δh = 0` on `[ξ₀, ∞)`:
`Δh` is a constant `c` there, so `h(ξ₀+n) = h(ξ₀) + n·c`, and boundedness forces `c = 0`. -/
theorem Δ_eq_zero_of_Δ_Δ (h : ℤ → ℝ) (B : ℝ) (hB : ∀ ξ, |h ξ| ≤ B) (ξ₀ : ℤ)
    (h2 : ∀ ξ, ξ₀ ≤ ξ → Δ (Δ h) ξ = 0) : ∀ ξ, ξ₀ ≤ ξ → Δ h ξ = 0 := by
  have hconst : ∀ n : ℕ, Δ h (ξ₀ + n) = Δ h ξ₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : Δ h (ξ₀ + n + 1) - Δ h (ξ₀ + n) = 0 := h2 (ξ₀ + n) (by omega)
      push_cast; rw [← add_assoc]; linarith
  have hlin : ∀ n : ℕ, h (ξ₀ + n) = h ξ₀ + n * Δ h ξ₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : Δ h (ξ₀ + n) = h (ξ₀ + n + 1) - h (ξ₀ + n) := rfl
      rw [hconst n] at e
      push_cast; rw [← add_assoc]; linarith
  have hc0 : Δ h ξ₀ = 0 := by
    by_contra hc
    have hc' : 0 < |Δ h ξ₀| := abs_pos.mpr hc
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * B / |Δ h ξ₀|)
    have hle : (n : ℝ) * |Δ h ξ₀| ≤ 2 * B := by
      have h1 := hB (ξ₀ + n)
      have h2 := hB ξ₀
      have e : |h (ξ₀ + n) - h ξ₀| = (n : ℝ) * |Δ h ξ₀| := by
        rw [hlin n, add_sub_cancel_left, abs_mul, Nat.abs_cast]
      rw [← e]
      calc |h (ξ₀ + n) - h ξ₀| ≤ |h (ξ₀ + n)| + |h ξ₀| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    rw [div_lt_iff₀ hc'] at hn
    linarith
  intro ξ hξ
  have := hconst (ξ - ξ₀).toNat
  rw [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this
  rw [this, hc0]

/-- If `f` is bounded and `Δ^{j+1} f = 0` on `[ξ₀, ∞)`, then `Δ f = 0` on `[ξ₀, ∞)`.
(Apply `Δ_eq_zero_of_Δ_Δ` to `Δ^{j-1} f, …, f`; this replaces Newton's formula
and "a bounded polynomial is constant".) -/
theorem Δ_eq_zero_of_iterate (f : ℤ → ℝ) (B : ℝ) (hB : ∀ ξ, |f ξ| ≤ B) (ξ₀ : ℤ) :
    ∀ j : ℕ, (∀ ξ, ξ₀ ≤ ξ → (Δ^[j + 1] f) ξ = 0) → ∀ ξ, ξ₀ ≤ ξ → Δ f ξ = 0 := by
  intro j
  induction j with
  | zero => intro h; simpa using h
  | succ j ih =>
    intro h
    apply ih
    have key := Δ_eq_zero_of_Δ_Δ (Δ^[j] f) (2 ^ j * B) (abs_iterate_Δ_le f B hB j) ξ₀ (by
      intro ξ hξ
      have := h ξ hξ
      rwa [Function.iterate_succ_apply', Function.iterate_succ_apply'] at this)
    intro ξ hξ
    rw [Function.iterate_succ_apply']
    exact key ξ hξ

/-- **Proposition 3.5(b).** For `ρ > 0`, `𝟙_𝒫 ∉ S^m_{ρ,0}` for any `m`.

Proof (in the paper, Prop. 3.5):
* Take `k > m/ρ`. If `𝟙_𝒫 ∈ S^m_{ρ,0}`, then `Δ^k 𝟙_𝒫(ξ) → 0` as `ξ → ∞`.
* `Δ^k 𝟙_𝒫(ξ) ∈ ℤ`, hence `Δ^k 𝟙_𝒫(ξ) = 0` for `ξ ≥ ξ₀`.
* A function on `ℤ` with `Δ^k f = 0` on `[ξ₀, ∞)` is a polynomial of degree `< k` there
  (Newton: `f(ξ₀ + n) = ∑_{j<k} C(n,j) Δ^j f(ξ₀)`).
* A bounded polynomial is constant; but `𝟙_𝒫` takes the values 0 and 1 infinitely often
  (`Nat.exists_infinite_primes` and the even numbers). Contradiction.

In Lean we take `k = ⌈m/ρ⌉₊ + 1` and, instead of Newton, `Δ_eq_zero_of_iterate` gives `Δ 𝟙_𝒫 = 0`
on `[ξ₀, ∞)`, which contradicts `𝟙_𝒫(p) = 1`, `𝟙_𝒫(p+1) = 0` for an odd prime `p ≥ ξ₀`. -/
theorem primeInd_not_mem (m ρ : ℝ) (hρ : 0 < ρ) : ¬ InS m ρ primeInd := by
  intro hS
  obtain ⟨C, hC⟩ := hS (⌈m / ρ⌉₊ + 1)
  have he : (m - ρ * ((⌈m / ρ⌉₊ + 1 : ℕ) : ℝ)) / 2 < 0 := by
    have h1 : m / ρ ≤ ⌈m / ρ⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hρ] at h1
    push_cast
    nlinarith
  have ht : Tendsto (fun ξ : ℤ => C * (1 + (ξ : ℝ) ^ 2) ^
      ((m - ρ * ((⌈m / ρ⌉₊ + 1 : ℕ) : ℝ)) / 2)) atTop (nhds 0) := by
    have h1 : Tendsto (fun ξ : ℤ => 1 + (ξ : ℝ) ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1
        ((tendsto_pow_atTop two_ne_zero).comp tendsto_intCast_atTop_atTop)
    have h2 := (tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp h1
    simp only [neg_neg] at h2
    simpa using h2.const_mul C
  obtain ⟨ξ₀, hξ₀⟩ := eventually_atTop.mp (ht.eventually_lt_const one_pos)
  have hint : ∀ ξ, ∃ z : ℤ, primeInd ξ = z := fun ξ => by
    unfold primeInd
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  have hzero : ∀ ξ, ξ₀ ≤ ξ → (Δ^[⌈m / ρ⌉₊ + 1] primeInd) ξ = 0 := by
    intro ξ hξ
    obtain ⟨z, hz⟩ := iterate_Δ_int primeInd hint _ ξ
    have hlt : |(z : ℝ)| < 1 := by rw [← hz]; exact lt_of_le_of_lt (hC ξ) (hξ₀ ξ hξ)
    have hz0 : z = 0 := by
      rw [← Int.cast_abs] at hlt
      have : |z| < 1 := by exact_mod_cast hlt
      exact Int.abs_lt_one_iff.mp this
    rw [hz, hz0]; simp
  have hΔ := Δ_eq_zero_of_iterate primeInd 1 abs_primeInd_le ξ₀ _ hzero
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (ξ₀.toNat + 3)
  have hodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hnp : ¬ (p + 1).Prime := by
    intro h
    have := h.even_iff.mp hodd.add_one
    omega
  have h := hΔ p (by omega)
  have e1 : ((p : ℤ) + 1).natAbs = p + 1 := by omega
  have e2 : (p : ℤ).natAbs = p := by omega
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  unfold Δ primeInd at h
  rw [e1, e2] at h
  norm_num [hp, hnp, hp0] at h
  omega

/-- Cramér model: density `1/log ξ` (cut off at `ξ ≥ 3`). -/
noncomputable def cramer (ξ : ℤ) : ℝ := if 3 ≤ ξ then 1 / Real.log ξ else 0

/-- **(NOT YET PROVED)** The Cramér model is a classical symbol: `∈ S^0_{1,0}`.
Plan: iterated mean value theorem, `Δ^k f(ξ) = f^{(k)}(ξ + θ)` with `θ ∈ (0,k)`, and
`|d^k/dt^k (1/log t)| ≤ C_k t^{-k}` for `t ≥ 3`. The `ξ < 3 + k` are absorbed into the constant. -/
theorem cramer_mem_S010 : InS 0 1 cramer := by
  sorry

end GoldbachPsido
