/-
  GoldbachPsido/Ramanujan.lean
  Ramanujan sums and the Λ_Q model (the "major arc part" as a periodic symbol).
  Everything in this file is stated with `sorry`; the identities were checked
  numerically (num/n3_symbols.py) but are not formalized.
-/
import Mathlib
import GoldbachPsido.FiniteCircle

open Finset

namespace GoldbachPsido

/-- Ramanujan sum `c_q(n) = ∑_{0 ≤ a < q, (a,q)=1} e(an/q)`. -/
noncomputable def ramanujan (q n : ℕ) : ℂ :=
  ∑ x ∈ (range q).filter (fun x => Nat.Coprime x q), (ζ q) ^ (x * n)

/-- **(NOT PROVED)** Kluyver's formula: `c_q(n) = ∑_{d ∣ gcd(q,n)} μ(q/d) d`. -/
theorem ramanujan_kluyver (q n : ℕ) (hq : 0 < q) :
    ramanujan q n =
      ∑ d ∈ (Nat.gcd q n).divisors, ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) * d := by
  sorry

/-- **(NOT PROVED)** For squarefree `q`:
`∑_{r ∣ q} μ(r)/φ(r) · c_r(n) = (q/φ(q)) · 𝟙[(n,q)=1]`. -/
theorem ramanujan_expansion_coprime (q n : ℕ) (hq : Squarefree q) :
    ∑ d ∈ q.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) / (Nat.totient d : ℂ) * ramanujan d n
      = if Nat.Coprime n q then (q : ℂ) / (Nat.totient q : ℂ) else 0 := by
  sorry

/-- **(NOT PROVED)** Orthogonality of Ramanujan sums over a full period
`L = lcm(q, q')`: `∑_{n<L} c_q(n) c_{q'}(N - n) = δ_{q q'} · L · c_q(N)`.
(Here `N - n` is read modulo `L`; in Lean it is convenient to work in `ZMod L`.)
This is the identity that produces the singular series in Prop. 3.6 of the paper. -/
theorem ramanujan_orthogonality (q q' N : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    ∑ n ∈ range (Nat.lcm q q'),
        ramanujan q n * ramanujan q' (N + Nat.lcm q q' - n % Nat.lcm q q')
      = if q = q' then (Nat.lcm q q' : ℂ) * ramanujan q N else 0 := by
  sorry

end GoldbachPsido
