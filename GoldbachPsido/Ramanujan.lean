/-
  GoldbachPsido/Ramanujan.lean
  Sumas de Ramanujan y el modelo Λ_Q (la "parte de arcos mayores" como símbolo periódico).
  Todo lo de este archivo queda enunciado con `sorry`; las identidades se comprobaron
  numéricamente (num/n3_symbols.py) pero no están formalizadas.
-/
import Mathlib
import GoldbachPsido.FiniteCircle

open Finset

namespace GoldbachPsido

/-- Suma de Ramanujan `c_q(n) = ∑_{0 ≤ a < q, (a,q)=1} e(an/q)`. -/
noncomputable def ramanujan (q n : ℕ) : ℂ :=
  ∑ x ∈ (range q).filter (fun x => Nat.Coprime x q), (ζ q) ^ (x * n)

/-- **(SIN DEMOSTRAR)** Fórmula de Kluyver: `c_q(n) = ∑_{d ∣ gcd(q,n)} μ(q/d) d`. -/
theorem ramanujan_kluyver (q n : ℕ) (hq : 0 < q) :
    ramanujan q n =
      ∑ d ∈ (Nat.gcd q n).divisors, ((ArithmeticFunction.moebius (q / d) : ℤ) : ℂ) * d := by
  sorry

/-- **(SIN DEMOSTRAR)** Para `q` libre de cuadrados:
`∑_{r ∣ q} μ(r)/φ(r) · c_r(n) = (q/φ(q)) · 𝟙[(n,q)=1]`. -/
theorem ramanujan_expansion_coprime (q n : ℕ) (hq : Squarefree q) :
    ∑ d ∈ q.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) / (Nat.totient d : ℂ) * ramanujan d n
      = if Nat.Coprime n q then (q : ℂ) / (Nat.totient q : ℂ) else 0 := by
  sorry

/-- **(SIN DEMOSTRAR)** Ortogonalidad de sumas de Ramanujan en un periodo completo
`L = lcm(q, q')`: `∑_{n<L} c_q(n) c_{q'}(N - n) = δ_{q q'} · L · c_q(N)`.
(Aquí `N - n` se interpreta módulo `L`; en Lean conviene trabajar en `ZMod L`.)
Es la identidad que produce la serie singular en la Prop. 3.6 del artículo. -/
theorem ramanujan_orthogonality (q q' N : ℕ) (hq : 0 < q) (hq' : 0 < q') :
    ∑ n ∈ range (Nat.lcm q q'),
        ramanujan q n * ramanujan q' (N + Nat.lcm q q' - n % Nat.lcm q q')
      = if q = q' then (Nat.lcm q q' : ℂ) * ramanujan q N else 0 := by
  sorry

end GoldbachPsido
