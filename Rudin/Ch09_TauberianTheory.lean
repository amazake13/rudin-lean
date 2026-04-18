import Mathlib.Analysis.Complex.AbelLimit

/-!
# Chapter 9 — Tauberian Theory

Rudin, *Functional Analysis* (2nd ed.), Chapter 9.

Note: Wiener's Tauberian theorem is not yet in mathlib. We record here
the Abel limit theorem — the elementary "abelian" partner of a
Tauberian statement, and the starting point for Wiener's proof via
the commutative Banach algebra $L^1(\mathbb{R})$ (Ch 11).
-/

namespace Rudin.Ch09

open Filter Topology Finset

/-- **Theorem 9.X (Abel's limit theorem, real version)** — If a real
power series $\sum a_n$ converges to $l$, then the associated
function $f(x) = \sum_n a_n x^n$ tends to $l$ as $x \to 1^{-}$. -/
theorem abel_limit {f : ℕ → ℝ} {l : ℝ}
    (h : Tendsto (fun n ↦ ∑ i ∈ range n, f i) atTop (𝓝 l)) :
    Tendsto (fun x ↦ ∑' n, f n * x ^ n) (𝓝[<] (1 : ℝ)) (𝓝 l) :=
  Real.tendsto_tsum_powerSeries_nhdsWithin_lt h

end Rudin.Ch09
