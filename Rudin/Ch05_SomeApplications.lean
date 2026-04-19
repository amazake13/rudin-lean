import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Chapter 5 — Some Applications

Rudin, *Functional Analysis* (2nd ed.), Chapter 5.
-/

namespace Rudin.Ch05

/-- **Theorem 5.7 (Stone–Weierstrass, real)** — If `X` is a compact
Hausdorff space and `A` is a real subalgebra of `C(X,ℝ)` that
separates points, then `A` is dense in `C(X,ℝ)`. -/
theorem stone_weierstrass {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA

/-- **Theorem 5.8 (Stone–Weierstrass, `RCLike` version)** — For
`𝕜 ∈ {ℝ, ℂ}` and `X` a compact Hausdorff space, a self-adjoint
star-subalgebra `A` of `C(X, 𝕜)` that separates points is dense. -/
theorem stone_weierstrass_star {𝕜 X : Type*} [RCLike 𝕜]
    [TopologicalSpace X] [CompactSpace X]
    (A : StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA

section BanachFixedPoint

variable {α : Type*} [MetricSpace α] [Nonempty α] [CompleteSpace α]
variable {K : ℝ≥0} {f : α → α}

/-- **Theorem 5.X (Banach fixed-point theorem, contraction mapping)** —
Let `(X, d)` be a nonempty complete metric space and let `f : X → X` be a
contraction, i.e. there exists `K < 1` with `d(f x, f y) ≤ K · d(x, y)`.
Then `f` has a unique fixed point, and the iterates `f^[n] x₀` converge
to it from any starting point `x₀`. -/
noncomputable def banach_fixedPoint (hf : ContractingWith K f) : α :=
  hf.fixedPoint f

/-- **Theorem 5.X (the fixed point is indeed fixed)** -/
theorem banach_fixedPoint_isFixedPt (hf : ContractingWith K f) :
    Function.IsFixedPt f (banach_fixedPoint hf) :=
  hf.fixedPoint_isFixedPt

/-- **Theorem 5.X (uniqueness of the fixed point)** -/
theorem banach_fixedPoint_unique (hf : ContractingWith K f)
    {x : α} (hx : Function.IsFixedPt f x) :
    x = banach_fixedPoint hf :=
  hf.fixedPoint_unique hx

/-- **Theorem 5.X (convergence of iterates)** — Iterates of a
contraction converge to the unique fixed point. -/
theorem banach_fixedPoint_tendsto (hf : ContractingWith K f) (x : α) :
    Filter.Tendsto (fun n => f^[n] x) Filter.atTop (𝓝 (banach_fixedPoint hf)) :=
  hf.tendsto_iterate_fixedPoint x

/-- **Theorem 5.X (a priori error estimate)** — After `n` iterates,
`d(f^[n] x₀, x*) ≤ d(x₀, f x₀) · K^n / (1 − K)`. -/
theorem banach_fixedPoint_apriori (hf : ContractingWith K f) (x : α) (n : ℕ) :
    dist (f^[n] x) (banach_fixedPoint hf) ≤
      dist x (f x) * (K : ℝ) ^ n / (1 - K) :=
  hf.apriori_dist_iterate_fixedPoint_le x n

end BanachFixedPoint

end Rudin.Ch05
