import Mathlib.Topology.ContinuousMap.StoneWeierstrass

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

end Rudin.Ch05
