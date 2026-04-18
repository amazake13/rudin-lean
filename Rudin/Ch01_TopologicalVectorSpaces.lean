import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull

/-!
# Chapter 1 — Topological Vector Spaces

Formalisation of Rudin, *Functional Analysis* (2nd ed.), Chapter 1.

Strategy: reuse mathlib's `IsTopologicalAddGroup` + `ContinuousSMul` +
`NormedSpace` scaffolding rather than redefining.
-/

namespace Rudin.Ch01

section TVS

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- **Theorem 1.6 (a)** — translation by `a` is a homeomorphism `E ≃ₜ E`. -/
def translationHomeo (a : E) : E ≃ₜ E := Homeomorph.addLeft a

/-- **Theorem 1.6 (b)** — multiplication by a nonzero scalar is a homeomorphism. -/
def smulHomeo {c : 𝕜} (hc : c ≠ 0) : E ≃ₜ E :=
  Homeomorph.smulOfNeZero c hc

end TVS

/-- **Theorem 1.22 (Heine–Borel in finite dimensions)** — In a
finite-dimensional normed space over `ℝ` or `ℂ`, a closed and bounded
set is compact. -/
theorem heine_borel (𝕜 : Type*) [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {s : Set E} (h_closed : IsClosed s) (h_bdd : Bornology.IsBounded s) :
    IsCompact s :=
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  Metric.isCompact_of_isClosed_isBounded h_closed h_bdd

section Minkowski

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- **Definition 1.33** — Minkowski functional (gauge) of a set. -/
noncomputable def minkowski (s : Set E) : E → ℝ := gauge s

omit [TopologicalSpace E] in
/-- **Theorem 1.35 (subadditivity of the Minkowski functional)** — If
`s` is convex and absorbs each point (equivalently, is absorbent), then
the Minkowski functional of `s` is subadditive. -/
theorem minkowski_add_le {s : Set E} (hs : Convex ℝ s) (absorbs : Absorbent ℝ s)
    (x y : E) :
    minkowski s (x + y) ≤ minkowski s x + minkowski s y :=
  gauge_add_le hs absorbs x y

end Minkowski

section LinearContinuity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Theorem 1.18 (continuity via boundedness)** — A linear map between
normed spaces is continuous as soon as it admits a constant `C` with
`‖f x‖ ≤ C · ‖x‖`. In a TVS setting this corresponds to Rudin's
characterisation of continuity of linear functionals by local boundedness
at the origin. -/
def linear_continuous_of_bounded (f : E →ₗ[𝕜] F) (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    E →L[𝕜] F :=
  f.mkContinuousOfExistsBound h

end LinearContinuity

section BalancedHull

variable (𝕜 : Type*) [NormedField 𝕜] [NormOneClass 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- **Definition 1.27** — The balanced hull of a set: the smallest
balanced set containing it. -/
abbrev balanced_hull (s : Set E) : Set E := balancedHull 𝕜 s

omit [NormOneClass 𝕜] in
/-- **Theorem 1.28** — The balanced hull of `s` is balanced. -/
theorem balanced_hull_is_balanced (s : Set E) : Balanced 𝕜 (balancedHull 𝕜 s) :=
  balancedHull.balanced s

/-- **Theorem 1.28** — `s ⊆ balancedHull s`. -/
theorem subset_balanced_hull {s : Set E} : s ⊆ balancedHull 𝕜 s :=
  _root_.subset_balancedHull 𝕜

end BalancedHull

end Rudin.Ch01
