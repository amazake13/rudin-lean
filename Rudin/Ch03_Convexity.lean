import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Chapter 3 — Convexity

Rudin, *Functional Analysis* (2nd ed.), Chapter 3.

Hahn–Banach (analytic and geometric) and Krein–Milman.
-/

namespace Rudin.Ch03

section HahnBanachAnalytic

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Theorem 3.2 (Hahn–Banach, analytic form)** — A linear functional
defined on a subspace of a real vector space `E` and dominated by a
sublinear functional `N` extends to a linear functional on the whole of
`E` that is still dominated by `N`. -/
theorem hahn_banach_extension (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
    (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y)
    (hf : ∀ x : f.domain, f x ≤ N x) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x, g x ≤ N x :=
  exists_extension_of_le_sublinear f N N_hom N_add hf

end HahnBanachAnalytic

section HahnBanachGeometric

variable {E : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

omit [T2Space E] in
/-- **Theorem 3.4 (Hahn–Banach, geometric separation)** — In a locally
convex Hausdorff TVS, a compact convex set and a disjoint closed convex
set can be strictly separated by a continuous linear functional. -/
theorem hahn_banach_separation {s t : Set E}
    (hs_conv : Convex ℝ s) (hs_cpt : IsCompact s)
    (ht_conv : Convex ℝ t) (ht_closed : IsClosed t) (h_disj : Disjoint s t) :
    ∃ (f : StrongDual ℝ E) (u v : ℝ),
      (∀ a ∈ s, f a < u) ∧ u < v ∧ ∀ b ∈ t, v < f b :=
  geometric_hahn_banach_compact_closed hs_conv hs_cpt ht_conv ht_closed h_disj

/-- **Theorem 3.23 (Krein–Milman)** — In a locally convex Hausdorff TVS,
every compact convex set is the closed convex hull of its extreme points. -/
theorem krein_milman {s : Set E} (hs_cpt : IsCompact s) (hs_conv : Convex ℝ s) :
    closure (convexHull ℝ (s.extremePoints ℝ)) = s :=
  closure_convexHull_extremePoints hs_cpt hs_conv

omit [T2Space E] in
/-- **Theorem 3.5 (closed convex vs. point)** — A closed convex set and
a point outside it can be strictly separated by a continuous linear
functional. -/
theorem hahn_banach_closed_point {s : Set E} {x : E}
    (hs_conv : Convex ℝ s) (hs_closed : IsClosed s) (hx : x ∉ s) :
    ∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ u < f x :=
  geometric_hahn_banach_closed_point hs_conv hs_closed hx

omit [T2Space E] in
/-- **Theorem 3.5 (two distinct points)** — In a locally convex $T_1$
TVS, any two distinct points are strictly separated by a continuous
linear functional. -/
theorem hahn_banach_point_point [T1Space E] {x y : E} (hxy : x ≠ y) :
    ∃ f : StrongDual ℝ E, f x < f y :=
  geometric_hahn_banach_point_point hxy

end HahnBanachGeometric

end Rudin.Ch03
