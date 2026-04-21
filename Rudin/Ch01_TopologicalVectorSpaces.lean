import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Basic

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

/-- **Theorem 1.6 (a)** — translation by `a` is a homeomorphism `E ≃ₜ E`.

Proof. The map `x ↦ a + x` is continuous since addition is jointly
continuous on a topological additive group and the first coordinate is
constant. Its inverse is translation by `-a`, which is continuous for
the same reason. Both inverses compose to the identity algebraically. -/
def translationHomeo (a : E) : E ≃ₜ E where
  toFun x := a + x
  invFun x := -a + x
  left_inv x := by simp [neg_add_cancel_left]
  right_inv x := by simp [add_neg_cancel_left]
  continuous_toFun := continuous_const.add continuous_id
  continuous_invFun := continuous_const.add continuous_id

/-- **Theorem 1.6 (b)** — multiplication by a nonzero scalar is a
homeomorphism.

Proof. Scalar multiplication `x ↦ c • x` is continuous because it
is the composition of `x ↦ (c, x)` (continuous) with the scalar
action (continuous by `ContinuousSMul`). The inverse is `c⁻¹ • ·`,
continuous by the same argument. The inverse relations reduce to
`c⁻¹ • c • x = x` via `inv_smul_smul₀ hc`. -/
def smulHomeo {c : 𝕜} (hc : c ≠ 0) : E ≃ₜ E where
  toFun x := c • x
  invFun x := c⁻¹ • x
  left_inv x := inv_smul_smul₀ hc x
  right_inv x := smul_inv_smul₀ hc x
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

/-- **Corollary of 1.6** — left-translation by `a` sends open sets to
open sets.

Proof. Express `(a + ·) '' s` as the preimage of `s` under translation
by `-a`. Translation by `-a` is continuous (Theorem 1.6 (a) applied to
`-a`), hence the preimage of the open `s` is open. -/
theorem translation_image_isOpen (a : E) {s : Set E} (hs : IsOpen s) :
    IsOpen ((a + ·) '' s) := by
  have heq : (a + ·) '' s = (fun x : E => -a + x) ⁻¹' s := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [neg_add_cancel_left] using hy
    · intro hx
      exact ⟨-a + x, hx, by simp [add_neg_cancel_left]⟩
  rw [heq]
  exact hs.preimage (continuous_const.add continuous_id)

omit [IsTopologicalAddGroup E] in
/-- **Corollary of 1.6** — scalar multiplication by a nonzero `c` sends
open sets to open sets.

Proof. Rewrite `(c • ·) '' s` as the preimage of `s` under `c⁻¹ • ·`.
The latter is continuous (Theorem 1.6 (b) applied to `c⁻¹`), so the
preimage of an open set is open. -/
theorem smul_image_isOpen {c : 𝕜} (hc : c ≠ 0) {s : Set E} (hs : IsOpen s) :
    IsOpen ((c • ·) '' s) := by
  have heq : (c • ·) '' s = (fun x : E => c⁻¹ • x) ⁻¹' s := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [inv_smul_smul₀ hc] using hy
    · intro hx
      exact ⟨c⁻¹ • x, hx, by simp [smul_inv_smul₀ hc]⟩
  rw [heq]
  exact hs.preimage (continuous_const.smul continuous_id)

end TVS

/-- **Theorem 1.22 (Heine–Borel in finite dimensions)** — In a
finite-dimensional normed space over a locally compact field `𝕜`, every
closed and bounded subset is compact.

Proof.
1. A finite-dimensional normed space over a locally compact field is a
   `ProperSpace`, i.e. every closed ball is compact. This is the content
   of `FiniteDimensional.proper`.
2. A bounded set `s` is contained in some closed ball `closedBall 0 R`.
3. The closed ball is compact (by step 1), hence `s` is a closed subset
   of a compact set, hence itself compact. -/
theorem heine_borel (𝕜 : Type*) [NontriviallyNormedField 𝕜] [LocallyCompactSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {s : Set E} (h_closed : IsClosed s) (h_bdd : Bornology.IsBounded s) :
    IsCompact s := by
  haveI : ProperSpace E := FiniteDimensional.proper 𝕜 E
  obtain ⟨R, hR⟩ := h_bdd.subset_closedBall (0 : E)
  exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E) R) h_closed hR

section Minkowski

open scoped Pointwise

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- **Definition 1.33** — Minkowski functional (gauge) of a set. -/
noncomputable def minkowski (s : Set E) : E → ℝ := gauge s

omit [TopologicalSpace E] in
/-- **Theorem 1.35 (subadditivity of the Minkowski functional)** — If
`s` is convex and absorbent, then the Minkowski functional of `s` is
subadditive: `μ(x + y) ≤ μ(x) + μ(y)`.

Proof. It suffices to show `μ(x + y) < μ(x) + μ(y) + ε` for every
`ε > 0`. Pick `a > μ(x)` with `a < μ(x) + ε/2` and `b > μ(y)` with
`b < μ(y) + ε/2`, and elements `u ∈ s`, `v ∈ s` with `x = a • u`,
`y = b • v` (existence from the definition of the gauge via
`exists_lt_of_gauge_lt`). By convexity of `s`,
`a • u + b • v = (a + b) • ((a/(a+b)) • u + (b/(a+b)) • v) ∈ (a+b) • s`,
so `μ(x + y) ≤ a + b < μ(x) + μ(y) + ε`. -/
theorem minkowski_add_le {s : Set E} (hs : Convex ℝ s) (absorbs : Absorbent ℝ s)
    (x y : E) :
    minkowski s (x + y) ≤ minkowski s x + minkowski s y := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨a, ha_pos, ha_lt, u, hu, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s x) (half_pos hε))
  obtain ⟨b, hb_pos, hb_lt, v, hv, rfl⟩ :=
    exists_lt_of_gauge_lt absorbs (lt_add_of_pos_right (gauge s y) (half_pos hε))
  calc
    gauge s (a • u + b • v) ≤ a + b := gauge_le_of_mem (by positivity) <| by
      rw [hs.add_smul ha_pos.le hb_pos.le]
      exact Set.add_mem_add (Set.smul_mem_smul_set hu) (Set.smul_mem_smul_set hv)
    _ < gauge s (a • u) + gauge s (b • v) + ε := by linarith

end Minkowski

section LinearContinuity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Theorem 1.18 (continuity via boundedness)** — A linear map between
normed spaces is continuous as soon as it admits a constant `C` with
`‖f x‖ ≤ C · ‖x‖`.

Proof. Let `C` be such a bound. For every `x`, the inequality
`‖f x - f 0‖ = ‖f x‖ ≤ C · ‖x‖ = C · ‖x - 0‖` combined with linearity
shows that `f` is Lipschitz with constant `|C|`, hence continuous; we
repackage this as a `ContinuousLinearMap` via
`AddMonoidHomClass.continuous_of_bound`. -/
def linear_continuous_of_bounded (f : E →ₗ[𝕜] F) (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    E →L[𝕜] F :=
  ⟨f, let ⟨C, hC⟩ := h; AddMonoidHomClass.continuous_of_bound f C hC⟩

end LinearContinuity

section BalancedHull

open scoped Pointwise

variable (𝕜 : Type*) [NormedField 𝕜] [NormOneClass 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- **Definition 1.27** — The balanced hull of a set is the union
`⋃ ‖r‖≤1, r • s`; equivalently, the smallest balanced set containing `s`. -/
abbrev balanced_hull (s : Set E) : Set E := balancedHull 𝕜 s

omit [NormOneClass 𝕜] in
/-- **Theorem 1.28 (balanced)** — `balancedHull s` is balanced.

Proof. Take `a` with `‖a‖ ≤ 1` and `x ∈ a • balancedHull 𝕜 s`. By the
definition of the hull as `⋃ ‖r‖≤1, r • s`, there exist `r` with
`‖r‖ ≤ 1` and `y ∈ r • s` with `x = a • y`. Then `x = (a • r) • z` for
some `z ∈ s`; since `‖a • r‖ = ‖a‖ · ‖r‖ ≤ 1 · 1 = 1`, the element
`x` lies in `(a r) • s ⊆ balancedHull 𝕜 s`. -/
theorem balanced_hull_is_balanced (s : Set E) : Balanced 𝕜 (balancedHull 𝕜 s) := by
  intro a ha
  simp_rw [balancedHull, Set.smul_set_iUnion₂, Set.subset_def, Set.mem_iUnion₂]
  rintro x ⟨r, hr, hx⟩
  rw [← smul_assoc] at hx
  exact ⟨a • r, (norm_mul_le _ _).trans (mul_le_one₀ ha (norm_nonneg r) hr), hx⟩

/-- **Theorem 1.28 (extension)** — `s ⊆ balancedHull 𝕜 s`.

Proof. For `x ∈ s`, take `r = 1`; then `‖1‖ = 1 ≤ 1` and
`x = 1 • x ∈ 1 • s`, so `x` belongs to the hull. -/
theorem subset_balanced_hull {s : Set E} : s ⊆ balancedHull 𝕜 s := fun _ hx =>
  mem_balancedHull_iff.2 ⟨1, norm_one.le, _, hx, one_smul _ _⟩

omit [NormOneClass 𝕜] in
/-- **Theorem 1.28 (minimality)** — If `t` is balanced and `s ⊆ t`,
then `balancedHull 𝕜 s ⊆ t`.

Proof. Let `x ∈ balancedHull 𝕜 s`. By definition there exist `r` with
`‖r‖ ≤ 1` and `y ∈ s` with `x = r • y`. Since `y ∈ t` by hypothesis and
`t` is balanced, `r • y ∈ t`. -/
theorem balanced_hull_minimal {s t : Set E} (ht : Balanced 𝕜 t) (h : s ⊆ t) :
    balancedHull 𝕜 s ⊆ t := by
  intro x hx
  obtain ⟨r, hr, y, hy, rfl⟩ := mem_balancedHull_iff.1 hx
  exact ht.smul_mem hr (h hy)

omit [NormOneClass 𝕜] in
/-- **Theorem 1.28 (monotonicity)** — `balancedHull` is monotone in `s`.

Proof. If `x ∈ balancedHull 𝕜 s`, write `x = r • y` with `‖r‖ ≤ 1` and
`y ∈ s`. Then `y ∈ t` since `s ⊆ t`, so `x ∈ r • t ⊆ balancedHull 𝕜 t`. -/
theorem balanced_hull_mono {s t : Set E} (hst : s ⊆ t) :
    balancedHull 𝕜 s ⊆ balancedHull 𝕜 t := by
  intro x hx
  rw [mem_balancedHull_iff] at *
  obtain ⟨r, hr₁, hr₂⟩ := hx
  exact ⟨r, hr₁, Set.smul_set_mono hst hr₂⟩

end BalancedHull

section Hausdorff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- **Theorem 1.12** — In the setting of Rudin (i.e. with all singletons
closed, `T1Space`), every topological vector space is Hausdorff.

Proof. In a topological additive group, `T2Space` is equivalent to the
closedness of `{0}` (mathlib's `IsTopologicalAddGroup.t2Space_iff_zero_closed`,
the additive variant of `IsTopologicalGroup.t2Space_iff_one_closed`).
The `T1Space` assumption gives `isClosed_singleton` for every point,
including the origin. -/
theorem t2_of_t1 [T1Space E] : T2Space E :=
  IsTopologicalAddGroup.t2Space_iff_zero_closed.mpr isClosed_singleton

end Hausdorff

section BalancedNhd

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

omit [IsTopologicalAddGroup E] in
/-- **Theorem 1.14 (a)** — Every neighbourhood of `0` contains a
balanced neighbourhood of `0`. In fact, the balanced neighbourhoods form
a basis for the neighbourhood filter of `0`.

Proof. `nhds_basis_balanced` packages precisely this statement: the
neighbourhood filter of `0` has a basis consisting of balanced sets,
obtained (constructively) by replacing each neighbourhood by its
balanced core. -/
theorem nhds_zero_has_basis_balanced :
    (nhds (0 : E)).HasBasis (fun s : Set E => s ∈ nhds (0 : E) ∧ Balanced 𝕜 s) id :=
  nhds_basis_balanced 𝕜 E

omit [IsTopologicalAddGroup E] in
/-- **Theorem 1.14 (a), existence version** — Every neighbourhood `U`
of `0` contains a balanced neighbourhood of `0`. -/
theorem exists_balanced_nhds_subset {U : Set E} (hU : U ∈ nhds (0 : E)) :
    ∃ V ∈ nhds (0 : E), Balanced 𝕜 V ∧ V ⊆ U :=
  ⟨balancedCore 𝕜 U, balancedCore_mem_nhds_zero hU,
    balancedCore_balanced U, balancedCore_subset U⟩

end BalancedNhd

section ClosureBalancedBounded

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- **Theorem 1.13 (e)** — If `B ⊆ E` is balanced, so is its closure. -/
theorem balanced_closure [ContinuousSMul 𝕜 E] {B : Set E}
    (hB : Balanced 𝕜 B) : Balanced 𝕜 (closure B) :=
  hB.closure

/-- **Theorem 1.13 (f)** — In a `T1` regular TVS, if `A ⊆ E` is
(von Neumann) bounded, so is its closure. -/
theorem vonNBounded_closure [T1Space E] [RegularSpace E]
    [ContinuousConstSMul 𝕜 E] {A : Set E} (hA : Bornology.IsVonNBounded 𝕜 A) :
    Bornology.IsVonNBounded 𝕜 (closure A) :=
  hA.closure

end ClosureBalancedBounded

section ClosureConvex

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]

/-- **Theorem 1.13 (d)** — If `C ⊆ F` is convex (real TVS), so is its
closure. -/
theorem convex_closure {C : Set F} (hC : Convex ℝ C) : Convex ℝ (closure C) :=
  hC.closure

end ClosureConvex

section CompactBounded

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [UniformSpace E]
variable [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]

/-- **Theorem 1.15 (b)** — Every compact subset of a TVS (working here
with its underlying uniform structure) is bounded.

Proof. A compact subset of a uniform space is totally bounded, and
totally bounded subsets are von Neumann bounded in any TVS. -/
theorem isVonNBounded_of_isCompact {K : Set E} (hK : IsCompact K) :
    Bornology.IsVonNBounded 𝕜 K :=
  hK.totallyBounded.isVonNBounded 𝕜

end CompactBounded

section Absorbent

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [ContinuousSMul 𝕜 E]

/-- **Theorem 1.15 (a)** — Every neighbourhood `V` of `0` is absorbent:
for every `x ∈ E`, there is a scalar `r` with `x ∈ r • V`. Equivalently,
`X = ⋃_{r > 0} r • V` (the form Rudin states with `rₙ → ∞`).

Proof. `absorbent_nhds_zero`: since scalar multiplication is continuous
and `0 • x = 0 ∈ V`, the set `{ a : 𝕜 | a • x ∈ V }` is a neighbourhood
of `0` in `𝕜`, so it contains arbitrarily small nonzero scalars; taking
`r = a⁻¹` one obtains `x ∈ r • V`. -/
theorem absorbent_nhds_zero' {V : Set E} (hV : V ∈ nhds (0 : E)) :
    Absorbent 𝕜 V :=
  absorbent_nhds_zero hV

end Absorbent

section LinearContinuity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [ContinuousSMul 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- **Theorem 1.17** — A linear map `Λ : E → F` between topological
vector spaces that is continuous at `0` is continuous everywhere.

Proof. Continuity at `0` plus the group-homomorphism property give
continuity at every point via translation: by `continuous_of_continuousAt_zero`
(the additive instance generated via `to_additive` from the monoid
version `continuous_of_continuousAt_one`). -/
theorem continuous_of_linear_continuousAt_zero
    (Λ : E →+ F) (h : ContinuousAt Λ 0) :
    Continuous Λ :=
  continuous_of_continuousAt_zero Λ h

/-- **Theorem 1.18 (part (a) ↔ (b))** — A linear functional `Λ : E → 𝕜`
on a TVS is continuous if and only if its kernel is closed.

Proof. If `Λ` is continuous then `ker Λ = Λ⁻¹{0}` is the preimage of
the closed singleton `{0}`, hence closed. Conversely, when the kernel
is closed, `LinearMap.continuous_of_isClosed_ker` builds a bounded
neighbourhood of `0` on which `Λ` stays away from any fixed scalar of
modulus `≥ 1`, and this local boundedness forces continuity at `0`,
hence everywhere by Theorem 1.17. -/
theorem linearFunctional_continuous_iff_ker_isClosed (Λ : E →ₗ[𝕜] 𝕜) :
    Continuous Λ ↔ IsClosed (LinearMap.ker Λ : Set E) :=
  Λ.continuous_iff_isClosed_ker

/-- **Theorem 1.18 (part (a) via nonvanishing on an open set)** — A
linear functional that is nonzero on some nonempty open set is
automatically continuous. -/
theorem linearFunctional_continuous_of_nonzero_on_open
    (Λ : E →ₗ[𝕜] 𝕜) {s : Set E} (hs₁ : IsOpen s) (hs₂ : s.Nonempty)
    (hs₃ : ∀ x ∈ s, Λ x ≠ 0) : Continuous Λ :=
  Λ.continuous_of_nonzero_on_open s hs₁ hs₂ hs₃

end LinearContinuity

section FiniteDimensional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E F : Type*}
variable [AddCommGroup E] [Module 𝕜 E] [UniformSpace E]
variable [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

/-- **Theorem 1.20 (Lemma)** — A linear map from `𝕜ⁿ` (finite-dimensional
Hausdorff `𝕜`-module) into a TVS is automatically continuous.

Proof. This is mathlib's `LinearMap.continuous_of_finiteDimensional`
which shows that every linear map on a finite-dimensional Hausdorff
`𝕜`-module is continuous. In Rudin's formulation one takes the domain
to be `ℂⁿ` and writes `f(z) = z₁u₁ + … + zₙuₙ`, deducing continuity
from the continuity of each coordinate projection combined with
addition and scalar multiplication continuity in the target. -/
theorem linear_from_finiteDimensional_continuous [T2Space E]
    [FiniteDimensional 𝕜 E] (Λ : E →ₗ[𝕜] F) : Continuous Λ :=
  Λ.continuous_of_finiteDimensional

/-- **Theorem 1.21 (b)** — Every finite-dimensional subspace of a
Hausdorff TVS is closed.

Proof. `Submodule.closed_of_finiteDimensional`: a finite-dimensional
subspace is automatically complete (via the uniform structure induced
from the topological additive group), hence closed. -/
theorem finiteDimensional_subspace_isClosed [T2Space E]
    (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsClosed (s : Set E) :=
  s.closed_of_finiteDimensional

/-- **Theorem 1.22 (Riesz, finite-dimensionality from local compactness)** —
Every locally compact topological vector space has finite dimension.

Proof. Pick a compact neighbourhood `K` of `0`. Compact sets are
totally bounded in a uniform space, and in a TVS a totally-bounded
neighbourhood of the origin forces finite-dimensionality
(`FiniteDimensional.of_totallyBounded_nhds_zero`). This is the
additive-group version of Riesz's theorem. -/
theorem finiteDimensional_of_locallyCompactSpace [T2Space E]
    [LocallyCompactSpace E] : FiniteDimensional 𝕜 E :=
  FiniteDimensional.of_locallyCompactSpace 𝕜

end FiniteDimensional

section MetricProperties

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Theorem 1.28 (a)** — On an additive group with a translation-invariant
pseudo-norm (equivalently, a translation-invariant pseudo-metric via
`d(x, y) = ‖x - y‖`), `‖n • x‖ ≤ n · ‖x‖` for every `n : ℕ`.

Proof. Mathlib's `norm_nsmul_le` supplies this inequality directly; it
is equivalent to `d(nx, 0) ≤ n · d(x, 0)` when the metric comes from a
seminorm. The underlying argument is a telescoping
`‖nx‖ ≤ Σ_{k=1}^{n} ‖x‖` obtained from the triangle inequality. -/
theorem norm_nsmul_le_nat (x : E) (n : ℕ) :
    ‖n • x‖ ≤ n * ‖x‖ :=
  norm_nsmul_le

end MetricProperties

end Rudin.Ch01
