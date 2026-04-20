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

end Rudin.Ch01
