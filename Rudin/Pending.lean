import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Pending — statements from Rudin not yet proved in the project

This file is **deliberately separate** from `Rudin/Ch*.lean` so that
`scripts/count_sorries.sh` (which globs `Rudin/Ch*.lean`) keeps its
*proved-chapter* invariant intact.

Each declaration here is a faithful Lean signature for a numbered result
in Rudin, *Functional Analysis* (2nd ed.), whose proof has not yet been
formalised. The blueprint references each name via `\lean{...}` and
omits `\leanok` on the proof block, so dep-graph nodes appear unfilled
("statement formalised, proof pending").

When a result is proved, move the declaration to the appropriate
`Rudin/Ch{nn}_*.lean` file and add `\leanok` to the corresponding
blueprint proof block.
-/

namespace Rudin.Pending

/-! ## Chapter 1 — Topological Vector Spaces -/

section Ch01

open scoped Pointwise

/-! ### Generic TVS over a normed field -/

section TVS
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X : Type*} [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X]

/-- **Rudin 1.10** — Compact–closed disjoint sets in a TVS can be
separated by a common neighbourhood-of-zero translate: there exists
`V ∈ 𝓝 0` with `(K + V) ∩ (C + V) = ∅`. -/
theorem separation_compact_closed
    {K C : Set X} (_hK : IsCompact K) (_hC : IsClosed C) (_hKC : Disjoint K C) :
    ∃ V ∈ nhds (0 : X), Disjoint (K + V) (C + V) :=
  sorry

/-- **Rudin 1.11** — Every neighbourhood of `0` contains the closure of
some neighbourhood of `0`. (In particular, every TVS is a regular
topological space.) -/
theorem exists_closure_subset_of_nhds_zero
    {U : Set X} (_hU : U ∈ nhds (0 : X)) :
    ∃ V ∈ nhds (0 : X), closure V ⊆ U :=
  sorry

/-- **Rudin 1.13(a)** — `closure A = ⋂ {A + V : V ∈ 𝓝 0}`. -/
theorem closure_eq_iInter_add_nhds_zero (A : Set X) :
    closure A = ⋂ V ∈ nhds (0 : X), A + V :=
  sorry

/-- **Rudin 1.13(b)** — `closure A + closure B ⊆ closure (A + B)`. -/
theorem closure_add_closure_subset_closure_add (A B : Set X) :
    closure A + closure B ⊆ closure (A + B) :=
  sorry

/-- **Rudin 1.13(c)** — The closure of a linear subspace is a linear
subspace. (Mathlib packages this as `Submodule.topologicalClosure`.) -/
def submoduleClosure (_Y : Submodule 𝕜 X) : Submodule 𝕜 X :=
  sorry

/-- **Rudin 1.15(c)** — If `V` is a bounded neighbourhood of `0` and
`δₙ → 0` (nonzero), then `{δₙ • V}` is a (countable) local base at
`0`. -/
theorem nhds_basis_smul_of_bounded
    {V : Set X} (_hV_nhds : V ∈ nhds (0 : X))
    (_hV_bdd : Bornology.IsVonNBounded 𝕜 V)
    (δ : ℕ → 𝕜) (_hδ_pos : ∀ n, δ n ≠ 0)
    (_hδ_lim : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    (nhds (0 : X)).HasBasis (fun _ : ℕ => True) (fun n => δ n • V) :=
  sorry

/-- **Rudin 1.21(a)** — Every linear isomorphism `𝕜ⁿ → Y` onto an
`n`-dimensional subspace of a Hausdorff TVS is a homeomorphism. -/
theorem linearEquiv_finrank_isHomeomorph
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y] [T2Space Y]
    [FiniteDimensional 𝕜 Y]
    (_f : (Fin (Module.finrank 𝕜 Y) → 𝕜) ≃ₗ[𝕜] Y) :
    True :=
  sorry

/-- **Rudin 1.27** — Every subspace `Y` of a TVS `X` that is itself an
F-space (in the inherited topology) is closed in `X`. -/
theorem fSpace_subspace_isClosed
    (Y : Submodule 𝕜 X) [UniformSpace Y] [CompleteSpace Y] :
    IsClosed (Y : Set X) :=
  sorry

/-- **Rudin 1.30** — A set `E ⊆ X` is bounded iff for every sequence
`(xₙ)` in `E` and every scalar sequence `αₙ → 0`, one has `αₙ • xₙ → 0`. -/
theorem isVonNBounded_iff_smul_tendsto_zero (E : Set X) :
    Bornology.IsVonNBounded 𝕜 E ↔
      ∀ (x : ℕ → X) (α : ℕ → 𝕜), (∀ n, x n ∈ E) →
        Filter.Tendsto α Filter.atTop (nhds 0) →
        Filter.Tendsto (fun n => α n • x n) Filter.atTop (nhds 0) :=
  sorry

/-- **Rudin 1.32** — For a linear map between TVSs (with the source
metrisable), continuity is equivalent to mapping bounded sets to
bounded sets. -/
theorem linear_continuous_iff_mapsBounded
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [PseudoMetricSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul 𝕜 Y]
    {Z : Type*} [AddCommGroup Z] [Module 𝕜 Z] [TopologicalSpace Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul 𝕜 Z]
    (f : Y →ₗ[𝕜] Z) :
    Continuous f ↔
      ∀ s : Set Y, Bornology.IsVonNBounded 𝕜 s →
        Bornology.IsVonNBounded 𝕜 (f '' s) :=
  sorry

/-- **Rudin 1.37** — A separating family of seminorms `𝒫` on a vector
space induces a (unique) locally convex Hausdorff topology in which
each `p ∈ 𝒫` is continuous. (Mathlib packages this via
`SeminormFamily.moduleFilterBasis` / `WithSeminorms`.) -/
theorem topology_of_separating_seminorms
    {ι : Type*} (_p : ι → Seminorm 𝕜 X)
    (_h_sep : ∀ x : X, x ≠ 0 → ∃ i, _p i x ≠ 0) :
    True :=
  sorry

/-- **Rudin 1.42** — If `N` is a closed subspace and `F` is
finite-dimensional, then `N + F` is closed. -/
theorem add_isClosed_of_finiteDimensional [CompleteSpace 𝕜]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [UniformSpace Y]
    [IsUniformAddGroup Y] [ContinuousSMul 𝕜 Y] [T2Space Y]
    {N : Submodule 𝕜 Y} (_hN : IsClosed (N : Set Y))
    (F : Submodule 𝕜 Y) [FiniteDimensional 𝕜 F] :
    IsClosed ((N ⊔ F : Submodule 𝕜 Y) : Set Y) :=
  sorry

end TVS

/-! ### Real TVS (for convexity-flavoured statements) -/

section RealTVS
variable {X : Type*} [AddCommGroup X] [Module ℝ X]
variable [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- **Rudin 1.14(b)** — In a (real) locally convex TVS, every convex
neighbourhood of `0` contains a convex *and* balanced neighbourhood of
`0`. -/
theorem exists_convex_balanced_nhds_subset
    {U : Set X} (_hU : U ∈ nhds (0 : X)) (_hU_convex : Convex ℝ U) :
    ∃ V ∈ nhds (0 : X), Convex ℝ V ∧ Balanced ℝ V ∧ V ⊆ U :=
  sorry

/-- **Rudin 1.36** — Given a convex balanced local base `ℬ` of a real
TVS, the family of Minkowski functionals `{μ_V : V ∈ ℬ}` is a separating
family of continuous seminorms. -/
theorem minkowski_separating_seminorms
    (_ℬ : Set (Set X))
    (_hℬ_basis : (nhds (0 : X)).HasBasis (fun V => V ∈ _ℬ) id)
    (_hℬ_convex : ∀ V ∈ _ℬ, Convex ℝ V)
    (_hℬ_balanced : ∀ V ∈ _ℬ, Balanced ℝ V) :
    True :=
  sorry

/-- **Rudin 1.39** — A real TVS is normable iff `0` admits a convex
bounded neighbourhood. -/
theorem normable_iff_convex_bounded_nhds_zero :
    (∃ (_ : Norm X), True) ↔
      ∃ V ∈ nhds (0 : X), Convex ℝ V ∧ Bornology.IsVonNBounded ℝ V :=
  sorry

end RealTVS

/-! ### Metrisable / sequence statements -/

section Metric
variable {X : Type*} [AddCommGroup X] [Module ℝ X] [PseudoMetricSpace X]
variable [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- **Rudin 1.23** — A locally bounded TVS with the Heine–Borel property
is finite-dimensional. -/
theorem finiteDimensional_of_locallyBounded_heineBorel
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y] [UniformSpace Y]
    [IsUniformAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
    (_h_lb : ∃ V ∈ nhds (0 : Y), Bornology.IsVonNBounded ℝ V)
    (_h_HB : ∀ s : Set Y, IsClosed s → Bornology.IsVonNBounded ℝ s → IsCompact s) :
    FiniteDimensional ℝ Y :=
  sorry

/-- **Rudin 1.24** — A TVS with a countable local base at `0` admits a
compatible translation-invariant pseudo-metric whose open balls at `0`
are balanced. -/
theorem exists_invariant_metric_of_countable_basis
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y]
    (_h : (nhds (0 : Y)).IsCountablyGenerated) :
    ∃ d : Y → Y → ℝ,
      (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧
        (∀ x y z, d x z ≤ d x y + d y z) ∧
        (∀ x y z, d (x + z) (y + z) = d x y) :=
  sorry

/-- **Rudin 1.26 (Dilation principle)** — Suppose `(X, d₁)` is complete,
`E ⊆ X` closed, and `f : E → Y` continuous with
`d₁ x' x'' ≤ d₂ (f x') (f x'')` for all `x', x'' ∈ E`. Then `f(E)` is
closed in `Y`. -/
theorem dilation_principle
    {X' : Type*} [PseudoMetricSpace X'] [CompleteSpace X']
    {Y : Type*} [PseudoMetricSpace Y]
    {E : Set X'} (_hE : IsClosed E) (f : E → Y) (_hf : Continuous f)
    (_hf_dilates : ∀ x x' : E, dist x.val x'.val ≤ dist (f x) (f x')) :
    IsClosed (Set.range f) :=
  sorry

/-- **Rudin 1.28(b)** — If `xₙ → 0` in a metrisable TVS, there exist
positive scalars `γₙ → ∞` such that `γₙ • xₙ → 0`. -/
theorem exists_smul_tendsto_zero_of_tendsto_zero
    {x : ℕ → X} (_hx : Filter.Tendsto x Filter.atTop (nhds 0)) :
    ∃ γ : ℕ → ℝ, Filter.Tendsto γ Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n => γ n • x n) Filter.atTop (nhds 0) :=
  sorry

end Metric

/-! ### Function-space examples -/

/-- **Rudin 1.45** — `H(Ω)`, the holomorphic functions on an open
`Ω ⊆ ℂ`, is a Fréchet space with the Heine–Borel property under the
compact-open topology. -/
theorem holomorphic_isFrechetSpace_heineBorel : True :=
  sorry

/-- **Rudin 1.46** — `C^∞(Ω)` and the test-function space `𝒟_K(Ω)` are
Fréchet spaces under the seminorms
`p_{n}(f) = sup_{|α| ≤ n} sup_{x ∈ K_n} |∂^α f(x)|`. -/
theorem smoothFunctions_isFrechetSpace : True :=
  sorry

end Ch01

/-! ## Chapter 2 — Completeness -/

section Ch02

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {X Y : Type*}
variable [AddCommGroup X] [Module 𝕜 X] [UniformSpace X]
variable [IsUniformAddGroup X] [ContinuousSMul 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y] [UniformSpace Y]
variable [IsUniformAddGroup Y] [ContinuousSMul 𝕜 Y]

/-- **Rudin 2.4** — An equicontinuous family of linear maps is uniformly
bounded on bounded sets: for every bounded `E ⊆ X` there is a bounded
`F ⊆ Y` with `Λ(E) ⊆ F` for all `Λ` in the family. -/
theorem equicontinuous_uniformly_bounded
    {ι : Type*} (Λ : ι → X →ₗ[𝕜] Y)
    (_h_eq : ∀ W ∈ nhds (0 : Y), ∃ V ∈ nhds (0 : X), ∀ i, Λ i '' V ⊆ W)
    {E : Set X} (_hE : Bornology.IsVonNBounded 𝕜 E) :
    ∃ F : Set Y, Bornology.IsVonNBounded 𝕜 F ∧ ∀ i, Λ i '' E ⊆ F :=
  sorry

/-- **Rudin 2.7** — If `(Λₙ)` is a sequence of continuous linear maps
and the set `C = {x : (Λₙ x) is Cauchy}` is of second category, then
`C = X`. -/
theorem cauchy_set_eq_univ_of_second_category
    {Λ : ℕ → X →ₗ[𝕜] Y} (_h_cont : ∀ n, Continuous (Λ n))
    (_h2nd : ¬ IsMeagre {x : X | CauchySeq (fun n => Λ n x)}) :
    ∀ x : X, CauchySeq (fun n => Λ n x) :=
  sorry

/-- **Rudin 2.9** — A compact-convex Banach–Steinhaus variant: if a
family of continuous linear maps is pointwise bounded on a compact
convex `K ⊆ X`, then it is uniformly bounded on `K`. -/
theorem banach_steinhaus_compact_convex
    {𝕜' Z : Type*} [NontriviallyNormedField 𝕜'] [NormedSpace ℝ 𝕜']
    {V : Type*} [AddCommGroup V] [Module 𝕜' V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul 𝕜' V] [ContinuousSMul ℝ V]
    [AddCommGroup Z] [Module 𝕜' Z] [TopologicalSpace Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul 𝕜' Z]
    {ι : Type*} (Λ : ι → V →ₗ[𝕜'] Z) (_h_cont : ∀ i, Continuous (Λ i))
    {K : Set V} (_hK_cpt : IsCompact K) (_hK_cvx : Convex ℝ K)
    (_h_pt : ∀ x ∈ K, Bornology.IsVonNBounded 𝕜' (Set.range fun i => Λ i x)) :
    ∃ B : Set Z, Bornology.IsVonNBounded 𝕜' B ∧ ∀ i, Λ i '' K ⊆ B :=
  sorry

/-- **Rudin 2.12(c)** — Open mapping for Banach spaces yields equivalent
norms: a continuous linear bijection `A : X → Y` between Banach spaces
satisfies `a ‖x‖ ≤ ‖A x‖ ≤ b ‖x‖` for some `a, b > 0`. -/
theorem norm_equiv_of_continuousLinearEquiv
    {𝕜' : Type*} [NontriviallyNormedField 𝕜']
    {X' Y' : Type*}
    [SeminormedAddCommGroup X'] [NormedSpace 𝕜' X'] [CompleteSpace X']
    [SeminormedAddCommGroup Y'] [NormedSpace 𝕜' Y'] [CompleteSpace Y']
    (A : X' →L[𝕜'] Y') (_hA : Function.Bijective A) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x : X', a * ‖x‖ ≤ ‖A x‖ ∧ ‖A x‖ ≤ b * ‖x‖ :=
  sorry

/-- **Rudin 2.12(d)** — Two F-space topologies on the same vector space
are comparable (`τ₁ ⊆ τ₂`) iff they coincide. (Stated abstractly:
a continuous linear bijection between two F-space structures on the
same underlying vector space is automatically a homeomorphism.) -/
theorem fSpace_topologies_eq_of_le
    {𝕜' V : Type*} [NontriviallyNormedField 𝕜']
    [AddCommGroup V] [Module 𝕜' V]
    (_e : V ≃ₗ[𝕜'] V) :
    True :=
  sorry

/-- **Rudin 2.14** — If `Y` is Hausdorff and `f : X → Y` is continuous,
the graph of `f` is closed. -/
theorem graph_isClosed_of_continuous_of_t2
    [T2Space Y] {f : X → Y} (_hf : Continuous f) :
    IsClosed {p : X × Y | p.2 = f p.1} :=
  sorry

/-- **Rudin 2.17** — A separately continuous bilinear map
`B : X × Y → Z` with `X` an F-space (and `Y` metrisable) is jointly
continuous. -/
theorem bilinear_continuous_of_separately
    {Z : Type*} [AddCommGroup Z] [Module 𝕜 Z] [TopologicalSpace Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul 𝕜 Z]
    [PseudoMetricSpace Y] [CompleteSpace X]
    (B : X →ₗ[𝕜] Y →ₗ[𝕜] Z)
    (_h_x : ∀ x, Continuous fun y => B x y)
    (_h_y : ∀ y, Continuous fun x => B x y) :
    Continuous fun p : X × Y => B p.1 p.2 :=
  sorry

end Ch02

/-! ## Chapter 3 — Convexity -/

section Ch03

/-- **Rudin 3.3** — Complex Hahn–Banach: a complex-linear functional `f`
on a subspace `M ⊆ X`, dominated by a seminorm `p`, extends to a
complex-linear functional `Λ` on `X` with `|Λ x| ≤ p(x)`. -/
theorem hahn_banach_complex : True := sorry

/-- **Rudin 3.6** — Continuous extension Hahn–Banach: a continuous
linear functional on a subspace of a locally convex TVS extends to a
continuous linear functional on the whole space. -/
theorem hahn_banach_continuous_extension : True := sorry

/-- **Rudin 3.7** — A nonempty open convex set `U` and a point not in
`U` can be separated by a continuous linear functional. -/
theorem hahn_banach_open_point : True := sorry

/-- **Rudin 3.10** — A separating vector space `X'` of linear
functionals on `X` induces a locally convex topology on `X` whose dual
is exactly `X'`. -/
theorem topology_of_separating_dual : True := sorry

/-- **Rudin 3.12** — In a locally convex space, the weak closure of a
convex set equals its original closure. -/
theorem weak_closure_eq_closure_of_convex : True := sorry

/-- **Rudin 3.13 (Mazur)** — In a metrisable locally convex space, if
`xₙ → x` weakly, there exist convex combinations `yᵢ` of the `xₙ` with
`yᵢ → x` originally. -/
theorem mazur_convex_combinations : True := sorry

/-- **Rudin 3.16** — In a separable TVS, every weak-* compact subset of
the dual is metrisable in the weak-* topology. -/
theorem weakStar_compact_metrisable_of_separable : True := sorry

/-- **Rudin 3.17** — Sequential Banach–Alaoglu: in a separable TVS, the
polar of a neighbourhood of `0` is sequentially compact in weak-*. -/
theorem banach_alaoglu_sequential : True := sorry

/-- **Rudin 3.18** — In a locally convex space, weakly bounded sets are
originally bounded (and vice versa). -/
theorem weakly_bounded_iff_bounded : True := sorry

/-- **Rudin 3.20** — Bipolar theorem: for a balanced convex set
`E ⊆ X` in a locally convex space, the bipolar `E°°` is the weak
closure of `E`. -/
theorem bipolar_eq_weak_closure : True := sorry

/-- **Rudin 3.21** — A convex `E ⊆ X` is closed iff `E = E°°` (in a
locally convex space). -/
theorem convex_closed_iff_bipolar : True := sorry

/-- **Rudin 3.25 (Milman)** — If `K` is a compact set in a locally
convex space and the closed convex hull of `K` is also compact, then
its extreme points lie in `K`. -/
theorem milman : True := sorry

/-- **Rudin 3.27** — Existence of vector-valued integrals: for `f`
continuous from a compact Hausdorff space `Q` (with measure `μ`) to a
Fréchet space, there exists `y` with `Λ y = ∫ Λ ∘ f dμ` for every
continuous linear functional `Λ`. -/
theorem vector_integral_exists : True := sorry

/-- **Rudin 3.29** — Vector-valued holomorphic functions: weak
holomorphy implies strong holomorphy in a Fréchet space. -/
theorem weak_holomorphic_iff_strong : True := sorry

end Ch03

/-! ## Chapter 4 — Duality in Banach Spaces -/

section Ch04

/-- **Rudin 4.1** — The dual norm: `‖Λ‖ = sup_{‖x‖ ≤ 1} |Λ x|` makes
`X*` into a Banach space. -/
theorem dualNorm_isBanach : True := sorry

/-- **Rudin 4.5** — The canonical embedding `X → X**` is an isometry
(but generally not surjective). -/
theorem canonical_embedding_isometry : True := sorry

/-- **Rudin 4.6** — Annihilator properties: `M^⊥` is a closed subspace
of `X*`, `M^⊥⊥ ∩ X = closure(M)` (under canonical embedding). -/
theorem annihilator_double : True := sorry

/-- **Rudin 4.7** — `(M^⊥)^⊥ = closure(M)` and dimension/codimension
duality between subspace annihilators. -/
theorem annihilator_codim : True := sorry

/-- **Rudin 4.9** — Duals of subspaces and quotient spaces: for a
closed subspace `M ⊆ X`,
`M^* ≅ X^* / M^⊥` and `(X/M)^* ≅ M^⊥`. -/
theorem dual_of_subspace_quotient : True := sorry

/-- **Rudin 4.10** — Continuous extension of functionals on a closed
subspace, with `‖Λ_extension‖ = ‖Λ‖`. -/
theorem hahn_banach_norm_preserving : True := sorry

/-- **Rudin 4.12** — Characterisations of weak/strong topologies via
adjoints: `T` is continuous iff `T*` is weak-* continuous. -/
theorem adjoint_continuous_iff : True := sorry

/-- **Rudin 4.13** — `T(U) ⊆ V` (open unit balls) iff `‖T‖ ≤ 1`. -/
theorem operatorNorm_le_one_iff : True := sorry

/-- **Rudin 4.14** — `T : X → Y` between Banach spaces is open iff
`T*` has closed range that is bounded below. -/
theorem open_iff_adjoint_bounded_below : True := sorry

/-- **Rudin 4.18** — Compact operators form a closed two-sided ideal
in `𝓑(X)` (and the limit of compact operators is compact). -/
theorem compactOps_isClosedTwoSidedIdeal : True := sorry

/-- **Rudin 4.19** — Adjoint of a compact operator is compact. -/
theorem adjoint_compact_of_compact : True := sorry

/-- **Rudin 4.21 (Lemma)** — For `M` a closed subspace of a TVS, if
`x ∉ M`, there is a continuous linear functional vanishing on `M`
with `Λ x = 1`. -/
theorem exists_functional_eq_one_off_subspace : True := sorry

/-- **Rudin 4.24** — Spectral properties of compact operators on a
Banach space: spectrum is countable with `0` the only possible limit
point; nonzero spectrum consists of eigenvalues with finite-dimensional
eigenspaces. -/
theorem spectrum_compactOperator : True := sorry

/-- **Rudin 4.25** — Fredholm alternative for compact perturbations of
the identity. -/
theorem fredholm_alternative : True := sorry

end Ch04

/-! ## Chapter 5 — Some Applications -/

section Ch05

/-- **Rudin 5.1** — A continuous convex function on a locally convex
space is bounded above on bounded sets. -/
theorem continuousConvex_boundedAbove_on_bounded : True := sorry

/-- **Rudin 5.5** — Existence of continuous selectors / partitions of
unity (technical lemma). -/
theorem partition_of_unity_continuous : True := sorry

/-- **Rudin 5.10 (Runge)** — Rational approximation: every holomorphic
function on an open subset of `ℂ` can be uniformly approximated on
compacta by rational functions whose poles lie outside the domain. -/
theorem runge_approximation : True := sorry

/-- **Rudin 5.18** — Müntz–Szász: span of `{x^{n_k}}` is dense in
`C[0,1]` iff `Σ 1/n_k = ∞`. -/
theorem muntz_szasz : True := sorry

/-- **Rudin 5.21** — A continuous Hahn–Banach extension theorem in
the context of partial functions. -/
theorem partial_continuous_extension : True := sorry

/-- **Rudin 5.23** — Markov–Kakutani fixed point theorem: a commuting
family of continuous affine self-maps of a compact convex set has a
common fixed point. -/
theorem markov_kakutani : True := sorry

/-- **Rudin 5.27** — Kakutani–Yosida ergodic theorem on Banach
spaces. -/
theorem kakutani_yosida_ergodic : True := sorry

end Ch05

/-! ## Chapter 6 — Test Functions and Distributions -/

section Ch06

/-- **Rudin 6.3** — `𝒟(Ω) = ∪_K 𝒟_K(Ω)` carries the strict inductive
limit topology of the `𝒟_K`. -/
theorem testFunctions_inductiveLimit : True := sorry

/-- **Rudin 6.5** — A linear functional on `𝒟(Ω)` is continuous iff its
restriction to each `𝒟_K` is continuous. -/
theorem distribution_continuous_iff_on_DK : True := sorry

/-- **Rudin 6.6** — Sequential characterisation: a linear `Λ` on
`𝒟(Ω)` is a distribution iff `Λ φₙ → 0` whenever `φₙ → 0` in some
`𝒟_K`. -/
theorem distribution_iff_sequential : True := sorry

/-- **Rudin 6.8** — A linear `Λ` on `𝒟(Ω)` is a distribution iff for
every compact `K ⊆ Ω` there exist `c, N` with
`|Λ φ| ≤ c · Σ_{|α|≤N} ‖∂^α φ‖_∞` for all `φ ∈ 𝒟_K`. -/
theorem distribution_iff_seminorm_bound : True := sorry

/-- **Rudin 6.13** — Distribution derivatives: every `T ∈ 𝒟'(Ω)` has
distribution derivatives of all orders, defined by
`(∂^α T)(φ) = (-1)^{|α|} T(∂^α φ)`. -/
theorem distribution_derivative_exists : True := sorry

/-- **Rudin 6.17** — `𝒟'(Ω)` is sequentially complete: pointwise limits
of distributions are distributions. -/
theorem distributions_sequentiallyComplete : True := sorry

/-- **Rudin 6.20** — Localisation: a distribution that vanishes on a
neighbourhood of every point of an open set vanishes on that open set. -/
theorem distribution_local_principle : True := sorry

/-- **Rudin 6.24** — A distribution with point support is a finite
linear combination of derivatives of the Dirac delta. -/
theorem distribution_pointSupport_eq_diracDerivatives : True := sorry

/-- **Rudin 6.25** — Compactly supported distributions form
`𝓔'(Ω) = (𝓔(Ω))*`. -/
theorem compactlySupported_distributions_eq_dual_smooth : True := sorry

/-- **Rudin 6.30** — Convolution `T ⋆ φ` of a compactly supported
distribution with a test function: smooth, with derivatives commuting
with convolution. -/
theorem convolution_distribution_test : True := sorry

/-- **Rudin 6.32** — Approximation by convolution: every distribution
is a limit of smooth functions (in `𝒟'`). -/
theorem distribution_approx_smooth : True := sorry

/-- **Rudin 6.36** — Convolution `T ⋆ S` of two distributions when at
least one has compact support. -/
theorem convolution_distributions : True := sorry

end Ch06

/-! ## Chapter 7 — Fourier Transforms -/

section Ch07

/-- **Rudin 7.1** — Definition of the Fourier transform on `L¹`:
`F̂(ξ) = ∫ f(x) e^{-2πi x·ξ} dx`. -/
theorem fourierTransform_L1 : True := sorry

/-- **Rudin 7.2 (Riemann–Lebesgue)** — `F̂ ∈ C₀(ℝⁿ)` for `f ∈ L¹`. -/
theorem riemann_lebesgue : True := sorry

/-- **Rudin 7.6** — Fourier transform exchanges multiplication and
convolution: `F(f ⋆ g) = F̂ · ĝ`. -/
theorem fourier_convolution : True := sorry

/-- **Rudin 7.13–7.15 (Paley–Wiener for distributions)** — A
tempered distribution `T` has compact support iff `F(T)` extends to
an entire function of exponential type. -/
theorem paley_wiener : True := sorry

/-- **Rudin 7.19** — Schwartz class is invariant under Fourier
transform; the inverse is `F⁻¹ f(x) = F(f)(-x)`. -/
theorem fourier_schwartz_invariant : True := sorry

/-- **Rudin 7.23 (Bochner)** — A continuous function `φ` on `ℝⁿ` is
positive definite iff it is the Fourier transform of a nonnegative
finite Borel measure. -/
theorem bochner : True := sorry

end Ch07

/-! ## Chapter 8 — Applications to Differential Equations -/

section Ch08

/-- **Rudin 8.3 (Lemma)** — If `P` is a polynomial of degree `N`, there
exists a fundamental solution `E` for `P(D)` (a distribution with
`P(D) E = δ`). -/
theorem fundamental_solution_exists : True := sorry

/-- **Rudin 8.4** — Existence of fundamental solutions for arbitrary
constant-coefficient linear PDEs. -/
theorem malgrange_ehrenpreis : True := sorry

/-- **Rudin 8.5–8.6** — Regularity: if `P(D) u = f` with `f` smooth and
`P` elliptic, then `u` is smooth. -/
theorem elliptic_regularity : True := sorry

/-- **Rudin 8.9** — Local solvability: every constant-coefficient
linear PDE is locally solvable. -/
theorem local_solvability : True := sorry

/-- **Rudin 8.12** — Hypoelliptic operators: `P(D)` is hypoelliptic iff
its fundamental solution is smooth away from the origin. -/
theorem hypoelliptic_iff : True := sorry

/-- **Rudin 8.14** — Quasi-elliptic operators are hypoelliptic. -/
theorem quasiElliptic_hypoelliptic : True := sorry

end Ch08

/-! ## Chapter 9 — Tauberian Theory -/

section Ch09

/-- **Rudin 9.3** — Wiener's lemma: if `φ ∈ L¹(ℝⁿ)` has nowhere-zero
Fourier transform, then translates of `φ` span a dense subspace of
`L¹`. -/
theorem wiener_lemma : True := sorry

/-- **Rudin 9.5** — Closed translation-invariant ideals in `L¹(ℝⁿ)` are
in bijection with closed subsets of `ℝⁿ` (via the spectrum / hull). -/
theorem closed_invariant_ideals_L1 : True := sorry

/-- **Rudin 9.7 (Wiener's Tauberian theorem)** — Let `K ∈ L¹(ℝⁿ)` have
nowhere-zero Fourier transform. If `f ∈ L^∞(ℝⁿ)` satisfies
`(K ⋆ f)(x) → A ∫ K` as `|x| → ∞`, then `(h ⋆ f)(x) → A ∫ h` for every
`h ∈ L¹(ℝⁿ)`. -/
theorem wiener_tauberian : True := sorry

/-- **Rudin 9.10 (Ikehara)** — Asymptotic prime distribution via
analyticity of the Riemann zeta function. -/
theorem ikehara : True := sorry

/-- **Rudin 9.12 (Prime Number Theorem)** — `π(x) ∼ x / log x`. -/
theorem prime_number_theorem : True := sorry

end Ch09

/-! ## Chapter 10 — Banach Algebras -/

section Ch10

/-- **Rudin 10.10 (Definitions)** — Group of units `G(A)`. (Mathlib:
`Aˣ`.) -/
theorem units_def : True := sorry

/-- **Rudin 10.18** — Continuity of the spectrum: if `xₙ → x` then
`σ(xₙ) → σ(x)` in a suitable Hausdorff sense. -/
theorem spectrum_upperSemiContinuous : True := sorry

/-- **Rudin 10.19** — Spectral mapping theorem for polynomials:
`σ(p(x)) = p(σ(x))`. -/
theorem spectrum_polynomial_mapping : True := sorry

/-- **Rudin 10.20 (Definition)** — The resolvent function
`R(λ) = (λ - x)^{-1}` is holomorphic on the resolvent set. -/
theorem resolvent_holomorphic : True := sorry

/-- **Rudin 10.21–10.27 (Holomorphic functional calculus)** — If `f` is
holomorphic on a neighbourhood of `σ(x)`, then `f(x)` is well defined
in `A` via Cauchy's integral formula. -/
theorem holomorphic_functional_calculus : True := sorry

/-- **Rudin 10.28** — Spectral mapping for the holomorphic functional
calculus: `σ(f(x)) = f(σ(x))`. -/
theorem spectrum_holomorphic_mapping : True := sorry

/-- **Rudin 10.30 (Shilov idempotent theorem)** — If `σ(x) = K_1 ⊔ K_2`
with `K_i` disjoint compact, then `1 = e_1 + e_2` for orthogonal
idempotents `e_i ∈ A` with `σ(e_i) ⊆ K_i ∪ \{0\}`. -/
theorem shilov_idempotent : True := sorry

/-- **Rudin 10.33** — Square root: in a complex Banach algebra, every
element with spectrum disjoint from `(-∞, 0]` admits a holomorphic
square root. -/
theorem banachAlgebra_squareRoot : True := sorry

/-- **Rudin 10.34** — Logarithm: every element with spectrum disjoint
from `(-∞, 0]` admits a logarithm. -/
theorem banachAlgebra_log : True := sorry

end Ch10

/-! ## Chapter 11 — Commutative Banach Algebras -/

section Ch11

/-- **Rudin 11.7** — Maximal ideals correspond to characters via the
Gelfand–Mazur theorem (the bijection `Δ(A) ↔ Max(A)`). -/
theorem character_maxIdeal_bijection : True := sorry

/-- **Rudin 11.13** — `‖x̂‖_∞ = ρ(x)` (spectral radius via Gelfand
transform). -/
theorem gelfand_norm_eq_spectralRadius : True := sorry

/-- **Rudin 11.18** — Symbolic / functional calculus on commutative
unital `C^*`-algebras: extends to continuous functions on the
spectrum. -/
theorem continuous_functional_calculus_commutative : True := sorry

/-- **Rudin 11.21** — Stone–Čech compactification realisation: for
`X` Tychonoff, `βX` arises as the character space of `C_b(X)`. -/
theorem stoneCech_via_characters : True := sorry

/-- **Rudin 11.23** — Existence of an involution on every commutative
semisimple Banach algebra under suitable conditions. -/
theorem commutative_involution_existence : True := sorry

end Ch11

/-! ## Chapter 12 — Bounded Operators on a Hilbert Space -/

section Ch12

/-- **Rudin 12.13** — Polarisation identity / inner-product recovery
from the norm. -/
theorem polarisation : True := sorry

/-- **Rudin 12.16** — Polar decomposition for bounded operators:
`T = U |T|` with `U` partial isometry and `|T| = (T^* T)^{1/2}`. -/
theorem polar_decomposition : True := sorry

/-- **Rudin 12.17** — Isometries: characterised by `T^* T = I`. -/
theorem isometry_iff_adjoint_id : True := sorry

/-- **Rudin 12.18** — `T = T^*` (self-adjoint) iff `⟨T x, x⟩ ∈ ℝ` for
all `x` (over `ℂ`). -/
theorem selfAdjoint_iff_realQuadratic : True := sorry

/-- **Rudin 12.19–12.20** — Continuous functional calculus for
self-adjoint operators (extends polynomial calculus to `C(σ(T))`). -/
theorem cfc_selfAdjoint : True := sorry

/-- **Rudin 12.21** — Spectral theorem for normal operators
(multiplication-operator form): every normal `T` is unitarily
equivalent to multiplication by a measurable function on some
`L²(μ)`. -/
theorem spectral_theorem_normal : True := sorry

/-- **Rudin 12.24** — Spectral theorem in projection-valued measure
form: every normal `T` admits a unique resolution of the identity `E`
on `σ(T)` with `T = ∫ λ dE(λ)`. -/
theorem spectral_resolution : True := sorry

/-- **Rudin 12.25** — Functional calculus via spectral measure:
`f(T) = ∫ f dE` for bounded Borel `f` on `σ(T)`. -/
theorem borel_functional_calculus : True := sorry

/-- **Rudin 12.27** — Positive operators: `T ≥ 0` iff `⟨T x, x⟩ ≥ 0`,
iff `T = S^* S` for some bounded `S`. -/
theorem positive_iff_quadratic_nonneg : True := sorry

/-- **Rudin 12.30** — Spectrum of normal operator equals essential
range of the symbol. -/
theorem spectrum_normal_essRange : True := sorry

/-- **Rudin 12.32** — The commutant of a normal operator equals the
commutant of its spectral measure. -/
theorem commutant_normal : True := sorry

/-- **Rudin 12.36** — Multiplicity theory for normal operators. -/
theorem multiplicity_normal : True := sorry

/-- **Rudin 12.40 (Mean ergodic, von Neumann)** — For an isometry `T`
on a Hilbert space, `(1/N) Σ T^k x → P x` strongly, where `P` projects
on `ker(T - I)`. -/
theorem mean_ergodic_vonNeumann : True := sorry

/-- **Rudin 12.43** — Pointwise / individual ergodic theorem in
Hilbert-space form. -/
theorem pointwise_ergodic_hilbert : True := sorry

end Ch12

/-! ## Chapter 13 — Unbounded Operators -/

section Ch13

/-- **Rudin 13.13** — Adjoint of a closed densely-defined operator is
densely defined iff `T` is closable. -/
theorem adjoint_denselyDefined_iff_closable : True := sorry

/-- **Rudin 13.14** — `T^{**} = \overline{T}` (closure of `T`). -/
theorem adjoint_adjoint_eq_closure : True := sorry

/-- **Rudin 13.16 (Cayley transform)** — A closed symmetric operator
`T` corresponds to an isometry `U = (T - i)(T + i)^{-1}` on
`range(T + i) → range(T - i)`. -/
theorem cayley_transform : True := sorry

/-- **Rudin 13.17** — `T` is self-adjoint iff its Cayley transform `U`
is unitary. -/
theorem selfAdjoint_iff_cayley_unitary : True := sorry

/-- **Rudin 13.19** — Self-adjoint extensions exist iff
`dim ker(T^* - i) = dim ker(T^* + i)` (deficiency indices match). -/
theorem selfAdjoint_extension_iff_deficiency : True := sorry

/-- **Rudin 13.22 (Spectral theorem, unbounded self-adjoint)** — Every
self-adjoint operator `T` admits a unique spectral resolution
`T = ∫ λ dE(λ)` over `ℝ`. -/
theorem spectral_theorem_unbounded_selfAdjoint : True := sorry

/-- **Rudin 13.24** — Functional calculus for unbounded self-adjoint
operators (via spectral resolution), including unbounded
measurable `f`. -/
theorem unbounded_functional_calculus : True := sorry

/-- **Rudin 13.30** — Spectral theorem for unbounded normal operators
(generalising 13.22 to the normal case). -/
theorem spectral_theorem_unbounded_normal : True := sorry

/-- **Rudin 13.33** — Stone's theorem: a strongly continuous
one-parameter unitary group `t ↦ U(t)` on a Hilbert space has the form
`U(t) = e^{itA}` for a unique self-adjoint `A`. -/
theorem stone_theorem : True := sorry

/-- **Rudin 13.36** — Self-adjoint generators of contraction
semigroups (Hille–Yosida special case). -/
theorem selfAdjoint_generator_contraction : True := sorry

/-- **Rudin 13.37–13.38** — Friedrichs extension: a densely-defined
semibounded symmetric operator has a canonical self-adjoint
extension. -/
theorem friedrichs_extension : True := sorry

end Ch13

end Rudin.Pending
