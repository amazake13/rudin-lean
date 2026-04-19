import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.FredholmAlternative

/-!
# Chapter 4 — Duality in Banach Spaces

Rudin, *Functional Analysis* (2nd ed.), Chapter 4.
-/

open scoped Topology

namespace Rudin.Ch04

section BanachAlaoglu

variable {𝕜 E : Type*}
  [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Theorem 4.3 (Banach–Alaoglu)** — Closed balls of the continuous
dual of a normed space are weak-* compact. -/
theorem banach_alaoglu (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsCompact (WeakDual.toStrongDual (𝕜 := 𝕜) (E := E) ⁻¹' Metric.closedBall x' r) :=
  WeakDual.isCompact_closedBall x' r

/-- **Theorem 4.3′ (Banach–Alaoglu, polar form)** — The polar of a
neighborhood of zero is weak-* compact. -/
theorem banach_alaoglu_polar {s : Set E} (hs : s ∈ nhds (0 : E)) :
    IsCompact (WeakDual.polar 𝕜 s) :=
  WeakDual.isCompact_polar 𝕜 hs

end BanachAlaoglu

/-- **Definition 4.4** — The canonical isometric embedding of a normed
space into its bidual. Rudin calls `E` *reflexive* when this embedding
is surjective. -/
noncomputable def doubleDualEmbedding (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] :
    E →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  NormedSpace.inclusionInDoubleDualLi 𝕜

section DualComplete

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E F : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Theorem 4.1** — The space of bounded operators into a Banach space
is itself a Banach space. In particular, the normed dual of any normed
space is a Banach space. -/
example : CompleteSpace (E →L[𝕜] F) := inferInstance

end DualComplete

section Polar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Definition 4.X (polar set)** — The polar of a set $s \subseteq E$
inside the continuous dual consists of functionals $\varphi$ with
$|\varphi(x)| \le 1$ for all $x \in s$. -/
abbrev polar (s : Set E) : Set (StrongDual 𝕜 E) := StrongDual.polar 𝕜 s

/-- **Theorem 4.X (polars are closed)** — The polar of any set is closed
in the strong dual. -/
theorem polar_isClosed (s : Set E) : IsClosed (StrongDual.polar 𝕜 s) :=
  NormedSpace.isClosed_polar 𝕜 s

/-- **Theorem 4.X (polar of closure equals polar)** — Taking the closure
of `s` does not change its polar. -/
theorem polar_closure (s : Set E) :
    StrongDual.polar 𝕜 (closure s) = StrongDual.polar 𝕜 s :=
  NormedSpace.polar_closure 𝕜 s

/-- **Corollary of Banach–Alaoglu** — The polar of a neighborhood of
zero in a normed space is norm-bounded in the strong dual. -/
theorem polar_isBounded_of_mem_nhds_zero {s : Set E} (hs : s ∈ 𝓝 (0 : E)) :
    Bornology.IsBounded (StrongDual.polar 𝕜 s) :=
  NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 hs

end Polar

section SeparatingDual

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Corollary of Hahn–Banach (separation of points)** — A vector in a
normed space is zero iff every continuous linear functional vanishes on
it. -/
theorem eq_zero_iff_forall_dual_eq_zero (x : E) :
    x = 0 ↔ ∀ g : StrongDual 𝕜 E, g x = 0 :=
  SeparatingDual.eq_zero_iff_forall_dual_eq_zero x

/-- **Corollary of Hahn–Banach** — Two vectors are equal iff every
continuous linear functional agrees on them. -/
theorem eq_iff_forall_dual_eq {x y : E} :
    x = y ↔ ∀ g : StrongDual 𝕜 E, g x = g y :=
  SeparatingDual.eq_iff_forall_dual_eq

end SeparatingDual

section CompactOperators

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Definition 4.18 (compact operator)** — A map `T : E → F`
between topological spaces is *compact* if there exists a compact set
`K ⊆ F` whose preimage under `T` is a neighborhood of zero. Equivalently
(for linear maps), `T` maps bounded sets to precompact sets. -/
abbrev isCompactOp (T : E → F) : Prop := IsCompactOperator T

/-- **Theorem 4.18 (zero is compact)** — The zero operator is compact. -/
theorem compact_operator_zero : IsCompactOperator (0 : E → F) :=
  isCompactOperator_zero

end CompactOperators

section FredholmAlternative

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

open Module End

/-- **Theorem 4.25 (Fredholm alternative)** — Let `T` be a compact
operator on a Banach space `X` and let `μ ≠ 0`. Then either `μ` is
an eigenvalue of `T`, or `μ` belongs to the resolvent set of `T`
(i.e. `T − μI` is invertible). There is no middle ground. -/
theorem fredholm_alternative {T : X →L[𝕜] X} (hT : IsCompactOperator T)
    {μ : 𝕜} (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ∨ μ ∈ resolventSet 𝕜 T :=
  hT.hasEigenvalue_or_mem_resolventSet hμ

/-- **Corollary of Theorem 4.25** — For a compact operator on a Banach
space, the nonzero spectrum consists precisely of eigenvalues. -/
theorem compact_spectrum_eq_eigenvalues {T : X →L[𝕜] X}
    (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0) :
    HasEigenvalue (T : End 𝕜 X) μ ↔ μ ∈ spectrum 𝕜 T :=
  hT.hasEigenvalue_iff_mem_spectrum hμ

end FredholmAlternative

end Rudin.Ch04
