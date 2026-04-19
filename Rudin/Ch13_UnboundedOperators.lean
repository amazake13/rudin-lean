import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Chapter 13 — Unbounded Operators

Rudin, *Functional Analysis* (2nd ed.), Chapter 13.

mathlib models densely-defined operators as `LinearPMap`: a submodule
`domain : Submodule R E` together with a linear map `domain →ₗ[R] F`.
Closedness of an operator is then closedness of its graph in `E × F`.
-/

open scoped InnerProductSpace

namespace Rudin.Ch13

section ClosedOperators

variable {R E F : Type*}
variable [CommRing R] [AddCommGroup E] [AddCommGroup F]
variable [Module R E] [Module R F]
variable [TopologicalSpace E] [TopologicalSpace F]

/-- **Definition 13.1 (closed operator)** — A densely-defined linear
operator `T` is *closed* iff its graph
`{ (x, T x) : x ∈ dom T }` is a closed subset of `E × F`. -/
abbrev IsClosedOperator (T : E →ₗ.[R] F) : Prop := T.IsClosed

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/-- **Definition 13.4 (closable operator)** — An operator `T` is
*closable* iff the closure of its graph in `E × F` is itself the graph
of a linear operator, called the *closure* of `T`. -/
abbrev IsClosableOperator (T : E →ₗ.[R] F) : Prop := T.IsClosable

/-- **Theorem 13.5** — Every closed operator is trivially closable. -/
theorem isClosable_of_isClosed {T : E →ₗ.[R] F} (hT : IsClosedOperator T) :
    IsClosableOperator T :=
  hT.isClosable

/-- **Definition 13.6 (closure of an operator)** — If `T` is closable,
`closure T` is the (unique) extension whose graph is the closure of
`T`'s graph; otherwise we set `closure T = T`. -/
noncomputable abbrev closure (T : E →ₗ.[R] F) : E →ₗ.[R] F := T.closure

/-- **Theorem 13.7 (the closure is closed)** — If `T` is closable,
then its closure `T̄` is a closed operator. -/
theorem closure_isClosed {T : E →ₗ.[R] F} (hT : IsClosableOperator T) :
    IsClosedOperator (closure T) :=
  hT.closure_isClosed

/-- **Theorem 13.7 (extension property of the closure)** — Every
closable operator extends to its closure: `T ≤ T̄`. -/
theorem le_closure (T : E →ₗ.[R] F) : T ≤ closure T :=
  LinearPMap.le_closure T

/-- **Theorem 13.7 (monotonicity of closure)** — If `T ≤ S` and `S` is
closable, then `T̄ ≤ S̄`. -/
theorem closure_mono {T S : E →ₗ.[R] F} (hS : IsClosableOperator S)
    (h : T ≤ S) : closure T ≤ closure S :=
  hS.closure_mono h

end ClosedOperators

section PMapAdjoint

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Definition 13.9 (adjoint of an unbounded operator)** — For a
densely-defined operator $T : E \to F$, its adjoint $T^{*}$ is defined
on the subspace of $y \in F$ for which $x \mapsto \langle T x, y\rangle$
is bounded on the domain of $T$. -/
noncomputable def pmapAdjoint (T : E →ₗ.[𝕜] F) : F →ₗ.[𝕜] E :=
  T.adjoint

omit [CompleteSpace F] in
/-- **Theorem 13.10** — The adjoint of any densely-defined operator is
closed. -/
theorem pmapAdjoint_isClosed {T : E →ₗ.[𝕜] F} (hT : Dense (T.domain : Set E)) :
    (pmapAdjoint T).IsClosed :=
  T.adjoint_isClosed hT

omit [CompleteSpace F] in
/-- **Theorem 13.11 (adjoint satisfies the formal-adjoint relation)** —
For a densely-defined operator, `⟪T x, y⟫ = ⟪x, T† y⟫` whenever
`x ∈ dom T` and `y ∈ dom T†`. -/
theorem pmapAdjoint_isFormalAdjoint {T : E →ₗ.[𝕜] F}
    (hT : Dense (T.domain : Set E)) :
    (pmapAdjoint T).IsFormalAdjoint T :=
  LinearPMap.adjoint_isFormalAdjoint hT

omit [CompleteSpace F] in
/-- **Theorem 13.9 (domain characterisation)** — `y` is in the domain of
the adjoint `T†` iff the linear form `x ↦ ⟪y, T x⟫` on `dom T` is
continuous. -/
theorem pmapAdjoint_domain_iff {T : E →ₗ.[𝕜] F} (y : F) :
    y ∈ (pmapAdjoint T).domain ↔
      Continuous ((innerₛₗ 𝕜 y).comp T.toFun) :=
  LinearPMap.mem_adjoint_domain_iff T y

omit [CompleteSpace F] in
/-- **Theorem 13.9 (domain via existence of a dual vector)** — If some
`w` satisfies `⟪w, x⟫ = ⟪y, T x⟫` for all `x ∈ dom T`, then `y` lies in
`dom T†`. -/
theorem pmapAdjoint_domain_of_exists {T : E →ₗ.[𝕜] F} (y : F)
    (h : ∃ w : E, ∀ x : T.domain, ⟪w, (x : E)⟫_𝕜 = ⟪y, T x⟫_𝕜) :
    y ∈ (pmapAdjoint T).domain :=
  T.mem_adjoint_domain_of_exists y h

end PMapAdjoint

end Rudin.Ch13
