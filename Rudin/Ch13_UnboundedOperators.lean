import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Chapter 13 — Unbounded Operators

Rudin, *Functional Analysis* (2nd ed.), Chapter 13.

mathlib models densely-defined operators as `LinearPMap`: a submodule
`domain : Submodule R E` together with a linear map `domain →ₗ[R] F`.
Closedness of an operator is then closedness of its graph in `E × F`.
-/

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

end ClosedOperators

end Rudin.Ch13
