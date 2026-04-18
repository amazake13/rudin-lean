import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Module.Basic

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

end Rudin.Ch01
