import Mathlib.Topology.Baire.Lemmas
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.RieszLemma

/-!
# Chapter 2 — Completeness

Rudin, *Functional Analysis* (2nd ed.), Chapter 2.

The four "corollaries of Baire" — Baire category, Banach–Steinhaus, open
mapping, closed graph — are all in mathlib.
-/

namespace Rudin.Ch02

/-- **Theorem 2.2 (Baire category theorem)** — In a Baire space (e.g. a
complete metric space, or a locally compact Hausdorff space) the
intersection of a countable family of dense open sets is dense. -/
theorem baire_category {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {ι : Sort*} [Countable ι] {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) (hd : ∀ i, Dense (U i)) :
    Dense (⋂ i, U i) :=
  dense_iInter_of_isOpen hU hd

section BanachSteinhaus

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Theorem 2.5 (Banach–Steinhaus, uniform boundedness)** — A pointwise
bounded family of continuous linear maps from a Banach space is uniformly
bounded in operator norm. -/
theorem banach_steinhaus {ι : Type*} {g : ι → E →L[𝕜] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' :=
  _root_.banach_steinhaus (g := g) h

end BanachSteinhaus

section OpenMappingAndClosedGraph

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Theorem 2.11 (Open mapping theorem)** — A surjective continuous
linear map between Banach spaces is open. -/
theorem open_mapping (f : E →L[𝕜] F) (hf : Function.Surjective f) :
    IsOpenMap f :=
  f.isOpenMap hf

/-- **Theorem 2.15 (Closed graph theorem)** — A linear map between Banach
spaces with closed graph is continuous. -/
theorem closed_graph (g : E →ₗ[𝕜] F) (hg : IsClosed (g.graph : Set (E × F))) :
    Continuous g :=
  g.continuous_of_isClosed_graph hg

end OpenMappingAndClosedGraph

section RieszLemma

variable {𝕜 E : Type*} [NormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **Theorem 2.X (Riesz's lemma)** — For any closed proper subspace
`F` of a normed space `E` and any `r < 1`, there exists `x₀ ∉ F` with
`r · ‖x₀‖ ≤ ‖x₀ - y‖` for all `y ∈ F`. -/
theorem riesz_lemma {F : Subspace 𝕜 E}
    (hFc : IsClosed (F : Set E)) (hFne : ∃ x : E, x ∉ F) {r : ℝ} (hr : r < 1) :
    ∃ x₀ : E, x₀ ∉ F ∧ ∀ y ∈ F, r * ‖x₀‖ ≤ ‖x₀ - y‖ :=
  _root_.riesz_lemma hFc hFne hr

end RieszLemma

end Rudin.Ch02
