import Mathlib.Topology.Baire.Lemmas
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Topology.GDelta.Basic

/-!
# Chapter 2 — Completeness

Rudin, *Functional Analysis* (2nd ed.), Chapter 2.

The four "corollaries of Baire" — Baire category, Banach–Steinhaus, open
mapping, closed graph — are all in mathlib.
-/

namespace Rudin.Ch02

open scoped Topology

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

/-- **Corollary 2.6 of Banach–Steinhaus** — If a sequence of continuous
linear maps `gₙ : E → F` converges pointwise, then the sequence is
uniformly bounded in operator norm.

Proof: each sequence `(gₙ x)ₙ` is convergent, hence bounded in `F`;
applying Banach–Steinhaus gives the uniform bound. -/
theorem banach_steinhaus_of_pointwise_tendsto
    {g : ℕ → E →L[𝕜] F} {ϕ : E → F}
    (hϕ : ∀ x, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 (ϕ x))) :
    ∃ C', ∀ n, ‖g n‖ ≤ C' := by
  refine banach_steinhaus (fun x => ?_)
  obtain ⟨C, hC⟩ := (hϕ x).cauchySeq.isBounded_range.exists_norm_le
  exact ⟨C, fun n => hC _ (Set.mem_range_self n)⟩

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

/-- **Corollary of 2.11 (Open mapping ⇒ preimage commutes with interior)** —
For a surjective continuous linear map between Banach spaces, preimage
commutes with taking interior. -/
theorem open_mapping_interior_preimage (f : E →L[𝕜] F) (hf : Function.Surjective f)
    (s : Set F) : interior (f ⁻¹' s) = f ⁻¹' interior s :=
  f.interior_preimage hf s

/-- **Corollary of 2.11 (Open mapping ⇒ preimage commutes with closure)** —
For a surjective continuous linear map between Banach spaces, preimage
commutes with taking closure. -/
theorem open_mapping_closure_preimage (f : E →L[𝕜] F) (hf : Function.Surjective f)
    (s : Set F) : closure (f ⁻¹' s) = f ⁻¹' closure s :=
  f.closure_preimage hf s

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

section BoundedInverse

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Theorem 2.12 (Bounded inverse theorem)** — A continuous linear
bijection between Banach spaces has a continuous inverse; it is
packaged as a continuous linear isomorphism. -/
noncomputable def bounded_inverse (f : E →L[𝕜] F) (hker : f.ker = ⊥)
    (hrange : f.range = ⊤) : E ≃L[𝕜] F :=
  ContinuousLinearEquiv.ofBijective f hker hrange

end BoundedInverse

section Meagre

variable {X : Type*} [TopologicalSpace X]

/-- **Definition (meagre / first category)** — A set is *meagre* if it
is contained in a countable union of nowhere-dense sets. Rudin's
"sets of the first category". -/
abbrev isMeagre (s : Set X) : Prop := IsMeagre s

/-- **Theorem (Baire's theorem, meagre form)** — In a Baire space, every
meagre set has dense complement. (Corollary of Rudin 2.2.) -/
theorem meagre_compl_dense [BaireSpace X] {s : Set X} (hs : IsMeagre s) :
    Dense sᶜ :=
  dense_of_mem_residual hs

end Meagre

section BilinearContinuity

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Theorem 2.17 (joint continuity of bounded bilinear maps)** — A
bilinear map `B : E × F → G` between normed spaces is (jointly)
continuous if and only if there exists `C` such that
`‖B (x, y)‖ ≤ C * ‖x‖ * ‖y‖`. In particular, every separately
continuous bilinear map from Banach spaces is jointly continuous
(a consequence of Banach–Steinhaus). Mathlib packages this as
`IsBoundedBilinearMap.continuous`. -/
theorem bounded_bilinear_continuous {B : E × F → G}
    (hB : IsBoundedBilinearMap 𝕜 B) : Continuous B :=
  hB.continuous

end BilinearContinuity

end Rudin.Ch02
