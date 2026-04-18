import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.DoubleDual

/-!
# Chapter 4 — Duality in Banach Spaces

Rudin, *Functional Analysis* (2nd ed.), Chapter 4.
-/

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

end Rudin.Ch04
