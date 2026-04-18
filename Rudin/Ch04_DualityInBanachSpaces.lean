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

end Polar

end Rudin.Ch04
