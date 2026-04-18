import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace

/-!
# Chapter 7 — Fourier Transforms

Rudin, *Functional Analysis* (2nd ed.), Chapter 7.
-/

namespace Rudin.Ch07

open SchwartzMap
open scoped SchwartzMap FourierTransform

section SchwartzFourier

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Theorem 7.4 (Fourier transform on the Schwartz space)** — The
Fourier transform is a continuous linear self-map of the Schwartz space
`𝓢(V, E)`. -/
noncomputable def fourierSchwartz : 𝓢(V, E) →L[𝕜] 𝓢(V, E) :=
  SchwartzMap.fourierTransformCLM 𝕜

end SchwartzFourier

section L2Fourier

variable {E F : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Theorem 7.9 (Plancherel, as an isometry on L²)** — The Fourier
transform extends to a linear isometric automorphism of
`L²(E; F)`. -/
noncomputable def fourierL2 :
    MeasureTheory.Lp (α := E) F 2 ≃ₗᵢ[ℂ] MeasureTheory.Lp (α := E) F 2 :=
  MeasureTheory.Lp.fourierTransformₗᵢ E F

open MeasureTheory in
/-- **Theorem 7.9 (Plancherel's identity)** — The Fourier transform
preserves the L² norm. -/
theorem plancherel (f : Lp (α := E) F 2) : ‖(𝓕 f : Lp (α := E) F 2)‖ = ‖f‖ :=
  Lp.norm_fourier_eq f

end L2Fourier

section FourierInversion

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Theorem 7.7 (Fourier inversion on Schwartz space)** — For
`f : 𝓢(V, E)`, the inverse Fourier transform undoes the Fourier
transform: $\mathcal{F}^{-1} \mathcal{F} f = f$. -/
theorem fourier_inversion (f : 𝓢(V, E)) : 𝓕⁻ (𝓕 f) = f :=
  FourierPair.fourierInv_fourier_eq f

end FourierInversion

end Rudin.Ch07
