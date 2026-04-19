import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Chapter 8 — Applications to Differential Equations

Rudin, *Functional Analysis* (2nd ed.), Chapter 8.

The Fourier transform intertwines differentiation and multiplication by
a polynomial, which is the starting point for applying Fourier analysis
to constant-coefficient linear PDEs.
-/

namespace Rudin.Ch08

open SchwartzMap
open scoped FourierTransform

variable (𝕜 : Type*) [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Theorem 8.X (Fourier transforms differentiation into multiplication)**
— On the Schwartz space, the Fourier transform satisfies
$\widehat{\partial f}(\xi) = 2\pi i \, \xi \cdot \widehat{f}(\xi)$,
which reduces constant-coefficient linear PDEs in $\mathcal{S}$ to
algebraic (multiplication) problems. -/
theorem fourier_fderiv_eq (f : 𝓢(V, E)) :
    𝓕 (fderivCLM 𝕜 V E f)
      = (2 * Real.pi * Complex.I) • smulRightCLM ℂ E (innerSL ℝ) (𝓕 f) :=
  fourier_fderivCLM_eq 𝕜 f

/-- **Theorem 8.X (dual: differentiation of the Fourier transform)** —
Conversely, differentiating the Fourier transform corresponds to
multiplication by `-(2πi) · x` before transforming: the Fourier
transform intertwines multiplication and differentiation on both sides. -/
theorem fderiv_fourier_eq (f : 𝓢(V, E)) :
    fderivCLM 𝕜 V E (𝓕 f)
      = 𝓕 (-(2 * Real.pi * Complex.I) • smulRightCLM ℂ E (innerSL ℝ) f) :=
  fderivCLM_fourier_eq 𝕜 f

end Rudin.Ch08
