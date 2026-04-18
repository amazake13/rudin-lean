import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Chapter 12 — Bounded Operators on a Hilbert Space

Rudin, *Functional Analysis* (2nd ed.), Chapter 12.
-/

namespace Rudin.Ch12

open scoped InnerProductSpace
open Module End

section Adjoint

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Theorem 12.9** — Every bounded operator `A : E →L[𝕜] F` between
Hilbert spaces has a unique adjoint `A† : F →L[𝕜] E` characterised by
`⟪A x, y⟫ = ⟪x, A† y⟫`. -/
noncomputable def adjoint (A : E →L[𝕜] F) : F →L[𝕜] E :=
  ContinuousLinearMap.adjoint A

/-- **Theorem 12.9 (defining relation)** — `⟪A† y, x⟫ = ⟪y, A x⟫`. -/
theorem adjoint_inner_left (A : E →L[𝕜] F) (x : E) (y : F) :
    ⟪adjoint A y, x⟫_𝕜 = ⟪y, A x⟫_𝕜 :=
  ContinuousLinearMap.adjoint_inner_left A x y

/-- **Theorem 12.9 (involution)** — `A†† = A`. -/
theorem adjoint_adjoint (A : E →L[𝕜] F) :
    adjoint (adjoint A) = A :=
  ContinuousLinearMap.adjoint_adjoint A

end Adjoint

section AdjointAlgebra

variable {𝕜 E F G : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- **Theorem 12.10 (adjoint of composition)** —
`(A ∘ B)† = B† ∘ A†`. -/
theorem adjoint_comp (A : F →L[𝕜] G) (B : E →L[𝕜] F) :
    ContinuousLinearMap.adjoint (A ∘L B)
      = ContinuousLinearMap.adjoint B ∘L ContinuousLinearMap.adjoint A :=
  ContinuousLinearMap.adjoint_comp A B

/-- **Theorem 12.11 (C$^{*}$-identity)** — `‖A† ∘ A‖ = ‖A‖²`. -/
theorem norm_adjoint_comp_self (A : E →L[𝕜] F) :
    ‖ContinuousLinearMap.adjoint A ∘L A‖ = ‖A‖ * ‖A‖ :=
  ContinuousLinearMap.norm_adjoint_comp_self A

end AdjointAlgebra

section SpectralTheorem

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {T : E →ₗ[𝕜] E}

/-- **Theorem 12.22 (Spectral theorem, finite-dimensional case)** —
A self-adjoint operator `T` on a finite-dimensional inner product space
is diagonalised by an isometry to the orthogonal direct sum of its
eigenspaces. -/
noncomputable def spectralDiagonalization (hT : T.IsSymmetric) :
    E ≃ₗᵢ[𝕜] PiLp 2 fun μ : Eigenvalues T => eigenspace T μ :=
  hT.diagonalization

/-- **Theorem 12.22 (diagonal action)** — Under the diagonalisation of
Theorem 12.22, `T` acts on the `μ`-th eigenspace by multiplication by
`μ`. -/
theorem spectralDiagonalization_apply_self_apply (hT : T.IsSymmetric)
    (v : E) (μ : Eigenvalues T) :
    spectralDiagonalization hT (T v) μ =
      (μ : 𝕜) • spectralDiagonalization hT v μ :=
  hT.diagonalization_apply_self_apply v μ

end SpectralTheorem

end Rudin.Ch12
