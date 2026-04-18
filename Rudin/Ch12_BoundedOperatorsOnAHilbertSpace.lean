import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

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

/-- **Corollary of 12.9** — The adjoint sends the zero operator to the
zero operator. Proven directly from the defining inner-product relation. -/
theorem adjoint_zero : adjoint (0 : E →L[𝕜] F) = 0 := by
  apply ContinuousLinearMap.ext
  intro y
  refine ext_inner_right 𝕜 fun x => ?_
  rw [adjoint_inner_left]
  simp

/-- **Corollary of 12.9** — The adjoint is additive: `(A + B)† = A† + B†`.
The inner-product characterisation reduces this to additivity of inner
products. -/
theorem adjoint_add (A B : E →L[𝕜] F) :
    adjoint (A + B) = adjoint A + adjoint B := by
  apply ContinuousLinearMap.ext
  intro y
  refine ext_inner_right 𝕜 fun x => ?_
  rw [adjoint_inner_left, ContinuousLinearMap.add_apply, inner_add_right,
      ← adjoint_inner_left A, ← adjoint_inner_left B,
      ← inner_add_left, ← ContinuousLinearMap.add_apply]

/-- **Corollary of 12.9** — `(-A)† = -A†`. -/
theorem adjoint_neg (A : E →L[𝕜] F) : adjoint (-A) = -adjoint A := by
  apply ContinuousLinearMap.ext
  intro y
  refine ext_inner_right 𝕜 fun x => ?_
  rw [adjoint_inner_left, ContinuousLinearMap.neg_apply, inner_neg_right,
      ← adjoint_inner_left A, ← inner_neg_left,
      ← ContinuousLinearMap.neg_apply]

/-- **Corollary of 12.9** — `(A - B)† = A† - B†`. -/
theorem adjoint_sub (A B : E →L[𝕜] F) :
    adjoint (A - B) = adjoint A - adjoint B := by
  rw [sub_eq_add_neg, adjoint_add, adjoint_neg, sub_eq_add_neg]

/-- **Corollary of 12.9** — Adjoining preserves operator norm:
`‖A†‖ = ‖A‖`. This follows because mathlib's `ContinuousLinearMap.adjoint`
is packaged as a (conjugate-linear) isometry. -/
theorem adjoint_norm (A : E →L[𝕜] F) :
    ‖adjoint A‖ = ‖A‖ :=
  ContinuousLinearMap.adjoint.norm_map A

variable (𝕜 E) in
/-- **Corollary of 12.9** — The identity operator is self-adjoint:
`1† = 1`. Proof: pair against every `x, y` — both sides give `⟪y, x⟫`. -/
theorem adjoint_one : (ContinuousLinearMap.adjoint (1 : E →L[𝕜] E)) = 1 := by
  apply ContinuousLinearMap.ext
  intro y
  refine ext_inner_right 𝕜 fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply]

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

/-- **Corollary of 12.10 + 12.9** — For any bounded operator `A`,
`A† A` is self-adjoint. Proof: $(A^{*} A)^{*} = A^{*} (A^{*})^{*} = A^{*} A$. -/
theorem isSelfAdjoint_adjoint_comp_self (A : E →L[𝕜] F) :
    IsSelfAdjoint (ContinuousLinearMap.adjoint A ∘L A) :=
  ContinuousLinearMap.isSelfAdjoint_iff'.mpr <| by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

end AdjointAlgebra

section SelfAdjoint

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Theorem 12.12 (self-adjoint ⇔ equals its adjoint)** — A bounded
operator `A` on a Hilbert space is self-adjoint iff `A† = A`. -/
theorem isSelfAdjoint_iff_adjoint_eq (A : E →L[𝕜] E) :
    IsSelfAdjoint A ↔ ContinuousLinearMap.adjoint A = A :=
  ContinuousLinearMap.isSelfAdjoint_iff' (A := A)

variable {T : E →ₗ[𝕜] E}

omit [CompleteSpace E] in
/-- **Theorem 12.23 (eigenvalues of a self-adjoint operator are real)** —
Every eigenvalue `μ` of a self-adjoint operator on an inner product
space satisfies `conj μ = μ`; in particular, for `𝕜 = ℂ` the spectrum
lies on the real line. -/
theorem self_adjoint_eigenvalue_real (hT : T.IsSymmetric) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue T μ) : star μ = μ :=
  hT.conj_eigenvalue_eq_self hμ

end SelfAdjoint

section Normal

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Theorem 12.26 (characterisation of normal operators)** —
An operator is normal iff `‖T v‖ = ‖T† v‖` for all `v`. -/
theorem isStarNormal_iff_norm_eq_adjoint (T : E →L[𝕜] E) :
    IsStarNormal T ↔ ∀ v : E, ‖T v‖ = ‖ContinuousLinearMap.adjoint T v‖ :=
  ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint

/-- **Theorem 12.26 (normal operators: kernel ⟂ range)** —
For a normal operator `T`, the orthogonal complement of the range
equals the kernel. -/
theorem normal_orthogonal_range {T : E →L[𝕜] E} (hT : IsStarNormal T) :
    T.rangeᗮ = T.ker :=
  ContinuousLinearMap.IsStarNormal.orthogonal_range hT

/-- **Corollary of 12.12 + 12.26** — Every self-adjoint operator is
normal. Proof: `star T = T` makes `star T * T = T * T = T * star T`. -/
theorem selfAdjoint_isStarNormal {T : E →L[𝕜] E} (hT : IsSelfAdjoint T) :
    IsStarNormal T :=
  ⟨by rw [hT]⟩

/-- **Corollary of 12.26** — For a normal operator, `ker T = ker T†`. -/
theorem normal_ker_adjoint {T : E →L[𝕜] E} (hT : IsStarNormal T) :
    (ContinuousLinearMap.adjoint T).ker = T.ker :=
  ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker hT

/-- **Corollary of 12.26** — For a normal `T`, `T v = 0 ↔ T† v = 0`. -/
theorem normal_apply_eq_zero_iff {T : E →L[𝕜] E} (hT : IsStarNormal T) (v : E) :
    ContinuousLinearMap.adjoint T v = 0 ↔ T v = 0 :=
  ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff hT v

end Normal

section OrthogonalProjection

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- **Definition (orthogonal projection onto a closed subspace)** —
Projection onto `U` along `Uᗮ`, as a bounded operator `E →L[𝕜] E`. -/
noncomputable def orthogonalProjection (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →L[𝕜] E :=
  U.starProjection

/-- **Theorem 12.14 (orthogonal projection is self-adjoint)** —
For any closed subspace `U` admitting an orthogonal projection,
the projection operator is self-adjoint. -/
theorem orthogonalProjection_isSelfAdjoint
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsSelfAdjoint (orthogonalProjection U) :=
  isSelfAdjoint_starProjection U

/-- **Corollary of 12.14** — An orthogonal projection is normal. -/
theorem orthogonalProjection_isStarNormal
    (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    IsStarNormal (orthogonalProjection U) :=
  selfAdjoint_isStarNormal (orthogonalProjection_isSelfAdjoint U)

end OrthogonalProjection

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
