import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# Chapter 11 — Commutative Banach Algebras

Rudin, *Functional Analysis* (2nd ed.), Chapter 11.
-/

namespace Rudin.Ch11

open WeakDual

section CommutativeComplexBanachAlgebra

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Definition 11.5** — The character space of a commutative complex
Banach algebra `A`: the continuous nonzero algebra homomorphisms
`A → ℂ`, equipped with the weak-* topology. -/
abbrev CharacterSpace : Type _ := characterSpace ℂ A

/-- **Theorem 11.9 (characters detect the spectrum)** — For any element
`a` of a commutative complex Banach algebra, `z ∈ spectrum ℂ a` iff
there exists a character `φ` with `φ a = z`. -/
theorem mem_spectrum_iff_exists_character (a : A) (z : ℂ) :
    z ∈ spectrum ℂ a ↔ ∃ φ : characterSpace ℂ A, φ a = z :=
  WeakDual.CharacterSpace.mem_spectrum_iff_exists

/-- **Definition 11.18 (Gelfand transform)** — The Gelfand transform
`A → C(Δ, ℂ)` is the algebra homomorphism sending each `a ∈ A` to
the function `φ ↦ φ a` on the character space `Δ`. -/
noncomputable def gelfand : A →ₐ[ℂ] C(characterSpace ℂ A, ℂ) :=
  gelfandTransform ℂ A

/-- **Theorem 11.9 (character space is compact)** — The character
space of a commutative complex Banach algebra is weak-$*$ compact. -/
example : CompactSpace (characterSpace ℂ A) := inferInstance

end CommutativeComplexBanachAlgebra

section CommutativeCStar

variable (A : Type*) [CommCStarAlgebra A]

/-- **Theorem 11.18 (Gelfand–Naimark, commutative case; isometry)** — For
a commutative unital C*-algebra `A`, the Gelfand transform
`A → C(Δ, ℂ)` is an isometry. -/
theorem gelfand_isometry : Isometry (gelfandTransform ℂ A) :=
  gelfandTransform_isometry A

/-- **Theorem 11.18 (Gelfand–Naimark, commutative case; bijection)** —
For a commutative unital C*-algebra `A`, the Gelfand transform is
bijective, giving an isometric *-isomorphism `A ≃ C(Δ, ℂ)`. -/
theorem gelfand_bijective : Function.Bijective (gelfandTransform ℂ A) :=
  gelfandTransform_bijective A

end CommutativeCStar

end Rudin.Ch11
