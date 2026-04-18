import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Chapter 10 — Banach Algebras

Rudin, *Functional Analysis* (2nd ed.), Chapter 10.

A complex Banach algebra in mathlib is an `A` with
`[NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]`.
Below, Rudin's headline theorems are recovered from mathlib.
-/

namespace Rudin.Ch10

open Filter Topology

section ComplexBanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Theorem 10.13 (nonempty spectrum)** — In a nontrivial complex Banach
algebra every element has nonempty spectrum. -/
theorem spectrum_nonempty [Nontrivial A] (a : A) : (spectrum ℂ a).Nonempty :=
  spectrum.nonempty a

/-- **Theorem 10.14 (Gelfand–Mazur)** — If every nonzero element of a complex
Banach algebra `A` is invertible, then `A` is ℂ-algebra-isomorphic to `ℂ`.

The hypothesis is phrased as `IsUnit a ↔ a ≠ 0` to allow application to
quotients of Banach algebras by maximal ideals (cf. Rudin 11.7). When `A`
is a `NormedDivisionRing` this reduces to `isUnit_iff_ne_zero`. -/
noncomputable def gelfandMazur (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) :
    ℂ ≃ₐ[ℂ] A :=
  NormedRing.algEquivComplexOfComplete hA

/-- **Theorem 10.13 (Gelfand spectral radius formula)** — For any element of
a complex Banach algebra, `‖aⁿ‖^(1/n)` converges to the spectral radius. -/
theorem gelfand_formula (a : A) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (‖a ^ n‖ ^ (1 / n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ a)) :=
  spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a

end ComplexBanachAlgebra

end Rudin.Ch10
