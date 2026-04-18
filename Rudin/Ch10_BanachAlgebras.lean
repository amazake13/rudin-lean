import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

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

omit [CompleteSpace A] in
/-- **Corollary** — In a nontrivial complex Banach algebra, `0` is in
the spectrum of the zero element, and nothing else. Proof: `z ∈ σ(0)`
iff `z • 1 - 0 = z • 1` is not a unit, iff `z = 0`. -/
theorem spectrum_zero [Nontrivial A] : spectrum ℂ (0 : A) = {0} := by
  ext z
  simp

/-- **Theorem 10.13 (spectrum bounded by norm)** — The spectrum of `a`
lies in the closed disk of radius `‖a‖` centered at zero. -/
theorem spectrum_subset_closedBall [NormOneClass A] (a : A) :
    spectrum ℂ a ⊆ Metric.closedBall (0 : ℂ) ‖a‖ :=
  spectrum.subset_closedBall_norm a

/-- **Theorem 10.13 (spectrum is compact)** — The spectrum of any
element of a complex Banach algebra is compact. -/
theorem spectrum_isCompact (a : A) : IsCompact (spectrum ℂ a) :=
  spectrum.isCompact a

/-- **Theorem 10.13 (resolvent set is open)** — The complement of the
spectrum in `ℂ` is open. -/
theorem resolventSet_isOpen (a : A) : IsOpen (resolventSet ℂ a) :=
  spectrum.isOpen_resolventSet a

/-- **Theorem 10.13 (spectral radius $\le$ norm)** — The spectral radius
of any element is bounded by its norm. -/
theorem spectralRadius_le_norm [NormOneClass A] (a : A) :
    spectralRadius ℂ a ≤ ‖a‖₊ :=
  spectrum.spectralRadius_le_nnnorm a

/-- **Corollary of 10.13** — $\rho(1) \le 1$. Follows from the spectral
radius formula and `‖1‖ = 1`. -/
theorem spectralRadius_one_le [NormOneClass A] :
    spectralRadius ℂ (1 : A) ≤ 1 := by
  have h := spectralRadius_le_norm (1 : A)
  simpa using h

end ComplexBanachAlgebra

section UnitsOpen

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- **Theorem 10.11 (units form an open set)** — In a Banach algebra
(more generally, a normed ring admitting summable geometric series),
the set of invertible elements is open. -/
theorem units_isOpen : IsOpen { x : R | IsUnit x } :=
  Units.isOpen

/-- **Theorem 10.12 (inversion is continuous)** — In a Banach algebra,
the inversion map `x ↦ x⁻¹` is continuous at every unit. -/
theorem inverse_continuousAt (x : Rˣ) : ContinuousAt Ring.inverse (x : R) :=
  NormedRing.inverse_continuousAt x

/-- **Theorem 10.7 (Neumann series)** — For `‖a‖ < 1` in a Banach
algebra, `1 - a` is a unit, witnessed explicitly via the geometric
series. -/
noncomputable def oneSubUnit (a : R) (h : ‖a‖ < 1) : Rˣ :=
  Units.oneSub a h

/-- **Theorem 10.7 (Neumann series formula)** — For `‖a‖ < 1`,
$(1 - a)^{-1} = \sum_{n \ge 0} a^n$. -/
theorem neumann_series (a : R) (h : ‖a‖ < 1) :
    ∑' n : ℕ, a ^ n = Ring.inverse (1 - a) :=
  geom_series_eq_inverse a h

/-- **Theorem 10.7 (`1 - a` is a unit for small `a`)** — If `‖a‖ < 1`,
then `1 - a` is invertible. -/
theorem isUnit_one_sub (a : R) (h : ‖a‖ < 1) : IsUnit (1 - a) :=
  ⟨Units.oneSub a h, rfl⟩

/-- **Corollary of 10.7** — If `‖a‖ < 1`, then `1 + a` is invertible.
Proof: rewrite `1 + a = 1 - (-a)` and observe `‖-a‖ = ‖a‖ < 1`. -/
theorem isUnit_one_add (a : R) (h : ‖a‖ < 1) : IsUnit (1 + a) := by
  have h' : ‖-a‖ < 1 := by rwa [norm_neg]
  have := isUnit_one_sub (-a) h'
  rwa [sub_neg_eq_add] at this

end UnitsOpen

end Rudin.Ch10
