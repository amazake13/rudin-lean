import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

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

omit [CompleteSpace A] in
/-- **Corollary of 10.13** — $\rho(0) = 0$. -/
theorem spectralRadius_zero_eq : spectralRadius ℂ (0 : A) = 0 :=
  spectrum.spectralRadius_zero

omit [CompleteSpace A] in
/-- **Corollary of 10.13** — In a nontrivial Banach algebra, $\rho(1) = 1$. -/
theorem spectralRadius_one_eq [Nontrivial A] :
    spectralRadius ℂ (1 : A) = 1 :=
  spectrum.spectralRadius_one

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

section SpectralRadiusPower

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

/-- **Theorem 10.13 (spectral radius and powers)** — For any element
`a` of a Banach algebra and any positive `n`, `ρ(a)ⁿ ≤ ρ(aⁿ)`.
This follows from the polynomial spectral mapping theorem. -/
theorem spectralRadius_pow_le (a : A) {n : ℕ} (hn : n ≠ 0) :
    (spectralRadius ℂ a) ^ n ≤ spectralRadius ℂ (a ^ n) :=
  spectrum.spectralRadius_pow_le a n hn

/-- **Corollary of 10.13** — Membership of the resolvent set can be
checked against the spectral radius: if `‖k‖ > ρ(a)`, then `k`
is in the resolvent set of `a`. -/
theorem mem_resolventSet_of_spectralRadius_lt [CompleteSpace A] {a : A} {k : ℂ}
    (h : spectralRadius ℂ a < ‖k‖₊) : k ∈ resolventSet ℂ a :=
  spectrum.mem_resolventSet_of_spectralRadius_lt h

/-- **Corollary of 10.13** — Norm bound for spectrum elements (general
form). -/
theorem norm_le_norm_mul_of_mem_spectrum [CompleteSpace A] {a : A} {k : ℂ}
    (hk : k ∈ spectrum ℂ a) : ‖k‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem hk

/-- **Corollary of 10.13** — The spectrum is bounded. -/
theorem spectrum_isBounded [CompleteSpace A] (a : A) :
    Bornology.IsBounded (spectrum ℂ a) :=
  spectrum.isBounded a

/-- **Corollary of 10.13** — The resolvent function tends to 0 at
infinity. -/
theorem resolvent_tendsto_zero [CompleteSpace A] (a : A) :
    Filter.Tendsto (resolvent a) (Bornology.cobounded ℂ) (nhds 0) :=
  spectrum.resolvent_tendsto_cobounded a

/-- **Spectral mapping for the exponential** — If `z ∈ σ(a)`, then
`exp z ∈ σ(exp a)`. -/
theorem exp_mem_spectrum_exp [CompleteSpace A] {a : A} {z : ℂ}
    (hz : z ∈ spectrum ℂ a) : NormedSpace.exp z ∈ spectrum ℂ (NormedSpace.exp a) :=
  spectrum.exp_mem_exp a hz

end SpectralRadiusPower

section SpectralMappingPolynomial

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

open Polynomial

/-- **Spectral mapping, polynomial inclusion** — For any polynomial `p`
and any `a`, `p(σ(a)) ⊆ σ(p(a))`. -/
theorem subset_polynomial_aeval (a : A) (p : ℂ[X]) :
    (eval · p) '' spectrum ℂ a ⊆ spectrum ℂ (aeval a p) :=
  spectrum.subset_polynomial_aeval a p

/-- **Spectral mapping for powers** — `k ∈ σ(a) → kⁿ ∈ σ(aⁿ)`. -/
theorem pow_mem_pow (a : A) (n : ℕ) {k : ℂ} (hk : k ∈ spectrum ℂ a) :
    k ^ n ∈ spectrum ℂ (a ^ n) :=
  spectrum.pow_mem_pow a n hk

/-- **Spectral mapping for polynomials (equality, complex case)** — If
`a` has nonempty spectrum in a complex Banach algebra and `deg p > 0`,
then `σ(p(a)) = p(σ(a))`. -/
theorem map_polynomial_aeval_of_degree_pos [CompleteSpace A] (a : A)
    (p : ℂ[X]) (hdeg : 0 < p.degree) :
    spectrum ℂ (aeval a p) = (fun k : ℂ => eval k p) '' spectrum ℂ a :=
  spectrum.map_polynomial_aeval_of_degree_pos a p hdeg

/-- **Spectral mapping for powers (equality, complex case)** — `σ(aⁿ) = (σ(a))ⁿ`
for `n > 0`. -/
theorem map_pow_of_pos [CompleteSpace A] (a : A) {n : ℕ} (hn : 0 < n) :
    spectrum ℂ (a ^ n) = (· ^ n) '' spectrum ℂ a :=
  spectrum.map_pow_of_pos a hn

end SpectralMappingPolynomial

end Rudin.Ch10
