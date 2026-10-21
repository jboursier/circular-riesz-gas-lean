/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Theorem 3 (CLT for singular linear statistics): the vocabulary of the challenge

The definitions of `Challenge.lean` of the same pair, copied verbatim and without the final
theorem. The solution states and proves the theorem on top of them.
-/

@[expose] public section

namespace Riesz1Audit.CentralLimitTheorem

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Model parameters. -/
@[reducible] def Parameters : Type :=
  {x : ℝ × ℝ // 0 < x.1 ∧ 0 < x.2 ∧ x.2 < 1}

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Ordered lift domain in a fundamental region. -/
def orderedDomain (N : ℕ+) : Set (Fin (N : ℕ) → ℝ) :=
  {x | StrictMono x ∧ 0 ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ < 1 ∧
    ∀ i, x i < x ⟨0, N.pos⟩ + 1}


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Configurations, with unique first lift in [0,1). -/
@[reducible] def Configuration (N : ℕ+) := orderedDomain N


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The range for a Riesz exponent. -/
@[reducible] def RieszExponent := {s : ℝ // 0 < s ∧ s < 1}


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The model exponent with its range proofs. -/
def parametersExponent (P : Parameters) : RieszExponent := ⟨P.val.2, P.property.2.1, P.property.2.2⟩


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Canonical analytic representative, twice Mathlib's even Hurwitz function.
The kernel of the paper is its restriction to x ≠ 0.
The Mathlib value at 0 is an analytic continuation with the collision term omitted. -/
def rieszRepresentative (s : RieszExponent) (x : UnitAddCircle) : ℝ :=
  2 * (HurwitzZeta.hurwitzZetaEven x (s.val : ℂ)).re


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Energy, ordered pairs counted twice. -/
def energy (s : RieszExponent) {N : ℕ+} (X : Configuration N) : ℝ :=
  (N : ℝ) ^ (-s.val) *
    ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.erase i,
      rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Lebesgue measure pulled back to the lift domain. -/
def configurationVolume (N : ℕ+) : Measure (Configuration N) :=
  (volume : Measure (Fin (N : ℕ) → ℝ)).comap Subtype.val


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Unnormalized Gibbs measure. -/
def gibbsWeight (P : Parameters) (N : ℕ+) : Measure (Configuration N) :=
  (configurationVolume N).withDensity (fun X => ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X)))


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Extended nonnegative partition function. -/
def partitionFunction (P : Parameters) (N : ℕ+) : ℝ≥0∞ := gibbsWeight P N Set.univ


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Gibbs law. Finiteness and positivity are separate analytic obligations,
never taken as hypotheses. -/
def gibbsMeasure (P : Parameters) (N : ℕ+) : Measure (Configuration N) :=
  (partitionFunction P N)⁻¹ • gibbsWeight P N


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Fixed real L² profile with an explicit representative, as in Assumption 1.1. -/
@[reducible] def Profile : Type :=
  {f : UnitAddCircle → ℝ // MemLp (fun x => (f x : ℂ)) 2 volume}

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Zero extension on the central interval. -/
def zeroExtension (p : Profile) (x : ℝ) : ℝ :=
  if |x| < 1 / 2 then p.val (x : UnitAddCircle) else 0


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Compact essential support with a fixed margin. This is (A4) of Assumption 1.1. -/
def CompactProfile (p : Profile) : Prop :=
  ∃ rho : ℝ, 0 < rho ∧ rho < 1 / 2 ∧
    ∀ᵐ x : ℝ, rho ≤ |x| → zeroExtension p x = 0


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Circle homogeneous Sobolev seminorm squared, permitting infinity. -/
def circleSobolevSq (r : ℝ) (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) : ℝ≥0∞ :=
  ∑' k : ℤ, if k = 0 then 0 else ENNReal.ofReal (|(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f.val k‖ ^ 2)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- H^r membership requires L² and finite seminorm. -/
def CircleSobolev (r : ℝ) (f : UnitAddCircle → ℂ) : Prop :=
  ∃ hf : MemLp f 2 volume, circleSobolevSq r ⟨f, hf⟩ < ⊤


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Line homogeneous Sobolev seminorm using the L² Fourier isometry. -/
def lineSobolevSq (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ≥0∞ :=
  ∫⁻ eta : ℝ, ENNReal.ofReal (|eta| ^ (2 * r) * ‖Lp.fourierTransformₗᵢ ℝ ℂ f eta‖ ^ 2)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Line H^r membership. -/
def LineSobolev (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  lineSobolevSq r f < ⊤


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Positive scales at most one. -/
@[reducible] def Scale := {ell : ℝ // 0 < ell ∧ ell ≤ 1}


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Fixed positive scales, as in Assumption 1.1. -/
@[reducible] def Scales : Type := ℕ+ → Scale

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Nℓ_N tends to infinity. -/
def Mesoscopic (ell : Scales) : Prop :=
  Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop atTop


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Quantitative profile data independent of scales and particle number,
as in Assumption 1.1. -/
@[reducible] def TestData : Type :=
  ℝ × ℝ × ℝ × (Σ p : ℕ+, Fin (p : ℕ) → ℝ)

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Positive circle lengths. -/
@[reducible] def Length := {L : ℝ // 0 < L}


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Unit length. -/
def unitLength : Length := ⟨1, zero_lt_one⟩


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Circle of length L. -/
@[reducible] def Circle (L : Length) := AddCircle L.val


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Central real representative. -/
def centralRep (L : Length) (x : Circle L) : ℝ := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact
  (AddCircle.equivIco L.val (-L.val / 2) x).val


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Periodization of a supported profile on a positive-length circle,
using the central fundamental interval. -/
def periodizedProfile (p : Profile) (L : Length) (x : Circle L) : ℝ :=
  ∑' n : ℤ, zeroExtension p (centralRep L x + (n : ℝ) * L.val)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Length of the observation circle. -/
def observationLength (ell : Scale) : Length := ⟨ell.val⁻¹, inv_pos.mpr ell.property.1⟩


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Arclength, with total mass L. -/
def arclength (L : Length) : Measure (Circle L) := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact
  volume


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Normalized Fourier coefficients on integrable functions. -/
def coeff (L : Length)
    (f : {f : Circle L → ℂ // Integrable f (arclength L)}) (k : ℤ) : ℂ := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact fourierCoeff f.val k

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Global Hölder regularity with a quantitative bound. -/
def HolderBound (L : Length) (r B : ℝ) (f : Circle L → ℝ) : Prop := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact
  Continuous f ∧ (∀ x, |f x| ≤ B) ∧
    ∀ x y, |f x - f y| ≤ B * dist x y ^ r


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Complex L² representatives are integrable on a finite circle. -/
theorem complexL2Integrable (L : Length) (f : Circle L → ℂ)
    (hf : MemLp f 2 (arclength L)) : Integrable f (arclength L) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  change Integrable f volume
  exact (show MemLp f 2 volume from hf).integrable (by norm_num)

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- (A1) of Assumption 1.1 in the distributional (Fourier coefficient) sense. -/
def PrimitiveRegularity (L : Length) (eta s B : ℝ) (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) : Prop :=
  ∃ Xi : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
    HolderBound L (1 - s + eta) B Xi.val ∧
    ∀ k : ℤ, k ≠ 0 →
      (2 * Real.pi * Complex.I * (k : ℂ) / L.val) * coeff L ⟨(fun x => (Xi.val x : ℂ)), complexL2Integrable L _ Xi.property⟩ k =
        coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Riesz normalization. -/
def rieszConstant (s : RieszExponent) : ℝ :=
  2 ^ (1 - s.val) * Real.sqrt Real.pi * Real.Gamma ((1 - s.val) / 2) / Real.Gamma (s.val / 2)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Mean-zero transport coefficients, hence the distribution uniquely. -/
def transportCoeffs (P : Parameters) (L : Length) (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    -((|2 * Real.pi * (k : ℝ) / L.val| ^ (1 - P.val.2) : ℝ) : ℂ) /
      ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) * (2 * Real.pi * Complex.I * (k : ℂ) / L.val)) *
        coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- (A2)–(A3) of Assumption 1.1, via an L² representative of the transport,
smooth off distinct marks. Derivatives are taken on real lifts. -/
def TransportRegularity (P : Parameters) (L : Length) (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (alpha C : ℝ) : Prop := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact
  Function.Injective (fun j => (marks j : Circle L)) ∧
  ∃ psi : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
    (∀ k, coeff L ⟨(fun x => (psi.val x : ℂ)), complexL2Integrable L _ psi.property⟩ k = transportCoeffs P L f k) ∧
    let lift := fun x : ℝ => psi.val (x : Circle L)
    ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      ContDiffAt ℝ 2 lift x ∧
      |deriv (deriv lift) x| ≤ C *
        ((if dist (x : Circle L) 0 ≤ 1 then
            ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - alpha) else 0) +
         (if 1 ≤ dist (x : Circle L) 0 then dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0))


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The zero extension retains the fixed profile's L² certificate. -/
theorem zeroExtensionL2 (p : Profile) :
    MemLp (fun x => (zeroExtension p x : ℂ)) 2 (volume : Measure ℝ) := by
  have h := p.property.comp_measurePreserving (AddCircle.measurePreserving_mk 1 (-(1 / 2)))
  have hsub : Set.Ioo (-(1 / 2) : ℝ) (1 / 2) ⊆ Set.Ioc (-(1 / 2)) (-(1 / 2) + 1) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have h' := h.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hind := (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).mpr h'
  convert hind using 1
  funext x
  simp only [Set.indicator_apply, zeroExtension, Function.comp_apply]
  have hiff : |x| < 1 / 2 ↔ x ∈ Set.Ioo (-(1 / 2)) (1 / 2) := abs_lt
  by_cases hx : |x| < 1 / 2
  · rw [ite_eq_left hx, ite_eq_left (hiff.mp hx)]
  · rw [ite_eq_right hx, ite_eq_right (mt hiff.mpr hx), Complex.ofReal_zero]

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- L² functions on the line restrict to the central circle representative. -/
theorem liftL2 (L : Length) (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    MemLp (fun x => g (centralRep L x)) 2 (arclength L) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have h := (hg.restrict (Set.Ioc (-L.val / 2) (-L.val / 2 + L.val))).memLp_liftIoc
  have hne : ∀ᵐ x : Circle L, x ≠ ((-L.val / 2 : ℝ) : Circle L) := by
    rw [ae_iff, show {x : Circle L | ¬x ≠ ((-L.val / 2 : ℝ) : Circle L)} =
      {((-L.val / 2 : ℝ) : Circle L)} from Set.ext fun _ => not_not]
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    simp [L.property.le]
  apply h.ae_eq
  filter_upwards [hne] with x hx
  exact AddCircle.liftIoc_eq_liftIco_of_ne hx

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Periodization on each observation circle is L², derived from Profile. -/
theorem periodizedProfileL2 (p : Profile) (ell : Scale) :
    MemLp (fun x => (periodizedProfile p (observationLength ell) x : ℂ)) 2
      (arclength (observationLength ell)) := by
  have hL : 1 ≤ (observationLength ell).val := by
    exact (one_le_inv₀ ell.property.1).mpr ell.property.2
  have : Fact (0 < (observationLength ell).val) := ⟨(observationLength ell).property⟩
  have heq (x : Circle (observationLength ell)) :
      periodizedProfile p (observationLength ell) x =
        zeroExtension p (centralRep (observationLength ell) x) := by
    unfold periodizedProfile
    rw [tsum_eq_single (0 : ℤ)]
    · simp only [Int.cast_zero, zero_mul, add_zero]
    · intro n hn
      have hu := (AddCircle.equivIco (observationLength ell).val
        (-(observationLength ell).val / 2) x).property
      have hdist : (1 / 2 : ℝ) ≤ |centralRep (observationLength ell) x +
          (n : ℝ) * (observationLength ell).val| := by
        change -(observationLength ell).val / 2 ≤ centralRep (observationLength ell) x ∧
          centralRep (observationLength ell) x <
            -(observationLength ell).val / 2 + (observationLength ell).val at hu
        rcases lt_or_gt_of_ne hn with hn | hn
        · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 from Int.le_sub_one_of_lt hn)
          have hmul := mul_le_mul_of_nonneg_right hn' (observationLength ell).property.le
          exact le_trans (by linarith [hu.2]) (neg_le_abs _)
        · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from hn)
          have hmul := mul_le_mul_of_nonneg_right hn' (observationLength ell).property.le
          exact le_trans (by linarith [hu.1]) (le_abs_self _)
      simp only [zeroExtension, ite_eq_right (not_lt.mpr hdist)]
  have h := liftL2 (observationLength ell) _ (zeroExtensionL2 p)
  simpa only [heq] using h

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Fixed profile at either macroscopic or shrinking scales, with uniform A1–A4 data.
See Assumption 1.1 of the paper. -/
def Admissible (P : Parameters) (p : Profile) (ell : Scales) (alpha : ℝ) (d : TestData) : Prop :=
  P.val.2 - 1 ≤ alpha ∧ alpha < P.val.2 / 2 ∧
  0 < d.1 ∧ d.1 < P.val.2 ∧ 0 < d.2.1 ∧ 0 < d.2.2.1 ∧
    (((∀ N, (ell N).val = 1) ∧
      PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
      TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 alpha d.2.2.1) ∨
     (CompactProfile p ∧
      Tendsto (fun n : ℕ => (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) ∧
      ∀ N, let L := observationLength (ell N)
        PrimitiveRegularity L d.1 P.val.2 d.2.1 ⟨periodizedProfile p L, periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P L ⟨periodizedProfile p L, periodizedProfileL2 p (ell N)⟩ d.2.2.2.1 d.2.2.2.2 alpha d.2.2.1))


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Pullback of the periodized compact profile to the unit circle. -/
def rescaledProfile (p : Profile) (ell : Scale) (x : UnitAddCircle) : ℝ :=
  zeroExtension p (centralRep unitLength x / ell.val)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Actual unit-circle test at a given scale.
The branch at scale one uses the general macroscopic profile. -/
def testAtScale (p : Profile) (ell : Scale) : UnitAddCircle → ℝ :=
  if ell.val = 1 then p.val else rescaledProfile p ell


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Scaling preserves L², derived from the original profile. -/
theorem rescaledProfileL2 (p : Profile) (ell : Scale) :
    MemLp (fun x => (rescaledProfile p ell x : ℂ)) 2 volume := by
  have hmap : MemLp (fun x => (zeroExtension p x : ℂ)) 2
      (Measure.map (fun x : ℝ => ell.val⁻¹ * x) volume) := by
    rw [Real.map_volume_mul_left (inv_ne_zero ell.property.1.ne')]
    exact (zeroExtensionL2 p).smul_measure ENNReal.ofReal_ne_top
  have hscaled := hmap.comp_of_map (measurable_const.mul measurable_id).aemeasurable
  have h := liftL2 unitLength _ hscaled
  change MemLp (fun x : UnitAddCircle =>
    (zeroExtension p (ell.val⁻¹ * centralRep unitLength x) : ℂ)) 2 volume at h
  simpa only [rescaledProfile, div_eq_mul_inv, mul_comm] using h

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Every actual test is L², with the certificate derived from Profile. -/
theorem testAtScaleL2 (p : Profile) (ell : Scale) :
    MemLp (fun x => (testAtScale p ell x : ℂ)) 2 volume := by
  unfold testAtScale
  split_ifs
  · exact p.property
  · exact rescaledProfileL2 p ell

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Circle variance parameter as an extended nonnegative real. -/
def circleVariance (P : Parameters) (p : Profile) (ell : Scale) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P)) * ell.val ^ (-P.val.2)) *
    circleSobolevSq ((1 - P.val.2) / 2) ⟨(fun x => (testAtScale p ell x : ℂ)), testAtScaleL2 p ell⟩


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Line variance parameter. -/
def lineVariance (P : Parameters) (f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P))) *
    lineSobolevSq ((1 - P.val.2) / 2) f


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The exact C¹ bounded-Lipschitz test class. -/
def BLTest (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧ (∀ x, |f x| ≤ 1) ∧ ∀ x, |deriv f x| ≤ 1


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Extended nonnegative bounded-Lipschitz distance. -/
def blDistance (mu nu : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ⨆ f : {f : ℝ → ℝ // BLTest f},
    ENNReal.ofReal |(∫ x, f.val x ∂mu) - ∫ x, f.val x ∂nu|


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Centered Gaussian, including variance zero. -/
def normalLaw (v : ℝ≥0) : Measure ℝ := ProbabilityTheory.gaussianReal 0 v


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Weak convergence of probability laws against bounded continuous functions. -/
def ConvergesInLaw (laws : ℕ → Measure ℝ) (limit : Measure ℝ) : Prop :=
  (∀ n, IsProbabilityMeasure (laws n)) ∧ IsProbabilityMeasure limit ∧
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂laws n) atTop (𝓝 (∫ x, f x ∂limit))


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Particle count n+1, for sequences starting at zero. -/
def particleNumber (n : ℕ) : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Gibbs normalization is a conclusion, including the nonzero finite partition
function. -/
def ModelWellDefined (P : Parameters) : Prop :=
  ∀ N : ℕ+, 0 < partitionFunction P N ∧ partitionFunction P N < ⊤ ∧
    IsProbabilityMeasure (gibbsMeasure P N)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Linear statistic of a real representative. -/
def linearStatistic {N : ℕ+} (f : UnitAddCircle → ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), f (X.val i : UnitAddCircle)


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Lebesgue-centered statistic. -/
def fluctuation {N : ℕ+} (f : {f : UnitAddCircle → ℝ // Integrable f volume}) (X : Configuration N) : ℝ :=
  linearStatistic f.val X - (N : ℝ) * ∫ x, f.val x


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Real L² representatives have a finite first moment on the circle. -/
theorem realL2Integrable (L : Length) (f : Circle L → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 (arclength L)) : Integrable f (arclength L) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hf' : MemLp f 2 (arclength L) := hf.re
  have : IsFiniteMeasure (arclength L) := by unfold arclength; infer_instance
  exact hf'.integrable (by norm_num)

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- First-moment certificate derived from the fixed profile, at every scale. -/
theorem testAtScaleL1 (p : Profile) (ell : Scale) : Integrable (testAtScale p ell) volume :=
  realL2Integrable unitLength _ (testAtScaleL2 p ell)

end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Normalized centered statistic. This is the statistic in Theorem 3 of the paper. -/
def normalizedStatistic (P : Parameters) (p : Profile) (ell : Scales)
    (N : ℕ+) (X : Configuration N) : ℝ :=
  ((N : ℝ) * (ell N).val) ^ (-P.val.2 / 2) * fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩ X


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Laws of the CLT variables (see Theorem 3). -/
def statisticLaws (P : Parameters) (p : Profile) (ell : Scales) (n : ℕ) : Measure ℝ :=
  (gibbsMeasure P (particleNumber n)).map (normalizedStatistic P p ell (particleNumber n))


end Riesz1

end

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Representation of a compact profile's zero extension in L². -/
def RepresentsZeroExtension (p : Profile) (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  (fun x => f x) =ᵐ[volume] (fun x => (zeroExtension p x : ℂ))


end Riesz1

end

end Riesz1Audit.CentralLimitTheorem

end
