/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityDecay
public import Riesz1.Variance.RegMicroKernelDifferentiable
public import Riesz1.ToMathlib.CircleFourierContinuousRepresentative
public import Mathlib.Analysis.PSeries

/-!
# Continuous profiles for negative singularity exponents

The Fourier decay, with a loss smaller than `-α`, is absolutely
summable when `α < 0`. Fourier synthesis supplies the unique continuous
representative on every relevant circle. The existence and uniqueness do
not require a uniform Fourier summation constant in the circle length.
This serves the continuous-extension clause in the proof of Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- (A1)–(A3) of Assumption 1.1 give summable profile coefficients for `α < 0`. -/
theorem regMicroKernel_summable_coeff_of_neg (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hαneg : α < 0) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n marks α C) :
    Summable (fun k => coeff L
      ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨K, _hK, hdecay⟩ := coeff_decay_of_primitive_transportRegularity P L η B hη hB
    f n marks α C hα0 hα1 hC hprim hreg (-α / 2) (by linarith)
  let e := α - 1 + (-α / 2)
  have he : e < -1 := by dsimp [e]; linarith
  let w := 2 * Real.pi / L.val
  have hw : 0 < w := div_pos (mul_pos (by norm_num) Real.pi_pos) L.property
  obtain ⟨M, hM⟩ := exists_nat_gt w⁻¹
  have hcofinite : ∀ᶠ k : ℤ in cofinite, (M : ℤ) ≤ |k| := by
    rw [eventually_cofinite]
    refine (Set.finite_Icc (-(M : ℤ)) (M : ℤ)).subset ?_
    intro k hk
    simp only [mem_ofPred_eq, not_le] at hk
    exact ⟨by linarith [neg_abs_le k], by linarith [le_abs_self k]⟩
  have hpower : Summable (fun k : ℤ => |(k : ℝ)| ^ e) := by
    simpa only [neg_neg] using Real.summable_abs_int_rpow (by linarith : 1 < -e)
  apply Summable.of_norm_bounded_eventually (hpower.mul_left (K * L.val⁻¹ * w ^ e))
  filter_upwards [hcofinite] with k hk
  have hkR : (M : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hk
  have hfreq : |2 * Real.pi * (k : ℝ) / L.val| = w * |(k : ℝ)| := by
    rw [show 2 * Real.pi * (k : ℝ) / L.val = w * (k : ℝ) by dsimp [w]; ring,
      abs_mul, abs_of_pos hw]
  have hfreq1 : 1 ≤ |2 * Real.pi * (k : ℝ) / L.val| := by
    rw [hfreq]
    have hm' : 1 < w * (M : ℝ) := by
      simpa only [mul_comm] using (inv_lt_iff_one_lt_mul₀ hw).mp hM
    nlinarith
  have hb := hdecay k hfreq1
  rw [hfreq, Real.mul_rpow hw.le (abs_nonneg _)] at hb
  exact hb.trans_eq (by dsimp [e]; ring)

/-- The unique continuous real profile representative when `α < 0`, obtained
from the hypotheses alone. Uniqueness is among all continuous a.e.
representatives, so no value at a marked point is chosen arbitrarily. -/
theorem regMicroKernel_continuous_profile_of_neg (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hαneg : α < 0) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n marks α C) :
    ∃! g : C(Circle L, ℝ), (g : Circle L → ℝ) =ᵐ[arclength L] f.val := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hs := regMicroKernel_summable_coeff_of_neg P L η B hη hB f n marks α C
    hα0 hα1 hαneg hC hprim hreg
  obtain ⟨g, hg⟩ := CircleFourier.exists_continuous_real_ae_eq_of_summable f.property hs
  refine ⟨g, hg, fun v hv => ?_⟩
  apply ContinuousMap.coe_injective
  exact (Continuous.ae_eq_iff_eq volume v.continuous g.continuous).mp (hv.trans hg.symm)

namespace Internal

/-- Identify a continuous profile with its absolutely convergent inverse
representative wherever that representative is differentiable. -/
theorem inverse_representative_eq_continuous (P : Parameters) (L : Length)
    {ι : Type*} [Finite ι] (marks : ι → ℝ) (q : ℝ → ℝ) (hq : Measurable q)
    (f : Circle L → ℝ) (g : C(Circle L, ℝ)) (m : ℝ)
    (hg : (g : Circle L → ℝ) =ᵐ[arclength L] f)
    (hrep : ∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
      f (x : Circle L) = m + inverseConv P L.val q x)
    (hdiff : ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      DifferentiableAt ℝ (fun t => m + inverseConv P L.val q t) x) :
    ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      (fun t : ℝ => g (t : Circle L)) =ᶠ[𝓝 x] (fun t => m + inverseConv P L.val q t) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let G := fun z : Circle L => m + inverseConvCircle P L q z
  have hme : MeasurableSet {z : Circle L | g z = G z} :=
    measurableSet_eq_fun g.continuous.measurable
      (measurable_const.add (measurable_inverseConvCircle P L hq))
  have hmap := (AddCircle.measurePreserving_mk L.val (-(L.val / 2))).map_eq
  rw [show -(L.val / 2) + L.val = L.val / 2 by ring] at hmap
  have hgcell := (AddCircle.measurePreserving_mk L.val (-(L.val / 2))).quasiMeasurePreserving.ae_eq_comp hg
  rw [show -(L.val / 2) + L.val = L.val / 2 by ring] at hgcell
  have hG : (g : Circle L → ℝ) =ᵐ[arclength L] G := by
    change ∀ᵐ z : Circle L ∂volume, g z = G z
    rw [← hmap]
    apply (ae_map_iff (AddCircle.continuous_mk' L.val).measurable.aemeasurable hme).mpr
    filter_upwards [hgcell, hrep] with t ht hrt
    exact ht.trans (hrt.trans (by dsimp [G]; rw [inverseConvCircle_coe]))
  have hGc : ContinuousOn (fun t : ℝ => G (t : Circle L))
      {x : ℝ | ∀ j, (x : Circle L) ≠ (marks j : Circle L)} := by
    simpa only [G, inverseConvCircle_coe] using
      (show ContinuousOn (fun t => m + inverseConv P L.val q t)
        {x : ℝ | ∀ j, (x : Circle L) ≠ (marks j : Circle L)} from
        fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
  intro x hx
  simpa only [G, inverseConvCircle_coe] using
    eventuallyEq_lift_of_ae_eq g.continuous hG (isOpen_unmarked_lift marks) hGc hx

end Internal

/-- For `α < 0` the inverse representative has a unique continuous extension
across the marks. The extension is locally identical to the specified inverse
convolution off the marks, including its classical derivatives. -/
theorem regMicroKernel_continuous_inverse_of_neg (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hαneg : α < 0) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n marks α C) :
    ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
      Continuous ψ.val ∧
      (∀ k : ℤ, coeff L
        ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k) ∧
      ∃ g : C(Circle L, ℝ),
        ((g : Circle L → ℝ) =ᵐ[arclength L] f.val) ∧
        (∀ v : C(Circle L, ℝ), ((v : Circle L → ℝ) =ᵐ[arclength L] f.val) → v = g) ∧
        let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
        let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
        ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          (fun t : ℝ => g (t : Circle L)) =ᶠ[𝓝 x] (fun t => m + inverseConv P L.val q t) := by
  obtain ⟨ψ, hc, hcoeff, hrep, hd⟩ := regMicroKernel_profile_classical P L η B hη hB
    f n marks α C hα0 hα1 hC hprim hreg
  obtain ⟨g, hg, huniq⟩ := regMicroKernel_continuous_profile_of_neg P L η B hη hB
    f n marks α C hα0 hα1 hαneg hC hprim hreg
  refine ⟨ψ, hc, hcoeff, g, hg, huniq, ?_⟩
  exact Internal.inverse_representative_eq_continuous P L marks
    (deriv (fun t : ℝ => ψ.val (t : Circle L))) (measurable_deriv _) f.val g _ hg hrep
    (fun x hx => (hd x hx).2.1)

end Riesz1
