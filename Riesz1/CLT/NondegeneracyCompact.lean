/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.NondegeneracyZero
public import Riesz1.Variance.RegUniformCompactVariance
import all Riesz1.Variance.LoopMaster

/-!
# Compact-profile variance bounds

The upper bound in the compact alternative of the nondegeneracy step in the proof of Theorem 3.
The regularized variance is `cltVariance` applied to `cltScaledLift`, with the periodized profile
as input.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz1
namespace Internal

lemma nondegeneracy_compact_lift_coeff {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (p : Profile) (a : Scale) {h : ℝ} (hh : 0 < h) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle =>
      (cltScaledLift hρ a hh
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ x : ℂ)) k =
      fourierCoeff (fun x => (testAtScale p a x : ℂ)) k *
        (mollifierFT ρ (h * k / (observationLength a).val) : ℂ) := by
  change Ioc (0 : ℝ) 1 at a
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let ξ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)} :=
    ⟨periodizedProfile p L, periodizedProfileL2 p a⟩
  have hdilate := CircleFourier.coeff_eq_of_scaled_lifts
    (f := fun x : Circle L => (cltRegCircle hρ L hh ξ x : ℂ))
    (g := fun x : UnitAddCircle => (cltScaledLift hρ a hh ξ x : ℂ))
    (fun t _ => by
      simp only [cltScaledLift, Function.Periodic.lift_coe]
      simp only [cltScaledFun]
      congr 3
      change t / a.val = a.val⁻¹ * t
      exact div_eq_inv_mul t a.val) k
  change fourierCoeff (fun x : UnitAddCircle => (cltScaledLift hρ a hh ξ x : ℂ)) k = _
  erw [hdilate, testAtScale_coeff_eq_periodized]
  have hloc := locallyIntegrable_circle_lift (complexL2Integrable L _ ξ.property).re
  exact fourierCoeff_circleMollify hρ hh hloc
    (fun t => by simp only [AddCircle.coe_add_period]) ξ.val
    (cltRegCircle hρ L hh ξ) (fun _ => rfl) (cltRegCircle_coe hρ L hh ξ) k

lemma nondegeneracy_compact_variance_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (P : Parameters) (p : Profile) (a : Scale) {h : ℝ} (hh : 0 < h) :
    cltVariance P a
      ⟨(fun x => (cltScaledLift hρ a hh
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ x : ℂ)),
        cltScaledLift_memLp hρ a hh _⟩ ≤ circleVariance P p a := by
  unfold cltVariance circleVariance
  refine mul_le_mul le_rfl ?_ zero_le zero_le
  unfold circleSobolevSq
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false, nondegeneracy_compact_lift_coeff, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    apply ENNReal.ofReal_le_ofReal
    have hm := mollifierFT_sq_le_one hρ.isCircleMollifier
      (h * k / (observationLength a).val)
    have hw : 0 ≤ |(k : ℝ)| ^ (2 * ((1 - P.val.2) / 2)) *
      ‖fourierCoeff (fun x => (testAtScale p a x : ℂ)) k‖ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hm hw]

lemma nondegeneracy_compact_upper_of_admissible (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (ell : Scales) (α : ℝ) (d : TestData)
    (h : Admissible P p ell α d) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Scale) (r : ℝ) (hr : 0 < r),
      let V := cltVariance P a
        ⟨(fun x => (cltScaledLift hρ a hr
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ x : ℂ)),
          cltScaledLift_memLp hρ a hr _⟩
      V < ⊤ ∧ Real.sqrt V.toReal ≤ C := by
  let f := (zeroExtensionL2 p).toLp _
  have hf : RepresentsZeroExtension p f := (zeroExtensionL2 p).coeFn_toLp
  obtain ⟨_, _, D, hD, hb⟩ := admissible_compact_variance P p hp ell α d h f hf
  let C := Real.sqrt ((lineVariance P f).toReal + D) + 1
  refine ⟨C, by dsimp [C]; positivity, fun a r hr => ?_⟩
  have hcircle := hb a
  have hbound : (circleVariance P p a).toReal ≤ (lineVariance P f).toReal + D := by
    have hpw : a.val ^ (2 - P.val.2) ≤ 1 :=
      Real.rpow_le_one a.property.1.le a.property.2 (by linarith [P.property.2.2])
    have hab := (le_abs_self _).trans hcircle.2.2
    nlinarith [mul_le_mul_of_nonneg_left hpw hD.le]
  have hle := Internal.nondegeneracy_compact_variance_le hρ P p a hr
  have hfin := hle.trans_lt hcircle.2.1
  refine ⟨hfin, ?_⟩
  exact (Real.sqrt_le_sqrt
    ((ENNReal.toReal_mono hcircle.2.1.ne hle).trans hbound)).trans (by dsimp [C]; linarith)

/-- The positive line limit gives a lower bound for the unsmoothed
variance on a whole interval of sufficiently small observation scales. -/
lemma nondegeneracy_compact_small_scales_of_admissible (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (ell : Scales) (α : ℝ) (d : TestData)
    (h : Admissible P p ell α d)
    (hz : ¬ zeroExtension p =ᵐ[volume] fun _ => 0) :
    ∃ c a₀ : ℝ, 0 < c ∧ 0 < a₀ ∧ ∀ a : Scale, a.val < a₀ →
      circleVariance P p a < ⊤ ∧ c ≤ Real.sqrt (circleVariance P p a).toReal := by
  let f := (zeroExtensionL2 p).toLp _
  have hf : RepresentsZeroExtension p f := (zeroExtensionL2 p).coeFn_toLp
  obtain ⟨_, hfin, _, _, hb⟩ := admissible_compact_variance P p hp ell α d h f hf
  have hnonzero : lineVariance P f ≠ 0 :=
    fun he => hz ((clt_nondegeneracy_compact_zero P p f hf).mp he)
  have hv : 0 < (lineVariance P f).toReal := ENNReal.toReal_pos hnonzero hfin.ne
  have hlim := admissible_compact_variance_tendsto P p hp ell α d h f hf
    (fun a : Scale => a) (l := comap (fun a : Scale => a.val) (𝓝 (0 : ℝ))) tendsto_comap
  have hevent := hlim.eventually (lt_mem_nhds (show
    (lineVariance P f).toReal / 2 < (lineVariance P f).toReal by linarith))
  obtain ⟨U, hU, hsub⟩ := mem_comap.mp hevent
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Real.sqrt ((lineVariance P f).toReal / 2), ε,
    Real.sqrt_pos.mpr (half_pos hv), hε, fun a ha => ⟨(hb a).2.1, ?_⟩⟩
  apply Real.sqrt_le_sqrt
  apply le_of_lt
  apply hsub
  apply hball
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos a.property.1] using ha

end Internal

/-- For a compact admissible profile, every regularized variance is finite
and uniformly bounded above. The constant is chosen before the admissible
scale sequence, the observation scale, and the smoothing radius. -/
theorem clt_nondegeneracy_compact_upper (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      ∀ (a : Scale) (r : ℝ) (hr : 0 < r),
        let V := cltVariance P a
          ⟨(fun x => (cltScaledLift hρ a hr
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ x : ℂ)),
            cltScaledLift_memLp hρ a hr _⟩
        V < ⊤ ∧ Real.sqrt V.toReal ≤ C := by
  classical
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨ell, hell⟩ := hex
    obtain ⟨C, hC, hb⟩ :=
      Internal.nondegeneracy_compact_upper_of_admissible P p hp ell α d hell ρ hρ
    exact ⟨C, hC, fun _ _ => hb⟩
  · exact ⟨1, one_pos, fun ell hell => (hex ⟨ell, hell⟩).elim⟩

/-- The lower-bound step near scale zero in the nondegeneracy argument for Theorem 3.
The constants precede every admissible sequence. This statement concerns
the unsmoothed variance. -/
theorem clt_nondegeneracy_compact_small_scales (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (α : ℝ) (d : TestData)
    (hz : ¬ zeroExtension p =ᵐ[volume] fun _ => 0) :
    ∃ c a₀ : ℝ, 0 < c ∧ 0 < a₀ ∧
      ∀ ell : Scales, Admissible P p ell α d →
        ∀ a : Scale, a.val < a₀ → circleVariance P p a < ⊤ ∧
          c ≤ Real.sqrt (circleVariance P p a).toReal := by
  classical
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d
  · obtain ⟨ell, hell⟩ := hex
    obtain ⟨c, a₀, hc, ha₀, hb⟩ :=
      Internal.nondegeneracy_compact_small_scales_of_admissible P p hp ell α d hell hz
    exact ⟨c, a₀, hc, ha₀, fun _ _ => hb⟩
  · exact ⟨1, 1, one_pos, one_pos, fun ell hell => (hex ⟨ell, hell⟩).elim⟩

end Riesz1
