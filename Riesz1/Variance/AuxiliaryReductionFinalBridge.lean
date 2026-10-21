/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliarySmoothing
public import Riesz1.Variance.OptimalScalingFiniteness
public import Riesz1.ToMathlib.VarianceThreeTerm

/-!
# Statistic and seminorm bridges for the convolution families

The relation `OptimalScalingTest` pairs the observation-circle function with
its physical unit-circle test. This file proves their almost everywhere
agreement and its consequences for the Gibbs variance and the
seminorm. No admissibility or analytic estimate is assumed in the bridges.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Riesz1.Internal

/-- Each actual family test is the pullback of its observation-circle
function, up to the original profile's null representative discrepancy. -/
theorem auxiliary_optimalScalingTest_ae (p : Profile) (ell : Scales) (N : ℕ+)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f) :
    (fun z => (v.val z : ℂ)) =ᵐ[volume]
      fun z => (loopMasterPullback (loopMasterLength (ell N)) f.val z : ℂ) := by
  rcases hv with ⟨hv, rfl⟩ | ⟨t, ht, _, _, hcases⟩
  · rw [hv]
    exact testAtScale_ae_eq_loopMasterPullback_periodizedProfile p (ell N)
  · rcases hcases with ⟨hv, rfl⟩ | ⟨hv, rfl⟩
    · rw [hv, auxiliary_pullback_reg]
    · filter_upwards [testAtScale_ae_eq_loopMasterPullback_periodizedProfile p (ell N)] with z hz
      rw [hv, loopMasterPullback_subCircleL2, auxiliary_pullback_reg]
      simp only [Complex.ofReal_sub]
      rw [hz]
      rfl

/-- The two variance encodings agree on every actual family test. -/
theorem auxiliary_scaledVariance_of_optimalScalingTest (P : Parameters) (p : Profile)
    (ell : Scales) (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f) :
    scaledVariance P (ell N) f =
      cltVariance P (ell N) ⟨(fun z => (v.val z : ℂ)), v.property⟩ := by
  unfold scaledVariance cltVariance
  congr 1
  exact circleSobolevSq_congr_ae _ _
    (auxiliary_optimalScalingTest_ae p ell N hρ r v f hv).symm

/-- Fluctuations respect almost everywhere equality of their tests. -/
theorem auxiliary_fluctuation_ae_eq (P : Parameters) (N : ℕ+)
    {v w : UnitAddCircle → ℝ} (hv : Integrable v volume) (hw : Integrable w volume)
    (hvw : v =ᵐ[volume] w) :
    fluctuation ⟨v, hv⟩ =ᵐ[gibbsMeasure P N] fluctuation ⟨w, hw⟩ := by
  filter_upwards [linearStatistic_ae_eq P N hvw] with X hX
  change linearStatistic v X - _ = linearStatistic w X - _
  rw [hX, integral_congr_ae hvw]

/-- The mixed statistic and the physical fluctuation agree almost surely. -/
theorem auxiliary_mixedStat_of_optimalScalingTest (P : Parameters) (p : Profile)
    (ell : Scales) (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f) :
    mixedStat P N (ell N) f =ᵐ[gibbsMeasure P N]
      fluctuation ⟨v.val, (optimalScaling_profile_memLp v).integrable one_le_two⟩ := by
  apply auxiliary_fluctuation_ae_eq
  filter_upwards [auxiliary_optimalScalingTest_ae p ell N hρ r v f hv] with z hz
  exact Complex.ofReal_injective hz.symm

/-- The extended variance respects almost everywhere equality,
with no finiteness assumption and arbitrary integrability certificates. -/
theorem auxiliary_variance_congr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F G : Ω → ℝ} (hF : Integrable F μ) (hG : Integrable G μ) (h : F =ᵐ[μ] G) :
    variance μ F hF = variance μ G hG := by
  unfold variance
  rw [integral_congr_ae h]
  exact lintegral_congr_ae (h.mono fun x hx => by dsimp only; rw [hx])

/-- Transfer of the full variance, before any real conversion. -/
theorem auxiliary_variance_of_optimalScalingTest (P : Parameters) (p : Profile)
    (ell : Scales) (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hv : OptimalScalingTest p ell N hρ r v f)
    (hF : Integrable (mixedStat P N (ell N) f) (gibbsMeasure P N)) :
    variance (gibbsMeasure P N) _ hF =
      variance (gibbsMeasure P N)
        (fluctuation ⟨v.val, (optimalScaling_profile_memLp v).integrable one_le_two⟩)
        (optimalScaling_fluctuation_integrable P N v) :=
  auxiliary_variance_congr hF (optimalScaling_fluctuation_integrable P N v)
    (auxiliary_mixedStat_of_optimalScalingTest P p ell N hρ r v f hv)

end Riesz1.Internal

end
