/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFamilyRegularization
public import Riesz1.Variance.QuantitativeVarianceInput

/-!
# Common support and square mass for the actual convolution families

These bounds apply to `OptimalScalingTest` itself, with one coefficient
before the extra radius. No replacement family or
regularization encoding is introduced.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- The original test and both convolution families have common bounded
support and square mass, on every observation circle. No admissibility
or shrinking-scale hypothesis is needed for these analytic assertions. -/
theorem regMicro_family_support_mass (p : Profile) (ell : Scales) (N : ℕ+)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (hf : OptimalScalingTest p ell N hρ r v f) :
    (∀ᵐ z ∂arclength (loopMasterLength (ell N)), 1 < dist z 0 → f.val z = 0) ∧
      (∫ z : UnitAddCircle,
        (loopMasterPullback (loopMasterLength (ell N)) f.val z)^2) ≤
        4*(ell N).val*∫ x : ℝ, (zeroExtension p x)^2 := by
  let a := ell N
  let L := loopMasterLength a
  let ξ := (⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ :
      {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
  let Q := ∫ z : UnitAddCircle, (loopMasterPullback L ξ.val z)^2
  have hQ : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  have hmass : Q = a.val*∫ x : ℝ, (zeroExtension p x)^2 := by
    change (∫ z : UnitAddCircle, (loopMasterPullback (observationLength a)
      (periodizedProfile p (observationLength a)) z)^2) = _
    rw [integral_sq_loopMasterPullback _ ⟨_, periodizedProfileL2 p a⟩,
      integral_sq_periodizedProfile p (observationLength a)
        ((one_le_inv₀ a.property.1).mpr a.property.2)]
    simp only [observationLength, inv_inv]
  have hsξ : ∀ z : Circle L, (1/2 : ℝ) < dist z 0 → ξ.val z = 0 :=
    regMicro_periodized_support_half p a
  have finish {F : Circle L → ℝ}
      (hs : ∀ᵐ z ∂arclength L, 1 < dist z 0 → F z = 0)
      (hm : (∫ z : UnitAddCircle, (loopMasterPullback L F z)^2) ≤ 4*Q) :
      (∀ᵐ z ∂arclength L, 1 < dist z 0 → F z = 0) ∧
        (∫ z : UnitAddCircle, (loopMasterPullback L F z)^2) ≤
          4*a.val*∫ x : ℝ, (zeroExtension p x)^2 := by
    refine ⟨hs, hm.trans_eq ?_⟩
    rw [hmass]
    ring
  dsimp only [OptimalScalingTest] at hf
  rcases hf with ⟨_hv, hfx⟩ | ⟨t, ht, ht1, _hregime, hbranch⟩
  · subst f
    apply finish (Eventually.of_forall fun z hz => hsξ z (by linarith))
    change Q ≤ 4*Q
    linarith
  · let g := loopMasterLengthTest L (cltRegCircle hρ L ht ξ) (cltRegCircle_contDiff hρ L ht ξ)
    have hsg : ∀ z : Circle L, 1 < dist z 0 → g.val z = 0 := by
      intro z hz
      exact regMicro_smoothing_support L ξ hρ ht (1/2)
        (Eventually.of_forall hsξ) z (by linarith)
    have hmg : (∫ z : UnitAddCircle, (loopMasterPullback L g.val z)^2) ≤ Q :=
      regMicro_smoothing_sq_le L ξ hρ ht
    rcases hbranch with ⟨_hv, hfg⟩ | ⟨_hv, hfe⟩
    · subst f
      exact finish (Eventually.of_forall hsg) (hmg.trans (by linarith))
    · subst f
      have hsE : ∀ᵐ z ∂arclength L, 1 < dist z 0 → (subCircleL2 ξ g).val z = 0 := by
        refine Eventually.of_forall fun z hz => ?_
        change ξ.val z-g.val z = 0
        rw [hsξ z (by linarith), hsg z hz, sub_self]
      have hm := regMicro_integral_error_sq_le hρ L ξ t ht
      exact finish hsE hm

end Riesz1.Internal
