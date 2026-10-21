/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryMixed
public import Riesz1.Kernel.AdmissibilityRegularityVariance
public import Riesz1.Kernel.AdmissibleExamplesCompactPrimitive
public import Riesz1.Frozen.PeriodizedProfileL2
public import Riesz1.CLT.NondegeneracyZero

/-!
# Profile bridge for the mixed mean-field variance

For a profile `p` and a scale `ℓ`, the periodization of `p` on the circle of length `ℓ⁻¹`,
pulled back to the unit circle, agrees almost everywhere with the unit-circle test
`testAtScale p ℓ`. Hence the variance `σ_ℓ²` of `Riesz1.scaledVariance`, evaluated on that
periodization, is `Riesz1.circleVariance` of `p` at `ℓ`
(`Riesz1.scaledVariance_periodizedProfile`).

The two circle lengths of value `ℓ⁻¹` (the length in the mixed mean-field variance of
Proposition 5.6 and the observation length of the periodization) are equal, so the periodization
lives on the circle used by `Riesz1.scaledVariance`
(`Riesz1.loopMasterLength_eq_observationLength`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Riesz1

/-- The length `ℓ⁻¹` of the mixed variance and the observation length of the periodization are
the same pair `⟨ℓ⁻¹, _⟩`, so they agree by definition. -/
theorem loopMasterLength_eq_observationLength (ℓ : Scale) :
    loopMasterLength ℓ = observationLength ℓ :=
  rfl

/-- For `|z| < 1/2`, the periodization of `p` on the circle of length `ℓ⁻¹`, pulled back to the unit
circle, is the zero extension of `p` at `z / ℓ`. The other lattice translates of the central
representative vanish, since the period `ℓ⁻¹` is at least one. -/
theorem loopMasterPullback_periodizedProfile_of_abs_lt (p : Profile) {ℓ : Scale} {z : ℝ}
    (hz : |z| < 1 / 2) :
    loopMasterPullback (observationLength ℓ) (periodizedProfile p (observationLength ℓ))
        (z : UnitAddCircle) =
      zeroExtension p (z / ℓ.val) := by
  have hLpos : 0 < (observationLength ℓ).val := (observationLength ℓ).property
  have hL1 : 1 ≤ (observationLength ℓ).val := (one_le_inv₀ ℓ.property.1).mpr ℓ.property.2
  have : Fact (0 < (observationLength ℓ).val) := ⟨hLpos⟩
  have hz' := abs_lt.mp hz
  -- The central representative of `z L` is `z L` itself, since `|z| < 1/2`.
  have hmem : z * (observationLength ℓ).val ∈
      Ico (-((observationLength ℓ).val / 2)) ((observationLength ℓ).val / 2) :=
    ⟨by linarith [mul_le_mul_of_nonneg_right hz'.1.le hLpos.le],
      by linarith [mul_lt_mul_of_pos_right hz'.2 hLpos]⟩
  rw [loopMasterPullback_coe]
  change periodizedProfile p (observationLength ℓ)
      ((z * (observationLength ℓ).val : ℝ) : Circle (observationLength ℓ)) = _
  unfold periodizedProfile
  rw [centralRep_coe_of_mem (observationLength ℓ) hmem, tsum_eq_single (0 : ℤ)]
  · simp only [Int.cast_zero, zero_mul, add_zero]
    -- `z * (ℓ⁻¹ : ℝ) = z / ℓ` holds by unfolding the definition of division.
    congr 1
  · intro n hn
    apply zeroExtension_eq_zero_of_half_le
    -- For `n ≠ 0`, the translate `z + n` lies at distance at least `1/2` from the origin.
    have hsum : 1 / 2 ≤ |z + n| := by
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
        exact le_trans (by linarith [hz'.2]) (neg_le_abs _)
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        exact le_trans (by linarith [hz'.1]) (le_abs_self _)
    rw [← add_mul, abs_mul, abs_of_pos hLpos]
    nlinarith [hsum, hL1]

/-- The unit-circle test at scale `ℓ` agrees almost everywhere with the pullback of the
periodization of `p` on the circle of length `ℓ⁻¹`. The only point left out is `1/2`, a null set. -/
theorem testAtScale_ae_eq_loopMasterPullback_periodizedProfile (p : Profile) (ℓ : Scale) :
    (fun x => (testAtScale p ℓ x : ℂ)) =ᵐ[volume]
      fun x => (loopMasterPullback (observationLength ℓ)
        (periodizedProfile p (observationLength ℓ)) x : ℂ) := by
  have hnull : ∀ᵐ x : UnitAddCircle ∂volume, x ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    refine ae_iff.2 ?_
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact volume_singleton_half
  filter_upwards [hnull] with x hx
  have : Fact (0 < unitLength.val) := ⟨unitLength.property⟩
  have hxz : ((centralRep unitLength x : ℝ) : UnitAddCircle) = x := by
    unfold centralRep
    exact AddCircle.coe_equivIco
  have hmem : -(1 / 2 : ℝ) ≤ centralRep unitLength x ∧ centralRep unitLength x < 1 / 2 := by
    have h := (AddCircle.equivIco unitLength.val (-unitLength.val / 2) x).property
    change -(1 : ℝ) / 2 ≤ centralRep unitLength x ∧
      centralRep unitLength x < -(1 : ℝ) / 2 + 1 at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hne : centralRep unitLength x ≠ -(1 / 2 : ℝ) := by
    intro hc
    apply hx
    rw [← hxz, hc, ← AddCircle.coe_add_period (1 : ℝ) (-(1 / 2 : ℝ))]
    norm_num
  have hlt : |centralRep unitLength x| < 1 / 2 := by
    rw [abs_lt]
    exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩
  obtain ⟨z, hzlt, rfl⟩ : ∃ z : ℝ, |z| < 1 / 2 ∧ x = (z : UnitAddCircle) :=
    ⟨centralRep unitLength x, hlt, hxz.symm⟩
  rw [testAtScale_coe_of_abs_lt p hzlt, loopMasterPullback_periodizedProfile_of_abs_lt p hzlt]

/-- **Profile bridge.** For every profile `p` and every scale `ℓ`, the variance `σ_ℓ²`
of the periodization of `p` on the circle of length `ℓ⁻¹` is the circle variance of `p` at
`ℓ`. -/
theorem scaledVariance_periodizedProfile (P : Parameters) (p : Profile) (ℓ : Scale) :
    scaledVariance P ℓ ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩ =
      circleVariance P p ℓ := by
  rw [circleVariance_eq_cltVariance]
  unfold scaledVariance cltVariance
  congr 1
  exact circleSobolevSq_congr_ae
    (loopMasterPullback_memLp (loopMasterLength ℓ)
      ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩)
    (testAtScaleL2 p ℓ) (testAtScale_ae_eq_loopMasterPullback_periodizedProfile p ℓ).symm

end Riesz1

end
end
