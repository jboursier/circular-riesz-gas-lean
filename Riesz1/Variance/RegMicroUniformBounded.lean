/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroUniformLocal
public import Riesz1.Variance.RegMicroUniformSupport

/-!
# The bounded microscopic-length regime

Lemma 5.3 for every bounded `K=Nℓ`, with a coefficient
before the observation scale and particle number. The proof applies the
local second moment to the actual error, whose microscopic support and
square mass are uniformly bounded. It includes `N=1` and does not need
admissibility.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- The error has bounded variance uniformly in every observation scale
with bounded `K`. The coefficient even precedes the mollifier. -/
theorem regMicro_bounded_K_variance (P : Parameters) (p : Profile) (K₀ : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (_hPL : External.PrekopaLeindler)
      (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (N : ℕ+) (a : Scale),
      1 ≤ cltK N a → cltK N a ≤ K₀ →
      let f := (⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ :
        {f : Circle (loopMasterLength a) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))})
      ∃ hE : MemLp (mixedStat P N a (subCircleL2 f (mixedReg hρ N a f))) 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤ ENNReal.ofReal D := by
  obtain ⟨C, hC, hlocal⟩ := regMicro_local_variance_ae P (2*K₀)
  let Q := ∫ x : ℝ, (zeroExtension p x)^2
  have hQ : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  refine ⟨4*C*max K₀ 0*Q+1, by positivity, fun hPL ρ hρ N a hK hKK => ?_⟩
  dsimp only
  let L := observationLength a
  let f := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
      {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
  let E := subCircleL2 f (mixedReg hρ N a f)
  let g := loopMasterPullback L E.val
  have hg : MemLp g 2 volume := (loopMasterPullback_memLp L E).re
  have hE : MemLp (mixedStat P N a E) 2 (gibbsMeasure P N) := memLp_fluctuation P N hg
  have hL : Fact (0 < L.val) := ⟨L.property⟩
  have := hL
  have hh : 0 < (cltK N a)⁻¹ := inv_pos.mpr (cltK_pos N a)
  have hs := regMicro_periodized_error_support p a hρ hh (inv_le_one_of_one_le₀ hK)
  have hsE : ∀ᵐ z ∂arclength L, 1 < dist z 0 → E.val z = 0 := hs
  have hmap : ∀ᵐ z ∂(volume : Measure UnitAddCircle).map
      (AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne'),
      1 < dist z 0 → E.val z = 0 := by
    rw [map_circleScale_volume]
    exact Measure.ae_smul_measure hsE _
  have hsg : ∀ᵐ z : UnitAddCircle, a.val < dist z 0 → g z = 0 := by
    filter_upwards [ae_of_ae_map
      (AddCircle.continuous_equivAddCircle ..).measurable.aemeasurable hmap] with z hz hd
    apply hz
    have hd' := circleScale_dist L.val z 0
    simp only [map_zero] at hd'
    rw [hd']
    have hm := mul_lt_mul_of_pos_left hd (inv_pos.mpr a.property.1)
    rw [inv_mul_cancel₀ a.property.1.ne'] at hm
    exact hm
  have hrad : 2*(N : ℝ)*a.val ≤ 2*K₀ := by
    change (N : ℝ)*a.val ≤ K₀ at hKK
    linarith
  have hv := hlocal hPL N 0 a.val hrad g hg hsg
  have hmass : (∫ z : UnitAddCircle, g z^2) ≤ 4*a.val*Q := by
    change (∫ z : UnitAddCircle, (loopMasterPullback L f.val z-
      loopMasterPullback L (cltRegCircle hρ L hh f) z)^2) ≤ 4*a.val*Q
    exact regMicro_periodized_error_sq_le p a hρ hh
  have hlin := memLp_linearStatistic P N hg
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hshift : variance (gibbsMeasure P N) (mixedStat P N a E) (hE.integrable one_le_two) =
      variance (gibbsMeasure P N) (linearStatistic g) (hlin.integrable one_le_two) :=
    frozenVariance_sub_const (hlin.integrable one_le_two) ((N : ℝ)*∫ z, g z)
  refine ⟨hE, hshift.trans_le (hv.trans (ENNReal.ofReal_le_ofReal ?_))⟩
  have hKQ : cltK N a*Q ≤ max K₀ 0*Q :=
    mul_le_mul_of_nonneg_right (hKK.trans (le_max_left _ _)) hQ
  have hm := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg hC.le (show 0 ≤ (N : ℝ) by positivity))
  change C*(N : ℝ)*(∫ z, g z^2) ≤ _
  calc
    _ ≤ C*(N : ℝ)*(4*a.val*Q) := hm
    _ = 4*C*(cltK N a*Q) := by unfold cltK; ring
    _ ≤ 4*C*(max K₀ 0*Q) := mul_le_mul_of_nonneg_left hKQ (by positivity)
    _ ≤ _ := by ring_nf; linarith

end Riesz1.Internal

namespace Riesz1

/-- The full microscopic rate in Lemma 5.3 on every
fixed bounded range `1≤K≤K₀`. No admissibility is needed in this regime.
All real exponents and all positive particle numbers are allowed. -/
theorem reg_micro_bounded_K (P : Parameters) (p : Profile) (K₀ α ε : ℝ)
    (hK₀ : 1 ≤ K₀) (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler)
      (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (N : ℕ+) (a : Scale),
      1 ≤ cltK N a → cltK N a ≤ K₀ →
      let f := (⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ :
        {f : Circle (loopMasterLength a) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))})
      ∃ hE : MemLp (mixedStat P N a (subCircleL2 f (mixedReg hρ N a f))) 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
          ENNReal.ofReal (C*cltK N a^ε*(cltK N a^(2*α)+cltK N a^(3*P.val.2-2))) := by
  obtain ⟨D, _hD, hb⟩ := Internal.regMicro_bounded_K_variance P p K₀
  obtain ⟨C, hC, hrate⟩ := Internal.regMicro_bounded_length_rate K₀ D P.val.2 α ε hK₀ hε
  refine ⟨C, hC, fun hPL ρ hρ N a hK hKK => ?_⟩
  obtain ⟨hE, hv⟩ := hb hPL ρ hρ N a hK hKK
  exact ⟨hE, hv.trans (ENNReal.ofReal_le_ofReal (hrate (cltK N a) hK hKK))⟩

end Riesz1
