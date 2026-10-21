/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFamilyMass
public import Riesz1.Variance.RegMicroUniformLocal

/-!
# Bounded microscopic lengths uniformly over both families

The bounded-`K` clause of Lemma 5.3, including the
original test and the two convolution families, with a single constant
before the scale sequence, particle number and extra family radius.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- The full microscopic regularization rate on a fixed bounded range
of `K`, uniformly over the actual `OptimalScalingTest` relation. This
requires no admissibility, covers `N=1`, and allows every real exponent.
The constant even precedes the mollifier and family-support parameter. -/
theorem regMicroFamily_bounded_K (P : Parameters) (p : Profile) (K₀ α ε : ℝ)
    (hK₀ : 1 ≤ K₀) (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler)
      (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (r : ℝ) (ell : Scales) (N : ℕ+),
      1 ≤ cltK N (ell N) → cltK N (ell N) ≤ K₀ →
      ∀ (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∃ hE : MemLp (mixedStat P N (ell N) (subCircleL2 f (mixedReg hρ N (ell N) f))) 2
            (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
            ENNReal.ofReal (C*cltK N (ell N)^ε*
              (cltK N (ell N)^(2*α)+cltK N (ell N)^(3*P.val.2-2))) := by
  obtain ⟨J, hJ, hlocal⟩ := regMicro_mixed_local_variance_ae P 2 K₀ (by norm_num)
  let Q := ∫ x : ℝ, (zeroExtension p x)^2
  have hQ : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
  let D := 16*J*K₀*Q
  obtain ⟨C, hC, hrate⟩ := regMicro_bounded_length_rate K₀ D P.val.2 α ε hK₀ hε
  refine ⟨C, hC, fun hPL ρ hρ r ell N hK hKK v f hf => ?_⟩
  let a := ell N
  let L := loopMasterLength a
  let E := subCircleL2 f (mixedReg hρ N a f)
  have hh : 0 < (cltK N a)⁻¹ := inv_pos.mpr (cltK_pos N a)
  have hh1 : (cltK N a)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  obtain ⟨hs, hm⟩ := regMicro_family_support_mass p ell N hρ r v f hf
  have hreg := regMicro_smoothing_support L f hρ hh 1 hs
  have hsE : ∀ᵐ z ∂arclength L, 2 < dist z 0 → E.val z = 0 := by
    filter_upwards [hs] with z hz hd
    change f.val z-cltRegCircle hρ L hh f z = 0
    rw [hz (by linarith), hreg z (by linarith), sub_self]
  have hmass : (∫ z : UnitAddCircle, (loopMasterPullback L E.val z)^2) ≤ 16*a.val*Q := by
    have he := regMicro_integral_error_sq_le hρ L f (cltK N a)⁻¹ hh
    change (∫ z : UnitAddCircle, (loopMasterPullback L f.val z-
      loopMasterPullback L (cltRegCircle hρ L hh f) z)^2) ≤ _
    calc
      _ ≤ 4*∫ z : UnitAddCircle, (loopMasterPullback L f.val z)^2 := he
      _ ≤ 4*(4*a.val*Q) := mul_le_mul_of_nonneg_left hm (by norm_num)
      _ = _ := by ring
  obtain ⟨hE, hv⟩ := hlocal hPL N a hKK E hsE
  refine ⟨hE, hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  calc
    _ ≤ J*(N : ℝ)*(16*a.val*Q) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 16*J*(cltK N a*Q) := by unfold cltK; ring
    _ ≤ D := by
      dsimp only [D]
      have hq := mul_le_mul_of_nonneg_right hKK hQ
      nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 16*J)]
    _ ≤ _ := hrate (cltK N a) hK hKK

end Riesz1.Internal
