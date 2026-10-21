/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreCriterion
public import Riesz1.HelfferSjostrand.BoundaryCoreDistribution
public import Riesz1.HelfferSjostrand.BoundaryCoreQuotientBarrier
public import Riesz1.HelfferSjostrand.GroundStateOperator
public import Riesz1.HelfferSjostrand.GroundStateCylinder

/-!
# The shifted source kernel vanishes by admissibility

The real quotient case: orthogonality to the
shifted differential source tests is transported by the ground-state
unitary, unfolded to the cover, and eliminated by the boundary barrier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff Laplacian

namespace Riesz1.Internal

/-- Admissibility discharges the shifted-kernel obligation for the actual
scalar source tests, with no distributional equation assumed. -/
theorem scalar_boundary_shift_kernel {N : ℕ+} {c C_N : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) (hadm : HsAdmissible χ C_N)
    {lam : ℝ} (hlam : C_N < lam)
    (u : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hker : ∀ f : HsTestFunction N,
      inner ℝ
        ((memLp_hsLangevin hadm.choose χ f
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))).toLp (hsLangevin χ f) +
          lam • hsSobolevValue _ (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩)) u = 0) :
    u = 0 := by
  let ν := (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  let dx := hsConfigurationVolume N
  let U := hsGroundStateEquiv χ hc (F := ℝ)
  let v := U u
  let V : HsCylinder N → ℝ := Function.extend Subtype.val (v : HsConfiguration N → ℝ) (fun _ => 0)
  have hV (x : HsConfiguration N) : V x.val = v x :=
    Subtype.val_injective.extend_apply _ _ x
  have hVL : MemLp (fun x : HsConfiguration N => V x.val) 2 dx := by
    simpa only [hV] using Lp.memLp v
  have hW : ContDiffOn ℝ ∞
      (fun y : HsEuclidean N => hsGroundStateCylinderPotential χ (QuotientAddGroup.mk y))
      (hsChamber N) := contDiffOn_hsGroundStatePotential χ
  have hp : ∀ g : HsTestFunction N,
      (∫ x : HsConfiguration N,
        (-Δ g.toFun (hsLiftPoint N x) +
          (hsGroundStateCylinderPotential χ x.val + lam) * g (hsLiftPoint N x)) * V x.val ∂dx) = 0 := by
    intro g
    let f := hsInverseGroundStateTest χ hadm.choose g
    let a : Lp ℝ 2 ν := (memLp_hsLangevin hadm.choose χ f ν).toLp (hsLangevin χ f)
    let b := hsSobolevValue ν (hsSobolevOfSmooth ν ⟨f.toFun, f.smoothOnClosure⟩)
    have hg : hsGroundStateTest χ hadm.choose f = g := hsGroundStateTest_inverse χ hc hadm.choose g
    have horth : inner ℝ (U (a + lam • b)) v = 0 := by
      rw [U.inner_map_map]
      exact hker f
    have hac : dx ≪ ν :=
      squareDensity_ac (measurable_hsGroundStateMultiplier χ)
        (hsGroundStateMultiplier_pos χ hc) (hsQuotientGibbsProbability_eq_groundStateDensity χ hc)
    have ha : (a : HsConfiguration N → ℝ) =ᵐ[ν] hsLangevin χ f :=
      (memLp_hsLangevin hadm.choose χ f ν).coeFn_toLp
    have hb : (b : HsConfiguration N → ℝ) =ᵐ[ν] hsSmoothValue f.toFun :=
      (f.smoothOnClosure.memLp_value ν).coeFn_toLp
    rw [L2.inner_def] at horth
    rw [← horth]
    apply integral_congr_ae
    filter_upwards [hsGroundStateEquiv_coeFn χ hc (a + lam • b),
      hac.ae_le (Lp.coeFn_add a (lam • b)), hac.ae_le (Lp.coeFn_smul lam b),
      hac.ae_le ha, hac.ae_le hb] with x hU hab hlb hax hbx
    have hx : (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) = x.val :=
      congrArg Subtype.val (hsChamberProjection_liftPoint x)
    have hw : hsGroundStateCylinderPotential χ x.val = hsGroundStatePotential χ (hsLiftPoint N x) := by
      rw [← hx]
      rfl
    have hcal := hsGroundStateTest_schrodinger χ hadm.choose f (hsLiftPoint_mem_chamber N x)
    rw [hg] at hcal
    have hval := hsGroundStateTest_apply χ hadm.choose f (hsLiftPoint N x)
    rw [hg] at hval
    change -Δ g.toFun (hsLiftPoint N x) + hsGroundStatePotential χ (hsLiftPoint N x) *
      g (hsLiftPoint N x) = hsGroundStateMultiplier χ x * hsLangevin χ f x at hcal
    change g (hsLiftPoint N x) = hsGroundStateMultiplier χ x * f (hsLiftPoint N x) at hval
    rw [hV, hw]
    simp only [Real.inner_apply]
    rw [hU, hab]
    simp only [Pi.add_apply]
    rw [hlb, hax]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hbx]
    simp only [hsSmoothValue]
    rw [show -Δ g.toFun (hsLiftPoint N x) +
      (hsGroundStatePotential χ (hsLiftPoint N x) + lam) * g (hsLiftPoint N x) =
        hsGroundStateMultiplier χ x * hsLangevin χ f x + lam * g (hsLiftPoint N x) by linarith [hcal], hval]
    ring
  have hsol := distributionalSchrodinger_of_source_pairings hadm.choose hW lam hVL hp
  have hzero := quotient_schrodinger_eq_zero_of_boundary_barrier hadm.choose hW hlam
    (fun x => by
      have hb := hsGroundStatePotential_boundary_lower χ hadm (hsLiftPoint_mem_chamber N x)
      have hx : (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) = x.val :=
        congrArg Subtype.val (hsChamberProjection_liftPoint x)
      change (hsQuotientBoundaryDistance N hadm.choose x)⁻¹ ^ 2 - C_N ≤
        hsGroundStateCylinderPotential χ x.val
      rw [← hx]
      exact hb) hVL hsol
  apply U.map_eq_zero_iff.mp
  apply Lp.ext
  filter_upwards [hzero, Lp.coeFn_zero ℝ 2 dx] with x hx hz
  change v x = (0 : Lp ℝ 2 dx) x
  rw [hz]
  exact (hV x).symm.trans hx

end Riesz1.Internal
