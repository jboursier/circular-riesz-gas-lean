/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GroundStateAnchoredTests
public import Riesz1.ToMathlib.PeriodizationLaplacian

/-!
# The anchored shifted kernel

Ground-state conjugation converts the test pairings to the
distributional Schrödinger equation. The anchored barrier then
eliminates the kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Laplacian

namespace Riesz1.Internal

/-- The anchored tests detect every vector orthogonal to their positive shift. -/
theorem anchored_boundary_shift_kernel {n : ℕ} {c C_N lam : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) (hadm : HsAdmissible χ C_N)
    (hlam : C_N < lam) (u : Lp ℝ 2 (anchoredMeasureE χ))
    (hker : ∀ f : anchoredTestSubmodule n,
      inner ℝ
        ((memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
          (anchoredLangevinExpr χ f.val) +
            lam • poissonAnchoredValue χ hc (anchoredTestHilbert χ hc f)) u = 0) : u = 0 := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let μ := anchoredMeasureE χ
  let dx : Measure (AnchoredEuclidean n) := volume.restrict (anchoredSimplex n)
  let U := anchoredGroundStateEquiv χ hc
  let v := U u
  have hac : dx ≪ μ := aeSquareDensity_ac (aemeasurable_anchoredGroundStateMultiplier χ)
    (anchoredGroundStateMultiplier_pos χ hc) (anchoredMeasureE_eq_groundStateDensity χ hc)
  have hp : ∀ g : anchoredTestSubmodule n,
      (∫ y, (-Δ g.val y + (hsAnchoredGroundStatePotential χ y + lam) * g.val y) * v y ∂dx) = 0 := by
    intro g
    let f := anchoredInverseGroundStateTest χ g
    let a : Lp ℝ 2 μ :=
      (memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).toLp
        (anchoredLangevinExpr χ f.val)
    let b := poissonAnchoredValue χ hc (anchoredTestHilbert χ hc f)
    have hg : anchoredGroundStateTest χ f = g := anchoredGroundStateTest_inverse χ hc g
    have ha : (a : AnchoredEuclidean n → ℝ) =ᵐ[μ] anchoredLangevinExpr χ f.val :=
      (memLp_anchoredLangevinExpr χ hc f.property.1 f.property.2.1 f.property.2.2).coeFn_toLp
    have hb : (b : AnchoredEuclidean n → ℝ) =ᵐ[μ] f.val :=
      (WeightedSobolev.memLp_of_smoothNearClosure (isBounded_anchoredSimplex n)
        (ae_mem_anchoredSimplex χ) (anchoredTestSmooth n f).property).1.coeFn_toLp
    have horth : inner ℝ (U (a + lam • b)) v = 0 := by
      rw [U.inner_map_map]
      exact hker f
    rw [L2.inner_def] at horth
    rw [← horth]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_anchoredSimplex n),
      anchoredGroundStateEquiv_coeFn χ hc (a + lam • b), hac.ae_le (Lp.coeFn_add a (lam • b)),
      hac.ae_le (Lp.coeFn_smul lam b), hac.ae_le ha, hac.ae_le hb] with y hy hU hab hlb hax hbx
    have hcal := anchoredGroundStateTest_schrodinger χ f hy
    have hval := anchoredGroundStateTest_apply χ f y
    rw [hg] at hcal hval
    simp only [Real.inner_apply]
    rw [hU, hab]
    simp only [Pi.add_apply]
    rw [hlb, hax]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hbx]
    rw [show -Δ g.val y + (hsAnchoredGroundStatePotential χ y + lam) * g.val y =
      anchoredGroundStateMultiplier χ y * anchoredLangevinExpr χ f.val y + lam * g.val y by linarith [hcal], hval]
    ring
  have hvL : MemLp (v : AnchoredEuclidean n → ℝ) 2 dx := Lp.memLp v
  have hvl : LocallySquareIntegrableOn (anchoredSimplex n) (v : AnchoredEuclidean n → ℝ) := by
    intro K _ hKU
    exact MemLp.mono_measure (Measure.restrict_mono hKU le_rfl) hvL
  have hvi := hvl.locallyIntegrableOn (isOpen_anchoredSimplex n)
  have hwv : LocallyIntegrableOn (fun y => (hsAnchoredGroundStatePotential χ y + lam) • v y)
      (anchoredSimplex n) := (hvl.smul_continuousOn
    ((contDiffOn_hsAnchoredGroundStatePotential χ).continuousOn.add continuousOn_const)
    ).locallyIntegrableOn (isOpen_anchoredSimplex n)
  have hsol : IsDistributionalSchrodingerSolution (anchoredSimplex n)
      (hsAnchoredGroundStatePotential χ) lam (v : AnchoredEuclidean n → ℝ) := by
    refine ⟨hvi, hwv, ?_⟩
    intro φ hφ hφc hφU
    have hz := hp ⟨φ, hφ, hφc, hφU⟩
    have hi := integrable_smul_of_compact_interior hwv hφ.continuous hφc hφU
    have hj := integrable_smul_of_compact_interior hvi (contDiff_laplacian hφ).continuous
      (hasCompactSupport_laplacian hφc) ((tsupport_laplacian_subset φ).trans hφU)
    have hfull : (∫ y, (-Δ φ y + (hsAnchoredGroundStatePotential χ y + lam) * φ y) * v y) = 0 := by
      rw [← hz]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hφy := image_eq_zero_of_notMem_tsupport (fun h => hy (hφU h))
      have hΔy := image_eq_zero_of_notMem_tsupport
        (fun h => hy (hφU (tsupport_laplacian_subset φ h)))
      simp only [hφy, hΔy, neg_zero, mul_zero, add_zero, zero_mul]
    have heq : (fun y => (-Δ φ y + (hsAnchoredGroundStatePotential χ y + lam) * φ y) * v y) =
        fun y => φ y • ((hsAnchoredGroundStatePotential χ y + lam) • v y) - (Δ φ) y • v y := by
      funext y
      simp only [smul_eq_mul]
      ring
    rw [heq, integral_sub hi hj] at hfull
    exact sub_eq_zero.mp hfull
  have hzero := anchored_schrodinger_eq_zero χ hc hadm hlam hvL hsol
  apply U.map_eq_zero_iff.mp
  apply Lp.ext
  exact hzero.trans (Lp.coeFn_zero ℝ 2 dx).symm

end Riesz1.Internal
