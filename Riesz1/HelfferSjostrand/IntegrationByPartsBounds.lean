/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Sobolev

/-!
# Finite norm of the scalar Langevin expression on interior tests

The integrability prerequisite for Gibbs integration by parts. Collision
separation of a test also separates its closed support. Consequently the
Langevin expression is continuous even across collision faces, where
the test vanishes locally, and has finite norm on the quotient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff ENNReal

namespace Riesz1

theorem HsTestFunction.tsupport_subset_chamber {N : ℕ+}
    (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N) : tsupport f.toFun ⊆ hsChamber N := by
  obtain ⟨δ, hδ, hs⟩ := f.support_distance hN
  have hcl : tsupport f.toFun ⊆ {x | δ ≤ hsBoundaryDistance N hN x} :=
    closure_minimal hs (isClosed_le continuous_const (hsBoundaryDistance_lipschitz N hN).continuous)
  intro x hx
  by_contra hxc
  have hd := hcl hx
  change δ ≤ infDist x (hsChamber N)ᶜ at hd
  rw [infDist_zero_of_mem hxc] at hd
  exact hδ.not_ge hd

/-- Local vanishing of a test kills both terms of its differential expression. -/
theorem hsLangevinExpression_eq_zero_of_not_mem_tsupport {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (f : HsTestFunction N) {x : HsEuclidean N}
    (hx : x ∉ tsupport f.toFun) :
    inner ℝ (gradient (hsPairExpression χ) x) (gradient f.toFun x) -
      Laplacian.laplacian f.toFun x = 0 := by
  have heq : f.toFun =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hx
  have hg := heq.gradient_eq
  have hl := (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
  simp only [gradient_fun_const] at hg
  simp only [InnerProductSpace.laplacian_const, Pi.zero_apply] at hl
  rw [hg, hl, inner_zero_right, sub_self]

/-- The ambient differential expression extends continuously across collisions
because its test has support separated from the boundary. -/
theorem continuous_hsLangevinExpression {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (f : HsTestFunction N) :
    Continuous (fun x : HsEuclidean N =>
      inner ℝ (gradient (hsPairExpression χ) x) (gradient f.toFun x) -
        Laplacian.laplacian f.toFun x) := by
  have hgf : Continuous (gradient f.toFun) :=
    (InnerProductSpace.toDual ℝ (HsEuclidean N)).symm.continuous.comp
      (f.smooth.continuous_fderiv (by norm_num))
  have hlf : Continuous (Laplacian.laplacian f.toFun) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    apply continuous_finsetSum
    intro i hi
    exact (f.smooth.continuous_iteratedFDeriv (m := 2) (by norm_num)).eval_const _
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ hsChamber N
  · have hH := (hsPairExpression_contDiffOn χ).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)
    have hgH : ContinuousAt (gradient (hsPairExpression χ)) x :=
      (InnerProductSpace.toDual ℝ (HsEuclidean N)).symm.continuous.continuousAt.comp
        (hH.continuousAt_fderiv (by norm_num))
    exact (hgH.inner hgf.continuousAt).sub hlf.continuousAt
  · have hxs : x ∉ tsupport f.toFun := fun hx' => hx (f.tsupport_subset_chamber hN hx')
    have heq : (fun y : HsEuclidean N =>
        inner ℝ (gradient (hsPairExpression χ) y) (gradient f.toFun y) -
          Laplacian.laplacian f.toFun y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport f.toFun).isOpen_compl.mem_nhds hxs] with y hy
      exact hsLangevinExpression_eq_zero_of_not_mem_tsupport χ f hy
    exact continuousAt_const.congr heq.symm

/-- The Langevin expression belongs to `L²` for every finite quotient measure,
in particular for the admissible Gibbs probability. -/
theorem memLp_hsLangevin {N : ℕ+} {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (f : HsTestFunction N)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    MemLp (hsLangevin χ f) 2 μ :=
  memLp_hsLiftPoint μ 2 (continuous_hsLangevinExpression hN χ f).continuousOn

end Riesz1

end
