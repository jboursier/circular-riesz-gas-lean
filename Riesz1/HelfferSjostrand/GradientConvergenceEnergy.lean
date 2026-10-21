/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceTests
public import Riesz1.ToMathlib.Variational.ProbabilityPoisson

/-! # The integrated commutator on the quotient source core

The vector form of the gradient of a scalar source test equals the squared
`L²` norm of its source Langevin operator, as in
Proposition 3.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

theorem hsGradient_hessian_commutator (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c)
    (f : HsTestFunction N) {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (gradient f.toFun x) (gradient f.toFun x) =
      ∑ i : Fin (N : ℕ),
        ((hsGradientTestDirection hN (hsLangevinTest hN χ f) (EuclideanSpace.single i 1)).toFun x -
          (hsLangevinTest hN χ (hsGradientTestDirection hN f (EuclideanSpace.single i 1))).toFun x) *
            (hsGradientTestDirection hN f (EuclideanSpace.single i 1)).toFun x := by
  have he := hsCommutator_linear_coordinates
    ((fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x).flip (gradient f.toFun x)) (gradient f.toFun x)
  simp only [ContinuousLinearMap.flip_apply] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  have h := langevin_direction_commutator
    ((hsPairExpression_contDiffOn χ).contDiffAt ((isOpen_hsChamber N).mem_nhds hx))
    f.smooth (EuclideanSpace.single i 1)
  change fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (EuclideanSpace.single i 1)
      (gradient f.toFun x) * gradient f.toFun x i = _
  rw [← h]
  congr 1
  exact (hsGradientTestTuple_apply hN f x i).symm

theorem hsGradient_pairEnergy_eq (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : HsTestFunction N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    let u := hsGradientTestTuple hN f
    let E := (memLp_hsTestEnergyFun χ hN hc μ u).toLp (hsTestEnergyFun χ u)
    inner ℝ E E = ∫ y, ∑ i : Fin (N : ℕ),
      (hsTestOnQuotient (hsGradientTestDirection hN (hsLangevinTest hN χ f)
        (EuclideanSpace.single i 1)) y -
        hsLangevin χ (hsGradientTestDirection hN f (EuclideanSpace.single i 1)) y) *
          hsTestOnQuotient (hsGradientTestDirection hN f (EuclideanSpace.single i 1)) y ∂μ := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  dsimp only
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_hsTestEnergyFun χ hN hc μ (hsGradientTestTuple hN f)).coeFn_toLp] with y hy
  rw [hy]
  change inner ℝ (hsHessianEnergy χ (hsLiftPoint N y) (hsTestVector (hsGradientTestTuple hN f) _))
    (hsHessianEnergy χ (hsLiftPoint N y) (hsTestVector (hsGradientTestTuple hN f) _)) = _
  rw [inner_hsHessianEnergy χ hc (hsLiftPoint_mem_chamber N y), hsTestVector_gradientTestTuple]
  exact hsGradient_hessian_commutator hN χ f (hsLiftPoint_mem_chamber N y)

theorem hsGradient_form_eq_dirichlet (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : HsTestFunction N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    let u := hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN f)
    hsVectorSobolevForm χ hN hc μ u u =
      hsDirichletForm μ (hsSobolevOfSmooth μ ⟨(hsLangevinTest hN χ f).toFun,
        (hsLangevinTest hN χ f).smoothOnClosure⟩)
        (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let g (i : Fin (N : ℕ)) := hsGradientTestDirection hN f (EuclideanSpace.single i 1)
  let L := hsLangevinTest hN χ f
  let A (i : Fin (N : ℕ)) := hsLangevin χ (g i)
  let B (i : Fin (N : ℕ)) := hsTestOnQuotient (g i)
  let C (i : Fin (N : ℕ)) := hsTestOnQuotient (hsGradientTestDirection hN L (EuclideanSpace.single i 1))
  let E := (memLp_hsTestEnergyFun χ hN hc μ (hsGradientTestTuple hN f)).toLp
    (hsTestEnergyFun χ (hsGradientTestTuple hN f))
  have hA (i) : MemLp (A i) 2 μ := memLp_hsLangevin hN χ (g i) μ
  have hB (i) : MemLp (B i) 2 μ := (g i).smoothOnClosure.memLp_value μ
  have hC (i) : MemLp (C i) 2 μ :=
    (hsGradientTestDirection hN L (EuclideanSpace.single i 1)).smoothOnClosure.memLp_value μ
  have hab (i) : Integrable (fun y => A i y * B i y) μ := (hA i).integrable_mul (hB i)
  have hdiff (i) : Integrable (fun y => (C i y - A i y) * B i y) μ :=
    ((hC i).sub (hA i)).integrable_mul (hB i)
  have hi (i : Fin (N : ℕ)) :
      hsDirichletForm μ (hsSobolevOfSmooth μ ⟨(g i).toFun, (g i).smoothOnClosure⟩)
        (hsSobolevOfSmooth μ ⟨(g i).toFun, (g i).smoothOnClosure⟩) = ∫ y, A i y * B i y ∂μ :=
    (hsIntegrationByParts_smooth hN χ hc (g i) (g i)).symm
  have he : inner ℝ E E = ∫ y, ∑ i, (C i y - A i y) * B i y ∂μ :=
    hsGradient_pairEnergy_eq hN χ hc f
  have hpoint (y : HsConfiguration N) : (∑ i, C i y * B i y) =
      inner ℝ (gradient L.toFun (hsLiftPoint N y)) (gradient f.toFun (hsLiftPoint N y)) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hb := hsGradientTestTuple_apply hN f (hsLiftPoint N y) i
    have hc' := hsGradientTestTuple_apply hN L (hsLiftPoint N y) i
    change (g i).toFun (hsLiftPoint N y) = _ at hb
    change (hsGradientTestDirection hN L (EuclideanSpace.single i 1)).toFun (hsLiftPoint N y) = _ at hc'
    change (hsGradientTestDirection hN L (EuclideanSpace.single i 1)).toFun (hsLiftPoint N y) *
      (g i).toFun (hsLiftPoint N y) = _
    rw [hc', hb]
    exact (Real.inner_apply _ _).symm
  change (∑ i : Fin (N : ℕ), hsDirichletForm μ
      (hsSobolevOfSmooth μ ⟨(g i).toFun, (g i).smoothOnClosure⟩)
      (hsSobolevOfSmooth μ ⟨(g i).toFun, (g i).smoothOnClosure⟩)) + inner ℝ E E = _
  simp_rw [hi]
  rw [he, ← integral_finsetSum _ (fun i _ => hab i),
    ← integral_add (integrable_finsetSum _ (fun i _ => hab i))
      (integrable_finsetSum _ (fun i _ => hdiff i)), hsGradient_dirichlet_tests]
  apply integral_congr_ae
  filter_upwards with y
  rw [← hpoint y, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The integrated commutator identity on the full quotient source core. -/
theorem hsGradient_vector_energy (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : HsTestFunction N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    let u := hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN f)
    hsVectorSobolevForm χ hN hc μ u u =
      ‖(memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f)‖ ^ 2 := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  dsimp only
  rw [hsGradient_form_eq_dirichlet, hsDirichletForm_symmetric,
    ← hsIntegrationByParts_smooth hN χ hc f (hsLangevinTest hN χ f), hsLangevinTest_onQuotient]
  rw [poisson_norm_sq μ]
  apply integral_congr_ae
  filter_upwards [(memLp_hsLangevin hN χ f μ).coeFn_toLp] with y hy
  rw [hy, pow_two]

end Riesz1
