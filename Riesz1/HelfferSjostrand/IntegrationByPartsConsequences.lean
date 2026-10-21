/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.IntegrationByPartsFull
public import Riesz1.HelfferSjostrand.NeumannOperator

/-!
# The Langevin expression in the Neumann graph

The full identity identifies the differential
expression on the actual test class with its variational
representative. Its symmetry and nonnegativity follow on that class.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (hN : 2 ≤ (N : ℕ))
  (χ : HsPairPotentials N c) (hc : 0 < c)

include hN

/-- The full integration by parts identity expressed using the energy form. -/
theorem hsIntegrationByParts_form (f : HsTestFunction N)
    (h : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    ∫ x, hsLangevin χ f x * hsSobolevValue
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) h x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      hsDirichletForm
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
        (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩) h := by
  rw [hsIntegrationByParts hN χ hc f h, hsDirichletForm_eq_integral]
  have hgrad : (hsSobolevGradient
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
      (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩) :
      HsConfiguration N → HsEuclidean N) =ᵐ[
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
      hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ :=
    (f.smoothOnClosure.memLp_gradient _).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hgrad] with x hx
  rw [hx]

/-- The differential expression belongs to the variational Neumann graph. -/
theorem hsLangevin_mem_neumannGraph (f : HsTestFunction N) :
    (hsSobolevOfSmooth
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
        ⟨f.toFun, f.smoothOnClosure⟩,
      (memLp_hsLangevin hN χ f
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))).toLp (hsLangevin χ f)) ∈
      hsNeumannGraph (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  intro h
  rw [← hsIntegrationByParts_form hN χ hc f h, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_hsLangevin hN χ f
    (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))).coeFn_toLp] with x hx
  rw [hx, Real.inner_apply]

/-- Smooth tests lie in the full variational domain and the operator agrees with `L₀`. -/
theorem hsNeumannOperator_on_test (f : HsTestFunction N) :
    ∃ hf : hsSobolevOfSmooth
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
        ⟨f.toFun, f.smoothOnClosure⟩ ∈
          hsNeumannDomain (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)),
      hsNeumannOperator χ hc ⟨_, hf⟩ =
        (memLp_hsLangevin hN χ f
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))).toLp (hsLangevin χ f) := by
  have hg := hsLangevin_mem_neumannGraph hN χ hc f
  refine ⟨⟨_, hg⟩, ?_⟩
  exact (hsNeumannOperator_eq_iff χ hc _ _).mpr hg

/-- Integration by parts on two actual tests. -/
theorem hsIntegrationByParts_smooth (f g : HsTestFunction N) :
    ∫ x, hsLangevin χ f x * hsTestOnQuotient g x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      hsDirichletForm
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
        (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩)
        (hsSobolevOfSmooth _ ⟨g.toFun, g.smoothOnClosure⟩) := by
  rw [← hsIntegrationByParts_form hN χ hc]
  have hval : (hsSobolevValue
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
      (hsSobolevOfSmooth _ ⟨g.toFun, g.smoothOnClosure⟩) : HsConfiguration N → ℝ) =ᵐ[
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
      hsTestOnQuotient g := (g.smoothOnClosure.memLp_value _).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hval] with x hx
  rw [hx]

/-- `L₀` is symmetric on the test class `𝒟_N`. -/
theorem hsLangevin_symmetric (f g : HsTestFunction N) :
    ∫ x, hsLangevin χ f x * hsTestOnQuotient g x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, hsTestOnQuotient f x * hsLangevin χ g x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  rw [hsIntegrationByParts_smooth hN χ hc, hsDirichletForm_symmetric,
    ← hsIntegrationByParts_smooth hN χ hc]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => mul_comm _ _)

/-- `L₀` is nonnegative on the test class `𝒟_N`. -/
theorem hsLangevin_nonnegative (f : HsTestFunction N) :
    0 ≤ ∫ x, hsLangevin χ f x * hsTestOnQuotient f x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  rw [hsIntegrationByParts_smooth hN χ hc]
  exact hsDirichletForm_nonnegative _ _

end Riesz1

end
