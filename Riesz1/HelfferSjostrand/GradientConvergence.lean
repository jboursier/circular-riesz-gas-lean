/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreCriterion

/-!
# Scalar consequences of graph convergence

The scalar domain assertion and convergence in `H¹` in the gradient part of
Proposition 3.1. These follow from the
Neumann resolvent. Convergence in the vector energy norm additionally needs
the integrated commutator identity and is not asserted in this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

namespace Internal

/-- A scalar graph sequence converges in the form norm when both graph entries converge. -/
theorem hsScalar_graph_limit (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : ℕ → HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (a : ℕ → Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hg : ∀ k, (f k, a k) ∈ hsNeumannGraph (hsQuotientGibbsProbability χ hc : Measure _))
    (v b : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hv : Tendsto (fun k => hsSobolevValue _ (f k)) atTop (𝓝 v))
    (hb : Tendsto a atTop (𝓝 b)) :
    ∃ φ : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)),
      hsSobolevValue _ φ = v ∧ (φ, b) ∈ hsNeumannGraph _ ∧
        Tendsto f atTop (𝓝 φ) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let φ := hsNeumannResolvent μ (b + v)
  have he (k : ℕ) : hsNeumannResolvent μ (a k + hsSobolevValue μ (f k)) = f k :=
    hsNeumannResolvent_graph_input χ hc (hg k)
  have hlim : Tendsto f atTop (𝓝 φ) := by
    have h := ((hsNeumannResolvent μ).continuous.tendsto (b + v)).comp (hb.add hv)
    change Tendsto (fun k => hsNeumannResolvent μ (a k + hsSobolevValue μ (f k)))
      atTop (𝓝 φ) at h
    simpa only [he] using h
  have hval : hsSobolevValue μ φ = v :=
    tendsto_nhds_unique (((hsSobolevValue μ).continuous.tendsto φ).comp hlim) hv
  refine ⟨φ, hval, ?_, hlim⟩
  have h := hsNeumannResolvent_mem_graph μ (b + v)
  rwa [hval, add_sub_cancel_right] at h

end Internal

/-- The first scalar energy identity in the commutator proposition. -/
theorem hsGradient_scalar_energy (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : HsTestFunction N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ‖hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩)‖ ^ 2 =
      ∫ x, hsTestOnQuotient f x * hsLangevin χ f x ∂μ := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  change ‖hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩)‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq]
  change hsDirichletForm μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩)
    (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) = _
  rw [← hsIntegrationByParts_smooth hN χ hc f f]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-- The scalar domain and `H¹` convergence assertions of
the gradient part of Proposition 3.1, on the full quotient.
The limiting gradient therefore also converges in `L²`. -/
theorem hsGradient_graph_convergence_scalar (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : ℕ → HsTestFunction N)
    (v a : Lp ℝ 2 (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hv : Tendsto (fun k => hsSobolevValue _
      (hsSobolevOfSmooth _ ⟨(f k).toFun, (f k).smoothOnClosure⟩)) atTop (𝓝 v))
    (ha : Tendsto (fun k => (memLp_hsLangevin hN χ (f k)
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))).toLp (hsLangevin χ (f k)))
      atTop (𝓝 a)) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ∃ φ : HsSobolev μ, hsSobolevValue μ φ = v ∧
      (∃ hφ : φ ∈ hsNeumannDomain μ, hsNeumannOperator χ hc ⟨φ, hφ⟩ = a) ∧
      Tendsto (fun k => hsSobolevOfSmooth μ ⟨(f k).toFun, (f k).smoothOnClosure⟩)
        atTop (𝓝 φ) ∧
      Tendsto (fun k => hsSobolevGradient μ
        (hsSobolevOfSmooth μ ⟨(f k).toFun, (f k).smoothOnClosure⟩))
        atTop (𝓝 (hsSobolevGradient μ φ)) := by
  obtain ⟨φ, hval, hg, hlim⟩ := Internal.hsScalar_graph_limit χ hc
    (fun k => hsSobolevOfSmooth _ ⟨(f k).toFun, (f k).smoothOnClosure⟩)
    (fun k => (memLp_hsLangevin hN χ (f k) _).toLp (hsLangevin χ (f k)))
    (fun k => hsLangevin_mem_neumannGraph hN χ hc (f k)) v a hv ha
  exact ⟨φ, hval, ⟨⟨a, hg⟩, (hsNeumannOperator_eq_iff χ hc _ a).mpr hg⟩, hlim,
    ((hsSobolevGradient _).continuous.tendsto φ).comp hlim⟩

end Riesz1
