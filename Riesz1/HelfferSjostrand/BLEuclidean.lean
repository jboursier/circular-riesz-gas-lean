/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLEuclideanSmooth
public import Riesz1.HelfferSjostrand.BLEuclideanVariational
public import Riesz1.ToMathlib.WeightedSobolev.Completion
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts

/-!
# The Euclidean Brascamp–Lieb inequality, for every weighted Sobolev function

This proves the Euclidean step of Lemma 3.6: for a bounded open convex `U`,
`V ∈ C²(U)` with `D²V ≥ κ I` on `U`, and `ν ∝ e^{-V} 1_U dx`, the normalization is finite and
positive, and for every `F ∈ H¹(ν)` with weak gradient `G`,

`Var_ν F ≤ ∫ G · (D²V)⁻¹ G dν`.

The inverse Hessian is written as the variational energy `sup_h (2⟪G, h⟫ - D²V(h, h))`, which is
equal to `⟪G, (D²V)⁻¹ G⟫` by the Lax–Milgram inverse. The equality is part of the conclusion.

For a smooth `F`, the inequality is `bl_euclidean_smooth`. For a general `F ∈ H¹(ν)`, the
approximating smooth functions `φ k` satisfy the inequality, and the limit passes through the
variance, the Lipschitz bound `bl_sSup_sub_le` on the energy, and Cauchy–Schwarz.

The only external hypothesis is `Riesz1.External.PrekopaLeindler`.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {d : ℕ}

/-- The Hessian of `V` is a symmetric bilinear form at each point of `U`, where `V` is `C²`. -/
theorem fderiv_fderiv_symm_of_mem {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V U) (ho : IsOpen U)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) :
    ∀ v w, fderiv ℝ (fderiv ℝ V) x v w = fderiv ℝ (fderiv ℝ V) x w v :=
  (hV.contDiffAt (ho.mem_nhds hx)).isSymmSndFDerivAt (by simp)

/-- At a point of `U`, the variational energy of any vector `g` is the inverse Hessian energy
`⟪g, (D²V)⁻¹ g⟫`, with the inverse given by the Lax–Milgram equivalence of the coercive Hessian. -/
theorem sSup_eq_inverse_hessian {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V U) (ho : IsOpen U)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ U) (g : EuclideanSpace ℝ (Fin d)) :
    ∃ hB : IsCoercive (fderiv ℝ (fderiv ℝ V) x),
      sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪g, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) =
        ⟪g, hB.continuousLinearEquivOfBilin.symm g⟫_ℝ := by
  have hB : IsCoercive (fderiv ℝ (fderiv ℝ V) x) :=
    ⟨κ, hκ, fun h => by simpa only [pow_two, mul_assoc] using hb x hx h⟩
  exact ⟨hB, bl_quadratic_sSup_eq_inverse hB (fderiv_fderiv_symm_of_mem hV ho hx) g⟩

/-- A function smooth near the closure of a bounded set is continuous on the set, and its
values and gradients are bounded there. -/
theorem bounds_of_smoothNearClosure {U : Set (EuclideanSpace ℝ (Fin d))}
    (hU : Bornology.IsBounded U) {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : WeightedSobolev.SmoothNearClosure U f) :
    ContinuousOn f U ∧ ∃ C, ∀ x ∈ U, ‖f x‖ ≤ C ∧ ‖gradient f x‖ ≤ C := by
  obtain ⟨W, hW, hUW, hfs⟩ : ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧
      closure U ⊆ W ∧ ContDiffOn ℝ ∞ f W := hf
  have hfc : ContinuousOn f (closure U) := hfs.continuousOn.mono hUW
  have hdc : ContinuousOn (fderiv ℝ f) (closure U) :=
    (hfs.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hUW
  have hgc : ContinuousOn (gradient f) (closure U) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp_continuousOn hdc
  obtain ⟨C1, h1⟩ := hU.isCompact_closure.exists_bound_of_continuousOn hfc
  obtain ⟨C2, h2⟩ := hU.isCompact_closure.exists_bound_of_continuousOn hgc
  refine ⟨hfc.mono subset_closure, max C1 C2, fun x hx => ?_⟩
  exact ⟨(h1 x (subset_closure hx)).trans (le_max_left _ _),
    (h2 x (subset_closure hx)).trans (le_max_right _ _)⟩

/-- The variational energy of an `L²` vector field is integrable, under any finite measure carried
by `U`. -/
theorem integrable_energy_field {U : Set (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ} {μ : Measure (EuclideanSpace ℝ (Fin d))}
    [IsFiniteMeasure μ] {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (hμU : ∀ᵐ x ∂μ, x ∈ U) {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hGL : MemLp G 2 μ) :
    Integrable (fun x => sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
      2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)) μ := by
  have hG₁ : Measurable (hGL.aestronglyMeasurable.mk G) :=
    hGL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae := hGL.aestronglyMeasurable.ae_eq_mk
  have hmeas : AEMeasurable (fun x => sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
      2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)) μ := by
    refine (aemeasurable_sSup_hessian hG₁ hμU hb hκ).congr ?_
    filter_upwards [hae] with x hx
    rw [hx]
  refine Integrable.mono' (hGL.norm.integrable_sq.div_const κ) hmeas.aestronglyMeasurable ?_
  filter_upwards [hμU] with x hx
  obtain ⟨h0, h1⟩ := bl_variational_energy_bounds (fderiv ℝ (fderiv ℝ V) x) (G x) hκ (hb x hx)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- The Euclidean Brascamp–Lieb inequality for a general `F ∈ H¹(ν)` with weak gradient `G`:
the variance is at most the inverse Hessian energy of `G`. -/
theorem bl_euclidean_H1 (hPL : Riesz1.External.PrekopaLeindler) (hd : 0 < d)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hne : U.Nonempty) (hc : Convex ℝ U)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hFG : WeightedSobolev.IsWeightedH1 ((volume.restrict U).tilted (fun x => -V x)) U F G) :
    (∫ x, (F x - ∫ y, F y ∂((volume.restrict U).tilted (fun x => -V x))) ^ 2
        ∂((volume.restrict U).tilted (fun x => -V x))) ≤
      ∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)
        ∂((volume.restrict U).tilted (fun x => -V x)) := by
  obtain ⟨hFL, hGL, φ, hφS, hT1, hT2⟩ := hFG
  obtain ⟨x0, hx0⟩ := hne
  have := bl_convex_isProbabilityMeasure hU hc ho ⟨x0, hx0⟩ hV hκ hb
  set ν := (volume.restrict U).tilted (fun x => -V x)
  have hν_ae : ∀ᵐ x ∂ν, x ∈ U :=
    (tilted_absolutelyContinuous _ _).ae_le (ae_restrict_mem ho.measurableSet)
  -- Each approximant is bounded and has bounded gradient on `U`.
  have hφb := fun k => bounds_of_smoothNearClosure hU (hφS k)
  have hφmem : ∀ k, MemLp (φ k) 2 ν := fun k => by
    obtain ⟨hcont, C, hC⟩ := hφb k
    exact memLp_tilted_of_bounded ho hcont (C := C) (fun x hx => (hC x hx).1)
  have hgmem : ∀ k, MemLp (gradient (φ k)) 2 ν := fun k => by
    obtain ⟨_, C, hC⟩ := hφb k
    refine MemLp.of_bound (measurable_gradient_euclidean (φ k)).aestronglyMeasurable C ?_
    filter_upwards [hν_ae] with x hx
    exact (hC x hx).2
  have hdiffmem : ∀ k, MemLp (fun x => ‖gradient (φ k) x - G x‖) 2 ν := fun k =>
    ((hgmem k).sub hGL).norm
  -- The `L²` convergence, in real integrals.
  have hd_k : Tendsto (fun k => ∫ x, (φ k x - F x) ^ 2 ∂ν) atTop (𝓝 0) :=
    WeightedSobolev.tendsto_integral_sq_of_lintegral
      (fun k => (hφmem k).aestronglyMeasurable.sub hFL.aestronglyMeasurable) hT1
  have he_k : Tendsto (fun k => ∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν) atTop (𝓝 0) :=
    WeightedSobolev.tendsto_integral_norm_sq_of_lintegral
      (fun k => (measurable_gradient_euclidean (φ k)).aestronglyMeasurable.sub
        hGL.aestronglyMeasurable) hT2
  -- The variances converge to the variance of `F`.
  have hVar : Tendsto (fun k => ∫ x, (φ k x - ∫ y, φ k y ∂ν) ^ 2 ∂ν) atTop
      (𝓝 (∫ x, (F x - ∫ y, F y ∂ν) ^ 2 ∂ν)) :=
    WeightedSobolev.tendsto_integral_sub_mean_sq hFL hφmem hd_k
  -- The smooth inequality for each approximant.
  have hsmooth : ∀ k, (∫ x, (φ k x - ∫ y, φ k y ∂ν) ^ 2 ∂ν) ≤
      ∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪gradient (φ k) x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂ν :=
    fun k => bl_euclidean_smooth hPL hd hU ho ⟨x0, hx0⟩ hc hV hκ hb (hφS k)
  -- The energy comparison, pointwise on `U`.
  have hpt : ∀ k, ∀ᵐ x ∂ν,
      sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪gradient (φ k) x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ≤
      sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) +
        4 / κ * (‖gradient (φ k) x - G x‖ ^ 2 + ‖gradient (φ k) x - G x‖ * ‖G x‖) := by
    intro k
    filter_upwards [hν_ae] with x hx
    have h1 := bl_sSup_sub_le (fderiv_fderiv_symm_of_mem hV ho hx) hκ (hb x hx)
      (gradient (φ k) x) (G x)
    have htri : ‖gradient (φ k) x‖ ≤ ‖gradient (φ k) x - G x‖ + ‖G x‖ := by
      have := norm_add_le (gradient (φ k) x - G x) (G x)
      rwa [sub_add_cancel] at this
    have hnn : 0 ≤ ‖gradient (φ k) x - G x‖ := norm_nonneg _
    have h2 : ‖gradient (φ k) x - G x‖ * ‖gradient (φ k) x‖ ≤
        ‖gradient (φ k) x - G x‖ ^ 2 + ‖gradient (φ k) x - G x‖ * ‖G x‖ := by
      nlinarith [mul_le_mul_of_nonneg_left htri hnn]
    have h3 : 4 * ‖gradient (φ k) x - G x‖ * ‖gradient (φ k) x‖ / κ ≤
        4 / κ * (‖gradient (φ k) x - G x‖ ^ 2 + ‖gradient (φ k) x - G x‖ * ‖G x‖) := by
      rw [show 4 * ‖gradient (φ k) x - G x‖ * ‖gradient (φ k) x‖ / κ =
        4 / κ * (‖gradient (φ k) x - G x‖ * ‖gradient (φ k) x‖) by ring]
      exact mul_le_mul_of_nonneg_left h2 (div_nonneg (by norm_num) hκ.le)
    linarith
  -- Integrability of the terms in the comparison.
  have hQGint := integrable_energy_field hκ hb hν_ae hGL
  have hQkint := fun k => integrable_energy_field hκ hb hν_ae (hgmem k)
  have ha2 : ∀ k, Integrable (fun x => ‖gradient (φ k) x - G x‖ ^ 2) ν := fun k =>
    (hdiffmem k).integrable_sq
  have hag : ∀ k, Integrable (fun x => ‖gradient (φ k) x - G x‖ * ‖G x‖) ν := fun k =>
    (hdiffmem k).integrable_mul hGL.norm
  -- The error term, and its bound by `ε k → 0`.
  set c : ℝ := Real.sqrt (∫ x, ‖G x‖ ^ 2 ∂ν)
  have hag_le : ∀ k, ∫ x, ‖gradient (φ k) x - G x‖ * ‖G x‖ ∂ν ≤
      Real.sqrt (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν) * c := by
    intro k
    have hcs := WeightedSobolev.abs_integral_mul_le_sqrt (hdiffmem k) hGL.norm
    exact (le_abs_self _).trans hcs
  have hk : ∀ k, (∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪gradient (φ k) x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂ν) ≤
      (∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂ν) +
      4 / κ * (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν +
        Real.sqrt (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν) * c) := by
    intro k
    have hEint : Integrable (fun x => 4 / κ * (‖gradient (φ k) x - G x‖ ^ 2 +
        ‖gradient (φ k) x - G x‖ * ‖G x‖)) ν :=
      ((ha2 k).add (hag k)).const_mul (4 / κ)
    have hsum : Integrable (fun x => sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) +
        4 / κ * (‖gradient (φ k) x - G x‖ ^ 2 + ‖gradient (φ k) x - G x‖ * ‖G x‖)) ν :=
      hQGint.add hEint
    have hmono := integral_mono_ae (hQkint k) hsum (hpt k)
    rw [integral_add hQGint hEint, integral_const_mul, integral_add (ha2 k) (hag k)] at hmono
    have hmul : 4 / κ * (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν +
        ∫ x, ‖gradient (φ k) x - G x‖ * ‖G x‖ ∂ν) ≤
        4 / κ * (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν +
          Real.sqrt (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν) * c) :=
      mul_le_mul_of_nonneg_left (by linarith [hag_le k]) (div_nonneg (by norm_num) hκ.le)
    linarith
  -- The error bound tends to zero.
  have hsqrt : Tendsto (fun k => Real.sqrt (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν)) atTop
      (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp he_k
    rw [Real.sqrt_zero] at h
    exact h
  have hε : Tendsto (fun k => 4 / κ * (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν +
      Real.sqrt (∫ x, ‖gradient (φ k) x - G x‖ ^ 2 ∂ν) * c)) atTop (𝓝 0) := by
    have h := ((he_k.add (hsqrt.mul_const c)).const_mul (4 / κ))
    simpa only [zero_add, zero_mul, mul_zero] using h
  -- Passing to the limit.
  have hlim := hε.const_add (∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂ν)
  rw [add_zero] at hlim
  exact le_of_tendsto_of_tendsto hVar hlim
    (Eventually.of_forall fun k => (hsmooth k).trans (hk k))

/-- **Euclidean Brascamp–Lieb inequality** (Euclidean step of Lemma 3.6).

Let `U ⊂ ℝ^d` be nonempty, bounded, open and convex, and let `V ∈ C²(U)` satisfy `D²V ≥ κ I`
for some `κ > 0`. Let `ν = (∫_U e^{-V})⁻¹ e^{-V} dx` on `U`. Then the normalization is finite and
positive, `ν` is a probability measure, and for every `F ∈ H¹(ν)` with weak gradient `G`,

`Var_ν F ≤ ∫ G · (D²V)⁻¹ G dν`.

The right side is written as the variational energy `sup_h (2⟪G, h⟫ - D²V(h, h))`, which equals
the inverse-Hessian energy `⟪G, (D²V)⁻¹ G⟫` at each point of `U`. This identity is part of the
conclusion. The right side is integrable and finite. The only external hypothesis is the
Prékopa–Leindler inequality `Riesz1.External.PrekopaLeindler`. -/
theorem brascamp_lieb_euclidean (hPL : Riesz1.External.PrekopaLeindler) (hd : 0 < d)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hne : U.Nonempty) (hc : Convex ℝ U)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V U) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    let ν := (volume.restrict U).tilted (fun x => -V x)
    (0 < ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))) ∧
    (∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))) < ⊤ ∧
    IsProbabilityMeasure ν ∧
    (∀ (F : EuclideanSpace ℝ (Fin d) → ℝ) (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      WeightedSobolev.IsWeightedH1 ν U F G →
      (∫ x, (F x - ∫ y, F y ∂ν) ^ 2 ∂ν) ≤
        ∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
          2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂ν ∧
      Integrable (fun x => sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
          2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)) ν ∧
      (∫⁻ x, ENNReal.ofReal (sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
          2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)) ∂ν) < ⊤) ∧
    (∀ (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)),
      x ∈ U → ∃ hB : IsCoercive (fderiv ℝ (fderiv ℝ V) x),
        sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
          2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) =
          ⟪G x, hB.continuousLinearEquivOfBilin.symm (G x)⟫_ℝ) := by
  intro ν
  obtain ⟨hZpos, hZfin⟩ := bl_convex_lintegral_bounds hU hc ho hne hV hκ hb
  have hprob : IsProbabilityMeasure ν := bl_convex_isProbabilityMeasure hU hc ho hne hV hκ hb
  refine ⟨hZpos, hZfin, hprob, ?_, ?_⟩
  · intro F G hFG
    have hVar := bl_euclidean_H1 hPL hd hU ho hne hc hV hκ hb hFG
    have hQint := integrable_energy_field (μ := ν) hκ hb
      ((tilted_absolutelyContinuous _ _).ae_le (ae_restrict_mem ho.measurableSet))
      hFG.memLp_grad
    refine ⟨hVar, hQint, ?_⟩
    have hnn : ∀ᵐ x ∂ν, 0 ≤ sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) := by
      filter_upwards [(tilted_absolutelyContinuous _ _).ae_le
        (ae_restrict_mem ho.measurableSet)] with x hx
      exact (bl_variational_energy_bounds (fderiv ℝ (fderiv ℝ V) x) (G x) hκ (hb x hx)).1
    rw [← ofReal_integral_eq_lintegral_ofReal hQint hnn]
    exact ENNReal.ofReal_lt_top
  · intro G x hx
    exact sSup_eq_inverse_hessian hV ho hκ hb hx (G x)

end Riesz1

end

end
