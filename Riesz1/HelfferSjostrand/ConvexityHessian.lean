/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ConvexityHessianDerivative
public import Riesz1.HelfferSjostrand.ConvexityHessianSchur
public import Riesz1.HelfferSjostrand.ConvexityHessianWeak
public import Riesz1.HelfferSjostrand.BLEuclidean
public import Riesz1.HelfferSjostrand.BLEuclideanNormalization
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Riesz1.Frozen.External.PrekopaLeindler

/-!
# Regularized marginal Hessian (part of the proof of Lemma 3.7)

Let `Q ⊆ ℝ^m × ℝ^n` be open and convex with locally bounded fibers, and let `K` be convex and
`C^∞` on `Q`. The fiber integral `J(z) = ∫_{Q_z} e^{-K(z,y)} dy` is positive and twice
differentiable at each `z` with `J(z) > 0`. This file proves the directional form of the
identity

`b · D²(-log J)(z) b = E_z[b · K_zz b] - Var_z(b · K_z) ≥ E_z[b · (K_zz - K_zy K_yy⁻¹ K_yz) b] ≥ 0`,

where `E_z` and `Var_z` are taken under the normalized fiber law `J(z)⁻¹ e^{-K(z,y)} dy` on `Q_z`.

The second derivative of `-log J` is taken along the line `s ↦ z + s b`. For a twice differentiable
function this is the quadratic form `b · D²(-log J)(z) b`.

The middle term is written as the infimum over `a ∈ ℝⁿ` of `D²K(z,y)((b, a), (b, a))`
(`schurEnergy`). Its minimizer is `a = -K_yy⁻¹ K_yz b`, and its value is the Schur complement, as
in the proof of Lemma 3.7.

Hypotheses. The hypotheses on the density `e^{-K}` and its `z`-derivatives are stated
with integrable majorants on compact sets of the projected interior (`hmaj`), and `C²` regularity
in `z` for almost every `y` (`hsmooth`). The uniform lower bound `K_yy ≥ aI` is `hyy`, and the
conditional `H¹` membership of `b · K_z` is `hH1`. The vanishing of the density to every order at
fiber boundaries is not assumed, since the proof does not use it. This is a generalization. The
polytope hypothesis is replaced by openness and convexity of `Q`, and `K ∈ C^∞` is used as stated.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff InnerProductSpace

namespace Riesz1.ConvexityHessian

variable {m n : ℕ}

variable {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
  {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}

/-- The integral against the normalized fiber law. -/
theorem integral_fiberLaw_eq (z : EuclideanSpace ℝ (Fin m))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ y, g y ∂(fiberLaw Q K z) =
      (fiberIntegral Q K z)⁻¹ * ∫ y in fiber Q z, Real.exp (-K (z, y)) * g y := by
  unfold fiberLaw fiberIntegral
  rw [integral_tilted]
  simp_rw [smul_eq_mul, div_eq_inv_mul, mul_assoc]
  rw [integral_const_mul]

/-- The integral of the indicator of a product function over a slice is the fiber integral. -/
theorem integral_indicator_slice (hQo : IsOpen Q) (G : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    ∫ y, Q.indicator G (z, y) = ∫ y in fiber Q z, G (z, y) := by
  rw [← integral_indicator (isOpen_fiber hQo z).measurableSet]
  rfl

theorem contDiffOn_fiber_fderiv (hQo : IsOpen Q) (hK : ContDiffOn ℝ ∞ K Q)
    (z : EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin m)) :
    ContDiffOn ℝ ∞ (fun y => fderiv ℝ K (z, y) (b, 0)) (fiber Q z) := by
  have hdK : ContDiffOn ℝ ∞ (fun q => fderiv ℝ K q (b, 0)) Q :=
    (hK.fderiv_of_isOpen hQo (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hφ : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin n) => (z, y)) :=
    contDiff_const.prodMk contDiff_id
  exact hdK.comp hφ.contDiffOn (fun y hy => hy)


/-- **Regularized marginal Hessian** (part of the proof of Lemma 3.7), in the
directional form: for `b ∈ ℝ^m`, the second derivative of `-log J` at `z` in direction `b` is
`E_z[b · K_zz b] - Var_z(b · K_z)`, the expectation and variance being taken under the fiber law
`J(z)⁻¹ e^{-K(z,y)} dy` on `Q_z`. The Schur energy `E_z[b · (K_zz - K_zy K_yy⁻¹ K_yz) b]`
(the infimum over `a` in `schurEnergy`) lies between `0` and that difference. -/
theorem convexity_exterior_hessian (hPL : External.PrekopaLeindler) (hn : 0 < n)
    (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hloc : ∀ z ∈ Prod.fst '' Q, ∃ U ∈ 𝓝 z, Bornology.IsBounded (Q ∩ (U ×ˢ univ)))
    (hK : ContDiffOn ℝ ∞ K Q) (hKc : ConvexOn ℝ Q K)
    (hmaj : ∀ C : Set (EuclideanSpace ℝ (Fin m)), IsCompact C → C ⊆ Prod.fst '' Q →
      ∃ M₀ M₁ M₂ : EuclideanSpace ℝ (Fin n) → ℝ, Integrable M₀ ∧ Integrable M₁ ∧
        Integrable M₂ ∧
        ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ C,
          |zeroExtension Q K (w, y)| ≤ M₀ y ∧
          ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y ∧
          ‖fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) w‖ ≤ M₂ y)
    (hsmooth : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ContDiff ℝ 2 (fun w => zeroExtension Q K (w, y)))
    {a : ℝ} (ha : 0 < a)
    (hyy : ∀ p ∈ Q, ∀ h : EuclideanSpace ℝ (Fin n),
      a * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ K) p (0, h) (0, h))
    (b : EuclideanSpace ℝ (Fin m)) {z : EuclideanSpace ℝ (Fin m)}
    (hz : 0 < fiberIntegral Q K z)
    (hH1 : ∃ G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      Riesz1.WeightedSobolev.IsWeightedH1 (fiberLaw Q K z) (fiber Q z)
        (fun y => fderiv ℝ K (z, y) (b, 0)) G) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => -Real.log (fiberIntegral Q K (z + s • b))) t) 0 =
        (∫ y, fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) ∂(fiberLaw Q K z)) -
          ∫ y, (fderiv ℝ K (z, y) (b, 0) -
            ∫ y', fderiv ℝ K (z, y') (b, 0) ∂(fiberLaw Q K z)) ^ 2 ∂(fiberLaw Q K z) ∧
      ∫ y, schurEnergy K z b y ∂(fiberLaw Q K z) ≤
        (∫ y, fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) ∂(fiberLaw Q K z)) -
          ∫ y, (fderiv ℝ K (z, y) (b, 0) -
            ∫ y', fderiv ℝ K (z, y') (b, 0) ∂(fiberLaw Q K z)) ^ 2 ∂(fiberLaw Q K z) ∧
      0 ≤ ∫ y, schurEnergy K z b y ∂(fiberLaw Q K z) := by
  have hK2 : ContDiffOn ℝ 2 K Q := hK.of_le (by simp)
  -- The point `z` projects into `Q`, since the fiber integral is positive.
  have hzP : z ∈ Prod.fst '' Q := by
    by_contra hnot
    have hempty : fiber Q z = ∅ := by
      ext y
      simp only [mem_empty_iff_false, iff_false]
      exact fun hy => hnot ⟨(z, y), hy, rfl⟩
    simp [fiberIntegral, hempty] at hz
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ Prod.fst '' Q := by
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (isOpenMap_fst Q hQo) z hzP
    exact ⟨ρ / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = r / (‖b‖ + 1) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hε : ∀ s ∈ ball (0 : ℝ) ε, z + s • b ∈ closedBall z r := by
    intro s hs
    rw [mem_ball, Real.dist_eq, sub_zero, hεdef, lt_div_iff₀ (by positivity)] at hs
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    nlinarith [abs_nonneg s, norm_nonneg b]
  have hpi : ∀ s ∈ ball (0 : ℝ) ε, z + s • b ∈ Prod.fst '' Q := fun s hs => hr (hε s hs)
  obtain ⟨M₀, M₁, M₂, hM₀, hM₁, hM₂, hmaj'⟩ :=
    hmaj (closedBall z r) (isCompact_closedBall z r) hr
  have hmaj0 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      |zeroExtension Q K (w, y)| ≤ M₀ y := hmaj'.mono fun y hy w hw => (hy w hw).1
  have hmaj1 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      ‖fderiv ℝ (fun w' => zeroExtension Q K (w', y)) w‖ ≤ M₁ y :=
    hmaj'.mono fun y hy w hw => (hy w hw).2.1
  have hmaj2 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ w ∈ closedBall z r,
      ‖fderiv ℝ (fderiv ℝ (fun w' => zeroExtension Q K (w', y))) w‖ ≤ M₂ y :=
    hmaj'.mono fun y hy w hw => (hy w hw).2.2
  -- The one-variable derivatives of `j(s) = ∫ zeroExtension (z + s b, y) dy`.
  have hj1 : ∀ s ∈ ball (0 : ℝ) ε, HasDerivAt (fun s : ℝ => ∫ y, zeroExtension Q K (z + s • b, y))
      (∫ y, firstCoef Q K b (z + s • b, y)) s := fun s hs =>
    hasDerivAt_integral_zeroExtension_line b hQo hQc hK2 hr hε hsmooth hM₀ hM₁ hmaj0 hmaj1 hs
  have hj2 : HasDerivAt (fun s : ℝ => ∫ y, firstCoef Q K b (z + s • b, y))
      (∫ y, secondCoef Q K b (z, y)) 0 := by
    have h := hasDerivAt_integral_deriv_zeroExtension_line b hQo hQc hK2 hεpos hr hε hsmooth
      hM₁ hM₂ hmaj1 hmaj2
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : ℝ) hεpos] with s hs
    refine integral_congr_ae ?_
    exact (ae_hasDerivAt_zeroExtension_line b hQo hQc hK2 z (hpi s hs)).mono
      fun y hy => hy.deriv.symm
  -- The Hessian of `-log j` at `0` in direction `b`.
  have hlog := deriv_deriv_neg_log_zero
    (j := fun s : ℝ => ∫ y, zeroExtension Q K (z + s • b, y))
    (j' := fun s : ℝ => ∫ y, firstCoef Q K b (z + s • b, y))
    (j'' := ∫ y, secondCoef Q K b (z, y))
    (Filter.eventually_of_mem (ball_mem_nhds (0 : ℝ) hεpos) fun s hs => hj1 s hs) hj2
    (by
      have hJ0 : ∫ y, zeroExtension Q K (z + (0 : ℝ) • b, y) = fiberIntegral Q K z := by
        rw [zero_smul, add_zero, fiberIntegral_eq_integral hQo]
      show 0 < ∫ y, zeroExtension Q K (z + (0 : ℝ) • b, y)
      rw [hJ0]
      exact hz)
  obtain ⟨G, hFG⟩ := hH1
  have hJ0 : ∫ y, zeroExtension Q K (z + (0 : ℝ) • b, y) = fiberIntegral Q K z := by
    rw [zero_smul, add_zero, fiberIntegral_eq_integral hQo]
  have hJne : fiberIntegral Q K z ≠ 0 := hz.ne'
  -- Integrability of the fiber integrand and of the second-order coefficient.
  have hzE : Integrable (fun y => zeroExtension Q K (z, y)) volume :=
    Integrable.mono' hM₀ (aestronglyMeasurable_zeroExtension_slice hQo hK2 z)
      (by
        filter_upwards [hmaj0] with y hy
        rw [Real.norm_eq_abs]
        exact hy z (mem_closedBall_self hr0.le))
  have hexpF : IntegrableOn (fun y => Real.exp (-K (z, y))) (fiber Q z) :=
    (integrable_indicator_iff (isOpen_fiber hQo z).measurableSet).1 hzE
  have hsecond : Integrable (fun y => secondCoef Q K b (z, y)) volume := by
    refine Integrable.mono' ((hM₂.mul_const ‖b‖).mul_const ‖b‖)
      (aestronglyMeasurable_secondCoef b hQo hK2 z) ?_
    filter_upwards [hmaj2, ae_hasDerivAt_deriv_zeroExtension_line b hQo hQc hK2 z hzP,
      hsmooth] with y hy2 hy4 hy3
    rw [← hy4.deriv]
    exact norm_deriv_deriv_comp_line_le (fun w => zeroExtension Q K (w, y)) z b 0 hy3
      (hy2 _ (hε 0 (mem_ball_self hεpos)))
  have hFH : IntegrableOn (fun y => Real.exp (-K (z, y)) *
      (fderiv ℝ K (z, y) (b, 0) ^ 2 - fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0)))
      (fiber Q z) :=
    (integrable_indicator_iff (isOpen_fiber hQo z).measurableSet).1 hsecond
  -- Integrability under the fiber law.
  have hF2 : Integrable (fun y => fderiv ℝ K (z, y) (b, 0) ^ 2) (fiberLaw Q K z) :=
    hFG.memLp_fun.integrable_sq
  have hFH_ν : Integrable (fun y => fderiv ℝ K (z, y) (b, 0) ^ 2 -
      fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0)) (fiberLaw Q K z) := by
    show Integrable _ ((volume.restrict (fiber Q z)).tilted fun y => -K (z, y))
    refine (integrable_tilted_iff ?_ _).2 ?_
    · exact hexpF
    · simp only [smul_eq_mul]
      exact hFH
  have hH_ν : Integrable (fun y => fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0))
      (fiberLaw Q K z) :=
    (hF2.sub hFH_ν).congr (Eventually.of_forall fun y => by simp)
  -- The first and second derivatives of `j` at `0`, in terms of the fiber law.
  have hfirst_val : ∫ y, firstCoef Q K b (z + (0 : ℝ) • b, y) =
      -(fiberIntegral Q K z * ∫ y, fderiv ℝ K (z, y) (b, 0) ∂(fiberLaw Q K z)) := by
    rw [zero_smul, add_zero]
    have e1 : ∫ y, firstCoef Q K b (z, y) =
        ∫ y in fiber Q z, -(Real.exp (-K (z, y)) * fderiv ℝ K (z, y) (b, 0)) :=
      integral_indicator_slice hQo (fun q => -(Real.exp (-K q) * fderiv ℝ K q (b, 0))) z
    have e2 := integral_fiberLaw_eq (Q := Q) (K := K) z (fun y => fderiv ℝ K (z, y) (b, 0))
    beta_reduce at e2
    rw [e1, integral_neg, e2, ← mul_assoc, mul_inv_cancel₀ hJne, one_mul]
  have hsecond_val : ∫ y, secondCoef Q K b (z, y) = fiberIntegral Q K z *
      ∫ y, (fderiv ℝ K (z, y) (b, 0) ^ 2 - fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0))
        ∂(fiberLaw Q K z) := by
    have e1 : ∫ y, secondCoef Q K b (z, y) = ∫ y in fiber Q z, Real.exp (-K (z, y)) *
        (fderiv ℝ K (z, y) (b, 0) ^ 2 - fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0)) :=
      integral_indicator_slice hQo (fun q => Real.exp (-K q) *
        (fderiv ℝ K q (b, 0) ^ 2 - fderiv ℝ (fderiv ℝ K) q (b, 0) (b, 0))) z
    have e2 := integral_fiberLaw_eq (Q := Q) (K := K) z (fun y =>
      fderiv ℝ K (z, y) (b, 0) ^ 2 - fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0))
    beta_reduce at e2
    rw [e1, e2, ← mul_assoc, mul_inv_cancel₀ hJne, one_mul]
  -- The Brascamp–Lieb inequality on the fiber.
  have hU : IsOpen (fiber Q z) := isOpen_fiber hQo z
  have hUb : Bornology.IsBounded (fiber Q z) := isBounded_fiber hloc hzP
  have hUc : Convex ℝ (fiber Q z) := convex_fiber hQc z
  have hUne : (fiber Q z).Nonempty := fiber_nonempty hzP
  have hV2 : ContDiffOn ℝ 2 (fun y => K (z, y)) (fiber Q z) :=
    hK2.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => hy)
  have hbV : ∀ x ∈ fiber Q z, ∀ h : EuclideanSpace ℝ (Fin n),
      a * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun y => K (z, y))) x h h := fun x hx h => by
    rw [fderiv_fderiv_fiber hQo hK2 hx h]
    exact hyy _ hx h
  have hBL := brascamp_lieb_euclidean hPL hn hUb hU hUne hUc hV2 ha hbV
  have : IsProbabilityMeasure (fiberLaw Q K z) := hBL.2.2.1
  obtain ⟨hVarBL, hSigInt, -⟩ := hBL.2.2.2.1 (fun y => fderiv ℝ K (z, y) (b, 0)) G hFG
  beta_reduce at hVarBL hSigInt
  -- The gradient of the fiber function is the weak gradient, almost everywhere.
  have hexp : Integrable (fun x => Real.exp (-(fun y => K (z, y)) x))
      (volume.restrict (fiber Q z)) :=
    bl_convex_exp_integrableOn hUb hUc hU hUne hV2 ha hbV
  have hweak := ae_gradient_eq_of_isWeightedH1_of_continuousOn (V := fun y => K (z, y)) hU hexp
    hV2.continuousOn (contDiffOn_fiber_fderiv hQo hK z b) hFG
  have hae_mem : ∀ᵐ y ∂(fiberLaw Q K z), y ∈ fiber Q z :=
    (tilted_absolutelyContinuous _ _).ae_le (ae_restrict_mem hU.measurableSet)
  have hSig : ∀ᵐ y ∂(fiberLaw Q K z), sSup (Set.range fun h : EuclideanSpace ℝ (Fin n) =>
        2 * ⟪G y, h⟫_ℝ - fderiv ℝ (fderiv ℝ (fun y' => K (z, y'))) y h h) =
      fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) - schurEnergy K z b y := by
    filter_upwards [hweak, hae_mem] with y hGy hyU
    refine sSup_fiber_energy_eq hQo hQc hKc hK2 hyU b (G y) fun h => ?_
    rw [hGy]
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply]
  have hS_int : Integrable (fun y => schurEnergy K z b y) (fiberLaw Q K z) := by
    refine (hH_ν.sub hSigInt).congr ?_
    filter_upwards [hSig] with y hy
    simp only [Pi.sub_apply]
    rw [hy]
    ring
  have hS_nonneg : 0 ≤ ∫ y, schurEnergy K z b y ∂(fiberLaw Q K z) :=
    integral_nonneg_of_ae (hae_mem.mono fun y hy => schurEnergy_nonneg hQo hQc hKc hK2 hy b)
  -- The variance bound, with the energy identified with `H - S`.
  have hBL_le : ∫ y, (fderiv ℝ K (z, y) (b, 0) - ∫ y', fderiv ℝ K (z, y') (b, 0)
      ∂(fiberLaw Q K z)) ^ 2 ∂(fiberLaw Q K z) ≤
      ∫ y, (fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) - schurEnergy K z b y)
        ∂(fiberLaw Q K z) :=
    hVarBL.trans_eq (integral_congr_ae hSig)
  rw [integral_sub hH_ν hS_int] at hBL_le
  -- The Hessian of `-log J`.
  have hVar := Riesz1.WeightedSobolev.integral_sub_mean_sq hFG.memLp_fun
  have hsub := integral_sub hF2 hH_ν
  have hmain : deriv (fun t : ℝ => deriv (fun s : ℝ => -Real.log (∫ y,
      zeroExtension Q K (z + s • b, y))) t) 0 =
        (∫ y, fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) ∂(fiberLaw Q K z)) -
          ∫ y, (fderiv ℝ K (z, y) (b, 0) -
            ∫ y', fderiv ℝ K (z, y') (b, 0) ∂(fiberLaw Q K z)) ^ 2 ∂(fiberLaw Q K z) := by
    have h := hlog
    beta_reduce at h
    rw [hJ0, hfirst_val, hsecond_val, hsub] at h
    rw [h, hVar]
    field_simp
    ring
  have hJ' : ∀ s : ℝ, fiberIntegral Q K (z + s • b) = ∫ y, zeroExtension Q K (z + s • b, y) :=
    fun s => fiberIntegral_eq_integral hQo _
  simp only [hJ']
  refine ⟨hmain, ?_, hS_nonneg⟩
  linarith


/-- The Schur energy is the Hessian quadratic form minus the energy of the inverse `yy`-Hessian:
`inf_a D²K(z,y)((b, a), (b, a)) = D²K(z,y)((b,0),(b,0)) - ⟪g, (D²_yy K)⁻¹ g⟫`, where
`g = ∇_y (DK(z,·)(b,0))(y)` is the gradient of the fiber function and `(D²_yy K)⁻¹` is the inverse
of the coercive `yy`-block, which exists by the bound `hyy`. This is the Schur complement
`b · (K_zz - K_zy K_yy⁻¹ K_yz) b`. -/
theorem schurEnergy_eq_inverse_hessian (hQo : IsOpen Q) (hQc : Convex ℝ Q)
    (hKc : ConvexOn ℝ Q K) (hK : ContDiffOn ℝ 2 K Q) {a : ℝ} (ha : 0 < a)
    (hyy : ∀ p ∈ Q, ∀ h : EuclideanSpace ℝ (Fin n),
      a * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ K) p (0, h) (0, h))
    {z : EuclideanSpace ℝ (Fin m)} {y : EuclideanSpace ℝ (Fin n)} (hy : (z, y) ∈ Q)
    (b : EuclideanSpace ℝ (Fin m)) :
    ∃ hB : IsCoercive (fderiv ℝ (fderiv ℝ (fun y' => K (z, y'))) y),
      schurEnergy K z b y = fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) -
        ⟪gradient (fun y' => fderiv ℝ K (z, y') (b, 0)) y,
          hB.continuousLinearEquivOfBilin.symm
            (gradient (fun y' => fderiv ℝ K (z, y') (b, 0)) y)⟫_ℝ := by
  have hU : IsOpen (fiber Q z) := isOpen_fiber hQo z
  have hyU : y ∈ fiber Q z := hy
  have hV2 : ContDiffOn ℝ 2 (fun y' => K (z, y')) (fiber Q z) :=
    hK.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y' hy' => hy')
  have hbV : ∀ x ∈ fiber Q z, ∀ h : EuclideanSpace ℝ (Fin n),
      a * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun y' => K (z, y'))) x h h := fun x hx h => by
    rw [fderiv_fderiv_fiber hQo hK hx h]
    exact hyy _ hx h
  obtain ⟨hB, hs⟩ := sSup_eq_inverse_hessian hV2 hU ha hbV hyU
    (gradient (fun y' => fderiv ℝ K (z, y') (b, 0)) y)
  refine ⟨hB, ?_⟩
  have hgrad : ∀ h : EuclideanSpace ℝ (Fin n), ⟪gradient (fun y' => fderiv ℝ K (z, y') (b, 0)) y, h⟫_ℝ =
      fderiv ℝ (fun y' => fderiv ℝ K (z, y') (b, 0)) y h := by
    intro h
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply]
  have hsup := sSup_fiber_energy_eq hQo hQc hKc hK hyU b
    (gradient (fun y' => fderiv ℝ K (z, y') (b, 0)) y) hgrad
  rw [hs] at hsup
  linarith

end Riesz1.ConvexityHessian

end

end
