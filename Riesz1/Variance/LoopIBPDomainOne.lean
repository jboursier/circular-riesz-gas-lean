/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPDomain
public import Riesz1.Variance.LoopIBPUniform
public import Riesz1.Variance.LoopIBPHS
public import Riesz1.HelfferSjostrand.VectorEnergySobolev

/-!
# Domain clause of Proposition 5.5 for one particle

For `N = 1` the quotient Gibbs law is the uniform law on the circle, and the Helffer–Sjöstrand
integration by parts used for `N ≥ 2` needs `2 ≤ N`. This file proves the Neumann identity for the
field potential `Φ_{ψ,a}` directly. On smooth periodic test functions it is the one-particle
integration by parts `integral_mul_loopOperatorPotential_one`. It extends to the whole Sobolev space
by density of the smooth core.

## Main results

* `loopPhi_mem_neumannGraph_one`: the pair `(Φ, 𝓛Φ)` lies in the Neumann graph for `N = 1`.
* `loopPhi_hsNeumannOperator_one`: the domain and value clause for `N = 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The one-particle chamber is the whole line, so every smooth core element is smooth on `ℝ`. -/
theorem hsChamber_one : hsChamber 1 = univ := by
  refine Set.eq_univ_of_forall fun x => ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [(fin_one_pnat_eq_zero i).trans (fin_one_pnat_eq_zero j).symm] at hij
    exact absurd hij (lt_irrefl _)
  · rw [fin_one_pnat_eq_zero i]
    show x 0 < x 0 + 1
    linarith

/-- A smooth core element for one particle is smooth on the whole Euclidean space. -/
theorem contDiff_of_hsSmoothCore_one (K : hsSmoothCore 1) : ContDiff ℝ ∞ K.1 := by
  obtain ⟨-, U, -, hsub, hcd⟩ := K.property
  rw [← contDiffOn_univ]
  refine hcd.mono ?_
  rw [← closure_univ, ← hsChamber_one]
  exact (closure_mono (subset_refl _)).trans hsub

/-- The one-particle lift of a smooth core element is torus smooth. -/
theorem isTorusSmooth_one_of_hsSmoothCore (K : hsSmoothCore 1) :
    IsTorusSmooth (fun x : Fin ((1 : ℕ+) : ℕ) → ℝ => K.1 (WithLp.toLp 2 x)) := by
  refine ⟨?_, fun k x => ?_⟩
  · exact (contDiff_of_hsSmoothCore_one K).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin ((1 : ℕ+) : ℕ) => ℝ)).symm.contDiff
  · have htr : (WithLp.toLp 2 (Function.update x k (x k + 1)) : HsEuclidean 1) =
        hsTranslate ((1 : ℤ) : ℝ) (WithLp.toLp 2 x) := by
      ext i
      have hik : i = k := (fin_one_pnat_eq_zero i).trans (fin_one_pnat_eq_zero k).symm
      subst hik
      simp only [hsTranslate, WithLp.ofLp_toLp, Int.cast_one]
      exact Function.update_self _ _ _
    dsimp only
    rw [htr]
    exact K.property.1 1 (WithLp.toLp 2 x)

/-- The gradient of a smooth core element is its gradient on the lift, almost everywhere. -/
theorem hsSobolevGradient_ofSmooth_ae {N : ℕ+} (μ : Measure (HsConfiguration N))
    [IsFiniteMeasure μ] (φ : hsSmoothCore N) :
    (hsSobolevGradient μ (hsSobolevOfSmooth μ φ) : HsConfiguration N → HsEuclidean N) =ᵐ[μ]
      hsSmoothGradient φ :=
  (φ.property.memLp_gradient μ).coeFn_toLp

/-- The value of a smooth core element is its lift, almost everywhere. -/
theorem hsSobolevValue_ofSmooth_ae {N : ℕ+} (μ : Measure (HsConfiguration N))
    [IsFiniteMeasure μ] (φ : hsSmoothCore N) :
    (hsSobolevValue μ (hsSobolevOfSmooth μ φ) : HsConfiguration N → ℝ) =ᵐ[μ]
      hsSmoothValue φ.1 := by
  rw [hsSobolevValue_hsSobolevOfSmooth]
  exact MemLp.coeFn_toLp _

/-- The Euclidean pairing of the gradients of the lifted potential and of a smooth function is the
coordinate pairing `∇F · ∇Φ` of the torus functions at the ordered point. -/
theorem inner_gradient_loopHS_eq_gradDot (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (N : ℕ+) (K : HsEuclidean N → ℝ)
    (hK : ContDiff ℝ ∞ K) (y : HsEuclidean N) :
    inner ℝ (gradient (loopHS ℓ a ψ N) y) (gradient K y) =
      gradDotPotential (fun x : Fin (N : ℕ) → ℝ => K (WithLp.toLp 2 x))
        (loopScalePotential ℓ a ψ (N : ℕ)) (WithLp.ofLp y) := by
  rw [inner_gradient_eq_sum_hsPartial]
  unfold gradDotPotential
  refine Finset.sum_congr rfl fun k _ => ?_
  have hL : DifferentiableAt ℝ (loopHS ℓ a ψ N) y :=
    (contDiff_loopHS ℓ a ψ hψ N).differentiable (by simp) y
  have hKd : DifferentiableAt ℝ K y := hK.differentiable (by simp) y
  rw [hsPartial_eq_partialDeriv (F := loopHS ℓ a ψ N)
      (G := loopScalePotential ℓ a ψ (N : ℕ)) univ_mem (fun z _ => rfl) hL k,
    hsPartial_eq_partialDeriv (F := K) (G := fun x : Fin (N : ℕ) → ℝ => K (WithLp.toLp 2 x))
      univ_mem (fun z _ => by simp) hKd k]
  ring

/-- Integration by parts for one particle: `E[F 𝓛Φ] = E[∇F · ∇Φ]` for every torus smooth `F`. The
mean of `𝓛Φ` is zero, so the covariance of clause 2 is the plain expectation of the product. -/
theorem integral_mul_loopOperatorPotential_one (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (F : (Fin 1 → ℝ) → ℝ)
    (hF : IsTorusSmooth F) :
    ∫ X : Configuration 1, F X.val * loopOperatorPotential P 1 ℓ a ψ X ∂gibbsMeasure P 1 =
      ∫ X : Configuration 1, gradDotPotential F (loopScalePotential ℓ a ψ 1) X.val
        ∂gibbsMeasure P 1 := by
  obtain ⟨⟨hL1, hmz⟩, hcov, -⟩ := loop_ibp_one P ℓ a ψ hψ
  rw [← hcov F hF]
  obtain ⟨M, hM⟩ := exists_bound_of_periodic (N := 1) hF.1.continuous hF.2
  have hLint : Integrable (loopOperatorPotential P 1 ℓ a ψ) (gibbsMeasure P 1) :=
    hL1.integrable one_le_two
  have hint : Integrable (fun X : Configuration 1 => F X.val * loopOperatorPotential P 1 ℓ a ψ X)
      (gibbsMeasure P 1) := by
    refine Integrable.mono' (hLint.norm.const_mul M) ?_ (Eventually.of_forall fun X => ?_)
    · exact ((hF.1.continuous.comp continuous_subtype_val).aestronglyMeasurable).mul
        hL1.aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM X.val) (abs_nonneg _)
  unfold gibbsCov
  simp only [hmz, sub_zero]
  have hsplit : ∀ X : Configuration 1,
      (F X.val - ∫ Y, F Y.val ∂gibbsMeasure P 1) * loopOperatorPotential P 1 ℓ a ψ X =
        F X.val * loopOperatorPotential P 1 ℓ a ψ X -
          (∫ Y, F Y.val ∂gibbsMeasure P 1) * loopOperatorPotential P 1 ℓ a ψ X :=
    fun X => by ring
  simp only [hsplit]
  rw [integral_sub hint (hLint.const_mul _), integral_const_mul, hmz, mul_zero, sub_zero]

/-- The Neumann identity for one particle on a smooth core element `K`: the Dirichlet form of
`Φ` against `K` is the `L²` pairing of `𝓛Φ` with `K`. -/
theorem neumann_identity_one (P : Parameters) (hPL : External.PrekopaLeindler)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (K : hsSmoothCore 1) :
    hsDirichletForm (rieszProb P 1 : Measure (HsConfiguration 1))
        (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1))
          (loopCore ℓ a ψ hψ hmean 1))
        (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1)) K) =
      inner ℝ ((memLp_loopLHS P hPL ℓ a ψ hψ 1).toLp
          (fun x : HsConfiguration 1 => loopLHS P 1 ℓ a ψ (hsLiftPoint 1 x)))
        (hsSobolevValue (rieszProb P 1 : Measure (HsConfiguration 1))
          (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1)) K)) := by
  have hK : ContDiff ℝ ∞ K.1 := contDiff_of_hsSmoothCore_one K
  have hL : hsDirichletForm (rieszProb P 1 : Measure (HsConfiguration 1))
        (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1))
          (loopCore ℓ a ψ hψ hmean 1))
        (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1)) K) =
      ∫ X : Configuration 1,
        gradDotPotential (fun x : Fin ((1 : ℕ+) : ℕ) → ℝ => K.1 (WithLp.toLp 2 x))
          (loopScalePotential ℓ a ψ 1) X.val ∂gibbsMeasure P 1 := by
    rw [hsDirichletForm_eq_integral]
    have hae : (fun x : HsConfiguration 1 =>
          inner ℝ (hsSobolevGradient (rieszProb P 1 : Measure (HsConfiguration 1))
              (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1))
                (loopCore ℓ a ψ hψ hmean 1)) x)
            (hsSobolevGradient (rieszProb P 1 : Measure (HsConfiguration 1))
              (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1)) K) x)) =ᵐ[
          (rieszProb P 1 : Measure (HsConfiguration 1))]
        fun x => (fun y : HsEuclidean 1 =>
          gradDotPotential (fun z : Fin ((1 : ℕ+) : ℕ) → ℝ => K.1 (WithLp.toLp 2 z))
            (loopScalePotential ℓ a ψ 1) (WithLp.ofLp y)) (hsLiftPoint 1 x) := by
      filter_upwards [hsSobolevGradient_ofSmooth_ae (rieszProb P 1 : Measure (HsConfiguration 1))
          (loopCore ℓ a ψ hψ hmean 1),
        hsSobolevGradient_ofSmooth_ae (rieszProb P 1 : Measure (HsConfiguration 1)) K]
        with x hx1 hx2
      rw [hx1, hx2]
      exact inner_gradient_loopHS_eq_gradDot ℓ a ψ hψ 1 K.1 hK (hsLiftPoint 1 x)
    refine (integral_congr_ae hae).trans
      ((integral_rieszProb_liftPoint P 1 (fun y : HsEuclidean 1 =>
        gradDotPotential (fun z : Fin ((1 : ℕ+) : ℕ) → ℝ => K.1 (WithLp.toLp 2 z))
          (loopScalePotential ℓ a ψ 1) (WithLp.ofLp y))).trans ?_)
    exact integral_congr_ae (Eventually.of_forall fun X => rfl)
  have hR : inner ℝ ((memLp_loopLHS P hPL ℓ a ψ hψ 1).toLp
          (fun x : HsConfiguration 1 => loopLHS P 1 ℓ a ψ (hsLiftPoint 1 x)))
        (hsSobolevValue (rieszProb P 1 : Measure (HsConfiguration 1))
          (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1)) K)) =
      ∫ X : Configuration 1, K.1 (WithLp.toLp 2 X.val) *
        loopOperatorPotential P 1 ℓ a ψ X ∂gibbsMeasure P 1 := by
    rw [L2.inner_def]
    have hae : (fun x : HsConfiguration 1 =>
          inner ℝ ((memLp_loopLHS P hPL ℓ a ψ hψ 1).toLp
              (fun y : HsConfiguration 1 => loopLHS P 1 ℓ a ψ (hsLiftPoint 1 y)) x)
            (hsSobolevValue (rieszProb P 1 : Measure (HsConfiguration 1))
              (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1)) K) x)) =ᵐ[
          (rieszProb P 1 : Measure (HsConfiguration 1))]
        fun x => (fun y : HsEuclidean 1 => loopLHS P 1 ℓ a ψ y * K.1 y) (hsLiftPoint 1 x) := by
      filter_upwards [((memLp_loopLHS P hPL ℓ a ψ hψ 1).coeFn_toLp),
        hsSobolevValue_ofSmooth_ae (rieszProb P 1 : Measure (HsConfiguration 1)) K]
        with x hx1 hx2
      rw [hx1, hx2]
      simp [hsSmoothValue, RCLike.inner_apply, mul_comm]
    refine (integral_congr_ae hae).trans
      ((integral_rieszProb_liftPoint P 1 (fun y : HsEuclidean 1 =>
        loopLHS P 1 ℓ a ψ y * K.1 y)).trans ?_)
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    dsimp only
    rw [loopLHS_eq_loopOperatorPotential P 1 ℓ a ψ hψ X]
    ring
  rw [hL, hR, integral_mul_loopOperatorPotential_one P ℓ a ψ hψ
    (fun x : Fin ((1 : ℕ+) : ℕ) → ℝ => K.1 (WithLp.toLp 2 x)) (isTorusSmooth_one_of_hsSmoothCore K)]
  rfl

/-- The field potential `Φ_{ψ,a}` lies in the Neumann graph of the quotient Gibbs law for one
particle, paired with the `L²` class of `𝓛Φ`. -/
theorem loopPhi_mem_neumannGraph_one (P : Parameters) (hPL : External.PrekopaLeindler)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1))
        (loopCore ℓ a ψ hψ hmean 1),
      (memLp_loopLHS P hPL ℓ a ψ hψ 1).toLp
        (fun x : HsConfiguration 1 => loopLHS P 1 ℓ a ψ (hsLiftPoint 1 x))) ∈
      hsNeumannGraph (rieszProb P 1 : Measure (HsConfiguration 1)) := by
  have key : ∀ h : HsSobolev (rieszProb P 1 : Measure (HsConfiguration 1)),
      hsDirichletForm (rieszProb P 1 : Measure (HsConfiguration 1))
          (hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1))
            (loopCore ℓ a ψ hψ hmean 1)) h =
        inner ℝ ((memLp_loopLHS P hPL ℓ a ψ hψ 1).toLp
            (fun x : HsConfiguration 1 => loopLHS P 1 ℓ a ψ (hsLiftPoint 1 x)))
          (hsSobolevValue (rieszProb P 1 : Measure (HsConfiguration 1)) h) := by
    intro h₀
    refine DenseRange.induction_on (denseRange_hsSobolevOfSmooth
      (rieszProb P 1 : Measure (HsConfiguration 1))) h₀ ?_ ?_
    · exact isClosed_eq (continuous_hsDirichletForm _ _)
        (continuous_const.inner (hsSobolevValue _).continuous)
    · exact fun K => neumann_identity_one P hPL ℓ a ψ hψ hmean K
  exact key

/-- **Domain and value clause for one particle.** The field potential `Φ_{ψ,a}` lies in the scalar
Neumann domain of the quotient Gibbs law for `N = 1`, and the Neumann operator at `Φ` is the `L²`
class of `𝓛Φ`. -/
theorem loopPhi_hsNeumannOperator_one (P : Parameters) (hPL : External.PrekopaLeindler)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    ∃ hΦ : hsSobolevOfSmooth (rieszProb P 1 : Measure (HsConfiguration 1))
        (loopCore ℓ a ψ hψ hmean 1) ∈
          hsNeumannDomain (rieszProb P 1 : Measure (HsConfiguration 1)),
      hsNeumannOperator (rieszPairs P 1)
          (hsRieszPairPotentials_curvature_pos 1 P.property.1 (parametersExponent P)) ⟨_, hΦ⟩ =
        (memLp_loopLHS P hPL ℓ a ψ hψ 1).toLp
          (fun x : HsConfiguration 1 => loopLHS P 1 ℓ a ψ (hsLiftPoint 1 x)) := by
  have hG := loopPhi_mem_neumannGraph_one P hPL ℓ a ψ hψ hmean
  exact ⟨(hsNeumannDomain_iff _ _).mpr ⟨_, hG⟩, (hsNeumannOperator_eq_iff _ _ _ _).mpr hG⟩

end Riesz1

end

end
