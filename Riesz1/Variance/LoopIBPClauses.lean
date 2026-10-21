/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPLimit
public import Riesz1.Variance.LoopIBPPeriodic

/-!
# Integration identities for the diagonal field, clauses 1 and 2 for `N ≥ 2`

Proposition 5.5, clauses 1 and 2, for `N ≥ 2`: the operator
`𝓛Φ = β ∇H_N · ∇Φ − ΔΦ` is square integrable with mean zero, and its covariance with a smooth
function `F` on the configuration torus is the Dirichlet pairing `E[∇F · ∇Φ]`.

The proof applies `loopLHS_integral_eq` to the constant function `1` (mean zero) and to the lift of
`F` (covariance). Square integrability follows from the uniform bound by the power sum of gaps.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The lift of a torus-smooth function is a smooth function on the Euclidean lift. -/
theorem contDiff_torusLift {N : ℕ+} {F : (Fin (N : ℕ) → ℝ) → ℝ} (hF : IsTorusSmooth F) :
    ContDiff ℝ ∞ (fun x : HsEuclidean N => F (WithLp.ofLp x)) :=
  hF.1.comp (contDiff_pi.mpr fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

/-- The lift of a torus-smooth function is periodic under integer translations. -/
theorem torusLift_periodic {N : ℕ+} {F : (Fin (N : ℕ) → ℝ) → ℝ} (hF : IsTorusSmooth F) (k : ℤ)
    (x : HsEuclidean N) :
    F (WithLp.ofLp (hsTranslate (k : ℝ) x)) = F (WithLp.ofLp x) := by
  have hof : (WithLp.ofLp (hsTranslate (k : ℝ) x) : Fin (N : ℕ) → ℝ) =
      fun i => WithLp.ofLp x i + (k : ℝ) := by
    funext i
    simp [hsTranslate_apply]
  rw [hof]
  exact periodic_translate_of_update hF.2 k (WithLp.ofLp x)

/-- Clauses 1 and 2 of Proposition 5.5 for `N ≥ 2`. -/
theorem loop_ibp_clauses_ge_two (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    (MemLp (loopOperatorPotential P N ℓ a ψ) 2 (gibbsMeasure P N) ∧
        ∫ X, loopOperatorPotential P N ℓ a ψ X ∂gibbsMeasure P N = 0) ∧
      (∀ F : (Fin (N : ℕ) → ℝ) → ℝ, IsTorusSmooth F →
        gibbsCov (gibbsMeasure P N) (fun X => F X.val) (loopOperatorPotential P N ℓ a ψ) =
          ∫ X, gradDotPotential F (loopScalePotential ℓ a ψ (N : ℕ)) X.val
            ∂gibbsMeasure P N) := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  have hI : ∀ X : Configuration N, loopOperatorPotential P N ℓ a ψ X =
      loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) := fun X =>
    (loopLHS_eq_loopOperatorPotential P N ℓ a ψ hψ X).symm
  -- square integrability from the uniform bound by the power sum of gaps
  have hmem : MemLp (loopOperatorPotential P N ℓ a ψ) 2 (gibbsMeasure P N) := by
    obtain ⟨KL, hKL0, hKL⟩ := exists_abs_loopLHS_le P ℓ a ψ hψ N
    have hL2 : MemLp (fun X : Configuration N => KL * (1 + gapPowerSum
        ((parametersExponent P).val + 1) X)) 2 (gibbsMeasure P N) :=
      ((memLp_const (1 : ℝ)).add (memLp_two_gapPowerSum P hPL N
        (by have := (parametersExponent P).property.1; linarith))).const_mul KL
    have hmeas : AEStronglyMeasurable (loopOperatorPotential P N ℓ a ψ) (gibbsMeasure P N) := by
      rw [show (loopOperatorPotential P N ℓ a ψ) = fun X => loopLHS P N ℓ a ψ
        (WithLp.toLp 2 X.val) from funext hI]
      exact (continuous_loopLHS_config P ℓ a ψ hψ).aestronglyMeasurable
    refine MemLp.of_le hL2 hmeas (Filter.Eventually.of_forall fun X => ?_)
    have h0 : 0 ≤ 1 + gapPowerSum ((parametersExponent P).val + 1) X := by
      have := gapPowerSum_nonneg ((parametersExponent P).val + 1) X
      linarith
    simp only [Real.norm_eq_abs, hI X, abs_mul, abs_of_nonneg hKL0, abs_of_nonneg h0]
    exact hKL X
  -- the mean-zero identity from the constant test function
  have hmeanzero : ∫ X, loopOperatorPotential P N ℓ a ψ X ∂gibbsMeasure P N = 0 := by
    have h1 := loopLHS_integral_eq P hPL N hN ℓ a ψ hψ hmean (fun _ => (1 : ℝ)) contDiff_const
      (fun _ _ => rfl) 1 (fun _ => le_of_eq abs_one) (fun k x => by simp [hsPartial])
    simp only [mul_one] at h1
    simp only [hI]
    rw [h1]
    simp [hsPartial]
  refine ⟨⟨hmem, hmeanzero⟩, ?_⟩
  intro F hF
  -- the covariance with a smooth function on the torus
  have hGc : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin (N : ℕ)) => F (WithLp.ofLp x)) :=
    contDiff_torusLift hF
  obtain ⟨MF, hMF⟩ := exists_bound_of_periodic hF.1.continuous hF.2
  obtain ⟨MD, hMD⟩ : ∃ M : ℝ, ∀ (k : Fin (N : ℕ)) (x : Fin (N : ℕ) → ℝ),
      |partialDeriv F k x| ≤ M := by
    have hk : ∀ k : Fin (N : ℕ), ∃ M, ∀ x, |partialDeriv F k x| ≤ M :=
      fun k => exists_bound_partialDeriv_of_periodic hF.1 hF.2 k
    choose Mk hMk using hk
    refine ⟨∑ k, |Mk k|, fun k x => (hMk k x).trans ?_⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Mk j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ k))
  set G : HsEuclidean N → ℝ := fun x => F (WithLp.ofLp x) with hGdef
  have hGper : ∀ (k : ℤ) (x : HsEuclidean N), G (hsTranslate (k : ℝ) x) = G x :=
    fun k x => torusLift_periodic hF k x
  have hGpart : ∀ (k : Fin (N : ℕ)) (x : HsEuclidean N),
      hsPartial G k x = partialDeriv F k (WithLp.ofLp x) := fun k x =>
    hsPartial_eq_partialDeriv (G := F) (U := univ) univ_mem (fun _ _ => rfl)
      ((hGc.differentiable (by simp)) x) k
  have hMG : ∀ x, |G x| ≤ max MF MD := fun x =>
    (hMF _).trans (le_max_left _ _)
  have hdG : ∀ (k : Fin (N : ℕ)) (x : HsEuclidean N), |hsPartial G k x| ≤ max MF MD :=
    fun k x => by
      rw [hGpart k x]
      exact (hMD k _).trans (le_max_right _ _)
  have h2 := loopLHS_integral_eq P hPL N hN ℓ a ψ hψ hmean G hGc hGper (max MF MD) hMG hdG
  -- the covariance reduces to `E[F 𝓛Φ]`, which is the Dirichlet pairing by `h2`
  have hL1 : Integrable (loopOperatorPotential P N ℓ a ψ) (gibbsMeasure P N) :=
    hmem.integrable (by norm_num)
  have hLc : Continuous (fun X : Configuration N => loopOperatorPotential P N ℓ a ψ X) := by
    rw [show (fun X : Configuration N => loopOperatorPotential P N ℓ a ψ X) =
      fun X => loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) from funext hI]
    exact continuous_loopLHS_config P ℓ a ψ hψ
  have hFc : Continuous (fun X : Configuration N => F X.val) :=
    hF.1.continuous.comp continuous_subtype_val
  have hint : Integrable (fun X : Configuration N => F X.val * loopOperatorPotential P N ℓ a ψ X)
      (gibbsMeasure P N) := by
    refine Integrable.mono' (hL1.norm.const_mul MF) (hFc.mul hLc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hMF X.val) (abs_nonneg _)
  unfold gibbsCov
  simp only [hmeanzero, sub_zero]
  have hsplit : ∀ X : Configuration N,
      (F X.val - ∫ Y, F Y.val ∂gibbsMeasure P N) * loopOperatorPotential P N ℓ a ψ X =
        F X.val * loopOperatorPotential P N ℓ a ψ X -
          (∫ Y, F Y.val ∂gibbsMeasure P N) * loopOperatorPotential P N ℓ a ψ X :=
    fun X => by ring
  simp only [hsplit]
  rw [integral_sub hint (hL1.const_mul _), integral_const_mul, hmeanzero, mul_zero, sub_zero]
  have hLHSeq : ∫ X : Configuration N, F X.val * loopOperatorPotential P N ℓ a ψ X ∂gibbsMeasure P N =
      ∫ X : Configuration N, loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) *
        G (WithLp.toLp 2 X.val) ∂gibbsMeasure P N :=
    integral_congr_ae (Filter.Eventually.of_forall fun X => by
      show F X.val * loopOperatorPotential P N ℓ a ψ X = loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) *
        G (WithLp.toLp 2 X.val)
      rw [hI X, mul_comm])
  rw [hLHSeq, h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  dsimp only
  unfold gradDotPotential
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsPartial_loopHS ℓ a ψ hψ N k (WithLp.toLp 2 X.val), hGpart k (WithLp.toLp 2 X.val)]
  ring

end Riesz1
