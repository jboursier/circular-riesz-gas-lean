/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlGapGeometry
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Inverse energy of the cutoff loop gap field

The first assertion of Proposition 5.9, for the actual
anchored inverse of the larger-window convexified law. Square
integrability is concluded, before the inverse is applied.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ContDiff

namespace Riesz1

/-- Proposition 5.9, gap-field assertion. The loss exponent
is chosen before epsilon and the spatial cutoff. The coefficient is
uniform even in the envelope amplitude, which appears explicitly squared.
No external inequality is needed for this assertion. -/
theorem varAl_gap_energy {s α γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 1 < γ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (β : ℝ) (hβ : 0 < β),
      let P : Parameters := ⟨(β, s), hβ, hs0, hs1⟩
      ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
      (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ε < min (1 / 8) ((1 - P.val.2 / 2) / 8) →
        ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
          ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
            0 < ℓ → ℓ ≤ 1 → ∀ (hK : 1 ≤ (n.succPNat : ℝ) * ℓ), 0 ≤ C₀ →
            ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
            (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne P.val.2 (1 - P.val.2 + α)
              ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
            (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo P.val.2 (1 - P.val.2 + α)
              ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
            let K := (n.succPNat : ℝ) * ℓ
            let Q := nearestTiltedPairs P n.succPNat hθ K (2 * γ) ε (by linarith)
            let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i =>
              loopCutoff P.val.2 γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
                gradWfield P.val.2 (loopTransport χ n.succPNat ℓ γ ψ)
                  n.succPNat ℓ γ (anchorVector (WithLp.ofLp y)) i.succ
            ∃ hv : MemLp v 2 (anchoredMeasureE Q),
              anchoredInverseEnergy Q
                (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
                (hv.toLp v) ≤ C * C₀ ^ 2 * K ^ (κ * ε) * (K + K ^ (2 * (1 - P.val.2 + α))) := by
  obtain ⟨κ, hκ, hb⟩ := varAl_gap_covector_bound hs0 hs1 hα hα2 hγ
  refine ⟨κ + (s + 2), by linarith, ?_⟩
  intro β hβ P
  obtain ⟨CE, hCE, he⟩ := nearestAnchored_inverse_energy P
  intro χ hχ hχc hχs hχ1 hχ01 ε hε hεs
  obtain ⟨Cg, hCg, hg⟩ := hb χ hχ hχc hχs hχ1 hχ01 ε hε hεs
  refine ⟨CE * Cg, mul_pos hCE hCg, ?_⟩
  intro n hn θ hθ ℓ C₀ ψ hℓ hℓ1 hK hC₀ hψ hp h1 h2
  let N := n.succPNat
  let K := (N : ℝ) * ℓ
  let Q := nearestTiltedPairs P N hθ K (2 * γ) ε (by linarith : 0 < K)
  let μ := anchoredMeasureE Q
  have hc := hsRieszPairPotentials_curvature_pos N P.2.1 (parametersExponent P)
  have := isProbabilityMeasure_anchoredMeasureE Q hc
  let ψγ := loopTransport χ N ℓ γ ψ
  let η := fun y : AnchoredEuclidean n => loopCutoff P.val.2 γ ε N ℓ (anchorVector (WithLp.ofLp y))
  let a := fun y : AnchoredEuclidean n => fun e : Fin (N : ℕ) =>
    -η y * gradWgap P.val.2 ψγ N ℓ γ (anchorVector (WithLp.ofLp y)) (e.val : ℤ)
  let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
    η y * gradWfield P.val.2 ψγ N ℓ γ (anchorVector (WithLp.ofLp y)) i.succ
  let R := Cg * C₀ ^ 2 * K ^ (κ * ε) * (K + K ^ (2 * (1 - P.val.2 + α)))
  have hR : 0 ≤ R := by dsimp [R, K]; positivity
  have hav : Continuous (fun y : AnchoredEuclidean n => anchorVector (WithLp.ofLp y)) :=
    (continuous_pi fun k => continuous_anchorVector_apply k).comp (PiLp.continuous_ofLp 2 _)
  have hψγ : ContDiff ℝ ∞ ψγ := contDiff_loopTransport hχ hψ hχs N hℓ γ
  have hηc : ContinuousOn η (anchoredSimplex n) :=
    (loopCutoff_locallyLipschitzOn P.val.2 γ ε N hℓ).continuousOn.comp hav.continuousOn
      (fun _ hy => varAl_anchorVector_mem hy)
  have haC (e : Fin (N : ℕ)) : ContinuousOn (fun y => a y e) (anchoredSimplex n) :=
    hηc.neg.mul ((varAlGap_continuousOn_covector P.2.2.1 P.2.2.2 hℓ hψγ (e.val : ℤ)).comp
      hav.continuousOn (fun _ hy => varAl_anchorVector_mem hy))
  have hbound : ∀ᵐ y ∂μ, (∑ e : Fin (N : ℕ), a y e ^ 2) ≤ R := by
    filter_upwards [ae_mem_anchoredSimplex Q] with y hy
    have hb' := hg N ℓ C₀ ψ (by simpa [N] using hn) hℓ hℓ1 hK hC₀ hψ hp h1 h2
      _ (varAl_anchorVector_mem hy)
    rw [varAlGap_sum_Ico] at hb'
    convert hb' using 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    dsimp [a, η, ψγ]
    ring
  have ha (e : Fin (N : ℕ)) : MemLp (fun y => a y e) 2 μ := by
    have ham : AEStronglyMeasurable (fun y => a y e) μ := by
      change AEStronglyMeasurable (fun y => a y e) (anchoredMeasureE Q)
      rw [← Measure.restrict_eq_self_of_ae_mem (ae_mem_anchoredSimplex Q)]
      exact (haC e).aestronglyMeasurable (isOpen_anchoredSimplex n).measurableSet
    apply MemLp.of_bound ham (1 + R)
    filter_upwards [hbound] with y hy
    have hsq : a y e ^ 2 ≤ R :=
      (Finset.single_le_sum (fun i _ => sq_nonneg (a y i)) (Finset.mem_univ e)).trans hy
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (a y e), abs_nonneg (a y e)]
  have hrep : ∀ᵐ y ∂μ, ∀ U : Fin n → ℝ,
      dotProd (WithLp.ofLp (v y)) U =
        ∑ e ∈ nearestPairs N (window N K (2 * γ)),
          a y e * (((n : ℝ) + 1) * edgeForm n e U) := by
    filter_upwards [ae_mem_anchoredSimplex Q] with y hy U
    exact varAlGap_covector_identity P.2.2.1 P.2.2.2
      (loopTransport_periodic hℓ χ hp) hK (by linarith) hy (η y) U
  have hv : MemLp v 2 μ := by
    apply MemLp.of_eval_piLp
    intro i
    apply MemLp.ae_eq _ (memLp_finsetSum (nearestPairs N (window N K (2 * γ)))
      (fun e _ => (ha e).mul_const (((n : ℝ) + 1) * edgeForm n e (Pi.single i (1 : ℝ)))))
    filter_upwards [hrep] with y hy
    exact (hy (Pi.single i (1 : ℝ))).symm.trans (by simp [dotProd, Pi.single_apply])
  refine ⟨hv, ?_⟩
  have hrepLp : ∀ᵐ y ∂μ, ∀ U : Fin n → ℝ,
      dotProd (WithLp.ofLp (hv.toLp v y)) U =
        ∑ e ∈ nearestPairs N (window N K (2 * γ)), a y e * (((n : ℝ) + 1) * edgeForm n e U) := by
    filter_upwards [hv.coeFn_toLp, hrep] with y hy hry U
    rw [hy]
    exact hry U
  have hI : (∫ y, ∑ e ∈ nearestPairs N (window N K (2 * γ)), a y e ^ 2 ∂μ) ≤ R := by
    have hmono : (∫ y, ∑ e ∈ nearestPairs N (window N K (2 * γ)), a y e ^ 2 ∂μ) ≤
        ∫ _y, R ∂μ := by
      apply integral_mono_ae
        (integrable_finsetSum _ fun e _ => (ha e).integrable_sq) (integrable_const R)
      filter_upwards [hbound] with y hy
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun e _ _ => sq_nonneg (a y e))).trans hy
    simpa using hmono
  have he' := he n hn θ hθ K (2 * γ) ε hK hε.le (hv.toLp v) a ha hrepLp
  have hK0 : 0 < K := by linarith
  have hpow : K ^ ((P.val.2 + 2) * ε) * K ^ (κ * ε) =
      K ^ ((κ + (P.val.2 + 2)) * ε) := by
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  calc anchoredInverseEnergy Q hc (hv.toLp v)
      ≤ CE * K ^ ((P.val.2 + 2) * ε) * R :=
        he'.trans (mul_le_mul_of_nonneg_left hI (by positivity))
    _ = (CE * Cg) * C₀ ^ 2 * K ^ ((κ + (P.val.2 + 2)) * ε) *
        (K + K ^ (2 * (1 - P.val.2 + α))) := by
      dsimp [R]
      rw [← hpow]
      ring

end Riesz1

end
