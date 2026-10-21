/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffDifferentiability
public import Riesz1.Variance.ConvexificationEnergyBound
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The cutoff field and its selected-edge coefficients

Coefficients are zeroed where the anchored differential vanishes. This permits
a bound on the statistic only where the gradient is nonzero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1

/-- The literal field `T ∇η*`, in the Euclidean realization of the
anchored coordinates. Scalar multiplication already makes it zero
where the gradient vanishes. -/
def anchoredCutoffField (n : ℕ) (s K γ ε : ℝ) (T : (Fin n → ℝ) → ℝ)
    (y : AnchoredEuclidean n) : AnchoredEuclidean n :=
  WithLp.toLp 2 fun i => T (WithLp.ofLp y) *
    fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y) (Pi.single i (1 : ℝ))

/-- The selected gap coefficients, set to zero wherever the anchored
differential vanishes, as required by the support-only bound on `T`. -/
def anchoredCutoffCoefficients (n : ℕ) (s K γ ε : ℝ) (T : (Fin n → ℝ) → ℝ)
    (y : AnchoredEuclidean n) (e : Fin (n.succPNat : ℕ)) : ℝ := by
  classical
  exact if fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y) = 0 then 0 else
    T (WithLp.ofLp y) * fderiv ℝ (gapCutoff n.succPNat s K γ ε)
      (anchoredGapVector n (WithLp.ofLp y)) (Pi.single e (1 : ℝ))

/-- Pairing the coordinate gradient with a vector recovers the
differential, everywhere on the ambient carrier. -/
theorem anchoredCutoffField_dotProd (n : ℕ) (s K γ ε : ℝ) (T : (Fin n → ℝ) → ℝ)
    (y : AnchoredEuclidean n) (U : Fin n → ℝ) :
    dotProd (WithLp.ofLp (anchoredCutoffField n s K γ ε T y)) U =
      T (WithLp.ofLp y) * fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y) U := by
  let L : (Fin n → ℝ) →L[ℝ] ℝ := fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y)
  have hL : L U = ∑ i, U i * L (Pi.single i (1 : ℝ)) := by
    conv_lhs => rw [pi_eq_sum_univ' U]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  change (∑ i, (T (WithLp.ofLp y) * L (Pi.single i (1 : ℝ))) * U i) = T (WithLp.ofLp y) * L U
  rw [hL, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem measurable_anchoredCutoffCoefficients (n : ℕ) (s K γ ε : ℝ)
    {T : (Fin n → ℝ) → ℝ} (hT : Measurable T) (e : Fin (n.succPNat : ℕ)) :
    Measurable (fun y => anchoredCutoffCoefficients n s K γ ε T y e) := by
  classical
  have hL := (measurable_fderiv ℝ (anchoredCutoff n.succPNat s K γ ε)).comp
    (PiLp.continuous_ofLp 2 _).measurable
  have hD := (measurable_fderiv_apply_const ℝ (gapCutoff n.succPNat s K γ ε)
    (Pi.single e (1 : ℝ))).comp
      ((measurable_anchoredGapVector n).comp (PiLp.continuous_ofLp 2 _).measurable)
  exact Measurable.ite (measurableSet_eq_fun hL measurable_const) measurable_const
    ((hT.comp (PiLp.continuous_ofLp 2 _).measurable).mul hD)

/-- Coefficients vanish on the cutoff plateau at every point. -/
theorem anchoredCutoffCoefficients_eq_zero_of_eq_one (n : ℕ) (s K γ ε : ℝ)
    (T : (Fin n → ℝ) → ℝ) (y : AnchoredEuclidean n)
    (hy : anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) = 1)
    (e : Fin (n.succPNat : ℕ)) : anchoredCutoffCoefficients n s K γ ε T y e = 0 := by
  have h := fderiv_anchoredCutoff_eq_zero_of_eq_one n.succPNat s K γ ε (WithLp.ofLp y) hy
  unfold anchoredCutoffCoefficients
  exact ite_eq_left h

/-- Measurable square-integrable coefficients and the exact covector
representation, with a bound on `T` only where the anchored gradient
is nonzero. -/
theorem anchoredCutoff_coefficients_data {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) (s K γ ε : ℝ)
    (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (T : (Fin n → ℝ) → ℝ) (hTm : Measurable T) (M D : ℝ) (hM : 0 ≤ M)
    (hT : ∀ y, fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) y ≠ 0 → |T y| ≤ M * K ^ D) :
    (∀ e, MemLp (fun y => anchoredCutoffCoefficients n s K γ ε T y e) 2 (anchoredMeasureE χ)) ∧
    (∀ᵐ y ∂anchoredMeasureE χ,
      (∀ e, |anchoredCutoffCoefficients n s K γ ε T y e| ≤ (M * K ^ D) * (76 * K ^ (2 * γ + ε))) ∧
      ∀ U : Fin n → ℝ, dotProd (WithLp.ofLp (anchoredCutoffField n s K γ ε T y)) U =
        ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
          anchoredCutoffCoefficients n s K γ ε T y e * (((n : ℝ) + 1) * edgeForm n e U)) := by
  classical
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have hB : 0 ≤ (M * K ^ D) * (76 * K ^ (2 * γ + ε)) := by positivity
  have hdata := anchoredMeasureE_cutoff_chain_ae hn χ s K γ ε hK hγ hs hε
  have hbound : ∀ᵐ y ∂anchoredMeasureE χ, ∀ e,
      |anchoredCutoffCoefficients n s K γ ε T y e| ≤ (M * K ^ D) * (76 * K ^ (2 * γ + ε)) := by
    filter_upwards [hdata] with y hy e
    unfold anchoredCutoffCoefficients
    split_ifs with h
    · simpa using hB
    · rw [abs_mul]
      exact mul_le_mul (hT _ h) (hy.2.1 e) (abs_nonneg _) (by positivity)
  refine ⟨fun e => MemLp.of_bound (measurable_anchoredCutoffCoefficients n s K γ ε hTm e).aestronglyMeasurable
    _ (hbound.mono fun y hy => by simpa only [Real.norm_eq_abs] using hy e), ?_⟩
  filter_upwards [hdata, hbound] with y hy hb
  refine ⟨hb, fun U => ?_⟩
  rw [anchoredCutoffField_dotProd]
  by_cases h : fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y) = 0
  · have ha0 (e : Fin (n.succPNat : ℕ)) : anchoredCutoffCoefficients n s K γ ε T y e = 0 := by
      unfold anchoredCutoffCoefficients
      exact ite_eq_left h
    simp_rw [ha0, zero_mul, Finset.sum_const_zero]
    have hU : fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) (WithLp.ofLp y) U = 0 :=
      congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L U) h
    rw [hU, mul_zero]
  · simp only [anchoredCutoffCoefficients, ite_eq_right h]
    rw [hy.2.2 U, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring

/-- The cutoff field belongs to the actual vector `L²` carrier.
No global bound on the statistic is needed. -/
theorem memLp_anchoredCutoffField {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) (s K γ ε : ℝ)
    (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (T : (Fin n → ℝ) → ℝ) (hTm : Measurable T) (M D : ℝ) (hM : 0 ≤ M)
    (hT : ∀ y, fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) y ≠ 0 → |T y| ≤ M * K ^ D) :
    MemLp (anchoredCutoffField n s K γ ε T) 2 (anchoredMeasureE χ) := by
  obtain ⟨ha, hdata⟩ := anchoredCutoff_coefficients_data hn χ hc s K γ ε hK hγ hs hε T hTm M D hM hT
  apply MemLp.of_eval_piLp
  intro i
  have hsum := memLp_finsetSum (nearestPairs n.succPNat (window n.succPNat K γ))
    (fun e _ => (ha e).mul_const (((n : ℝ) + 1) * edgeForm n e (Pi.single i (1 : ℝ))))
  apply MemLp.ae_eq _ hsum
  filter_upwards [hdata] with y hy
  exact (hy.2 (Pi.single i (1 : ℝ))).symm.trans (by simp [dotProd, Pi.single_apply])

/-- Integrating the coefficient squares costs only the selected-edge
count and the probability of the bad set. -/
theorem integral_anchoredCutoffCoefficients_sq_le {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (hc : 0 < c) (s K γ ε : ℝ)
    (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (T : (Fin n → ℝ) → ℝ) (hTm : Measurable T) (M D : ℝ) (hM : 0 ≤ M)
    (hT : ∀ y, fderiv ℝ (anchoredCutoff n.succPNat s K γ ε) y ≠ 0 → |T y| ≤ M * K ^ D) :
    (∫ y, ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
      anchoredCutoffCoefficients n s K γ ε T y e ^ 2 ∂anchoredMeasureE χ) ≤
        (8 * K ^ γ) * ((M * K ^ D) * (76 * K ^ (2 * γ + ε))) ^ 2 *
          (anchoredMeasureE χ).real {y | anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) ≠ 1} := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  obtain ⟨ha, hdata⟩ := anchoredCutoff_coefficients_data hn χ hc s K γ ε hK hγ hs hε T hTm M D hM hT
  let S := {y : AnchoredEuclidean n | anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) ≠ 1}
  let B := (8 * K ^ γ) * ((M * K ^ D) * (76 * K ^ (2 * γ + ε))) ^ 2
  have hS : MeasurableSet S :=
    (((measurable_anchoredCutoff (N := n.succPNat) s K γ ε).comp (PiLp.continuous_ofLp 2 _).measurable)
      (measurableSet_singleton 1)).compl
  have hI : Integrable (fun y => ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
      anchoredCutoffCoefficients n s K γ ε T y e ^ 2) (anchoredMeasureE χ) :=
    integrable_finsetSum _ fun e _ => (ha e).integrable_sq
  have hb : ∀ᵐ y ∂anchoredMeasureE χ,
      (∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
        anchoredCutoffCoefficients n s K γ ε T y e ^ 2) ≤ S.indicator (fun _ => B) y := by
    filter_upwards [hdata] with y hy
    by_cases hyS : y ∈ S
    · rw [Set.indicator_of_mem hyS]
      calc (∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
          anchoredCutoffCoefficients n s K γ ε T y e ^ 2)
          ≤ ∑ _e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
            ((M * K ^ D) * (76 * K ^ (2 * γ + ε))) ^ 2 := by
            apply Finset.sum_le_sum
            intro e _
            simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hy.1 e)
        _ = ((nearestPairs n.succPNat (window n.succPNat K γ)).card : ℝ) *
            ((M * K ^ D) * (76 * K ^ (2 * γ + ε))) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ B := mul_le_mul_of_nonneg_right (card_nearestPairs_window_le hK hγ) (sq_nonneg _)
    · rw [Set.indicator_of_notMem hyS]
      have hplateau : anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y) = 1 := by
        simpa only [S, Set.mem_ofPred_eq, not_not] using hyS
      simp only [anchoredCutoffCoefficients_eq_zero_of_eq_one n s K γ ε T y hplateau,
        sq, zero_mul, Finset.sum_const_zero, le_refl]
  have h := integral_mono_ae hI ((integrable_const B).indicator hS) hb
  rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm] at h
  exact h

end Riesz1

end
