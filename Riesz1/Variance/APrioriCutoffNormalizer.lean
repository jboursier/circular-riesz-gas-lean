/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.NearestForcing
public import Riesz1.Rigidity.GapLawMoments

/-!
# Uniform normalization on bounded ranges of the scale

The bounded-scale step in the cutoff part of Lemma 5.2. The unit mean
of every gap and Markov's inequality give a single event of probability
at least one half on which all selected gaps, and hence the forcing, are
uniformly bounded. No rigidity or external hypothesis is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset

namespace Riesz1

/-- A forcing cutoff has a uniform quadratic bound on its whole carrier. -/
theorem forcingCutoff_le_sq {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {t : ℝ} (ht : 0 ≤ t) :
    θ t ≤ t ^ 2 := by
  have h := cutoff_le_sq (hθ.1.of_le (by simp)) hθ.2.1 hθ.2.2.2.1 t ht
  have hm : 0 ≤ max (t - 1) 0 := le_max_right _ _
  have hmt : max (t - 1) 0 ≤ t := max_le (by linarith) ht
  exact h.trans (by nlinarith)

namespace Internal

/-- Internal event comparison for the actual exponential normalizer. -/
theorem forcedNormalizer_lower_of_event (P : Parameters) (N : ℕ+)
    {G : Configuration N → ℝ} (hG : Measurable G) (hG0 : ∀ X, 0 ≤ G X)
    {E : Set (Configuration N)} (hE : MeasurableSet E) (B : ℝ)
    (hB : ∀ X ∈ E, G X ≤ B) :
    Real.exp (-P.val.1 * B) * (gibbsMeasure P N).real E ≤ forcedNormalizer P N G := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hmono : ∫ X, E.indicator (fun _ => Real.exp (-P.val.1 * B)) X ∂gibbsMeasure P N ≤
      forcedNormalizer P N G := by
    apply integral_mono ((integrable_const _).indicator hE) (integrable_exp_neg hG hG0)
    intro X
    by_cases hX : X ∈ E
    · rw [Set.indicator_of_mem hX]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hB X hX) (by linarith [P.2.1]))
    · rw [Set.indicator_of_notMem hX]
      exact (Real.exp_pos _).le
  rw [integral_indicator_const _ hE, smul_eq_mul, mul_comm] at hmono
  exact hmono

end Internal

/-- **Bounded-scale normalization, from the cutoff part of Lemma 5.2.**
The lower bound is uniform in the particle number, cutoff, and scale
`1 ≤ K ≤ K₀`. Its dependence is only on the fixed parameters displayed
before `N`, and in fact only on `β`, `γ`, and `K₀`.
-/
theorem nearestNormalizer_uniform_bounded (P : Parameters) (γ ε K₀ : ℝ)
    (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hK₀ : 1 ≤ K₀) :
    ∃ z : ℝ, 0 < z ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ K : ℝ, 1 ≤ K → K ≤ K₀ →
        z ≤ forcedNormalizer P N (nearestForcing θ N K γ ε) := by
  let m : ℝ := 8 * K₀ ^ γ
  let R : ℝ := 2 * (m + 1)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have hR : 0 < R := by dsimp [R]; linarith
  refine ⟨Real.exp (-P.val.1 * (m * R ^ 2)) / 2, by positivity,
    fun N hN θ hθ K hK hKK => ?_⟩
  have := isProbabilityMeasure_gibbsMeasure P N
  have hKpos : 0 < K := by linarith
  let E := nearestPairs N (window N K γ)
  let S : Configuration N → ℝ := fun X => ∑ e ∈ E, gap X ((e.val : ℕ) : ℤ)
  have hSm : Measurable S := Finset.measurable_sum _ fun _ _ => measurable_gap _
  have hSi : Integrable S (gibbsMeasure P N) :=
    integrable_finsetSum _ fun e _ => integrable_gap P N (e.val : ℤ)
  have hS0 (X : Configuration N) : 0 ≤ S X :=
    Finset.sum_nonneg fun e _ => (gap_pos X _).le
  have hSint : (∫ X, S X ∂gibbsMeasure P N) = (E.card : ℝ) := by
    rw [integral_finsetSum _ (fun e _ => integrable_gap P N (e.val : ℤ))]
    simp only [integral_gap_gibbsMeasure P N hN, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (E.card : ℝ) ≤ m :=
    (card_nearestPairs_window_le hK hγ).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hKK hγ) (by norm_num))
  have hbad : (gibbsMeasure P N).real {X | R ≤ S X} ≤ 1 / 2 := by
    have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hS0) hSi R
    rw [hSint] at h
    dsimp [R] at h
    nlinarith [measureReal_nonneg (μ := gibbsMeasure P N) (s := {X | R ≤ S X})]
  let A : Set (Configuration N) := {X | R ≤ S X}ᶜ
  have hA : MeasurableSet A := (measurableSet_le measurable_const hSm).compl
  have hprob : 1 / 2 ≤ (gibbsMeasure P N).real A := by
    rw [show A = {X | R ≤ S X}ᶜ from rfl,
      probReal_compl_eq_one_sub (measurableSet_le measurable_const hSm)]
    linarith
  have hbound : ∀ X ∈ A, nearestForcing θ N K γ ε X ≤ m * R ^ 2 := by
    intro X hX
    have hSX : S X < R := not_le.mp hX
    have hKe : 1 ≤ K ^ ε := Real.one_le_rpow hK hε
    have hKe0 : 0 < K ^ ε := Real.rpow_pos_of_pos hKpos _
    have he (e : Fin (N : ℕ)) (he : e ∈ E) : θ (gap X (e.val : ℤ) / K ^ ε) ≤ R ^ 2 := by
      have hgS : gap X (e.val : ℤ) ≤ S X :=
        Finset.single_le_sum (f := fun e : Fin (N : ℕ) => gap X (e.val : ℤ))
          (fun e _ => (gap_pos X _).le) he
      have hq : gap X (e.val : ℤ) / K ^ ε ≤ R := by
        rw [div_le_iff₀ hKe0]
        nlinarith
      have hq0 : 0 ≤ gap X (e.val : ℤ) / K ^ ε := div_nonneg (gap_pos X _).le hKe0.le
      exact (forcingCutoff_le_sq hθ hq0).trans (by nlinarith)
    calc nearestForcing θ N K γ ε X
        ≤ ∑ _e ∈ E, R ^ 2 := Finset.sum_le_sum he
      _ = (E.card : ℝ) * R ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ m * R ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  have hz := Internal.forcedNormalizer_lower_of_event P N (measurable_nearestForcing hθ)
    (nearestForcing_nonneg hθ hKpos) hA (m * R ^ 2) hbound
  calc Real.exp (-P.val.1 * (m * R ^ 2)) / 2
      ≤ Real.exp (-P.val.1 * (m * R ^ 2)) * (gibbsMeasure P N).real A := by
        nlinarith [Real.exp_pos (-P.val.1 * (m * R ^ 2))]
    _ ≤ forcedNormalizer P N (nearestForcing θ N K γ ε) := hz

end Riesz1

end
