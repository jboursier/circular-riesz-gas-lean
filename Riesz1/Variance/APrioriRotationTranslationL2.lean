/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationTranslationBound
public import Riesz1.Variance.APrioriRotationTranslationGood
public import Riesz1.Variance.APrioriRotationVariance
public import Riesz1.Variance.APrioriRotationOriginL2

/-!
# The `L²` bound of the translation error

The translation error in the rotation part of Lemma 5.2: under the joint law of `(D, y)`, the
squared translation error has integral at most `C_ε K^{c ε} (1 + K^{2λ})`, with `c` depending
only on `λ`, and `C` depending on the model, `λ`, `γ` and `ε`.

The joint law is `1_{0 < D < w(y)} dD dμ*(y)` with `w(y) = N y_1` (`Riesz1.sizeBiasWeight`), where
`μ*` is `Riesz1.rotAnchoredLaw`. On the good event, the deterministic bound of
`Riesz1.translationError_good_le` applies for every `D < w`. On the complement, the uniform bound
`Riesz1.abs_translationError_le_uniform` applies, and the complement has probability `C K^{-B}`
by `Riesz1.gibbs_bad_bound`. The weight `w` has bounded second moment by
`Riesz1.exists_lintegral_gap_sq_le`, so Cauchy–Schwarz (in the form `w ≤ (q w²)/2 + 1/(2q)`)
absorbs the bad part.
-/

@[expose] public section

open MeasureTheory Set

namespace Riesz1

/-- **Translation error, `L²` bound** (the translation error claim in the rotation part of
Lemma 5.2). Let `P` be the model parameters and `λ ≥ 0`, and let `γ > 1`. There is `c > 0` such that
for every `ε > 0` there is `C ≥ 0` with: for every `N ≥ 2`, `0 < ℓ ≤ 1` with `K = N ℓ ≥ 1`, and
every `C¹` function `f` of period `1/ℓ` with `f(1/(2ℓ)) = 0` satisfying the derivative bound of the
kernel, the joint integral of `Δ_D(y)²` over `0 < D < w(y)` against `μ*` is at most
`C K^{c ε} (1 + K^{2λ})`. The Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler` are explicit hypotheses. -/
theorem translation_lintegral_sq_le (P : Parameters) (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) {lam : ℝ} (hlam : 0 ≤ lam) {γ : ℝ} (hγ : 1 < γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ+) (ℓ : ℝ) (hN : 2 ≤ (N : ℕ)), 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) → f (1 / ℓ / 2) = 0 →
        (∀ u ∈ Set.Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
          |deriv f u| ≤ (if |u| ≤ 2 then 1 / (max |u| (((N : ℕ) : ℝ) * ℓ)⁻¹) ^ (1 + lam) else 0) +
            (if 2 ≤ |u| then 1 / |u| ^ (3 - P.val.2) else 0)) →
        ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
            ENNReal.ofReal (translationError N ℓ γ f D y ^ 2)) ∂(rotAnchoredLaw P N) ≤
          ENNReal.ofReal (C * (((N : ℕ) : ℝ) * ℓ) ^ (c * ε) *
            (1 + (((N : ℕ) : ℝ) * ℓ) ^ (2 * lam))) := by
  have hbeta : 0 < P.val.1 := P.property.1
  have hs : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hγ0 : 0 ≤ γ := by linarith
  refine ⟨2 * (3 + lam), by linarith, fun ε hε => ?_⟩
  -- The auxiliary exponents: `ε' ≤ min(ε, ε₀, 1)` and the exponent `B` of the bad event.
  set s : ℝ := P.val.2 with hs_def
  set ε₀ : ℝ := γ * (1 - s / 2) with hε₀_def
  have hε₀ : 0 < ε₀ := mul_pos (by linarith) (by linarith)
  set ε' : ℝ := min (min ε ε₀) 1 with hε'_def
  have hε'0 : 0 < ε' := lt_min (lt_min hε hε₀) one_pos
  have hε'ε₀ : ε' ≤ ε₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε'ε : ε' ≤ ε := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  set Bexp : ℝ := 4 * γ + 4 * lam + 4 * ε₀ + 1 with hBexp_def
  have hBexp : 0 < Bexp := by rw [hBexp_def]; linarith
  obtain ⟨Cg, hCg, hgap⟩ := exists_lintegral_gap_sq_le P hPL
  obtain ⟨CB, hCB, hbad⟩ := gibbs_bad_bound P hBE hPL hγ hε'0 hBexp
  have hcomp := Internal.aPrioriGood_complete_of_rigidity P.val.1 s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL P.val.1 s hbeta hs hs1) γ hγ
  have hsupp := hcomp.2.2.1
  refine ⟨goodConst s γ lam ε' ^ 2 * ((Cg + 1) / 2) +
      324 * kernelSupConst s lam ε' ^ 2 * ((Cg + CB) / 2), ?_, fun N ℓ hN hℓ hℓ1 hK1 f hf hper
      hzero hder => ?_⟩
  · have h1 : 0 ≤ (Cg + 1) / 2 := by linarith
    have h2 : 0 ≤ (Cg + CB) / 2 := by linarith
    exact add_nonneg (mul_nonneg (sq_nonneg _) h1) (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) h2)
  -- Notation for this `N` and `ℓ`.
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  set K : ℝ := ((N : ℕ) : ℝ) * ℓ with hK_def
  have hK0 : 0 < K := by linarith
  have hs2 : s < 2 := by linarith
  have hdm : ∀ u ∈ Set.Icc (-(1 / ℓ / 2)) (1 / ℓ / 2), |deriv f u| ≤ derivMajorant K lam s |u| :=
    fun u hu => abs_deriv_le_derivMajorant hK0 (hder u hu)
  obtain ⟨Mb, hMb_def⟩ : ∃ Mb : ℝ, Mb = 2 * (9 * K ^ γ) * (kernelSupConst s lam ε' * K ^ (lam + ε')) :=
    ⟨_, rfl⟩
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = K ^ (-(Bexp / 2)) := ⟨_, rfl⟩
  obtain ⟨A1, hA1_def⟩ : ∃ A1 : ℝ, A1 = (goodConst s γ lam ε' * K ^ (lam + (3 + lam) * ε')) ^ 2 :=
    ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq_def]; exact Real.rpow_pos_of_pos hK0 _
  have hA1nn : 0 ≤ A1 := by rw [hA1_def]; exact sq_nonneg _
  have hMb2nn : 0 ≤ Mb ^ 2 := sq_nonneg _
  -- The good event, the translation bound on it, and the uniform bound.
  have hsupp' : ∀ X : Configuration N, goodCutoff N s K γ ε' X = 1 → X ∈ goodEvent N s K γ ε' :=
    fun X hX => hsupp N ε' K hK0 X (by rw [hX]; norm_num)
  have hgapK : ∀ X : Configuration N, goodCutoff N s K γ ε' X = 1 → gap X 0 ≤ K ^ ε' := by
    intro X hX
    have hlab0 : labelOf N 0 = (⟨0, N.pos⟩ : Fin (N : ℕ)) := by
      have := labelOf_natCast N ⟨0, N.pos⟩
      simpa using this
    have hlab1 : labelOf N ((0 : ℤ) + 1) = (⟨1, by omega⟩ : Fin (N : ℕ)) := by
      rw [zero_add]
      have := labelOf_natCast N ⟨1, by omega⟩
      simpa using this
    exact (APG.gap_bounds_of_labels (hsupp' X hX) (c := 0)
      (by rw [hlab0]; exact origin_mem_window N hK1)
      (by rw [hlab1]; exact one_mem_window N hN hK1 hγ0)).2
  have hunif : ∀ (D : ℝ) (y : Fin (N : ℕ) → ℝ), |translationError N ℓ γ f D y| ≤ Mb := by
    intro D y
    rw [hMb_def]
    exact abs_translationError_le_uniform N hs2 hK1 hγ0 hlam hε'0 hℓ hf hper hzero hder D y
  set bad : Set (Configuration N) := {X | goodCutoff N s K γ ε' X ≠ 1} with hbad_def
  -- The pointwise bound of the inner integral, on the good and on the bad event.
  have hpt : ∀ X : Configuration N,
      (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN (rotAnchorVec N X)),
        ENNReal.ofReal (translationError N ℓ γ f D (rotAnchorVec N X) ^ 2)) ≤
      ENNReal.ofReal A1 * ENNReal.ofReal (gap X 0) +
        ENNReal.ofReal (Mb ^ 2 * q / 2) * ENNReal.ofReal (gap X 0 ^ 2) +
        bad.indicator (fun _ => ENNReal.ofReal (Mb ^ 2 / (2 * q))) X := by
    intro X
    rw [sizeBiasWeight_anchorVec N hN X]
    have hw0 : 0 ≤ gap X 0 := (gap_pos X 0).le
    by_cases hXG : goodCutoff N s K γ ε' X = 1
    · have hnotbad : X ∉ bad := by
        intro h
        exact (h : goodCutoff N s K γ ε' X ≠ 1) hXG
      have hind : bad.indicator (fun _ => ENNReal.ofReal (Mb ^ 2 / (2 * q))) X = 0 :=
        Set.indicator_of_notMem hnotbad _
      have hle : (∫⁻ D in Ioo (0 : ℝ) (gap X 0),
          ENNReal.ofReal (translationError N ℓ γ f D (rotAnchorVec N X) ^ 2)) ≤
          ∫⁻ D in Ioo (0 : ℝ) (gap X 0), ENNReal.ofReal A1 := by
        refine setLIntegral_mono' measurableSet_Ioo fun D hD => ENNReal.ofReal_le_ofReal ?_
        have hgoodD := translationError_good_le hs hs1 hlam hγ hε'0 hε'1 (by linarith [hε'ε₀, hε'ε₀])
          N ℓ hℓ hℓ1 hK1 hf hper hdm (hsupp' X hXG) hD.1.le
          (le_trans hD.2.le (hgapK X hXG))
        rw [hA1_def, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hgoodD 2
      have hval : ∫⁻ D in Ioo (0 : ℝ) (gap X 0), ENNReal.ofReal A1 =
          ENNReal.ofReal A1 * ENNReal.ofReal (gap X 0) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
      rw [hind, add_zero]
      calc _ ≤ ∫⁻ D in Ioo (0 : ℝ) (gap X 0), ENNReal.ofReal A1 := hle
        _ = ENNReal.ofReal A1 * ENNReal.ofReal (gap X 0) := hval
        _ ≤ _ := le_add_of_nonneg_right zero_le
    · have hXbad : X ∈ bad := hXG
      have hind : bad.indicator (fun _ => ENNReal.ofReal (Mb ^ 2 / (2 * q))) X =
          ENNReal.ofReal (Mb ^ 2 / (2 * q)) := Set.indicator_of_mem hXbad _
      have hle : (∫⁻ D in Ioo (0 : ℝ) (gap X 0),
          ENNReal.ofReal (translationError N ℓ γ f D (rotAnchorVec N X) ^ 2)) ≤
          ∫⁻ D in Ioo (0 : ℝ) (gap X 0), ENNReal.ofReal (Mb ^ 2) := by
        refine setLIntegral_mono' measurableSet_Ioo fun D _ => ENNReal.ofReal_le_ofReal ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hunif D _) 2
      have hval : ∫⁻ D in Ioo (0 : ℝ) (gap X 0), ENNReal.ofReal (Mb ^ 2) =
          ENNReal.ofReal (Mb ^ 2) * ENNReal.ofReal (gap X 0) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
      have h3 : ENNReal.ofReal (Mb ^ 2) * ENNReal.ofReal (gap X 0) ≤
          ENNReal.ofReal (Mb ^ 2 * q / 2) * ENNReal.ofReal (gap X 0 ^ 2) +
            ENNReal.ofReal (Mb ^ 2 / (2 * q)) := by
        rw [← ENNReal.ofReal_mul hMb2nn, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have key : Mb ^ 2 / (2 * q) * (q * gap X 0 - 1) ^ 2 =
            Mb ^ 2 * q / 2 * gap X 0 ^ 2 + Mb ^ 2 / (2 * q) - Mb ^ 2 * gap X 0 := by
          field_simp
          ring
        have hnn : 0 ≤ Mb ^ 2 / (2 * q) * (q * gap X 0 - 1) ^ 2 :=
          mul_nonneg (div_nonneg hMb2nn (by linarith)) (sq_nonneg _)
        linarith [key, hnn]
      rw [hind]
      calc _ ≤ ∫⁻ D in Ioo (0 : ℝ) (gap X 0), ENNReal.ofReal (Mb ^ 2) := hle
        _ = ENNReal.ofReal (Mb ^ 2) * ENNReal.ofReal (gap X 0) := hval
        _ ≤ ENNReal.ofReal (Mb ^ 2 * q / 2) * ENNReal.ofReal (gap X 0 ^ 2) +
            ENNReal.ofReal (Mb ^ 2 / (2 * q)) := h3
        _ ≤ _ := add_le_add (le_add_of_nonneg_left zero_le) le_rfl
  -- Measurability of the inner integral in the anchored vector.
  have hμ : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hcont : Continuous (fun p : ℝ × (Fin (N : ℕ) → ℝ) => translationError N ℓ γ f p.1 p.2) := by
    unfold translationError
    refine Continuous.sub (continuous_finsetSum _ fun i _ => ?_)
      (continuous_finsetSum _ fun i _ => ?_)
    · exact hf.continuous.comp (by fun_prop)
    · exact hf.continuous.comp (by fun_prop)
  have hmeasΔ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) =>
      ENNReal.ofReal (translationError N ℓ γ f p.1 p.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hcont.pow 2).measurable
  have hψ := measurable_lintegral_arc_sq hN (fun D y => translationError N ℓ γ f D y) hmeasΔ
  have hmeasW : Measurable (fun X : Configuration N => ENNReal.ofReal (gap X 0)) :=
    ENNReal.measurable_ofReal.comp (measurable_gap 0)
  have hmeasW2 : Measurable (fun X : Configuration N => ENNReal.ofReal (gap X 0 ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_gap 0).pow_const 2)
  -- The second moment of the weight, and the probability of the bad event.
  have hI1 : ∫⁻ X, ENNReal.ofReal (gap X 0) ∂(gibbsMeasure P N) ≤ ENNReal.ofReal ((Cg + 1) / 2) := by
    have hpw : ∀ X : Configuration N, ENNReal.ofReal (gap X 0) ≤
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X 0 ^ 2) + ENNReal.ofReal (1 / 2) := by
      intro X
      rw [← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_nonneg (gap X 0 - 1)]
    calc ∫⁻ X, ENNReal.ofReal (gap X 0) ∂(gibbsMeasure P N)
        ≤ ∫⁻ X, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X 0 ^ 2) + ENNReal.ofReal (1 / 2))
            ∂(gibbsMeasure P N) := lintegral_mono hpw
      _ = ENNReal.ofReal (1 / 2) * ∫⁻ X, ENNReal.ofReal (gap X 0 ^ 2) ∂(gibbsMeasure P N) +
            ENNReal.ofReal (1 / 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hmeasW2, lintegral_const,
            measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal Cg + ENNReal.ofReal (1 / 2) := by
          gcongr
          exact hgap N hN
      _ = ENNReal.ofReal ((Cg + 1) / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by norm_num)]
          congr 1
          ring
  have hI2 : ∫⁻ X, ENNReal.ofReal (gap X 0 ^ 2) ∂(gibbsMeasure P N) ≤ ENNReal.ofReal Cg :=
    hgap N hN
  have hbadμ : gibbsMeasure P N bad ≤ ENNReal.ofReal (CB * K ^ (-Bexp)) :=
    hbad N ℓ hN hℓ hℓ1 hK1
  -- The identity `K^{-B} = q²` of the bad-event exponent.
  have hKq : K ^ (-Bexp) = q ^ 2 := by
    rw [hq_def, ← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    congr 1
    push_cast
    ring
  -- The three pieces of the integrand: good part, second moment, and bad indicator.
  have hsq : ∀ x : ℝ, (K ^ x) ^ 2 = K ^ (2 * x) := by
    intro x
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    congr 1
    push_cast
    ring
  have hsplitK : K ^ (γ + lam + ε') = K ^ γ * K ^ (lam + ε') := by
    rw [show γ + lam + ε' = γ + (lam + ε') by ring, Real.rpow_add hK0]
  have hMb' : Mb = 18 * kernelSupConst s lam ε' * K ^ (γ + lam + ε') := by
    rw [hMb_def, hsplitK]
    ring
  have hMbq : Mb ^ 2 * q ≤ 324 * kernelSupConst s lam ε' ^ 2 := by
    have hpow2 : (18 * kernelSupConst s lam ε' * K ^ (γ + lam + ε')) ^ 2 =
        324 * kernelSupConst s lam ε' ^ 2 * K ^ (2 * (γ + lam + ε')) := by
      rw [← hsq]
      ring
    have e1 : Mb ^ 2 * q = 324 * kernelSupConst s lam ε' ^ 2 *
        K ^ (2 * (γ + lam + ε') + -(Bexp / 2)) := by
      rw [hMb', hq_def, hpow2, Real.rpow_add hK0 (2 * (γ + lam + ε')) (-(Bexp / 2))]
      ring
    rw [e1]
    have hexp : 2 * (γ + lam + ε') + -(Bexp / 2) ≤ 0 := by
      rw [hBexp_def]
      linarith [hε'ε₀]
    have hle1 : K ^ (2 * (γ + lam + ε') + -(Bexp / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hK1 hexp
    have hM0 : 0 ≤ 324 * kernelSupConst s lam ε' ^ 2 := by positivity
    exact mul_le_of_le_one_right hM0 hle1
  have hA1le : A1 ≤ goodConst s γ lam ε' ^ 2 * (K ^ (2 * lam) * K ^ (2 * (3 + lam) * ε)) := by
    rw [hA1_def]
    have h1 : (K ^ (lam + (3 + lam) * ε')) ^ 2 ≤ K ^ (2 * lam) * K ^ (2 * (3 + lam) * ε) := by
      rw [hsq, ← Real.rpow_add hK0]
      apply Real.rpow_le_rpow_of_exponent_le hK1
      nlinarith [mul_le_mul_of_nonneg_left hε'ε (by linarith : (0 : ℝ) ≤ 3 + lam)]
    calc (goodConst s γ lam ε' * K ^ (lam + (3 + lam) * ε')) ^ 2
        = goodConst s γ lam ε' ^ 2 * (K ^ (lam + (3 + lam) * ε')) ^ 2 := by ring
      _ ≤ goodConst s γ lam ε' ^ 2 * (K ^ (2 * lam) * K ^ (2 * (3 + lam) * ε)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- Integrate the pointwise bound against the Gibbs measure, and split the three terms.
  unfold rotAnchoredLaw
  rw [lintegral_map hψ (measurable_rotAnchorVec N)]
  refine (lintegral_mono hpt).trans ?_
  have hmeasT1 : Measurable (fun X : Configuration N => ENNReal.ofReal A1 * ENNReal.ofReal (gap X 0)) :=
    hmeasW.const_mul _
  have hmeasT2 : Measurable (fun X : Configuration N =>
      ENNReal.ofReal (Mb ^ 2 * q / 2) * ENNReal.ofReal (gap X 0 ^ 2)) := hmeasW2.const_mul _
  have hmeasT12 : Measurable (fun X : Configuration N =>
      ENNReal.ofReal A1 * ENNReal.ofReal (gap X 0) +
        ENNReal.ofReal (Mb ^ 2 * q / 2) * ENNReal.ofReal (gap X 0 ^ 2)) := hmeasT1.add hmeasT2
  rw [lintegral_add_left hmeasT12, lintegral_add_left hmeasT1,
    lintegral_const_mul _ hmeasW, lintegral_const_mul _ hmeasW2]
  have hI3 : ∫⁻ X, bad.indicator (fun _ => ENNReal.ofReal (Mb ^ 2 / (2 * q))) X ∂(gibbsMeasure P N) ≤
      ENNReal.ofReal (Mb ^ 2 / (2 * q)) * ENNReal.ofReal (CB * K ^ (-Bexp)) :=
    (lintegral_indicator_const_le _ _).trans
      (mul_le_mul_of_nonneg_left hbadμ (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal (Mb ^ 2 / (2 * q))))
  have hcomb := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hI1 (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal A1))
    (mul_le_mul_of_nonneg_left hI2 (zero_le : (0 : ENNReal) ≤ ENNReal.ofReal (Mb ^ 2 * q / 2))))
    hI3
  refine hcomb.trans ?_
  -- Convert the sum of the three products into one `ofReal`.
  have hCgp : 0 ≤ (Cg + 1) / 2 := by linarith
  have hCBp : 0 ≤ (Cg + CB) / 2 := by linarith
  have hP : 0 ≤ A1 * ((Cg + 1) / 2) := mul_nonneg hA1nn hCgp
  have hQ1 : 0 ≤ Mb ^ 2 * q / 2 := div_nonneg (mul_nonneg hMb2nn hq0.le) (by norm_num)
  have hQ : 0 ≤ Mb ^ 2 * q / 2 * Cg := mul_nonneg hQ1 hCg.le
  have hR1 : 0 ≤ Mb ^ 2 / (2 * q) := div_nonneg hMb2nn (by linarith)
  have hR : 0 ≤ Mb ^ 2 / (2 * q) * (CB * K ^ (-Bexp)) :=
    mul_nonneg hR1 (mul_nonneg hCB.le (Real.rpow_nonneg hK0.le _))
  have hEq : ENNReal.ofReal A1 * ENNReal.ofReal ((Cg + 1) / 2) +
      ENNReal.ofReal (Mb ^ 2 * q / 2) * ENNReal.ofReal Cg +
      ENNReal.ofReal (Mb ^ 2 / (2 * q)) * ENNReal.ofReal (CB * K ^ (-Bexp)) =
      ENNReal.ofReal (A1 * ((Cg + 1) / 2) + Mb ^ 2 * q / 2 * Cg +
        Mb ^ 2 / (2 * q) * (CB * K ^ (-Bexp))) := by
    rw [ENNReal.ofReal_add (add_nonneg hP hQ) hR, ENNReal.ofReal_add hP hQ,
      ENNReal.ofReal_mul hA1nn, ENNReal.ofReal_mul hQ1, ENNReal.ofReal_mul hR1]
  rw [hEq]
  apply ENNReal.ofReal_le_ofReal
  -- The real estimate: the constant `C` absorbs the two terms.
  have e3 : Mb ^ 2 / (2 * q) * (CB * K ^ (-Bexp)) = Mb ^ 2 * q / 2 * CB := by
    rw [hKq]
    field_simp
  have hX1 : 1 ≤ K ^ (2 * lam) := Real.one_le_rpow hK1 (by linarith)
  have hX2 : 1 ≤ K ^ (2 * (3 + lam) * ε) :=
    Real.one_le_rpow hK1 (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hε.le)
  have hXX : K ^ (2 * lam) * K ^ (2 * (3 + lam) * ε) ≤
      K ^ (2 * (3 + lam) * ε) * (1 + K ^ (2 * lam)) := by
    nlinarith
  have hY : 1 ≤ K ^ (2 * (3 + lam) * ε) * (1 + K ^ (2 * lam)) :=
    one_le_mul_of_one_le_of_one_le hX2 (by linarith)
  have hG' : 0 ≤ goodConst s γ lam ε' ^ 2 * ((Cg + 1) / 2) := mul_nonneg (sq_nonneg _) hCgp
  have hM' : 0 ≤ 324 * kernelSupConst s lam ε' ^ 2 * ((Cg + CB) / 2) :=
    mul_nonneg (by positivity) hCBp
  have t1 : A1 * ((Cg + 1) / 2) ≤
      goodConst s γ lam ε' ^ 2 * ((Cg + 1) / 2) * (K ^ (2 * (3 + lam) * ε) * (1 + K ^ (2 * lam))) := by
    calc A1 * ((Cg + 1) / 2)
        ≤ goodConst s γ lam ε' ^ 2 * (K ^ (2 * lam) * K ^ (2 * (3 + lam) * ε)) * ((Cg + 1) / 2) :=
          mul_le_mul_of_nonneg_right hA1le hCgp
      _ = goodConst s γ lam ε' ^ 2 * ((Cg + 1) / 2) * (K ^ (2 * lam) * K ^ (2 * (3 + lam) * ε)) := by
          ring
      _ ≤ goodConst s γ lam ε' ^ 2 * ((Cg + 1) / 2) *
          (K ^ (2 * (3 + lam) * ε) * (1 + K ^ (2 * lam))) :=
          mul_le_mul_of_nonneg_left hXX hG'
  have t2 : Mb ^ 2 * q / 2 * (Cg + CB) ≤
      324 * kernelSupConst s lam ε' ^ 2 * ((Cg + CB) / 2) *
        (K ^ (2 * (3 + lam) * ε) * (1 + K ^ (2 * lam))) := by
    calc Mb ^ 2 * q / 2 * (Cg + CB) = (Mb ^ 2 * q) * ((Cg + CB) / 2) := by ring
      _ ≤ 324 * kernelSupConst s lam ε' ^ 2 * ((Cg + CB) / 2) := mul_le_mul_of_nonneg_right hMbq hCBp
      _ ≤ 324 * kernelSupConst s lam ε' ^ 2 * ((Cg + CB) / 2) *
          (K ^ (2 * (3 + lam) * ε) * (1 + K ^ (2 * lam))) := le_mul_of_one_le_right hM' hY
  have hLHS : A1 * ((Cg + 1) / 2) + Mb ^ 2 * q / 2 * Cg + Mb ^ 2 / (2 * q) * (CB * K ^ (-Bexp)) =
      A1 * ((Cg + 1) / 2) + Mb ^ 2 * q / 2 * (Cg + CB) := by
    rw [e3]
    ring
  have hRHS : (goodConst s γ lam ε' ^ 2 * ((Cg + 1) / 2) +
      324 * kernelSupConst s lam ε' ^ 2 * ((Cg + CB) / 2)) * K ^ (2 * (3 + lam) * ε) *
      (1 + K ^ (2 * lam)) =
      goodConst s γ lam ε' ^ 2 * ((Cg + 1) / 2) *
        (K ^ (2 * (3 + lam) * ε) * (1 + K ^ (2 * lam))) +
      324 * kernelSupConst s lam ε' ^ 2 * ((Cg + CB) / 2) *
        (K ^ (2 * (3 + lam) * ε) * (1 + K ^ (2 * lam))) := by
    ring
  rw [hLHS, hRHS]
  linarith [t1, t2]

end Riesz1
