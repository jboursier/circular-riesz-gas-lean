/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.AssemblyInput
public import Riesz1.CLT.AssemblyStein
public import Riesz1.CLT.AssemblyBound
public import Riesz1.CLT.Smoothing
public import Riesz1.Variance.LoopMasterExistence
public import Riesz1.CLT.NondegeneracyZero
public import Riesz1.CLT.NondegeneracyRegularized

/-!
# Bounded-Lipschitz distance of the normalized statistic (Theorem 3, the rate assertion)

Under the nondegeneracy bound `c ≤ σ_reg` for large `K = Nℓ_N`, the bounded-Lipschitz distance
from the law of `F_N = normalizedStatistic` to `N(0, σ_{ℓ_N}²)` is at most a constant times
`K^{eps + max((s-1)/2, -r)}`, for every `eps > 0`. The proof is the chain of estimates in the
proof of Theorem 3:

* smoothing: `‖F_N - G_N‖₂` (`clt_smoothing_complete_of_variance_uniform`,
  `clt_smoothing_lipschitz`).
* Stein and the two transport errors (`assembly_stein_identity` with the copies of the first and
  second error bounds in the proof of Theorem 3).
* the standard deviations `σ_reg` and `σ_{ℓ_N}` (`cltVariance_sqrt_sub_le` and
  `blDistance_gaussianReal_le`).

The exponent arithmetic is `assembly_exponent_bound`, and the scales with `K < K₀` are absorbed
into the constant, since the distance is at most two.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace Riesz1.Internal

/-- The exponent bookkeeping of the bounded-Lipschitz estimate (pure real analysis). Every power
of `K` produced by the smoothing, Stein and standard-deviation estimates is at most the final
exponent `eps + max((s-1)/2, -r)`, with `r = (2-s)(s-2α)/(2(4+s))` and `δ = K^{-(2-s)/(4+s)}`. -/
theorem assembly_exponent_bound (s α eps Cs C₁ C₂ M κ0 τ₁ τ₂ τ₃ K : ℝ) (hs0 : 0 < s)
    (hs1 : s < 1) (hα : α < s / 2) (heps : 0 < eps) (hK : 1 ≤ K) (hCs : 0 ≤ Cs) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hM : 0 ≤ M) (hκ0 : 0 ≤ κ0) (hτ₁ : τ₁ = eps / 2) (hτ₂ : 0 < τ₂)
    (hτ₂le : τ₂ ≤ eps / 2) (hτ₃le : τ₃ ≤ eps / 2) :
    Cs * ((K ^ (-((2 - s) / (4 + s)))) ^ (s / 2 - α - τ₁) +
        K ^ (max ((s - 1) / 2) (α - s / 2) + τ₁)) +
      ((C₁ * M) * K ^ (s / 2 - 1 + τ₂) * (K ^ (-((2 - s) / (4 + s)))) ^ (-2 - α - τ₂) +
        C₂ * K ^ (max ((s - 1) / 2) (α - s / 2) + τ₃)) +
      κ0 * (Cs * (K ^ (-((2 - s) / (4 + s)))) ^ (s / 2 - α - τ₁)) ≤
    (2 * Cs + C₁ * M + C₂ + κ0 * Cs) *
      K ^ (eps + max ((s - 1) / 2) (-((2 - s) * (s - 2 * α) / (2 * (4 + s))))) := by
  have hK0 : 0 < K := by linarith
  set dd := (2 - s) / (4 + s) with hdd
  set A := s / 2 - α with hA
  set r := (2 - s) * (s - 2 * α) / (2 * (4 + s)) with hr
  set q := max ((s - 1) / 2) (α - s / 2) with hq
  set p := eps + max ((s - 1) / 2) (-r) with hp
  have hdd0 : 0 < dd := div_pos (by linarith) (by linarith)
  have hdd1 : dd ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hA0 : 0 < A := by rw [hA]; linarith
  have hr_dA : r = dd * A := by
    rw [hr, hdd, hA]; field_simp
  have hsid : s / 2 - 1 + dd * (2 + α) = -r := by
    rw [hr_dA, hA]; rw [hdd]; field_simp; ring
  have hqr : α - s / 2 ≤ -r := by
    rw [hr_dA]; nlinarith [mul_nonneg hA0.le (sub_nonneg.mpr hdd1)]
  have key : ∀ x : ℝ, (K ^ (-dd)) ^ x = K ^ (-dd * x) := fun x => (Real.rpow_mul hK0.le _ _).symm
  have e1 : (K ^ (-dd)) ^ (s / 2 - α - τ₁) = K ^ (-r + dd * τ₁) := by
    rw [key, show -dd * (s / 2 - α - τ₁) = -r + dd * τ₁ by rw [hr_dA, hA]; ring]
  have e2 : (K ^ (-dd)) ^ (-2 - α - τ₂) = K ^ (dd * (2 + α + τ₂)) := by
    rw [key]; congr 1; ring
  have e3 : K ^ (s / 2 - 1 + τ₂) * K ^ (dd * (2 + α + τ₂)) = K ^ (-r + (1 + dd) * τ₂) := by
    rw [← Real.rpow_add hK0]; congr 1; rw [← hsid]; ring
  have hpr : -r ≤ max ((s - 1) / 2) (-r) := le_max_right _ _
  have hpq : α - s / 2 ≤ max ((s - 1) / 2) (-r) := hqr.trans hpr
  have hqp : q ≤ max ((s - 1) / 2) (-r) := max_le (le_max_left _ _) hpq
  have l1 : -r + dd * τ₁ ≤ p := by
    have : dd * τ₁ ≤ eps := by rw [hτ₁]; nlinarith
    rw [hp]; linarith
  have l2 : q + τ₁ ≤ p := by
    rw [hτ₁, hp]; linarith
  have l3 : -r + (1 + dd) * τ₂ ≤ p := by
    have : (1 + dd) * τ₂ ≤ eps := by nlinarith
    rw [hp]; linarith
  have l4 : q + τ₃ ≤ p := by
    rw [hp]; linarith
  have hpow : ∀ x y : ℝ, x ≤ y → K ^ x ≤ K ^ y := fun x y h => Real.rpow_le_rpow_of_exponent_le hK h
  rw [e1, e2]
  have t1 : K ^ (-r + dd * τ₁) ≤ K ^ p := hpow _ _ l1
  have t2 : K ^ (q + τ₁) ≤ K ^ p := hpow _ _ l2
  have t3 : K ^ (-r + (1 + dd) * τ₂) ≤ K ^ p := hpow _ _ l3
  have t4 : K ^ (q + τ₃) ≤ K ^ p := hpow _ _ l4
  have hmul : (C₁ * M) * K ^ (s / 2 - 1 + τ₂) * K ^ (dd * (2 + α + τ₂)) ≤ (C₁ * M) * K ^ p := by
    rw [mul_assoc, e3]
    exact mul_le_mul_of_nonneg_left t3 (mul_nonneg hC₁ hM)
  have hA1 : Cs * (K ^ (-r + dd * τ₁) + K ^ (q + τ₁)) ≤ Cs * (K ^ p + K ^ p) :=
    mul_le_mul_of_nonneg_left (add_le_add t1 t2) hCs
  have hA2 : C₂ * K ^ (q + τ₃) ≤ C₂ * K ^ p := mul_le_mul_of_nonneg_left t4 hC₂
  have hA3 : κ0 * (Cs * K ^ (-r + dd * τ₁)) ≤ κ0 * (Cs * K ^ p) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t1 hCs) hκ0
  nlinarith [hA1, hA2, hA3, hmul]

/-- The small-scale absorption: for `1 ≤ K ≤ K₀`, the constant `2 max(1, K₀^{-p})` bounds `2`
after multiplication by `K^p`. -/
lemma assembly_small_scale (K K₀ p : ℝ) (hK : 1 ≤ K) (hKK₀ : K < K₀) :
    2 ≤ (2 * max 1 (K₀ ^ (-p))) * K ^ p := by
  have hK0 : 0 < K := by linarith
  have hK₀0 : 0 < K₀ := by linarith
  rcases le_total 0 p with hp | hp
  · have h1 : 1 ≤ K ^ p := Real.one_le_rpow hK hp
    have h2 : 1 ≤ max 1 (K₀ ^ (-p)) := le_max_left _ _
    nlinarith
  · have h1 : K₀ ^ (-p) * K ^ p ≥ 1 := by
      have hle : K ^ p ≥ K₀ ^ p := Real.rpow_le_rpow_of_nonpos hK0 hKK₀.le hp
      have hK0p : 0 < K₀ ^ p := Real.rpow_pos_of_pos hK₀0 p
      have hinv : K₀ ^ (-p) * K₀ ^ p = 1 := by
        rw [← Real.rpow_add hK₀0]; simp
      nlinarith [Real.rpow_pos_of_pos hK₀0 (-p)]
    have h2 : K₀ ^ (-p) ≤ max 1 (K₀ ^ (-p)) := le_max_right _ _
    have hKp : 0 < K ^ p := Real.rpow_pos_of_pos hK0 p
    nlinarith [Real.rpow_pos_of_pos hK₀0 (-p)]

/-- **Nondegenerate bounded-Lipschitz bound.** Let `P`, `p`, `α`, `d` be data with `α < s/2`, and
let `c > 0` and `K₁ ≥ 1` be such that every admissible scale with `Nℓ_N ≥ K₁` has regularized
standard deviation at least `c`. Then for every `eps > 0` there is `C > 0` such that for every
admissible scale sequence and every particle number with `Nℓ_N ≥ 1`, the law of the normalized
statistic is within the bounded-Lipschitz distance `C (Nℓ_N)^{eps + max((s-1)/2, -r)}` of
`N(0, σ_{ℓ_N}²)`. -/
theorem assembly_bl_bound_of_nondegenerate (hPL : External.PrekopaLeindler)
    (hErr1 : AssemblyErrorOneConclusion) (hErr2 : AssemblyErrorTwoConclusion)
    (hQVU : QuantitativeVarianceUniformConclusion) (P : Parameters) (p : Profile) (α : ℝ)
    (d : TestData) (hα : α < P.val.2 / 2) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (eps : ℝ)
    (heps : 0 < eps) (c K₁ : ℝ) (hc : 0 < c)
    (hnd : ∀ ell : Scales, Admissible P p ell α d → ∀ N : ℕ+, K₁ ≤ (N : ℝ) * (ell N).val →
      cltVariance P (ell N)
          ⟨(fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
            cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩ < ⊤ ∧
        c ≤ Real.sqrt (cltVariance P (ell N)
          ⟨(fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
            cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩).toReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d → ∀ N : ℕ+,
      1 ≤ (N : ℝ) * (ell N).val →
      ∃ law : ProbabilityMeasure ℝ,
        (law : Measure ℝ) = (gibbsMeasure P N).map (normalizedStatistic P p ell N) ∧
        blDistance law ⟨normalLaw (circleVariance P p (ell N)).toNNReal,
          by unfold normalLaw; infer_instance⟩ ≤
          ENNReal.ofReal (C * ((N : ℝ) * (ell N).val) ^
            (eps + max ((P.val.2 - 1) / 2) (-((2 - P.val.2) * (P.val.2 - 2 * α) / (2 * (4 + P.val.2)))))) := by
  -- Constants of the three estimates, each with its own threshold.
  obtain ⟨Cs, Ks, hCs, hKs, hsm⟩ :=
    clt_smoothing_complete_of_variance_uniform hQVU P p α d ρ hρ (eps / 2) (half_pos heps)
  obtain ⟨τ₀, hτ₀, hE1⟩ := hErr1 P p α d hρ
  obtain ⟨τ₀', hτ₀', hE2⟩ := hErr2 P p α d hρ
  have hτ₂pos : 0 < min (τ₀ / 2) (eps / 2) := lt_min (half_pos hτ₀) (half_pos heps)
  have hτ₃pos : 0 < min (τ₀' / 2) (eps / 2) := lt_min (half_pos hτ₀') (half_pos heps)
  obtain ⟨C₁, K₃, hC₁, hK₃, hE1'⟩ :=
    hE1 (min (τ₀ / 2) (eps / 2)) hτ₂pos (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hτ₀))
  obtain ⟨C₂, K₄, hC₂, hK₄, hE2'⟩ :=
    hE2 (min (τ₀' / 2) (eps / 2)) hτ₃pos (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hτ₀'))
  have hτ₂le : min (τ₀ / 2) (eps / 2) ≤ eps / 2 := min_le_right _ _
  have hτ₃le : min (τ₀' / 2) (eps / 2) ≤ eps / 2 := min_le_right _ _
  set τ₁ : ℝ := eps / 2 with hτ₁def
  set τ₂ : ℝ := min (τ₀ / 2) (eps / 2) with hτ₂def
  set τ₃ : ℝ := min (τ₀' / 2) (eps / 2) with hτ₃def
  have hτ₂pos' : 0 < τ₂ := hτ₂pos
  have hτ₃pos' : 0 < τ₃ := hτ₃pos
  -- Global constants, independent of the scale sequence and of `N`.
  set K₀ : ℝ := max (max K₃ K₄) (max Ks K₁) with hK₀def
  set κ0 : ℝ := ∫ x, |x| ∂(ProbabilityTheory.gaussianReal 0 1) with hκ0def
  have hκ0 : 0 ≤ κ0 := integral_nonneg fun x => abs_nonneg x
  set M : ℝ := Real.sqrt (2 / Real.pi) / c with hMdef
  have hM : 0 ≤ M := div_nonneg (Real.sqrt_nonneg _) hc.le
  set Cmain : ℝ := 2 * Cs + C₁ * M + C₂ + κ0 * Cs with hCmaindef
  have hCmainpos : 0 < Cmain := by
    have h1 := mul_nonneg hC₁.le hM
    have h2 := mul_nonneg hκ0 hCs.le
    rw [hCmaindef]; linarith
  set pexp : ℝ := eps + max ((P.val.2 - 1) / 2) (-((2 - P.val.2) * (P.val.2 - 2 * α) /
    (2 * (4 + P.val.2)))) with hpexpdef
  set Cfin : ℝ := max Cmain (2 * max 1 (K₀ ^ (-pexp))) with hCfindef
  refine ⟨Cfin, lt_of_lt_of_le hCmainpos (le_max_left _ _), ?_⟩
  intro ell hadm N hK1
  set K : ℝ := (N : ℝ) * (ell N).val with hKdef
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  refine ⟨⟨(gibbsMeasure P N).map (normalizedStatistic P p ell N), inferInstance⟩, rfl, ?_⟩
  by_cases hKK : K₀ ≤ K
  · -- The main estimate: the scale is large, so the three error terms all apply.
    have hK3 : K₃ ≤ K := ((le_max_left K₃ K₄).trans (le_max_left _ _)).trans hKK
    have hK4 : K₄ ≤ K := ((le_max_right K₃ K₄).trans (le_max_left _ _)).trans hKK
    have hKs' : Ks ≤ K := ((le_max_left Ks K₁).trans (le_max_right _ _)).trans hKK
    have hK1' : K₁ ≤ K := ((le_max_right Ks K₁).trans (le_max_right _ _)).trans hKK
    -- Smoothing at this scale.
    have hsmN := hsm ell hadm N hKs'
    dsimp only at hsmN
    obtain ⟨hVe, hsqE, -, hL2⟩ := hsmN
    -- Nondegeneracy of the regularized profile.
    obtain ⟨hVg, hcg⟩ := hnd ell hadm N hK1'
    -- The smooth transport of the regularized profile.
    obtain ⟨ψ, hψ, htr⟩ := loopMaster_exists_transport_length P (loopMasterLength (ell N))
      (cltReg hρ P N (ell N) ⟨periodizedProfile p (observationLength (ell N)),
        periodizedProfileL2 p (ell N)⟩)
      (cltReg_contDiff hρ P N (ell N) ⟨periodizedProfile p (observationLength (ell N)),
        periodizedProfileL2 p (ell N)⟩)
    -- The standard deviation of the regularized profile and its variance identity.
    set σ : ℝ := Real.sqrt (cltVariance P (ell N)
      ⟨(fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
        cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩).toReal
      with hσdef
    have hσpos : 0 < σ := lt_of_lt_of_le hc hcg
    have hσV : ENNReal.ofReal (σ ^ 2) = cltVariance P (ell N)
        ⟨(fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
          cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩ := by
      rw [hσdef, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVg.ne]
    have hG2 := (smoothing_statistics_memLp P p ell N hρ).2
    have hF2 := (smoothing_statistics_memLp P p ell N hρ).1
    have hGm : AEMeasurable (cltStat P N (ell N)
        (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩))
        (gibbsMeasure P N) := hG2.aestronglyMeasurable.aemeasurable
    have hFm : AEMeasurable (normalizedStatistic P p ell N) (gibbsMeasure P N) :=
      hF2.aestronglyMeasurable.aemeasurable
    -- Stein bound for every bounded-Lipschitz test: the two transport errors.
    have hstein : ∀ f : ℝ → ℝ, BLTest f →
        |(∫ X, f (cltStat P N (ell N) (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩) X)
            ∂(gibbsMeasure P N)) -
          ∫ z, f (σ * z) ∂(ProbabilityTheory.gaussianReal 0 1)| ≤
        C₁ * M * K ^ (P.val.2 / 2 - 1 + τ₂) * cltDelta P N (ell N) ^ (-2 - α - τ₂) +
          C₂ * K ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ₃) := by
      intro f hf
      obtain ⟨u, hu1, hub, hu'b, hid⟩ := assembly_stein_identity hPL P N (ell N) hK1 hρ _ ψ hψ htr σ
        hσpos hσV hG2 hf
      rw [hid, abs_neg]
      have hM' : ∀ x, |deriv u x| ≤ M := fun x =>
        (hu'b x).trans (div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hc hcg)
      have hE1b := hE1' ell hadm N hK3 ψ hψ htr σ hσV u hu1 ⟨1, hub⟩ M hM'
      have hE2b := hE2' ell hadm N hK4 ψ hψ htr u hu1 1 hub
      rw [mul_one] at hE2b
      exact (abs_add_le _ _).trans (add_le_add hE1b hE2b)
    -- The three estimates, each a bound on the bounded-Lipschitz distance.
    set B1 : ℝ := Cs * (cltDelta P N (ell N) ^ (P.val.2 / 2 - α - τ₁) +
      K ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ₁)) with hB1def
    set B2 : ℝ := C₁ * M * K ^ (P.val.2 / 2 - 1 + τ₂) * cltDelta P N (ell N) ^ (-2 - α - τ₂) +
      C₂ * K ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ₃) with hB2def
    set B3 : ℝ := κ0 * (Cs * cltDelta P N (ell N) ^ (P.val.2 / 2 - α - τ₁)) with hB3def
    have hFi : ∀ f : ℝ → ℝ, BLTest f →
        Integrable (fun X => f (normalizedStatistic P p ell N X)) (gibbsMeasure P N) :=
      fun f hf => Integrable.of_bound (hf.1.continuous.comp_aestronglyMeasurable hFm.aestronglyMeasurable)
        1 (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hf.2.1 _)
    have hGi : ∀ f : ℝ → ℝ, BLTest f →
        Integrable (fun X => f (cltStat P N (ell N) (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩) X))
          (gibbsMeasure P N) :=
      fun f hf => Integrable.of_bound (hf.1.continuous.comp_aestronglyMeasurable hGm.aestronglyMeasurable)
        1 (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hf.2.1 _)
    have h1 := blDistance_map_le (gibbsMeasure P N) hFm hGm (B := B1) fun f hf =>
      (clt_smoothing_lipschitz P p ell N hρ f (blTest_lipschitz hf) (hFi f hf) (hGi f hf)).trans hL2
    have h2 := blDistance_map_le_gaussian (gibbsMeasure P N) hGm ⟨σ, hσpos.le⟩ (B := B2) hstein
    -- The standard deviations: `σ_reg` against `σ_{ℓ_N}`, through the seminorm triangle inequality.
    set fS : {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
      ⟨(fun x => (testAtScale p (ell N) x : ℂ)), testAtScaleL2 p (ell N)⟩ with hfS
    set gS : {f : UnitAddCircle → ℂ // MemLp f 2 volume} :=
      ⟨(fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
        cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩ with hgS
    have hfSfin : cltVariance P (ell N) fS ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.add_ne_top.mpr ⟨hVg.ne, hVe.ne⟩)) (nondegeneracy_variance_two_term P (ell N) fS gS)
    have htri := cltVariance_sqrt_sub_le P (ell N) fS gS hfSfin hVg.ne hVe.ne
    have hsl' : ∀ sl : ℝ≥0, sl = NNReal.sqrt (circleVariance P p (ell N)).toNNReal →
        (sl : ℝ) = Real.sqrt (cltVariance P (ell N) fS).toReal := by
      intro sl hsl; rw [hsl, Real.coe_sqrt]; rfl
    have h3 : blDistance ⟨gaussianReal 0 (⟨σ, hσpos.le⟩ ^ 2), inferInstance⟩
        ⟨normalLaw (circleVariance P p (ell N)).toNNReal, by unfold normalLaw; infer_instance⟩ ≤
        ENNReal.ofReal B3 := by
      set sl : ℝ≥0 := NNReal.sqrt (circleVariance P p (ell N)).toNNReal with hsl
      have hraw := blDistance_gaussianReal_le ⟨σ, hσpos.le⟩ sl
      have hnorm : (⟨gaussianReal 0 (sl ^ 2), inferInstance⟩ : ProbabilityMeasure ℝ) =
          ⟨normalLaw (circleVariance P p (ell N)).toNNReal, by unfold normalLaw; infer_instance⟩ :=
        Subtype.ext (by unfold normalLaw; rw [hsl, NNReal.sq_sqrt])
      rw [hnorm] at hraw
      have hcoe : |σ - (sl : ℝ)| ≤ Cs * cltDelta P N (ell N) ^ (P.val.2 / 2 - α - τ₁) := by
        rw [hsl' sl hsl, abs_sub_comm]
        exact htri.trans hsqE
      calc _ ≤ ENNReal.ofReal (|σ - (sl : ℝ)| * κ0) := hraw
        _ ≤ ENNReal.ofReal B3 := ENNReal.ofReal_le_ofReal (by
          rw [hB3def]
          calc |σ - (sl : ℝ)| * κ0 = κ0 * |σ - (sl : ℝ)| := mul_comm _ _
            _ ≤ κ0 * (Cs * cltDelta P N (ell N) ^ (P.val.2 / 2 - α - τ₁)) :=
              mul_le_mul_of_nonneg_left hcoe hκ0)
    -- The three distances add up, and the exponents bound the sum.
    have hδpos : 0 ≤ cltDelta P N (ell N) := (cltDelta_pos P N (ell N)).le
    have hB1nn : 0 ≤ B1 := by
      rw [hB1def]
      exact mul_nonneg hCs.le (add_nonneg (Real.rpow_nonneg hδpos _) (Real.rpow_nonneg hK0.le _))
    have hB2nn : 0 ≤ B2 := by
      rw [hB2def]
      exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hM) (Real.rpow_nonneg hK0.le _))
        (Real.rpow_nonneg hδpos _)) (mul_nonneg hC₂.le (Real.rpow_nonneg hK0.le _))
    have hB3nn : 0 ≤ B3 := by
      rw [hB3def]
      exact mul_nonneg hκ0 (mul_nonneg hCs.le (Real.rpow_nonneg hδpos _))
    have hexp := assembly_exponent_bound P.val.2 α eps Cs C₁ C₂ M κ0 τ₁ τ₂ τ₃ K
      P.property.2.1 P.property.2.2 hα heps hK1 hCs.le hC₁.le hC₂.le hM hκ0 rfl hτ₂pos' hτ₂le hτ₃le
    have hδK : cltDelta P N (ell N) = K ^ (-((2 - P.val.2) / (4 + P.val.2))) := rfl
    rw [← hδK] at hexp
    have hfin : B1 + B2 + B3 ≤ Cmain * K ^ pexp := hexp
    calc _ ≤ blDistance ⟨(gibbsMeasure P N).map (normalizedStatistic P p ell N), inferInstance⟩
          ⟨(gibbsMeasure P N).map (cltStat P N (ell N) (cltScaledFun hρ (ell N)
            (cltDelta_pos P N (ell N)) ⟨periodizedProfile p (observationLength (ell N)),
            periodizedProfileL2 p (ell N)⟩)), inferInstance⟩ +
        blDistance ⟨(gibbsMeasure P N).map (cltStat P N (ell N) (cltScaledFun hρ (ell N)
            (cltDelta_pos P N (ell N)) ⟨periodizedProfile p (observationLength (ell N)),
            periodizedProfileL2 p (ell N)⟩)), inferInstance⟩ ⟨normalLaw (circleVariance P p (ell N)).toNNReal,
          by unfold normalLaw; infer_instance⟩ := blDistance_triangle _ _ _
      _ ≤ ENNReal.ofReal B1 + (ENNReal.ofReal B2 + ENNReal.ofReal B3) := by
          refine add_le_add h1 (le_trans ?_ (add_le_add h2 h3))
          exact blDistance_triangle _ _ _
      _ = ENNReal.ofReal (B1 + (B2 + B3)) := by
          rw [ENNReal.ofReal_add hB1nn (add_nonneg hB2nn hB3nn),
            ENNReal.ofReal_add hB2nn hB3nn]
      _ ≤ ENNReal.ofReal (Cmain * K ^ pexp) := ENNReal.ofReal_le_ofReal (by rw [← add_assoc]; exact hfin)
      _ ≤ ENNReal.ofReal (Cfin * K ^ pexp) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hK0.le _))
  · -- The scale is below the threshold: the distance is at most two.
    have hKK' : K < K₀ := not_le.mp hKK
    have hsmall := assembly_small_scale K K₀ pexp hK1 hKK'
    refine (blDistance_le_two _ _).trans ?_
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    apply ENNReal.ofReal_le_ofReal
    calc (2 : ℝ) ≤ (2 * max 1 (K₀ ^ (-pexp))) * K ^ pexp := hsmall
      _ ≤ Cfin * K ^ pexp :=
        mul_le_mul_of_nonneg_right (by rw [hCfindef]; linarith [le_max_right Cmain (2 * max 1 (K₀ ^ (-pexp)))])
          (Real.rpow_nonneg hK0.le _)

end Riesz1.Internal

end
end
