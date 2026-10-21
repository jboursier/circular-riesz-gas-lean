/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Elementary.Covariance
public import Riesz1.ToMathlib.Elementary.Absorption
public import Riesz1.ToMathlib.LogConcave.InverseInterpolation

/-!
# Covariance and absorption for inverse moments

Internal probability-space algebra used in Lemma 4.5.
The hypotheses are IBP identities, not additional assumptions on Lemma 4.5.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Internal covariance calculation from the three integration-by-parts identities. -/
theorem inverse_covariance_recurrence_internal {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (Y b : Ω → ℝ) (I : Set ℝ)
    (v : ℝ → ℝ) (hI : ∀ t ∈ I, 0 < t) (hY : ∀ x, Y x ∈ I) (hpos : ∀ x, 0 < Y x)
    (hb : ∀ x, b x = v (Y x)) (hv : MonotoneOn v I)
    {a s q : ℝ} (hs : 0 < s) (hq : 0 < q)
    (hiY : Integrable Y μ) (hmean : (∫ x, Y x ∂μ) = 1)
    (hi : ∀ r : ℝ, 0 ≤ r → Integrable (fun x => Y x ^ (-r)) μ)
    (hw : Integrable (fun x => b x - a * Y x ^ (-(s + 1))) μ)
    (hyw : Integrable (fun x => Y x * (b x - a * Y x ^ (-(s + 1)))) μ)
    (hqw : Integrable (fun x => Y x ^ (-q) * (b x - a * Y x ^ (-(s + 1)))) μ)
    (h0 : (∫ x, b x - a * Y x ^ (-(s + 1)) ∂μ) = 0)
    (h1 : (∫ x, Y x * (b x - a * Y x ^ (-(s + 1))) ∂μ) = 1)
    (h2 : (∫ x, Y x ^ (-q) * (b x - a * Y x ^ (-(s + 1))) ∂μ) =
      -q * ∫ x, Y x ^ (-(q + 1)) ∂μ) :
    a * ((∫ x, Y x ^ (-(s + 1)) ∂μ) - ∫ x, Y x ^ (-s) ∂μ) ≤ 1 ∧
    a * (∫ x, Y x ^ (-(q + s + 1)) ∂μ) ≤
      a * (∫ x, Y x ^ (-q) ∂μ) * (∫ x, Y x ^ (-(s + 1)) ∂μ) +
        q * ∫ x, Y x ^ (-(q + 1)) ∂μ := by
  have hy (x : Ω) : Y x * Y x ^ (-(s + 1)) = Y x ^ (-s) := by
    nth_rw 1 [← Real.rpow_one (Y x)]
    rw [← Real.rpow_add (hpos x)]
    congr 1
    ring
  have hqpow (x : Ω) : Y x ^ (-q) * Y x ^ (-(s + 1)) = Y x ^ (-(q + s + 1)) := by
    rw [← Real.rpow_add (hpos x)]
    congr 1
    ring
  have hib : Integrable b μ := (hw.add ((hi (s + 1) (by linarith)).const_mul a)).congr
    (ae_of_all μ fun x => by dsimp; ring)
  have hiyb : Integrable (fun x => Y x * b x) μ :=
    (hyw.add ((hi s hs.le).const_mul a)).congr (ae_of_all μ fun x => by
      dsimp
      rw [← hy x]
      ring)
  have hiqb : Integrable (fun x => Y x ^ (-q) * b x) μ :=
    (hqw.add ((hi (q + s + 1) (by linarith)).const_mul a)).congr (ae_of_all μ fun x => by
      dsimp
      rw [← hqpow x]
      ring)
  have eb : (∫ x, b x ∂μ) = a * ∫ x, Y x ^ (-(s + 1)) ∂μ := by
    rw [integral_sub hib ((hi (s + 1) (by linarith)).const_mul a), integral_const_mul] at h0
    linarith
  have eyb : (∫ x, Y x * b x ∂μ) = 1 + a * ∫ x, Y x ^ (-s) ∂μ := by
    have he : (fun x => Y x * (b x - a * Y x ^ (-(s + 1)))) =
        fun x => Y x * b x - a * Y x ^ (-s) := by
      funext x
      rw [← hy x]
      ring
    rw [he, integral_sub hiyb ((hi s hs.le).const_mul a), integral_const_mul] at h1
    linarith
  have eqb : (∫ x, Y x ^ (-q) * b x ∂μ) =
      a * (∫ x, Y x ^ (-(q + s + 1)) ∂μ) - q * ∫ x, Y x ^ (-(q + 1)) ∂μ := by
    have he : (fun x => Y x ^ (-q) * (b x - a * Y x ^ (-(s + 1)))) =
        fun x => Y x ^ (-q) * b x - a * Y x ^ (-(q + s + 1)) := by
      funext x
      rw [← hqpow x]
      ring
    rw [he, integral_sub hiqb ((hi (q + s + 1) (by linarith)).const_mul a), integral_const_mul] at h2
    linarith
  have hc1 := covariance_nonneg_of_monotone Y hY id v (fun _ _ _ _ h => h) hv
    hiY (by simpa only [← hb] using hib) (by simpa only [← hb, id_eq] using hiyb)
  have hc2 := covariance_nonpos_of_antitone_monotone Y hY (fun t => t ^ (-q)) v
    (fun x hx y hy hxy => Real.rpow_le_rpow_of_nonpos (hI x hx) hxy (neg_nonpos.mpr hq.le)) hv
    (hi q hq.le) (by simpa only [← hb] using hib) (by simpa only [← hb] using hiqb)
  simp only [id_eq, ← hb, hmean, eb, eyb, eqb, one_mul] at hc1 hc2
  constructor <;> nlinarith [hc1, hc2]

/-- Internal scalar absorption, choosing the bound before the moment sequence. -/
theorem exists_inverse_moment_bound_internal {a s p : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ → ℝ,
      (∀ r, 0 ≤ r → 0 ≤ M r) →
      (∀ r t, 0 ≤ r → 0 < t → r ≤ t → M r ≤ M t ^ (r / t)) →
      a * (M (s + 1) - M s) ≤ 1 →
      (∀ q, 0 < q → a * M (q + s + 1) ≤
        a * M q * M (s + 1) + q * M (q + 1)) → M p ≤ C := by
  let D := max ((2 : ℝ) ^ (1 / (1 - s / (s + 1)))) (2 / a)
  have hD : 0 < D := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 / a) (le_max_right _ _)
  have hu : s / (s + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hbase (M : ℝ → ℝ) (hn : ∀ r, 0 ≤ r → 0 ≤ M r)
      (hi : ∀ r t, 0 ≤ r → 0 < t → r ≤ t → M r ≤ M t ^ (r / t))
      (hb : a * (M (s + 1) - M s) ≤ 1) : M (s + 1) ≤ D := by
    have hh := hi s (s + 1) hs.le (by linarith) (by linarith)
    have hh' : M (s + 1) - M s ≤ 1 / a := (le_div_iff₀ ha).mpr (by nlinarith only [hb])
    have hf : M (s + 1) ≤ M (s + 1) ^ (s / (s + 1)) + 1 / a := by linarith
    simpa only [D, div_eq_mul_inv, one_mul] using
      le_max_of_le_rpow_add (M (s + 1)) (1 / a) (s / (s + 1))
        (hn _ (by linarith)) hu hf
  by_cases hps : p ≤ s + 1
  · refine ⟨D ^ (p / (s + 1)), Real.rpow_pos_of_pos hD _, ?_⟩
    intro M hn hi hb _
    exact (hi p (s + 1) hp.le (by linarith) hps).trans
      (Real.rpow_le_rpow (hn _ (by linarith)) (hbase M hn hi hb) (by positivity))
  · let q := p - s - 1
    have hq : 0 < q := by dsimp [q]; linarith
    have he : q + s + 1 = p := by dsimp [q]; ring
    have hpu : q / p < 1 := (div_lt_one hp).mpr (by dsimp [q]; linarith)
    have hpv : (q + 1) / p < 1 := (div_lt_one hp).mpr (by dsimp [q]; linarith)
    let C := max ((4 * D) ^ (1 / (1 - q / p))) ((4 * (q / a)) ^ (1 / (1 - (q + 1) / p)))
    refine ⟨C, lt_of_lt_of_le (by positivity : (0 : ℝ) < (4 * D) ^ (1 / (1 - q / p)))
      (le_max_left _ _), ?_⟩
    intro M hn hi hb hrec
    apply le_max_of_le_add_rpow (M p) D (q / a) (q / p) ((q + 1) / p)
      (hn p hp.le) hD (div_pos hq ha) hpu hpv
    have hb' := hbase M hn hi hb
    have hrec' := hrec q hq
    rw [he] at hrec'
    have hrec'' : M p ≤ M q * M (s + 1) + (q / a) * M (q + 1) := by
      apply (le_of_mul_le_mul_left _ ha)
      calc a * M p ≤ a * M q * M (s + 1) + q * M (q + 1) := hrec'
           _ = a * (M q * M (s + 1) + (q / a) * M (q + 1)) := by field_simp
    have hq' := hi q p hq.le hp (by dsimp [q]; linarith)
    have hq1 := hi (q + 1) p (by linarith) hp (by dsimp [q]; linarith)
    calc M p ≤ M q * M (s + 1) + (q / a) * M (q + 1) := hrec''
         _ ≤ M p ^ (q / p) * D + (q / a) * M p ^ ((q + 1) / p) :=
           add_le_add (mul_le_mul hq' hb' (hn _ (by linarith)) (Real.rpow_nonneg (hn p hp.le) _))
             (mul_le_mul_of_nonneg_left hq1 (div_nonneg hq.le ha.le))
         _ = D * M p ^ (q / p) + (q / a) * M p ^ ((q + 1) / p) := by ring

end Riesz1

end
