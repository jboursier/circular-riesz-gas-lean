/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscCountsFixed
public import Riesz1.CLT.GapsDiscStripsDifference

/-!
# Coupling of interval counts at nearby scales

Part of Corollary 1, the case of a positive limit scale. The
normalized count at a scale `ℓ` is `N^{-s/2} W(ℓ)` times the centred arc count, where
`W(ℓ) = 1/sqrt(V_s(2aℓ))`. For two scales `ℓ` and `g`, the difference of the two normalized counts
is controlled in `L¹` by the strip estimate (`gapsDisc_strips_shift`) and by the scale-one second
moment bound (`arc_scale_one_integral_sq_le`). The coupling bound of `BLCoupling` then turns this
into a bound on the bounded-Lipschitz distance of the two count laws.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- The scale factor `W(ℓ) = 1/sqrt(V_s(2aℓ))` of the normalized count. -/
def countFactor (P : Parameters) (a x : ℝ) : ℝ :=
  1 / Real.sqrt (periodicZeta (parametersExponent P) ((2 * a * x : ℝ) : UnitAddCircle))

/-- The normalized count is `N^{-s/2} W(ℓ)` times the centred arc count. -/
lemma normalizedCount_eq_countFactor (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (N : ℕ+) (X : Configuration N) :
    normalizedCount P a ha0 ha1 ell N X =
      (N : ℝ) ^ (-P.val.2 / 2) * countFactor P a (ell N).val *
        (arcCount 0 (a * (ell N).val) X - (N : ℝ) * (2 * (a * (ell N).val))) := by
  have hℓ : 0 < (ell N).val := (ell N).property.1
  have hℓ1 : (ell N).val ≤ 1 := (ell N).property.2
  have h0 : 0 < 2 * a * (ell N).val := by positivity
  have h1 : 2 * a * (ell N).val < 1 := by nlinarith
  have hV : 0 < periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle) :=
    periodicZeta_pos _ h0 h1
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  rw [normalizedCount_eq_arcCount, countFactor, div_eq_mul_one_div,
    inv_sqrt_scale_one P.val.2 (N : ℝ) _ hNpos hV]
  ring

/-- The fixed-scale count at the constant scale `g` has the same form. -/
lemma normalizedCount_const_eq (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) (N : ℕ+) (X : Configuration N) :
    normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N X =
      (N : ℝ) ^ (-P.val.2 / 2) * countFactor P a g *
        (arcCount 0 (a * g) X - (N : ℝ) * (2 * (a * g))) :=
  normalizedCount_eq_countFactor P ha0 ha1 (constScales g hg0 hg1) N X

/-- The scale factor is continuous at a positive scale. -/
lemma countFactor_tendsto (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) {g : ℝ}
    (hg0 : 0 < g) (hg1 : g ≤ 1) {ι : Type*} {l : Filter ι} (ℓ : ι → ℝ)
    (hℓ : Tendsto ℓ l (𝓝 g)) :
    Tendsto (fun i => countFactor P a (ℓ i)) l (𝓝 (countFactor P a g)) := by
  have hcont : Continuous (fun x : ℝ => periodicZeta (parametersExponent P)
      ((2 * a * x : ℝ) : UnitAddCircle)) := by
    have h := periodicZeta_continuous (parametersExponent P)
    exact h.comp (continuous_const.mul continuous_id)
  have hV : 0 < periodicZeta (parametersExponent P) ((2 * a * g : ℝ) : UnitAddCircle) :=
    periodicZeta_pos _ (by positivity) (by nlinarith)
  have hcf : ContinuousAt (fun x : ℝ => countFactor P a x) g := by
    unfold countFactor
    refine ContinuousAt.div continuousAt_const ?_ (Real.sqrt_pos.mpr hV).ne'
    exact (Real.continuous_sqrt.comp hcont).continuousAt
  exact (hcf.tendsto).comp hℓ

/-- The rpow identity `N^{-s/2} sqrt(K N^s) = sqrt K` for positive `N`. -/
lemma rpow_neg_half_mul_sqrt (N s K : ℝ) (hN : 0 < N) (hK : 0 ≤ K) :
    N ^ (-s / 2) * Real.sqrt (K * N ^ s) = Real.sqrt K := by
  have hNs : 0 ≤ N ^ s := (Real.rpow_pos_of_pos hN s).le
  have hsq : Real.sqrt (N ^ s) = N ^ (s / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le, show s * (1 / 2) = s / 2 by ring]
  rw [Real.sqrt_mul hK, hsq, show -s / 2 = -(s / 2) by ring, Real.rpow_neg hN.le]
  have hp : 0 < N ^ (s / 2) := Real.rpow_pos_of_pos hN _
  field_simp

/-- **Difference of two counts at nearby scales.** Let `ℓ = (ell N).val` and suppose
`a |ℓ - g| ≤ 1/4`. The `L¹` norm of the difference of the normalized counts at `ℓ` and at the
constant scale `g` is at most `W(ℓ) C (N^{-s/2} + (a|ℓ-g|)^{s/2}) + sqrt K |W(ℓ) - W(g)|`, with
`C` from `gapsDisc_strips_shift` and `K` from the scale-one second moment bound at half-width `a g`.
-/
theorem integral_normalizedCount_sub_le (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1) (a : ℝ) (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (ell : Scales) (N : ℕ+),
      a * |(ell N).val - g| ≤ 1 / 4 →
      ∫ X, |normalizedCount ⟨(beta, s), hbeta, hs, hs1⟩ a ha0 ha1 ell N X -
          normalizedCount ⟨(beta, s), hbeta, hs, hs1⟩ a ha0 ha1 (constScales g hg0 hg1) N X|
        ∂(gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N) ≤
          countFactor ⟨(beta, s), hbeta, hs, hs1⟩ a (ell N).val *
              (C * ((N : ℝ) ^ (-s / 2) + (a * |(ell N).val - g|) ^ (s / 2))) +
            Real.sqrt K * |countFactor ⟨(beta, s), hbeta, hs, hs1⟩ a (ell N).val -
              countFactor ⟨(beta, s), hbeta, hs, hs1⟩ a g| := by
  obtain ⟨C, hC, hstrip⟩ := gapsDisc_strips_shift beta s hbeta hs hs1 hQV a ha0 ha1
  obtain ⟨K₀, hK₀⟩ := arc_scale_one_integral_sq_le beta s hbeta hs hs1 hQV (a * g)
    (mul_pos ha0 hg0) (by nlinarith)
  refine ⟨C, max K₀ 0, hC.le, le_max_right _ _, fun ell N hab => ?_⟩
  set P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩ with hPdef
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hℓ0 : 0 < (ell N).val := (ell N).property.1
  have hℓ1 : (ell N).val ≤ 1 := (ell N).property.2
  set ℓ := (ell N).val with hℓdef
  set W := countFactor P a ℓ with hWdef
  set Wg := countFactor P a g with hWgdef
  have hW0 : 0 ≤ W := by rw [hWdef, countFactor]; positivity
  have hWg0 : 0 ≤ Wg := by rw [hWgdef, countFactor]; positivity
  set Nh : ℝ := (N : ℝ) ^ (-s / 2) with hNhdef
  have hNh0 : 0 ≤ Nh := Real.rpow_nonneg (by positivity) _
  set E : Configuration N → ℝ := fun X => (arcCount 0 (a * ℓ) X - (N : ℝ) * (2 * (a * ℓ))) -
    (arcCount 0 (a * g) X - (N : ℝ) * (2 * (a * g))) with hEdef
  set F : Configuration N → ℝ := fun X => arcCount 0 (a * g) X - (N : ℝ) * (2 * (a * g))
    with hFdef
  have hmemA : MemLp (arcIndicator 0 (a * ℓ)) 2 volume := by
    simpa using (memLp_arcIndicator 0 (a * ℓ)).re
  have hmemG : MemLp (arcIndicator 0 (a * g)) 2 volume := by
    simpa using (memLp_arcIndicator 0 (a * g)).re
  have hLa : Integrable (fun X : Configuration N => arcCount 0 (a * ℓ) X - (N : ℝ) * (2 * (a * ℓ)))
      (gibbsMeasure P N) := integrable_abs_arcCount_sub P N 0 (a * ℓ) _ hmemA
  have hLg : Integrable (fun X : Configuration N => arcCount 0 (a * g) X - (N : ℝ) * (2 * (a * g)))
      (gibbsMeasure P N) := integrable_abs_arcCount_sub P N 0 (a * g) _ hmemG
  have hIE : Integrable E (gibbsMeasure P N) := hLa.sub hLg
  have hIF : Integrable F (gibbsMeasure P N) := hLg
  have hdecomp : ∀ X, normalizedCount P a ha0 ha1 ell N X -
      normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N X =
        Nh * W * E X + Nh * (W - Wg) * F X := by
    intro X
    rw [normalizedCount_eq_countFactor P ha0 ha1 ell N X,
      normalizedCount_const_eq P ha0 ha1 g hg0 hg1 N X]
    simp only [hEdef, hFdef, hNhdef, hWdef, hWgdef, hℓdef]
    ring
  have hpt : ∀ X, |normalizedCount P a ha0 ha1 ell N X -
      normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N X| ≤
        Nh * W * |E X| + Nh * |W - Wg| * |F X| := by
    intro X
    have h1 : |Nh * W * E X| = Nh * W * |E X| := by
      rw [abs_mul, abs_of_nonneg (mul_nonneg hNh0 hW0)]
    have h2 : |Nh * (W - Wg) * F X| = Nh * |W - Wg| * |F X| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hNh0]
    rw [hdecomp X]
    calc |Nh * W * E X + Nh * (W - Wg) * F X|
        ≤ |Nh * W * E X| + |Nh * (W - Wg) * F X| := abs_add_le _ _
      _ = Nh * W * |E X| + Nh * |W - Wg| * |F X| := by rw [h1, h2]
  have hdiffInt : Integrable (fun X => normalizedCount P a ha0 ha1 ell N X -
      normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N X) (gibbsMeasure P N) := by
    have hfun : (fun X => normalizedCount P a ha0 ha1 ell N X -
        normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N X) =
          fun X => Nh * W * E X + Nh * (W - Wg) * F X := funext hdecomp
    rw [hfun]
    exact (hIE.const_mul _).add (hIF.const_mul _)
  have hbnd : Integrable (fun X => Nh * W * |E X| + Nh * |W - Wg| * |F X|)
      (gibbsMeasure P N) :=
    ((hIE.abs).const_mul _).add ((hIF.abs).const_mul _)
  have hmono := integral_mono_ae hdiffInt.abs hbnd (Eventually.of_forall hpt)
  rw [integral_add ((hIE.abs).const_mul _) ((hIF.abs).const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  -- the strip estimate for the first term
  have hE : Nh * ∫ X, |E X| ∂(gibbsMeasure P N) ≤ C * (Nh + (a * |ℓ - g|) ^ (s / 2)) :=
    hstrip N ℓ g hℓ0 hℓ1 hg0 hg1 hab
  -- the scale-one second moment for the second term
  have hF2 : ∫ X, (F X) ^ 2 ∂(gibbsMeasure P N) ≤ max K₀ 0 * (N : ℝ) ^ s :=
    le_trans (hK₀ N) (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by positivity) _))
  have hMF : MemLp F 2 (gibbsMeasure P N) :=
    (memLp_linearStatistic P N hmemG).sub (memLp_const _)
  have hsqrtF : Nh * ∫ X, |F X| ∂(gibbsMeasure P N) ≤ Real.sqrt (max K₀ 0) := by
    have h1 := gapsDisc_integral_abs_le_sqrt_integral_sq (gibbsMeasure P N) F hMF
    have h2 : Real.sqrt (∫ X, (F X) ^ 2 ∂(gibbsMeasure P N)) ≤
        Real.sqrt (max K₀ 0 * (N : ℝ) ^ s) := Real.sqrt_le_sqrt hF2
    calc Nh * ∫ X, |F X| ∂(gibbsMeasure P N)
        ≤ Nh * Real.sqrt (max K₀ 0 * (N : ℝ) ^ s) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) hNh0
      _ = Real.sqrt (max K₀ 0) := rpow_neg_half_mul_sqrt _ _ _ (by positivity) (le_max_right _ _)
  calc ∫ X, |normalizedCount P a ha0 ha1 ell N X -
        normalizedCount P a ha0 ha1 (constScales g hg0 hg1) N X| ∂(gibbsMeasure P N)
      ≤ Nh * W * ∫ X, |E X| ∂(gibbsMeasure P N) + Nh * |W - Wg| * ∫ X, |F X| ∂(gibbsMeasure P N) :=
        hmono
    _ = W * (Nh * ∫ X, |E X| ∂(gibbsMeasure P N)) +
          |W - Wg| * (Nh * ∫ X, |F X| ∂(gibbsMeasure P N)) := by ring
    _ ≤ W * (C * (Nh + (a * |ℓ - g|) ^ (s / 2))) + |W - Wg| * Real.sqrt (max K₀ 0) :=
        add_le_add (mul_le_mul_of_nonneg_left hE hW0)
          (mul_le_mul_of_nonneg_left hsqrtF (abs_nonneg _))
    _ = W * (C * (Nh + (a * |ℓ - g|) ^ (s / 2))) + Real.sqrt (max K₀ 0) * |W - Wg| := by ring

end Riesz1

end
end
