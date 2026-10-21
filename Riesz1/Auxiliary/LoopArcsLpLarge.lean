/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLpMoments
public import Riesz1.Auxiliary.LoopArcsLpMeasure
public import Riesz1.Auxiliary.LoopArcsDerivs
public import Riesz1.ToMathlib.LintegralPowerTail

/-!
# The large region of the cell estimate

The arcs part of Lemma 5.8, large region `u + v ≥ 1`. The integrand
`‖g_N'''(u+v)‖ ‖A_t(u)‖ ‖B_t(v)‖` over `0 < u ≤ N/2`, `0 < v ≤ N/2 - u`, `u + v ≥ 1` and the unit
cell in `t` has `L^p` norm in the configuration bounded uniformly in `N` and the cell.

The estimate is the weighted Hölder inequality `lintegral_lintegral_rpow_le_weighted` with the
separable weight `g(u) g(v)`, `g(x) = (1 + |x|)^{-κ}`, `κ = 1 + η`, `η = (1/2 - δ)/2`. The
discrepancy moments enter as the hypothesis `hmom`, the `2p`-th moment of the count minus the
arclength, which the rigidity bundle provides. With `|g'''(r)| ≤ C r^{-s-3}` and `r ≥ 1`, the
per-variable exponent is `e = -p(3-2δ)/2 + κ(p-1)` and `e + 1 = -(1/2-δ)(p+1)/2 < 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- The large region of the cell estimate at the half period `R`: parameters `(t, u, v)` with
`0 < u ≤ R`, `0 < v ≤ R - u` and `u + v ≥ 1`. The time `t` is free. -/
def largeRegion (R : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {θ | (0 < θ.2.1 ∧ θ.2.1 ≤ R) ∧ (0 < θ.2.2 ∧ θ.2.2 ≤ R - θ.2.1) ∧ 1 ≤ θ.2.1 + θ.2.2}

/-- The large-region integrand at a parameter `θ = (t, u, v)` and a configuration `X`:
`‖g_N'''(u+v)‖ ‖loopCount(t-u, u) - u‖ ‖loopCount(t, v) - v‖` on the large region, and `0`
elsewhere. On `0 < u, v ≤ N/2` the arc discrepancies are these counts minus the arclengths
(`loopDiscrepancy_eq_sub`). -/
def largeIntegrand (s : ℝ) (N : ℕ+) (θ : ℝ × ℝ × ℝ) (X : Configuration N) : ℝ≥0∞ :=
  (largeRegion ((N : ℝ) / 2)).indicator (fun θ =>
    ‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ
      * ‖loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1‖ₑ
      * ‖loopCount θ.1 θ.2.2 X - θ.2.2‖ₑ) θ

/-- The large region is a measurable set. -/
theorem measurableSet_largeRegion (R : ℝ) : MeasurableSet (largeRegion R) := by
  have hu : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.1) := measurable_fst.comp measurable_snd
  have hv : Measurable (fun θ : ℝ × ℝ × ℝ => θ.2.2) := measurable_snd.comp measurable_snd
  have hP1 : MeasurableSet {θ : ℝ × ℝ × ℝ | 0 < θ.2.1} := measurableSet_lt measurable_const hu
  have hP2 : MeasurableSet {θ : ℝ × ℝ × ℝ | θ.2.1 ≤ R} := measurableSet_le hu measurable_const
  have hP3 : MeasurableSet {θ : ℝ × ℝ × ℝ | 0 < θ.2.2} := measurableSet_lt measurable_const hv
  have hP4 : MeasurableSet {θ : ℝ × ℝ × ℝ | θ.2.2 ≤ R - θ.2.1} :=
    measurableSet_le hv (measurable_const.sub hu)
  have hP5 : MeasurableSet {θ : ℝ × ℝ × ℝ | 1 ≤ θ.2.1 + θ.2.2} :=
    measurableSet_le measurable_const (hu.add hv)
  have key : largeRegion R = ({θ : ℝ × ℝ × ℝ | 0 < θ.2.1} ∩ {θ | θ.2.1 ≤ R})
      ∩ (({θ : ℝ × ℝ × ℝ | 0 < θ.2.2} ∩ {θ | θ.2.2 ≤ R - θ.2.1})
        ∩ {θ | 1 ≤ θ.2.1 + θ.2.2}) := by
    ext θ
    simp only [largeRegion, mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  rw [key]
  exact (hP1.inter hP2).inter ((hP3.inter hP4).inter hP5)

/-- **Measurability of the large-region integrand** in the parameter and the configuration. -/
theorem measurable_largeIntegrand (s : ℝ) (N : ℕ+) :
    Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => largeIntegrand s N q.1 q.2) := by
  have hu : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.2.1) := by fun_prop
  have hv : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.2.2) := by fun_prop
  have ht : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.1) := by fun_prop
  have hX : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N => q.2) := by fun_prop
  have hg3 := measurable_iteratedDeriv_three s N
  have hc1 := measurable_loopCount_of (N := N) (c := fun q => q.2)
    (a := fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.1 - q.1.2.1)
    (r := fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.2.1) (ht.sub hu) hu hX
  have hc2 := measurable_loopCount_of (N := N) (c := fun q => q.2)
    (a := fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.1)
    (r := fun q : (ℝ × ℝ × ℝ) × Configuration N => q.1.2.2) ht hv hX
  have hG : Measurable (fun q : (ℝ × ℝ × ℝ) × Configuration N =>
      ‖iteratedDeriv 3 (loopArcG s N) (q.1.2.1 + q.1.2.2)‖ₑ
        * ‖loopCount (q.1.1 - q.1.2.1) q.1.2.1 q.2 - q.1.2.1‖ₑ
        * ‖loopCount q.1.1 q.1.2.2 q.2 - q.1.2.2‖ₑ) := by
    refine ((hg3.comp (hu.add hv)).enorm.mul ((hc1.sub hu).enorm)).mul ((hc2.sub hv).enorm)
  have hS : MeasurableSet {q : (ℝ × ℝ × ℝ) × Configuration N | q.1 ∈ largeRegion ((N : ℝ) / 2)} :=
    (measurableSet_largeRegion _).preimage measurable_fst
  have heq : (fun q : (ℝ × ℝ × ℝ) × Configuration N => largeIntegrand s N q.1 q.2)
      = {q : (ℝ × ℝ × ℝ) × Configuration N | q.1 ∈ largeRegion ((N : ℝ) / 2)}.indicator
          (fun q => ‖iteratedDeriv 3 (loopArcG s N) (q.1.2.1 + q.1.2.2)‖ₑ
            * ‖loopCount (q.1.1 - q.1.2.1) q.1.2.1 q.2 - q.1.2.1‖ₑ
            * ‖loopCount q.1.1 q.1.2.2 q.2 - q.1.2.2‖ₑ) := by
    funext q
    by_cases h : q.1 ∈ largeRegion ((N : ℝ) / 2)
    · simp only [largeIntegrand, Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈ {q : (ℝ × ℝ × ℝ) × Configuration N | q.1 ∈ largeRegion ((N : ℝ) / 2)} from h)]
    · simp only [largeIntegrand, Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show q ∉ {q : (ℝ × ℝ × ℝ) × Configuration N | q.1 ∈ largeRegion ((N : ℝ) / 2)} from h)]
  rw [heq]
  exact hG.indicator hS

/-- **Separation of the large-region singularity.** For `u, v > 0` with `u + v ≥ 1`,
`(u + v)^{-s-3} ≤ 4^{(s+3)/2} ((1+u)^{-(s+3)/2} (1+v)^{-(s+3)/2})`. The inequality
`4 (u+v)^2 ≥ (1+u)(1+v)` holds because `2(u+v) ≥ 1+u` and `2(u+v) ≥ 1+v`. -/
theorem rpow_neg_sum_le_separated {s u v : ℝ} (hs : 0 < s) (hu : 0 < u) (hv : 0 < v)
    (h1 : 1 ≤ u + v) :
    (u + v) ^ (-s - 3) ≤ 4 ^ ((s + 3) / 2)
      * ((1 + u) ^ (-((s + 3) / 2)) * (1 + v) ^ (-((s + 3) / 2))) := by
  set q : ℝ := (s + 3) / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  have hsum : 0 < u + v := by linarith
  have key : ((u + v) ^ (2 : ℝ)) ^ (-q) = (u + v) ^ (-s - 3) := by
    rw [← Real.rpow_mul hsum.le, hq]
    congr 1
    ring
  have hle : (1 + u) * (1 + v) / 4 ≤ (u + v) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    nlinarith
  have hpos : 0 < (1 + u) * (1 + v) / 4 := by positivity
  have hmono := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith : -q ≤ 0)
  rw [key] at hmono
  have hsplit : ((1 + u) * (1 + v) / 4) ^ (-q) = 4 ^ q * ((1 + u) ^ (-q) * (1 + v) ^ (-q)) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.mul_rpow (by linarith) (by linarith),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_inv_eq_mul]
    ring
  rw [hsplit] at hmono
  exact hmono

/-- The `1/2`-power of the `2p`-th power of an `ENNReal` real power. -/
theorem ofReal_rpow_two_mul_half {x p : ℝ} (_hx : 0 ≤ x) :
    (ENNReal.ofReal x ^ (2 * p)) ^ (1 / 2 : ℝ) = ENNReal.ofReal x ^ p := by
  rw [← ENNReal.rpow_mul]
  congr 1
  ring

/-- **Pointwise `p`-th moment on the large region.** For `θ` in the large region, the `p`-th
lower moment of the large-region integrand over the configuration is bounded by
`(C (u+v)^{-s-3})^p (M(1+u)^{s/2+δ})^p (M(1+v)^{s/2+δ})^p`. Outside the large region the
integrand vanishes. -/
theorem lintegral_largeIntegrand_pow_le {s δ p M C : ℝ} (_hs : 0 < s) (hp : 1 ≤ p) (hM : 0 ≤ M)
    (_hC : 0 ≤ C) {N : ℕ+} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hmom : ∀ a u : ℝ, 0 < u → u ≤ (N : ℝ) / 2 →
      ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p) ∂μ
        ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p))
    (hgC : ∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 3 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (C * r ^ (-s - 3)))
    (θ : ℝ × ℝ × ℝ) :
    ∫⁻ X, largeIntegrand s N θ X ^ p ∂μ
      ≤ (largeRegion ((N : ℝ) / 2)).indicator (fun θ : ℝ × ℝ × ℝ =>
          ENNReal.ofReal (C * (θ.2.1 + θ.2.2) ^ (-s - 3)) ^ p
            * (ENNReal.ofReal (M * (1 + θ.2.1) ^ (s / 2 + δ)) ^ p
              * ENNReal.ofReal (M * (1 + θ.2.2) ^ (s / 2 + δ)) ^ p)) θ := by
  have hp0 : 0 < p := by linarith
  by_cases hθ : θ ∈ largeRegion ((N : ℝ) / 2)
  · rw [Set.indicator_of_mem hθ]
    obtain ⟨⟨hu0, huR⟩, ⟨hv0, hvR⟩, h1⟩ := hθ
    have hvR' : θ.2.2 ≤ (N : ℝ) / 2 := by linarith
    have hfun : ∀ X, largeIntegrand s N θ X
        = ‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ
          * (‖loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1‖ₑ
            * ‖loopCount θ.1 θ.2.2 X - θ.2.2‖ₑ) := by
      intro X
      rw [largeIntegrand, Set.indicator_of_mem (show θ ∈ largeRegion ((N : ℝ) / 2) from
        ⟨⟨hu0, huR⟩, ⟨hv0, hvR⟩, h1⟩), mul_assoc]
    simp only [hfun]
    have hr : ‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ
        ≤ ENNReal.ofReal (C * (θ.2.1 + θ.2.2) ^ (-s - 3)) :=
      hgC (θ.2.1 + θ.2.2) (by linarith) (by linarith)
    have hXA : Measurable (fun X : Configuration N => loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1) :=
      (measurable_loopCount_of (N := N) (c := id) (a := fun _ => θ.1 - θ.2.1)
        (r := fun _ => θ.2.1) measurable_const measurable_const measurable_id).sub measurable_const
    have hXB : Measurable (fun X : Configuration N => loopCount θ.1 θ.2.2 X - θ.2.2) :=
      (measurable_loopCount_of (N := N) (c := id) (a := fun _ => θ.1)
        (r := fun _ => θ.2.2) measurable_const measurable_const measurable_id).sub measurable_const
    have hcs := lintegral_enorm_rpow_mul_le μ hXA hXB hp
    have hA := hmom (θ.1 - θ.2.1) θ.2.1 hu0 huR
    have hB := hmom θ.1 θ.2.2 hv0 hvR'
    have hAB : (∫⁻ X, ‖loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (M * (1 + θ.2.1) ^ (s / 2 + δ)) ^ p := by
      calc _ ≤ (ENNReal.ofReal (M * (1 + θ.2.1) ^ (s / 2 + δ)) ^ (2 * p)) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow hA (by norm_num)
        _ = _ := ofReal_rpow_two_mul_half (by
            exact (mul_nonneg hM (Real.rpow_nonneg (by linarith) _)))
    have hBB : (∫⁻ X, ‖loopCount θ.1 θ.2.2 X - θ.2.2‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (M * (1 + θ.2.2) ^ (s / 2 + δ)) ^ p := by
      calc _ ≤ (ENNReal.ofReal (M * (1 + θ.2.2) ^ (s / 2 + δ)) ^ (2 * p)) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow hB (by norm_num)
        _ = _ := ofReal_rpow_two_mul_half (by
            exact (mul_nonneg hM (Real.rpow_nonneg (by linarith) _)))
    have hne : ‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ ^ p ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hp0.le
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr)
    calc ∫⁻ X, (‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ
            * (‖loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1‖ₑ
              * ‖loopCount θ.1 θ.2.2 X - θ.2.2‖ₑ)) ^ p ∂μ
        = ‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ ^ p
            * ∫⁻ X, ‖loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1‖ₑ ^ p
              * ‖loopCount θ.1 θ.2.2 X - θ.2.2‖ₑ ^ p ∂μ := by
          rw [← lintegral_const_mul' _ _ hne]
          refine lintegral_congr fun X => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      _ ≤ ‖iteratedDeriv 3 (loopArcG s N) (θ.2.1 + θ.2.2)‖ₑ ^ p
            * ((∫⁻ X, ‖loopCount (θ.1 - θ.2.1) θ.2.1 X - θ.2.1‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ)
              * (∫⁻ X, ‖loopCount θ.1 θ.2.2 X - θ.2.2‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ)) :=
          mul_le_mul' le_rfl hcs
      _ ≤ ENNReal.ofReal (C * (θ.2.1 + θ.2.2) ^ (-s - 3)) ^ p
            * (ENNReal.ofReal (M * (1 + θ.2.1) ^ (s / 2 + δ)) ^ p
              * ENNReal.ofReal (M * (1 + θ.2.2) ^ (s / 2 + δ)) ^ p) :=
          mul_le_mul' (ENNReal.rpow_le_rpow hr hp0.le) (mul_le_mul' hAB hBB)
  · rw [Set.indicator_of_notMem hθ]
    have hz : ∀ X, largeIntegrand s N θ X = 0 := fun X => by
      rw [largeIntegrand, Set.indicator_of_notMem hθ]
    simp [hz, ENNReal.zero_rpow_of_pos hp0]

/-- **Tail integral.** For `e < -1`, `∫⁻_{x > 0} (1 + x)^e dx = -1/(e+1)`. -/
theorem lintegral_Ioi_one_add_rpow {e : ℝ} (he : e < -1) :
    ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 + x) ^ e)
      = ENNReal.ofReal (-1 / (e + 1)) := by
  have h := lintegral_Ioi_add_left (fun w => ENNReal.ofReal (w ^ e)) 1 0
  simp only [add_zero] at h
  rw [h, lintegral_Ioi_rpow (by norm_num : (0 : ℝ) < 1) he, Real.one_rpow]

/-- **Product of parameter integrals.** For the parameter measure `μt ⊗ (μu ⊗ μv)` and
measurable `ψ`, `χ`, the lower integral of `ψ(u) χ(v)` over the parameter is
`μt(univ) · ∫⁻ ψ dμu · ∫⁻ χ dμv`. -/
theorem lintegral_prod_pair_mul {μt μu μv : Measure ℝ} [SFinite μt] [SFinite μu] [SFinite μv]
    {ψ χ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) (hχ : Measurable χ) :
    ∫⁻ θ : ℝ × ℝ × ℝ, ψ θ.2.1 * χ θ.2.2 ∂(μt.prod (μu.prod μv))
      = μt Set.univ * (∫⁻ x, ψ x ∂μu) * (∫⁻ x, χ x ∂μv) := by
  have hm : Measurable (fun θ : ℝ × ℝ × ℝ => ψ θ.2.1 * χ θ.2.2) :=
    (hψ.comp (measurable_fst.comp measurable_snd)).mul
      (hχ.comp (measurable_snd.comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  calc ∫⁻ t, ∫⁻ p : ℝ × ℝ, ψ (t, p).2.1 * χ (t, p).2.2 ∂(μu.prod μv) ∂μt
      = ∫⁻ _t, (∫⁻ x, ψ x ∂μu) * ∫⁻ x, χ x ∂μv ∂μt :=
        lintegral_congr fun t => lintegral_prod_mul hψ.aemeasurable hχ.aemeasurable
    _ = μt Set.univ * (∫⁻ x, ψ x ∂μu) * (∫⁻ x, χ x ∂μv) := by
        rw [lintegral_const]
        ring

/-- **Exponent of the large-region bound.** The weight exponent `κ = 1 + (1/2 - δ)/2` and the
per-variable exponent `e = -p(3/2 - δ) + κ(p-1)`. It follows that `e + 1 < 0`. -/
theorem large_exponent_lt {p δ : ℝ} (hδ1 : δ < 1 / 4) (hp : 1 ≤ p) :
    -(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1) < -1 := by
  nlinarith

/-- **Real large-region bound.** For `u, v > 0` with `u + v ≥ 1`, the product of the `p`-th
power of `C (u+v)^{-s-3}`, of the moments `(M(1+u)^{s/2+δ})^p (M(1+v)^{s/2+δ})^p`, and of the
weight `((1+u)^{-κ})^{1-p} ((1+v)^{-κ})^{1-p}` is bounded by
`C^p 4^{(s+3)p/2} M^{2p} (1+u)^e (1+v)^e`. -/
theorem large_real_bound {s δ p C M u v : ℝ} (hs : 0 < s) (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hM : 0 ≤ M) (hu : 0 < u) (hv : 0 < v) (h1 : 1 ≤ u + v) :
    (C * (u + v) ^ (-s - 3)) ^ p
        * ((M * (1 + u) ^ (s / 2 + δ)) ^ p * (M * (1 + v) ^ (s / 2 + δ)) ^ p)
        * (((1 + u) ^ (-(1 + (1 / 2 - δ) / 2))) ^ (1 - p)
          * ((1 + v) ^ (-(1 + (1 / 2 - δ) / 2))) ^ (1 - p))
      ≤ C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p)
        * ((1 + u) ^ (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1))
          * (1 + v) ^ (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1))) := by
  set q : ℝ := (s + 3) / 2 with hq
  set σ : ℝ := s / 2 + δ with hσ
  set κ : ℝ := 1 + (1 / 2 - δ) / 2 with hκ
  have ha : 0 < 1 + u := by linarith
  have hb : 0 < 1 + v := by linarith
  have hp0 : 0 < p := by linarith
  have hsep := rpow_neg_sum_le_separated hs hu hv h1
  rw [← hq] at hsep
  have hX0 : 0 ≤ (u + v) ^ (-s - 3) := Real.rpow_nonneg (by linarith) _
  -- the singular factor, raised to the power `p`
  have hX : ((u + v) ^ (-s - 3)) ^ p ≤ (4 ^ q) ^ p * ((1 + u) ^ (-q)) ^ p * ((1 + v) ^ (-q)) ^ p := by
    have hmono := Real.rpow_le_rpow hX0 hsep hp0.le
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity)] at hmono
    simpa [mul_assoc] using hmono
  -- the exponents of `1 + u` and `1 + v`, combined
  have ea : ∀ x : ℝ, 0 < x → x ^ (-q * p) * x ^ (σ * p) * x ^ (-κ * (1 - p))
      = x ^ (-(p * (3 / 2 - δ)) + κ * (p - 1)) := by
    intro x hx
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    rw [hq, hσ, hκ]
    ring
  have hM2 : M ^ (2 * p) = M ^ p * M ^ p := by
    rw [← Real.rpow_add' hM (by linarith)]
    congr 1
    ring
  have hXp : (C * (u + v) ^ (-s - 3)) ^ p = C ^ p * ((u + v) ^ (-s - 3)) ^ p :=
    Real.mul_rpow hC hX0
  have hMa : (M * (1 + u) ^ σ) ^ p = M ^ p * (1 + u) ^ (σ * p) := by
    rw [Real.mul_rpow hM (by positivity), ← Real.rpow_mul ha.le]
  have hMb : (M * (1 + v) ^ σ) ^ p = M ^ p * (1 + v) ^ (σ * p) := by
    rw [Real.mul_rpow hM (by positivity), ← Real.rpow_mul hb.le]
  have hWa : ((1 + u) ^ (-κ)) ^ (1 - p) = (1 + u) ^ (-κ * (1 - p)) := by
    rw [← Real.rpow_mul ha.le]
  have hWb : ((1 + v) ^ (-κ)) ^ (1 - p) = (1 + v) ^ (-κ * (1 - p)) := by
    rw [← Real.rpow_mul hb.le]
  have hPa : ((1 + u) ^ (-q)) ^ p = (1 + u) ^ (-q * p) := by
    rw [← Real.rpow_mul ha.le]
  have hPb : ((1 + v) ^ (-q)) ^ p = (1 + v) ^ (-q * p) := by
    rw [← Real.rpow_mul hb.le]
  rw [hXp, hMa, hMb, hWa, hWb]
  calc C ^ p * ((u + v) ^ (-s - 3)) ^ p * (M ^ p * (1 + u) ^ (σ * p) * (M ^ p * (1 + v) ^ (σ * p)))
        * ((1 + u) ^ (-κ * (1 - p)) * (1 + v) ^ (-κ * (1 - p)))
      ≤ C ^ p * ((4 ^ q) ^ p * ((1 + u) ^ (-q * p)) * ((1 + v) ^ (-q * p)))
        * (M ^ p * (1 + u) ^ (σ * p) * (M ^ p * (1 + v) ^ (σ * p)))
        * ((1 + u) ^ (-κ * (1 - p)) * (1 + v) ^ (-κ * (1 - p))) := by
        rw [← hPa, ← hPb]
        gcongr
    _ = C ^ p * (4 ^ q) ^ p * M ^ (2 * p)
        * ((1 + u) ^ (-(p * (3 / 2 - δ)) + κ * (p - 1))
          * (1 + v) ^ (-(p * (3 / 2 - δ)) + κ * (p - 1))) := by
        rw [hM2, ← ea (1 + u) ha, ← ea (1 + v) hb]
        ring

/-- The large-region parameter measure `dt|_{(m, m+1]} ⊗ (du|_{(0,R]} ⊗ dv|_{(0,R]})`. -/
def loopArcLargeMeasure (m : ℝ) (N : ℕ+) : Measure (ℝ × ℝ × ℝ) :=
  (volume.restrict (Ioc m (m + 1))).prod
    ((volume.restrict (Ioc 0 ((N : ℝ) / 2))).prod (volume.restrict (Ioc 0 ((N : ℝ) / 2))))

/-- The weight `w(t, u, v) = g(u) g(v)` with `g(x) = (1 + |x|)^{-κ}`, as a real number. -/
def largeWeightReal (κ : ℝ) (θ : ℝ × ℝ × ℝ) : ℝ :=
  (1 + |θ.2.1|) ^ (-κ) * (1 + |θ.2.2|) ^ (-κ)

/-- The large-region parameter measure is `σ`-finite. -/
instance sFinite_loopArcLargeMeasure (m : ℝ) (N : ℕ+) : SFinite (loopArcLargeMeasure m N) := by
  unfold loopArcLargeMeasure
  infer_instance

/-- **Pointwise weighted moment.** On the large region, the `p`-th moment of the large-region
integrand against the weight `w^{1-p}` is bounded by `D · (1+u)^e (1+v)^e`, with the constant
`D = C^p 4^{(s+3)p/2} M^{2p}` and `e` the exponent of `large_exponent_lt`. -/
theorem large_pointwise_weighted {s δ p M C : ℝ} (hs : 0 < s) (hp : 1 ≤ p) (hM : 0 ≤ M)
    (hC : 0 ≤ C) {N : ℕ+} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hmom : ∀ a u : ℝ, 0 < u → u ≤ (N : ℝ) / 2 →
      ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p) ∂μ
        ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p))
    (hgC : ∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 3 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (C * r ^ (-s - 3)))
    (θ : ℝ × ℝ × ℝ) (hθ : θ ∈ largeRegion ((N : ℝ) / 2)) :
    (∫⁻ X, largeIntegrand s N θ X ^ p ∂μ)
        * ENNReal.ofReal (largeWeightReal (1 + (1 / 2 - δ) / 2) θ) ^ (1 - p)
      ≤ ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
        * (ENNReal.ofReal ((1 + |θ.2.1|) ^ (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1)))
          * ENNReal.ofReal ((1 + |θ.2.2|) ^ (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1)))) := by
  have hp0 : 0 < p := by linarith
  obtain ⟨⟨hu0, huR⟩, ⟨hv0, hvR⟩, h1⟩ := hθ
  have hθ' : θ ∈ largeRegion ((N : ℝ) / 2) := ⟨⟨hu0, huR⟩, ⟨hv0, hvR⟩, h1⟩
  have hK := lintegral_largeIntegrand_pow_le hs hp hM hC hmom hgC θ
  rw [Set.indicator_of_mem hθ'] at hK
  have hreal := large_real_bound (δ := δ) hs hp hC hM hu0 hv0 h1
  have hWpos : 0 < largeWeightReal (1 + (1 / 2 - δ) / 2) θ := by
    unfold largeWeightReal
    have h1 : (0 : ℝ) < (1 + |θ.2.1|) ^ (-(1 + (1 / 2 - δ) / 2)) :=
      Real.rpow_pos_of_pos (by positivity) _
    have h2 : (0 : ℝ) < (1 + |θ.2.2|) ^ (-(1 + (1 / 2 - δ) / 2)) :=
      Real.rpow_pos_of_pos (by positivity) _
    exact mul_pos h1 h2
  rw [abs_of_pos hu0, abs_of_pos hv0]
  have hW : (ENNReal.ofReal (largeWeightReal (1 + (1 / 2 - δ) / 2) θ)) ^ (1 - p)
      = ENNReal.ofReal (((1 + θ.2.1) ^ (-(1 + (1 / 2 - δ) / 2))) ^ (1 - p)
          * ((1 + θ.2.2) ^ (-(1 + (1 / 2 - δ) / 2))) ^ (1 - p)) := by
    rw [ENNReal.ofReal_rpow_of_pos hWpos, largeWeightReal, abs_of_pos hu0, abs_of_pos hv0,
      Real.mul_rpow (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)]
  have hC1 : 0 ≤ C * (θ.2.1 + θ.2.2) ^ (-s - 3) :=
    mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  have hM1 : 0 ≤ M * (1 + θ.2.1) ^ (s / 2 + δ) :=
    mul_nonneg hM (Real.rpow_nonneg (by linarith) _)
  have hM2 : 0 ≤ M * (1 + θ.2.2) ^ (s / 2 + δ) :=
    mul_nonneg hM (Real.rpow_nonneg (by linarith) _)
  calc (∫⁻ X, largeIntegrand s N θ X ^ p ∂μ)
          * ENNReal.ofReal (largeWeightReal (1 + (1 / 2 - δ) / 2) θ) ^ (1 - p)
      ≤ (ENNReal.ofReal (C * (θ.2.1 + θ.2.2) ^ (-s - 3)) ^ p
            * (ENNReal.ofReal (M * (1 + θ.2.1) ^ (s / 2 + δ)) ^ p
              * ENNReal.ofReal (M * (1 + θ.2.2) ^ (s / 2 + δ)) ^ p))
          * ENNReal.ofReal (largeWeightReal (1 + (1 / 2 - δ) / 2) θ) ^ (1 - p) :=
        mul_le_mul' hK le_rfl
    _ = ENNReal.ofReal ((C * (θ.2.1 + θ.2.2) ^ (-s - 3)) ^ p
            * ((M * (1 + θ.2.1) ^ (s / 2 + δ)) ^ p * (M * (1 + θ.2.2) ^ (s / 2 + δ)) ^ p)
            * (((1 + θ.2.1) ^ (-(1 + (1 / 2 - δ) / 2))) ^ (1 - p)
              * ((1 + θ.2.2) ^ (-(1 + (1 / 2 - δ) / 2))) ^ (1 - p))) := by
        have hA' : 0 ≤ (C * (θ.2.1 + θ.2.2) ^ (-s - 3)) ^ p := Real.rpow_nonneg hC1 _
        have hB' : 0 ≤ (M * (1 + θ.2.1) ^ (s / 2 + δ)) ^ p := Real.rpow_nonneg hM1 _
        have hC' : 0 ≤ (M * (1 + θ.2.2) ^ (s / 2 + δ)) ^ p := Real.rpow_nonneg hM2 _
        have hX' : 0 ≤ (C * (θ.2.1 + θ.2.2) ^ (-s - 3)) ^ p
            * ((M * (1 + θ.2.1) ^ (s / 2 + δ)) ^ p * (M * (1 + θ.2.2) ^ (s / 2 + δ)) ^ p) :=
          mul_nonneg hA' (mul_nonneg hB' hC')
        rw [hW, ENNReal.ofReal_rpow_of_nonneg hC1 hp0.le,
          ENNReal.ofReal_rpow_of_nonneg hM1 hp0.le, ENNReal.ofReal_rpow_of_nonneg hM2 hp0.le,
          ← ENNReal.ofReal_mul hB', ← ENNReal.ofReal_mul hA',
          ← ENNReal.ofReal_mul (mul_nonneg hA' (mul_nonneg hB' hC'))]
    _ ≤ ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p)
            * ((1 + θ.2.1) ^ (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1))
              * (1 + θ.2.2) ^ (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1)))) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
        * (ENNReal.ofReal ((1 + θ.2.1) ^ (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1)))
          * ENNReal.ofReal ((1 + θ.2.2) ^ (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1)))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]

/-- **Large-region bound, uniform in `N` and the cell.** The `L^p` norm in the configuration of
the large-region integral over the cell is bounded by an explicit constant, independent of `N`
and `m`. -/
theorem lintegral_largeIntegrand_lp_le {s δ p M C : ℝ} (hs : 0 < s)
    (hδ1 : δ < 1 / 4) (hp : 1 ≤ p) (hM : 0 ≤ M) (hC : 0 ≤ C) (m : ℝ) {N : ℕ+}
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hmom : ∀ a u : ℝ, 0 < u → u ≤ (N : ℝ) / 2 →
      ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p) ∂μ
        ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p))
    (hgC : ∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 3 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (C * r ^ (-s - 3))) :
    ∫⁻ X, (∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure m N)) ^ p ∂μ
      ≤ (ENNReal.ofReal (-1 / (-(1 + (1 / 2 - δ) / 2) + 1))
          * ENNReal.ofReal (-1 / (-(1 + (1 / 2 - δ) / 2) + 1))) ^ (p - 1)
        * (ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
          * (ENNReal.ofReal (-1 / (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1) + 1))
            * ENNReal.ofReal (-1 / (-(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1) + 1)))) := by
  have hp0 : 0 < p := by linarith
  have hκ1 : -(1 + (1 / 2 - δ) / 2) < -1 := by
    have : (0 : ℝ) < 1 / 2 - δ := by linarith
    linarith
  have he : -(p * (3 / 2 - δ)) + (1 + (1 / 2 - δ) / 2) * (p - 1) < -1 :=
    large_exponent_lt hδ1 hp
  have := sFinite_loopArcLargeMeasure m N
  set κ : ℝ := 1 + (1 / 2 - δ) / 2 with hκ
  set e : ℝ := -(p * (3 / 2 - δ)) + κ * (p - 1) with he_def
  have hWpos : ∀ θ : ℝ × ℝ × ℝ, 0 < largeWeightReal κ θ := fun θ => by
    unfold largeWeightReal
    have h1 : (0 : ℝ) < (1 + |θ.2.1|) ^ (-κ) := Real.rpow_pos_of_pos (by positivity) _
    have h2 : (0 : ℝ) < (1 + |θ.2.2|) ^ (-κ) := Real.rpow_pos_of_pos (by positivity) _
    exact mul_pos h1 h2
  have habs : Measurable (fun x : ℝ => |x|) := continuous_abs.measurable
  have hwm : Measurable (fun θ : ℝ × ℝ × ℝ => ENNReal.ofReal (largeWeightReal κ θ)) := by
    refine Measurable.ennreal_ofReal ?_
    unfold largeWeightReal
    refine Measurable.mul ?_ ?_
    · exact (measurable_const.add (habs.comp (measurable_fst.comp measurable_snd))).pow_const _
    · exact (measurable_const.add (habs.comp (measurable_snd.comp measurable_snd))).pow_const _
  have hw0 : ∀ θ : ℝ × ℝ × ℝ, ENNReal.ofReal (largeWeightReal κ θ) ≠ 0 :=
    fun θ => (ENNReal.ofReal_pos.mpr (hWpos θ)).ne'
  have hwt : ∀ θ : ℝ × ℝ × ℝ, ENNReal.ofReal (largeWeightReal κ θ) ≠ ⊤ :=
    fun θ => ENNReal.ofReal_ne_top
  -- Step 1: weighted Hölder in the parameter.
  have H1 := lintegral_lintegral_rpow_le_weighted (μ := μ) (ν := loopArcLargeMeasure m N)
    (F := fun θ X => largeIntegrand s N θ X) (measurable_largeIntegrand s N) hwm hw0 hwt hp
  -- Step 2: the weighted moments are bounded by the explicit integrand on the large region.
  have H2 : ∫⁻ θ, (∫⁻ X, largeIntegrand s N θ X ^ p ∂μ)
      * ENNReal.ofReal (largeWeightReal κ θ) ^ (1 - p) ∂(loopArcLargeMeasure m N)
      ≤ ∫⁻ θ, (largeRegion ((N : ℝ) / 2)).indicator (fun θ : ℝ × ℝ × ℝ =>
          ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
            * (ENNReal.ofReal ((1 + |θ.2.1|) ^ e) * ENNReal.ofReal ((1 + |θ.2.2|) ^ e))) θ
        ∂(loopArcLargeMeasure m N) := by
    refine lintegral_mono fun θ => ?_
    by_cases hθ : θ ∈ largeRegion ((N : ℝ) / 2)
    · rw [Set.indicator_of_mem hθ]
      exact large_pointwise_weighted hs hp hM hC hmom hgC θ hθ
    · rw [Set.indicator_of_notMem hθ]
      have hz : ∀ X, largeIntegrand s N θ X = 0 := fun X => by
        rw [largeIntegrand, Set.indicator_of_notMem hθ]
      simp [hz, ENNReal.zero_rpow_of_pos hp0]
  -- Step 3: drop the indicator and factor the parameter integral.
  have H3 : ∫⁻ θ, (largeRegion ((N : ℝ) / 2)).indicator (fun θ : ℝ × ℝ × ℝ =>
          ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
            * (ENNReal.ofReal ((1 + |θ.2.1|) ^ e) * ENNReal.ofReal ((1 + |θ.2.2|) ^ e))) θ
        ∂(loopArcLargeMeasure m N)
      ≤ ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
        * (ENNReal.ofReal (-1 / (e + 1)) * ENNReal.ofReal (-1 / (e + 1))) := by
    refine (lintegral_mono fun θ => Set.indicator_le_self' (fun _ _ => zero_le) θ).trans ?_
    have hfac : ∫⁻ θ, ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
            * (ENNReal.ofReal ((1 + |θ.2.1|) ^ e) * ENNReal.ofReal ((1 + |θ.2.2|) ^ e))
          ∂(loopArcLargeMeasure m N)
        = ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
          * ∫⁻ θ, (ENNReal.ofReal ((1 + |θ.2.1|) ^ e) * ENNReal.ofReal ((1 + |θ.2.2|) ^ e))
            ∂(loopArcLargeMeasure m N) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [hfac]
    refine mul_le_mul' le_rfl ?_
    have hm := lintegral_prod_pair_mul (μt := volume.restrict (Ioc m (m + 1)))
      (μu := volume.restrict (Ioc 0 ((N : ℝ) / 2))) (μv := volume.restrict (Ioc 0 ((N : ℝ) / 2)))
      (ψ := fun x => ENNReal.ofReal ((1 + |x|) ^ e)) (χ := fun x => ENNReal.ofReal ((1 + |x|) ^ e))
      (ENNReal.measurable_ofReal.comp ((measurable_const.add habs).pow_const e))
      (ENNReal.measurable_ofReal.comp ((measurable_const.add habs).pow_const e))
    unfold loopArcLargeMeasure
    rw [hm]
    have hcell : (volume.restrict (Ioc m (m + 1))) Set.univ = 1 := by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      simp
    have hint : ∀ R : ℝ, ∫⁻ x, ENNReal.ofReal ((1 + |x|) ^ e) ∂(volume.restrict (Ioc 0 R))
        ≤ ENNReal.ofReal (-1 / (e + 1)) := by
      intro R
      refine (lintegral_mono_set Set.Ioc_subset_Ioi_self).trans ?_
      rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun x => ENNReal.ofReal ((1 + x) ^ e))
        (fun x hx => by
          show ENNReal.ofReal ((1 + |x|) ^ e) = ENNReal.ofReal ((1 + x) ^ e)
          rw [abs_of_pos (Set.mem_Ioi.mp hx)])]
      exact (lintegral_Ioi_one_add_rpow he).le
    rw [hcell, one_mul]
    exact mul_le_mul' (hint _) (hint _)
  -- Step 4: the weight integral.
  have hW : ∫⁻ θ, ENNReal.ofReal (largeWeightReal κ θ) ∂(loopArcLargeMeasure m N)
      ≤ ENNReal.ofReal (-1 / (-κ + 1)) * ENNReal.ofReal (-1 / (-κ + 1)) := by
    have hfac : ∀ θ : ℝ × ℝ × ℝ, ENNReal.ofReal (largeWeightReal κ θ)
        = ENNReal.ofReal ((1 + |θ.2.1|) ^ (-κ)) * ENNReal.ofReal ((1 + |θ.2.2|) ^ (-κ)) := by
      intro θ
      unfold largeWeightReal
      exact ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)
    simp_rw [hfac]
    have hm := lintegral_prod_pair_mul (μt := volume.restrict (Ioc m (m + 1)))
      (μu := volume.restrict (Ioc 0 ((N : ℝ) / 2))) (μv := volume.restrict (Ioc 0 ((N : ℝ) / 2)))
      (ψ := fun x => ENNReal.ofReal ((1 + |x|) ^ (-κ)))
      (χ := fun x => ENNReal.ofReal ((1 + |x|) ^ (-κ)))
      (ENNReal.measurable_ofReal.comp ((measurable_const.add habs).pow_const _))
      (ENNReal.measurable_ofReal.comp ((measurable_const.add habs).pow_const _))
    unfold loopArcLargeMeasure
    rw [hm]
    have hcell : (volume.restrict (Ioc m (m + 1))) Set.univ = 1 := by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      simp
    have hint : ∀ R : ℝ, ∫⁻ x, ENNReal.ofReal ((1 + |x|) ^ (-κ)) ∂(volume.restrict (Ioc 0 R))
        ≤ ENNReal.ofReal (-1 / (-κ + 1)) := by
      intro R
      refine (lintegral_mono_set Set.Ioc_subset_Ioi_self).trans ?_
      rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun x => ENNReal.ofReal ((1 + x) ^ (-κ)))
        (fun x hx => by
          show ENNReal.ofReal ((1 + |x|) ^ (-κ)) = ENNReal.ofReal ((1 + x) ^ (-κ))
          rw [abs_of_pos (Set.mem_Ioi.mp hx)])]
      exact (lintegral_Ioi_one_add_rpow hκ1).le
    rw [hcell, one_mul]
    exact mul_le_mul' (hint _) (hint _)
  -- Step 5: combine.
  have hWp : (∫⁻ θ, ENNReal.ofReal (largeWeightReal κ θ) ∂(loopArcLargeMeasure m N)) ^ (p - 1)
      ≤ (ENNReal.ofReal (-1 / (-κ + 1)) * ENNReal.ofReal (-1 / (-κ + 1))) ^ (p - 1) :=
    ENNReal.rpow_le_rpow hW (by linarith)
  calc ∫⁻ X, (∫⁻ θ, largeIntegrand s N θ X ∂(loopArcLargeMeasure m N)) ^ p ∂μ
      ≤ (∫⁻ θ, ENNReal.ofReal (largeWeightReal κ θ) ∂(loopArcLargeMeasure m N)) ^ (p - 1)
          * ∫⁻ θ, (∫⁻ X, largeIntegrand s N θ X ^ p ∂μ)
              * ENNReal.ofReal (largeWeightReal κ θ) ^ (1 - p) ∂(loopArcLargeMeasure m N) := H1
    _ ≤ (ENNReal.ofReal (-1 / (-κ + 1)) * ENNReal.ofReal (-1 / (-κ + 1))) ^ (p - 1)
          * (ENNReal.ofReal (C ^ p * (4 ^ ((s + 3) / 2)) ^ p * M ^ (2 * p))
            * (ENNReal.ofReal (-1 / (e + 1)) * ENNReal.ofReal (-1 / (e + 1)))) :=
        mul_le_mul' hWp (H2.trans H3)

end Riesz1

end
end
