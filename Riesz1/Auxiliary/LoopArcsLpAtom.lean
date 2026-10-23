/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLpLarge

/-!
# The atom of the cell estimate

The arcs part of Lemma B.2, atomic term `g_N''(N/2) ∫_0^{N/2} A_t(u) B_t(N/2 - u) du`.
The `L^p` norm of the atom over the configuration is bounded uniformly in `N` and the cell: the
Hölder inequality over the parameter `(t, u) ∈ (m, m+1] × (0, N/2]` gives a factor `R^p` with
`R = N/2`, which the factor `|g_N''(R)|^p ≤ C^p R^{-p(s+2)}` absorbs up to `R^{p(2δ-1)} ≤ 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- The atom integrand at `θ = (t, u)` and a configuration `X`: `‖loopCount(t-u, u) - u‖ ·
‖loopCount(t, N/2 - u) - (N/2 - u)‖` for `0 < u ≤ N/2`, and `0` elsewhere. -/
def atomIntegrand (_s : ℝ) (N : ℕ+) (θ : ℝ × ℝ) (X : Configuration N) : ℝ≥0∞ :=
  (Ioc (0 : ℝ) ((N : ℝ) / 2)).indicator (fun u =>
    ‖loopCount (θ.1 - u) u X - u‖ₑ * ‖loopCount θ.1 ((N : ℝ) / 2 - u) X - ((N : ℝ) / 2 - u)‖ₑ)
    θ.2

/-- The atom parameter measure `dt|_{(m, m+1]} ⊗ du|_{(0, N/2]}`. -/
def atomMeasure (m : ℝ) (N : ℕ+) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc m (m + 1))).prod (volume.restrict (Ioc (0 : ℝ) ((N : ℝ) / 2)))

instance sFinite_atomMeasure (m : ℝ) (N : ℕ+) : SFinite (atomMeasure m N) := by
  unfold atomMeasure
  infer_instance

/-- The atom integrand is measurable in the parameter and the configuration. -/
theorem measurable_atomIntegrand (s : ℝ) (N : ℕ+) :
    Measurable (fun q : (ℝ × ℝ) × Configuration N => atomIntegrand s N q.1 q.2) := by
  have hu : Measurable (fun q : (ℝ × ℝ) × Configuration N => q.1.2) := by fun_prop
  have ht : Measurable (fun q : (ℝ × ℝ) × Configuration N => q.1.1) := by fun_prop
  have hX : Measurable (fun q : (ℝ × ℝ) × Configuration N => q.2) := by fun_prop
  have hc1 := measurable_loopCount_of (N := N) (c := fun q => q.2)
    (a := fun q : (ℝ × ℝ) × Configuration N => q.1.1 - q.1.2)
    (r := fun q : (ℝ × ℝ) × Configuration N => q.1.2) (ht.sub hu) hu hX
  have hR : Measurable (fun q : (ℝ × ℝ) × Configuration N => (N : ℝ) / 2 - q.1.2) :=
    measurable_const.sub hu
  have hc2 := measurable_loopCount_of (N := N) (c := fun q => q.2)
    (a := fun q : (ℝ × ℝ) × Configuration N => q.1.1)
    (r := fun q : (ℝ × ℝ) × Configuration N => (N : ℝ) / 2 - q.1.2) ht hR hX
  have hF : Measurable (fun q : (ℝ × ℝ) × Configuration N =>
      ‖loopCount (q.1.1 - q.1.2) q.1.2 q.2 - q.1.2‖ₑ
        * ‖loopCount q.1.1 ((N : ℝ) / 2 - q.1.2) q.2 - ((N : ℝ) / 2 - q.1.2)‖ₑ) :=
    ((hc1.sub hu).enorm).mul ((hc2.sub hR).enorm)
  have hS : MeasurableSet {q : (ℝ × ℝ) × Configuration N | q.1.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} :=
    (measurableSet_Ioc.preimage (measurable_snd.comp measurable_fst))
  have heq : (fun q : (ℝ × ℝ) × Configuration N => atomIntegrand s N q.1 q.2)
      = {q : (ℝ × ℝ) × Configuration N | q.1.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)}.indicator
          (fun q => ‖loopCount (q.1.1 - q.1.2) q.1.2 q.2 - q.1.2‖ₑ
            * ‖loopCount q.1.1 ((N : ℝ) / 2 - q.1.2) q.2 - ((N : ℝ) / 2 - q.1.2)‖ₑ) := by
    funext q
    by_cases h : q.1.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)
    · have h' : q ∈ {q : (ℝ × ℝ) × Configuration N | q.1.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} := h
      rw [atomIntegrand, Set.indicator_of_mem h', Set.indicator_of_mem h]
    · have h' : q ∉ {q : (ℝ × ℝ) × Configuration N | q.1.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)} := h
      rw [atomIntegrand, Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  rw [heq]
  exact hF.indicator hS

/-- The count is zero on the empty arc of length zero. -/
theorem loopCount_zero_radius {N : ℕ+} (a : ℝ) (X : Configuration N) : loopCount a 0 X = 0 := by
  have hempty : microArc N a 0 = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
    obtain ⟨σ, hσ, _⟩ := hz
    linarith [hσ.1, hσ.2]
  simp [loopCount, hempty]

/-- **Real atom bound.** For `R ≥ 1`, `0 < δ < 1/2`, `C, M ≥ 0` and `s > 0`:
`(C R^{-s-2})^p R^p (M (1+R)^{s/2+δ})^{2p} ≤ C^p M^{2p} 2^{(s+2δ)p}`. -/
theorem atom_real_bound {s δ p C M R : ℝ} (hs : 0 < s) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (hM : 0 ≤ M) (hR : 1 ≤ R) :
    (C * R ^ (-s - 2)) ^ p * R ^ p * (M * (1 + R) ^ (s / 2 + δ)) ^ (2 * p)
      ≤ C ^ p * M ^ (2 * p) * 2 ^ ((s + 2 * δ) * p) := by
  have hR0 : 0 < R := by linarith
  have hp0 : 0 < p := by linarith
  have hσ : 0 ≤ s / 2 + δ := by linarith
  -- `1 + R ≤ 2 R`, hence `(1+R)^σ ≤ 2^σ R^σ`
  have h2R : (1 + R) ^ (s / 2 + δ) ≤ 2 ^ (s / 2 + δ) * R ^ (s / 2 + δ) := by
    rw [← Real.mul_rpow (by norm_num) hR0.le]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hσ
  have hA : (M * (1 + R) ^ (s / 2 + δ)) ^ (2 * p)
      ≤ M ^ (2 * p) * (2 ^ (s / 2 + δ) * R ^ (s / 2 + δ)) ^ (2 * p) := by
    rw [Real.mul_rpow hM (Real.rpow_nonneg (by linarith) _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.rpow_nonneg (by linarith) _)
      h2R (by linarith)) (Real.rpow_nonneg hM _)
  have e2 : (2 ^ (s / 2 + δ) * R ^ (s / 2 + δ)) ^ (2 * p)
      = 2 ^ ((s + 2 * δ) * p) * (R ^ (s / 2 + δ)) ^ (2 * p) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hR0.le _),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    ring
  have hRexp : (R ^ (-s - 2)) ^ p * R ^ p * (R ^ (s / 2 + δ)) ^ (2 * p)
      = R ^ (p * (2 * δ - 1)) := by
    have h1 : (R ^ (-s - 2)) ^ p = R ^ ((-s - 2) * p) := (Real.rpow_mul hR0.le _ _).symm
    have h2 : (R ^ (s / 2 + δ)) ^ (2 * p) = R ^ ((s / 2 + δ) * (2 * p)) :=
      (Real.rpow_mul hR0.le _ _).symm
    rw [h1, h2, ← Real.rpow_add hR0, ← Real.rpow_add hR0]
    congr 1
    ring
  have hRle : R ^ (p * (2 * δ - 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by nlinarith)
  have e1 : (C * R ^ (-s - 2)) ^ p = C ^ p * (R ^ (-s - 2)) ^ p :=
    Real.mul_rpow hC (Real.rpow_nonneg hR0.le _)
  calc (C * R ^ (-s - 2)) ^ p * R ^ p * (M * (1 + R) ^ (s / 2 + δ)) ^ (2 * p)
      ≤ (C * R ^ (-s - 2)) ^ p * R ^ p * (M ^ (2 * p) * (2 ^ (s / 2 + δ) * R ^ (s / 2 + δ)) ^ (2 * p)) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ = C ^ p * M ^ (2 * p) * 2 ^ ((s + 2 * δ) * p)
          * ((R ^ (-s - 2)) ^ p * R ^ p * (R ^ (s / 2 + δ)) ^ (2 * p)) := by
        rw [e1, e2]
        ring
    _ ≤ C ^ p * M ^ (2 * p) * 2 ^ ((s + 2 * δ) * p) * 1 := by
        rw [hRexp]
        exact mul_le_mul_of_nonneg_left hRle (by positivity)
    _ = C ^ p * M ^ (2 * p) * 2 ^ ((s + 2 * δ) * p) := mul_one _

/-- **Moment of the atom integrand.** For `0 < u ≤ N/2` the `p`-th lower moment over the
configuration of the atom integrand is at most `(M(1+N/2)^{s/2+δ})^{2p}`-type product. -/
theorem lintegral_atomIntegrand_pow_le {s δ p M : ℝ} (hs : 0 < s) (hδ0 : 0 < δ) (hp : 1 ≤ p)
    (hM : 0 ≤ M) {N : ℕ+} {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hmom : ∀ a u : ℝ, 0 < u → u ≤ (N : ℝ) / 2 →
      ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p) ∂μ
        ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p))
    (θ : ℝ × ℝ) :
    ∫⁻ X, atomIntegrand s N θ X ^ p ∂μ
      ≤ (Ioc (0 : ℝ) ((N : ℝ) / 2)).indicator (fun _ : ℝ =>
          ENNReal.ofReal (M * (1 + (N : ℝ) / 2) ^ (s / 2 + δ)) ^ p
            * ENNReal.ofReal (M * (1 + (N : ℝ) / 2) ^ (s / 2 + δ)) ^ p) θ.2 := by
  have hp0 : 0 < p := by linarith
  by_cases hu : θ.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2)
  · rw [Set.indicator_of_mem hu]
    obtain ⟨hu0, huR⟩ := hu
    have hfun : ∀ X, atomIntegrand s N θ X
        = ‖loopCount (θ.1 - θ.2) θ.2 X - θ.2‖ₑ
          * ‖loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)‖ₑ := by
      intro X
      rw [atomIntegrand, Set.indicator_of_mem (show θ.2 ∈ Ioc (0 : ℝ) ((N : ℝ) / 2) from
        ⟨hu0, huR⟩)]
    simp only [hfun]
    have hXA : Measurable (fun X : Configuration N => loopCount (θ.1 - θ.2) θ.2 X - θ.2) :=
      (measurable_loopCount_of (N := N) (c := id) (a := fun _ => θ.1 - θ.2) (r := fun _ => θ.2)
        measurable_const measurable_const measurable_id).sub measurable_const
    have hXB : Measurable (fun X : Configuration N =>
        loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)) :=
      (measurable_loopCount_of (N := N) (c := id) (a := fun _ => θ.1)
        (r := fun _ => (N : ℝ) / 2 - θ.2) measurable_const measurable_const measurable_id).sub
        measurable_const
    have hcs := lintegral_enorm_rpow_mul_le μ hXA hXB hp
    have hA := hmom (θ.1 - θ.2) θ.2 hu0 huR
    have hMono : M * (1 + θ.2) ^ (s / 2 + δ) ≤ M * (1 + (N : ℝ) / 2) ^ (s / 2 + δ) := by
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) (by
        have : (0 : ℝ) ≤ s / 2 + δ := by linarith
        exact this)) hM
    have hAB : (∫⁻ X, ‖loopCount (θ.1 - θ.2) θ.2 X - θ.2‖ₑ ^ (2 * p) ∂μ) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (M * (1 + (N : ℝ) / 2) ^ (s / 2 + δ)) ^ p := by
      calc _ ≤ (ENNReal.ofReal (M * (1 + θ.2) ^ (s / 2 + δ)) ^ (2 * p)) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow hA (by norm_num)
        _ ≤ (ENNReal.ofReal (M * (1 + (N : ℝ) / 2) ^ (s / 2 + δ)) ^ (2 * p)) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hMono)
              (by linarith)) (by norm_num)
        _ = _ := ofReal_rpow_two_mul_half (mul_nonneg hM (Real.rpow_nonneg (by linarith) _))
    have hBB : (∫⁻ X, ‖loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)‖ₑ ^ (2 * p) ∂μ)
        ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (M * (1 + (N : ℝ) / 2) ^ (s / 2 + δ)) ^ p := by
      by_cases hRu : (N : ℝ) / 2 - θ.2 = 0
      · have hz : ∀ X : Configuration N,
            ‖loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)‖ₑ = 0 :=
          fun X => by
            rw [hRu, loopCount_zero_radius]
            simp
        have h0 : ∫⁻ X, ‖loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)‖ₑ ^ (2 * p) ∂μ
            = 0 := by
          simp only [hz, ENNReal.zero_rpow_of_pos (show (0 : ℝ) < 2 * p by linarith)]
          exact lintegral_zero
        rw [h0, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact zero_le
      · have hR' : 0 < (N : ℝ) / 2 - θ.2 :=
          lt_of_le_of_ne (by linarith) (Ne.symm hRu)
        have hB := hmom θ.1 ((N : ℝ) / 2 - θ.2) hR' (by linarith)
        have hMono' : M * (1 + ((N : ℝ) / 2 - θ.2)) ^ (s / 2 + δ)
            ≤ M * (1 + (N : ℝ) / 2) ^ (s / 2 + δ) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) (by linarith) (by
            have : (0 : ℝ) ≤ s / 2 + δ := by linarith
            exact this)) hM
        calc _ ≤ (ENNReal.ofReal (M * (1 + ((N : ℝ) / 2 - θ.2)) ^ (s / 2 + δ)) ^ (2 * p))
              ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hB (by norm_num)
          _ ≤ (ENNReal.ofReal (M * (1 + (N : ℝ) / 2) ^ (s / 2 + δ)) ^ (2 * p)) ^ (1 / 2 : ℝ) :=
              ENNReal.rpow_le_rpow (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hMono')
                (by linarith)) (by norm_num)
          _ = _ := ofReal_rpow_two_mul_half (mul_nonneg hM (Real.rpow_nonneg (by linarith) _))
    calc ∫⁻ X, (‖loopCount (θ.1 - θ.2) θ.2 X - θ.2‖ₑ
          * ‖loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)‖ₑ) ^ p ∂μ
        = ∫⁻ X, ‖loopCount (θ.1 - θ.2) θ.2 X - θ.2‖ₑ ^ p
            * ‖loopCount θ.1 ((N : ℝ) / 2 - θ.2) X - ((N : ℝ) / 2 - θ.2)‖ₑ ^ p ∂μ :=
          lintegral_congr fun X => ENNReal.mul_rpow_of_nonneg _ _ hp0.le
      _ ≤ _ := hcs
      _ ≤ _ := mul_le_mul' hAB hBB
  · rw [Set.indicator_of_notMem hu]
    have hz : ∀ X : Configuration N, atomIntegrand s N θ X = 0 := fun X => by
      rw [atomIntegrand, Set.indicator_of_notMem (show θ.2 ∉ Ioc (0 : ℝ) ((N : ℝ) / 2) from hu)]
    simp [hz, ENNReal.zero_rpow_of_pos hp0]

/-- The atom parameter measure has total mass `N/2`. -/
theorem atomMeasure_univ (m : ℝ) (N : ℕ+) (_hR : 0 ≤ (N : ℝ) / 2) :
    atomMeasure m N Set.univ = ENNReal.ofReal ((N : ℝ) / 2) := by
  unfold atomMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ,
    Measure.restrict_apply_univ, Real.volume_Ioc, Real.volume_Ioc]
  simp

/-- **Integrated atom bound.** For `N ≥ 2`, the `L^p` norm over the configuration of the atom
`‖g_N''(N/2)‖ ∫_{cell} ∫_0^{N/2} A_t(u) B_t(N/2-u) du dt` is bounded by an explicit constant,
uniform in `N` and the cell. -/
theorem loopArc_atom_lp_le {s δ p M C : ℝ} (hs : 0 < s) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (hp : 1 ≤ p) (hM : 0 ≤ M) (hC : 0 ≤ C) (m : ℝ) {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hmom : ∀ a u : ℝ, 0 < u → u ≤ (N : ℝ) / 2 →
      ∫⁻ X, ‖loopCount a u X - u‖ₑ ^ (2 * p) ∂μ
        ≤ ENNReal.ofReal (M * (1 + u) ^ (s / 2 + δ)) ^ (2 * p))
    (hg2 : ∀ r : ℝ, 0 < r → r ≤ (N : ℝ) / 2 →
      ‖iteratedDeriv 2 (loopArcG s N) r‖ₑ ≤ ENNReal.ofReal (C * r ^ (-s - 2))) :
    ∫⁻ X, (‖iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)‖ₑ
        * ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N)) ^ p ∂μ
      ≤ ENNReal.ofReal (C ^ p * M ^ (2 * p) * 2 ^ ((s + 2 * δ) * p)) := by
  have hp0 : 0 < p := by linarith
  have hR1 : (1 : ℝ) ≤ (N : ℝ) / 2 := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have := sFinite_atomMeasure m N
  set R : ℝ := (N : ℝ) / 2 with hR
  set σ : ℝ := s / 2 + δ with hσ
  set c : ℝ≥0∞ := ENNReal.ofReal (M * (1 + R) ^ σ) ^ p * ENNReal.ofReal (M * (1 + R) ^ σ) ^ p
    with hc
  -- Step 1: Hölder in the parameter with the unit weight.
  have H := lintegral_lintegral_rpow_le_weighted μ (atomMeasure m N)
    (F := fun θ X => atomIntegrand s N θ X) (measurable_atomIntegrand s N)
    (w := fun _ => (1 : ℝ≥0∞)) measurable_const (fun _ => one_ne_zero) (fun _ => ENNReal.one_ne_top) hp
  -- Step 2: the total mass.
  have hmass : ∫⁻ _ : ℝ × ℝ, (1 : ℝ≥0∞) ∂(atomMeasure m N) = ENNReal.ofReal R := by
    rw [lintegral_const, one_mul, atomMeasure_univ m N (by linarith)]
  -- Step 3: the moment integral against the parameter.
  have hind : ∫⁻ θ, (Ioc (0 : ℝ) R).indicator (fun _ : ℝ => c) θ.2 ∂(atomMeasure m N)
      = ENNReal.ofReal R * c := by
    unfold atomMeasure
    have hmeas : Measurable (fun θ : ℝ × ℝ => (Ioc (0 : ℝ) R).indicator (fun _ : ℝ => c) θ.2) :=
      (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
    rw [lintegral_prod (fun θ : ℝ × ℝ => (Ioc (0 : ℝ) R).indicator (fun _ : ℝ => c) θ.2)
      hmeas.aemeasurable]
    have hinner : ∀ t : ℝ, ∫⁻ y, (Ioc (0 : ℝ) R).indicator (fun _ : ℝ => c) y
        ∂(volume.restrict (Ioc (0 : ℝ) R)) = c * ENNReal.ofReal R := by
      intro t
      rw [lintegral_indicator_const measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
        Set.inter_self, Real.volume_Ioc, sub_zero]
    calc ∫⁻ t, ∫⁻ y, (Ioc (0 : ℝ) R).indicator (fun _ : ℝ => c) (t, y).2
            ∂(volume.restrict (Ioc (0 : ℝ) R)) ∂(volume.restrict (Ioc m (m + 1)))
        = ∫⁻ _t, c * ENNReal.ofReal R ∂(volume.restrict (Ioc m (m + 1))) :=
          lintegral_congr fun t => hinner t
      _ = ENNReal.ofReal R * c := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
          simp only [add_sub_cancel_left, ENNReal.ofReal_one]
          ring
  have hstep : ∫⁻ θ, (∫⁻ X, atomIntegrand s N θ X ^ p ∂μ) * (1 : ℝ≥0∞) ^ (1 - p)
      ∂(atomMeasure m N) ≤ ENNReal.ofReal R * c := by
    rw [← hind]
    refine lintegral_mono fun θ => ?_
    rw [ENNReal.one_rpow, mul_one]
    exact lintegral_atomIntegrand_pow_le hs hδ0 hp hM hmom θ
  -- Step 4: Hölder inequality for the `p`-th power of the atom.
  have hx0 : (ENNReal.ofReal R) ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hxt : ENNReal.ofReal R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hJ : ∫⁻ X, (∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N)) ^ p ∂μ
      ≤ ENNReal.ofReal R ^ p * c := by
    have hmass' : ∫⁻ _ : ℝ × ℝ, (1 : ℝ≥0∞) ∂(atomMeasure m N) = ENNReal.ofReal R := hmass
    calc _ ≤ (∫⁻ θ, (1 : ℝ≥0∞) ∂(atomMeasure m N)) ^ (p - 1)
          * ∫⁻ θ, (∫⁻ X, atomIntegrand s N θ X ^ p ∂μ) * (1 : ℝ≥0∞) ^ (1 - p)
            ∂(atomMeasure m N) := H
      _ ≤ ENNReal.ofReal R ^ (p - 1) * (ENNReal.ofReal R * c) := by
          rw [hmass']
          exact mul_le_mul' le_rfl hstep
      _ = ENNReal.ofReal R ^ p * c := by
          have hsplit : ENNReal.ofReal R ^ p = ENNReal.ofReal R ^ (p - 1) * ENNReal.ofReal R := by
            have h := ENNReal.rpow_add (p - 1) 1 hx0 hxt
            rw [ENNReal.rpow_one, show p - 1 + 1 = p by ring] at h
            exact h
          rw [hsplit]
          ring
  -- Step 5: the atom term with the factor `‖g_N''(N/2)‖`.
  have hg2R : ‖iteratedDeriv 2 (loopArcG s N) R‖ₑ ≤ ENNReal.ofReal (C * R ^ (-s - 2)) :=
    hg2 R (by linarith) le_rfl
  have hY : 0 ≤ M * (1 + R) ^ σ := mul_nonneg hM (Real.rpow_nonneg (by linarith) _)
  have hXC : 0 ≤ C * R ^ (-s - 2) := mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  have hfin : ENNReal.ofReal (C * R ^ (-s - 2)) ^ p * (ENNReal.ofReal R ^ p * c)
      = ENNReal.ofReal ((C * R ^ (-s - 2)) ^ p * R ^ p * (M * (1 + R) ^ σ) ^ (2 * p)) := by
    have h1 : 0 ≤ (M * (1 + R) ^ σ) ^ p := Real.rpow_nonneg hY _
    have h2 : 0 ≤ R ^ p := Real.rpow_nonneg (by linarith) _
    have h3 : 0 ≤ (C * R ^ (-s - 2)) ^ p := Real.rpow_nonneg hXC _
    rw [ENNReal.ofReal_rpow_of_nonneg hXC hp0.le, ENNReal.ofReal_rpow_of_nonneg (by linarith) hp0.le,
      hc, ENNReal.ofReal_rpow_of_nonneg hY hp0.le, ← ENNReal.ofReal_mul h1,
      ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h3]
    congr 1
    rw [show (2 * p) = p + p by ring, Real.rpow_add' hY (by linarith)]
    ring
  calc ∫⁻ X, (‖iteratedDeriv 2 (loopArcG s N) R‖ₑ
          * ∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N)) ^ p ∂μ
      = ∫⁻ X, ‖iteratedDeriv 2 (loopArcG s N) R‖ₑ ^ p
          * (∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N)) ^ p ∂μ :=
        lintegral_congr fun X => ENNReal.mul_rpow_of_nonneg _ _ hp0.le
    _ = ‖iteratedDeriv 2 (loopArcG s N) R‖ₑ ^ p
          * ∫⁻ X, (∫⁻ θ, atomIntegrand s N θ X ∂(atomMeasure m N)) ^ p ∂μ :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hg2R))
    _ ≤ ENNReal.ofReal (C * R ^ (-s - 2)) ^ p * (ENNReal.ofReal R ^ p * c) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hg2R hp0.le) hJ
    _ = ENNReal.ofReal ((C * R ^ (-s - 2)) ^ p * R ^ p * (M * (1 + R) ^ σ) ^ (2 * p)) := hfin
    _ ≤ ENNReal.ofReal (C ^ p * M ^ (2 * p) * 2 ^ ((s + 2 * δ) * p)) :=
        ENNReal.ofReal_le_ofReal (atom_real_bound hs hδ0 hδ1 hp hC hM hR1)

end Riesz1

end
end
