/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsComplete
public import Riesz1.Auxiliary.LoopCrudeOne

/-!
# The crude microscopic loop bound

The crude part of Lemma B.2: for `C¹` `N`-periodic `b`,
`‖L(b)‖_{L^p} ≤ C_{β,s,p} ∑_{m=0}^{N-1} sup_{z∈[m,m+1]} |b'(z)|`, uniformly in `N`.

For `N ≥ 2` the identity `L(b) = -2 ∫_{N𝕋} b' Λ` splits into the `N` unit cells and the cell `L^p`
bound applies. For `N = 1` the arc decomposition is unavailable and the deterministic bound
`loopArcL_one_abs_le` is used instead. The suprema are written as `sSup` of the image of `|b'|` on
`[m, m+1]`, which is nonempty and bounded because `b'` is continuous.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

namespace Riesz1

/-- The supremum of `|b'|` over the unit cell `[m, m+1]`. -/
def cellSup (b : ℝ → ℝ) (m : ℕ) : ℝ :=
  sSup ((fun z => |deriv b z|) '' Icc (m : ℝ) ((m : ℝ) + 1))

/-- The supremum over a cell bounds `|b'|` on the cell, for a `C¹` function. -/
theorem abs_deriv_le_cellSup {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b) (m : ℕ) {t : ℝ}
    (ht : t ∈ Icc (m : ℝ) ((m : ℝ) + 1)) : |deriv b t| ≤ cellSup b m := by
  have hcont : ContinuousOn (fun z => |deriv b z|) (Icc (m : ℝ) ((m : ℝ) + 1)) :=
    (hb.continuous_deriv le_rfl).abs.continuousOn
  have hbdd : BddAbove ((fun z => |deriv b z|) '' Icc (m : ℝ) ((m : ℝ) + 1)) :=
    (isCompact_Icc.image_of_continuousOn hcont).bddAbove
  exact le_csSup hbdd ⟨t, ht, rfl⟩

/-- The cell suprema are nonnegative. -/
theorem cellSup_nonneg (b : ℝ → ℝ) (m : ℕ) : 0 ≤ cellSup b m :=
  Real.sSup_nonneg fun _ ⟨_, _, hz⟩ => hz ▸ abs_nonneg _

/-- The arc integral over the unit cell `[m, m+1]` is bounded by the cell supremum times the
arclength integral of `|Λ|`. -/
theorem norm_cell_integral_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+} (X : Configuration N)
    {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b) (m : ℕ) (hm : m < N) :
    ‖∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), deriv b t * loopArcLambda s N X t‖
      ≤ cellSup b m * ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t| := by
  have hsub : Ioc (m : ℝ) ((m : ℝ) + 1) ⊆ Ioc (0 : ℝ) (N : ℝ) := by
    intro t ht
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmN : (m : ℝ) + 1 ≤ (N : ℝ) := by
      have : m + 1 ≤ (N : ℕ) := hm
      exact_mod_cast this
    exact ⟨lt_of_le_of_lt hm0 ht.1, ht.2.trans hmN⟩
  have hΛint : IntegrableOn (fun t => loopArcLambda s N X t) (Ioc (m : ℝ) ((m : ℝ) + 1)) :=
    (integrable_loopArcLambda s hs0 hs1 N X).mono_set hsub
  have hbcont : Continuous (deriv b) := hb.continuous_deriv le_rfl
  have hmeas : AEStronglyMeasurable (fun t => deriv b t * loopArcLambda s N X t)
      (volume.restrict (Ioc (m : ℝ) ((m : ℝ) + 1))) :=
    hbcont.aestronglyMeasurable.mul hΛint.aestronglyMeasurable
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioc (m : ℝ) ((m : ℝ) + 1))),
      ‖deriv b t * loopArcLambda s N X t‖ ≤ cellSup b m * |loopArcLambda s N X t| := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_deriv_le_cellSup hb m ⟨ht.1.le, ht.2⟩)
      (abs_nonneg _)
  have hint : Integrable (fun t => cellSup b m * |loopArcLambda s N X t|)
      (volume.restrict (Ioc (m : ℝ) ((m : ℝ) + 1))) :=
    (hΛint.abs).const_mul _
  calc ‖∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), deriv b t * loopArcLambda s N X t‖
      ≤ ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), cellSup b m * |loopArcLambda s N X t| :=
        norm_integral_le_of_norm_le hint hbound
    _ = cellSup b m * ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t| :=
        integral_const_mul _ _

/-- The arc integral of `b' Λ` over `(0, N]` is the sum over the `N` unit cells. -/
theorem loopArcL_abs_le_cells {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) (X : Configuration N)
    {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b) (hper : Function.Periodic b (N : ℝ)) :
    |loopArcL s N b X| ≤ 2 * ∑ m ∈ range (N : ℕ), cellSup b m
      * ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t| := by
  have hbcont : Continuous (deriv b) := hb.continuous_deriv le_rfl
  have hΛN : IntegrableOn (fun t => loopArcLambda s N X t) (Ioc (0 : ℝ) (N : ℝ)) :=
    integrable_loopArcLambda s hs0 hs1 N X
  have hcellint : ∀ m ∈ range (N : ℕ), IntervalIntegrable (fun t => deriv b t * loopArcLambda s N X t)
      volume ((fun k : ℕ => (k : ℝ)) m) ((fun k : ℕ => (k : ℝ)) (m + 1)) := by
    intro m hm
    have hm' : m < N := Finset.mem_range.mp hm
    have hsub : Ioc ((m : ℕ) : ℝ) (((m : ℕ) : ℝ) + 1) ⊆ Ioc (0 : ℝ) (N : ℝ) := by
      intro t ht
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hmN : (m : ℝ) + 1 ≤ (N : ℝ) := by
        have : m + 1 ≤ (N : ℕ) := hm'
        exact_mod_cast this
      exact ⟨lt_of_le_of_lt hm0 ht.1, ht.2.trans hmN⟩
    have hΛ : IntegrableOn (fun t => loopArcLambda s N X t) (Ioc (m : ℝ) ((m : ℝ) + 1)) :=
      hΛN.mono_set hsub
    have hint : IntegrableOn (fun t => deriv b t * loopArcLambda s N X t)
        (Ioc (m : ℝ) ((m : ℝ) + 1)) := by
      refine Integrable.mono' (hΛ.abs.const_mul (cellSup b m))
        (hbcont.aestronglyMeasurable.mul hΛ.aestronglyMeasurable) ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_deriv_le_cellSup hb m ⟨ht.1.le, ht.2⟩)
        (abs_nonneg _)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp)]
    simpa using hint
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t => deriv b t * loopArcLambda s N X t) (a := fun k : ℕ => (k : ℝ))
    (n := (N : ℕ)) (fun k hk => hcellint k (Finset.mem_range.mpr hk))
  simp only [Nat.cast_zero] at hsplit
  rw [loopArcL_eq_integral_lambda s hs0 hs1 N b hb hper X, abs_mul, abs_neg, abs_two,
    ← hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hm' : m < N := Finset.mem_range.mp hm
  have hc := norm_cell_integral_le hs0 hs1 X hb m hm'
  have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
  rw [intervalIntegral.integral_of_le hle]
  push_cast
  simpa only [Real.norm_eq_abs] using hc

/-- The arc functional is a measurable function of the configuration. -/
theorem stronglyMeasurable_loopArcL {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+)
    {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b) (hper : Function.Periodic b (N : ℝ)) :
    StronglyMeasurable (fun X : Configuration N => loopArcL s N b X) := by
  have hfun : (fun X : Configuration N => loopArcL s N b X)
      = fun X => -2 * ∫ t in Ioc (0 : ℝ) (N : ℝ), deriv b t * loopArcLambda s N X t := by
    funext X
    rw [loopArcL_eq_integral_lambda s hs0 hs1 N b hb hper X,
      intervalIntegral.integral_of_le (by positivity)]
  rw [hfun]
  have hbcont : Continuous (deriv b) := hb.continuous_deriv le_rfl
  have hF : StronglyMeasurable (fun z : Configuration N × ℝ =>
      deriv b z.2 * loopArcLambda s N z.1 z.2) :=
    ((hbcont.measurable.comp measurable_snd).stronglyMeasurable).mul
      (stronglyMeasurable_loopArcLambda s N)
  exact (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) (N : ℝ)))
    (f := fun z : Configuration N × ℝ => deriv b z.2 * loopArcLambda s N z.1 z.2) hF).const_mul _

/-- The cell functional `∫_{[m, m+1]} |Λ|` is strongly measurable in the configuration. -/
theorem stronglyMeasurable_cellAbs {s : ℝ} (N : ℕ+) (m : ℝ) :
    StronglyMeasurable (fun X : Configuration N => ∫ t in Ioc m (m + 1), |loopArcLambda s N X t|) := by
  have hsm : StronglyMeasurable (fun z : Configuration N × ℝ => |loopArcLambda s N z.1 z.2|) := by
    have h0 := (stronglyMeasurable_loopArcLambda s N).norm
    simpa only [Real.norm_eq_abs] using h0
  exact hsm.integral_prod_right' (ν := volume.restrict (Ioc m (m + 1)))

/-- **Crude microscopic loop bound**, the crude part of Lemma B.2, conditional on the
rigidity conclusion. There is `C ≥ 0` such that, assuming the Prékopa–Leindler inequality
`External.PrekopaLeindler`, every `N` and every `C¹` `N`-periodic `b` satisfy
`‖L(b)‖_{L^p} ≤ C ∑_{m=0}^{N-1} sup_{z∈[m,m+1]} |b'(z)|`. -/
theorem loopArc_crude_of_rigidity {beta s : ℝ} (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Internal.RigidityConclusion beta s hbeta hs hs1) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (b : ℝ → ℝ),
      ContDiff ℝ 1 b → Function.Periodic b (N : ℝ) →
        eLpNorm (fun X : Configuration N => loopArcL s N b X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
          ≤ ENNReal.ofReal (C * ∑ m ∈ Finset.range (N : ℕ),
              sSup ((fun z => |deriv b z|) '' Icc (m : ℝ) ((m : ℝ) + 1))) := by
  obtain ⟨C₂, hC₂, hcomp⟩ := loopArc_complete_of_rigidity hbeta hs hs1 hRig hp
  obtain ⟨C₁, hC₁, hone⟩ := loopArcL_one_abs_le hs hs1
  refine ⟨2 * C₂ + C₁, by linarith, fun hPL N b hb hper => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) :=
    (modelWellDefined _ N).2.2
  have hp0 : (0 : ℝ) < p := by linarith
  have hpE : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hpT : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum_nonneg : 0 ≤ ∑ m ∈ Finset.range (N : ℕ),
      sSup ((fun z => |deriv b z|) '' Icc (m : ℝ) ((m : ℝ) + 1)) :=
    Finset.sum_nonneg fun m _ => Real.sSup_nonneg fun x ⟨z, _, hz⟩ => hz ▸ abs_nonneg _
  rcases (show (N : ℕ) = 1 ∨ 2 ≤ (N : ℕ) by have := N.pos; omega) with hN1 | hN2
  · -- the case `N = 1`: the deterministic bound
    have hN : N = 1 := PNat.coe_eq_one_iff.mp hN1
    subst hN
    set M : ℝ := sSup ((fun z => |deriv b z|) '' Icc (0 : ℝ) 1) with hM
    have hbdd : BddAbove ((fun z => |deriv b z|) '' Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn (hb.continuous_deriv le_rfl).abs.continuousOn).bddAbove
    have hMb : ∀ z ∈ Icc (0 : ℝ) 1, |deriv b z| ≤ M := fun z hz => le_csSup hbdd ⟨z, hz, rfl⟩
    have hM0 : 0 ≤ M := Real.sSup_nonneg fun x ⟨z, _, hz⟩ => hz ▸ abs_nonneg _
    have hper1 : Function.Periodic b 1 := by simpa using hper
    have hpt : ∀ X : Configuration 1, ‖loopArcL s 1 b X‖ ≤ C₁ * M := fun X => by
      rw [Real.norm_eq_abs]
      exact hone b M hb hper1 hMb X
    have hL := eLpNorm_mono_real (p := ENNReal.ofReal p)
      (μ := gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) 1)
      (stronglyMeasurable_loopArcL hs hs1 1 hb hper).aestronglyMeasurable hpt
    rw [eLpNorm_const (C₁ * M) hpE (IsProbabilityMeasure.ne_zero _), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal (mul_nonneg hC₁ hM0)] at hL
    have hsum1 : (∑ m ∈ Finset.range ((1 : ℕ+) : ℕ),
        sSup ((fun z => |deriv b z|) '' Icc (m : ℝ) ((m : ℝ) + 1))) = M := by
      simp [hM]
    rw [hsum1]
    refine hL.trans (ENNReal.ofReal_le_ofReal ?_)
    nlinarith
  · -- the case `N ≥ 2`: the cell decomposition
    have hpt : ∀ X : Configuration N, ‖loopArcL s N b X‖
        ≤ 2 * ∑ m ∈ Finset.range (N : ℕ), cellSup b m
          * ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t| := fun X => by
      rw [Real.norm_eq_abs]
      exact loopArcL_abs_le_cells hs hs1 N X hb hper
    have h1 := eLpNorm_mono_real (p := ENNReal.ofReal p)
      (μ := gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
      (stronglyMeasurable_loopArcL hs hs1 N hb hper).aestronglyMeasurable hpt
    have hg : (fun X : Configuration N => 2 * ∑ m ∈ Finset.range (N : ℕ), cellSup b m
          * ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|)
        = ∑ m ∈ Finset.range (N : ℕ), (fun X : Configuration N =>
            (2 * cellSup b m) • ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|) := by
      funext X
      simp only [Finset.sum_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hterm : ∀ m ∈ Finset.range (N : ℕ), eLpNorm (fun X : Configuration N =>
        (2 * cellSup b m) • ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|)
          (ENNReal.ofReal p) (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
        ≤ ENNReal.ofReal (2 * C₂ * cellSup b m) := by
      intro m hm
      have hm' : m < N := Finset.mem_range.mp hm
      have hF := (hcomp hPL N hN2 b hb hper m hm').2.2
      have hnn : 0 ≤ 2 * cellSup b m := mul_nonneg (by norm_num) (cellSup_nonneg b m)
      have hsm := eLpNorm_const_smul (𝕜 := ℝ) (2 * cellSup b m)
        (fun X : Configuration N => ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|)
        (ENNReal.ofReal p) (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
      refine (le_of_eq hsm).trans ?_
      rw [Real.enorm_eq_ofReal hnn]
      calc ENNReal.ofReal (2 * cellSup b m) * _ ≤ ENNReal.ofReal (2 * cellSup b m)
            * ENNReal.ofReal C₂ := mul_le_mul' le_rfl hF
        _ = ENNReal.ofReal (2 * C₂ * cellSup b m) := by
            rw [← ENNReal.ofReal_mul hnn]
            ring_nf
    have hsum_eq : ∑ m ∈ Finset.range (N : ℕ), ENNReal.ofReal (2 * C₂ * cellSup b m)
        = ENNReal.ofReal (∑ m ∈ Finset.range (N : ℕ), 2 * C₂ * cellSup b m) :=
      (ENNReal.ofReal_sum_of_nonneg fun m _ => mul_nonneg (by linarith)
        (cellSup_nonneg b m)).symm
    have hcs : ∑ m ∈ Finset.range (N : ℕ), 2 * C₂ * cellSup b m
        = 2 * C₂ * ∑ m ∈ Finset.range (N : ℕ), cellSup b m := by
      rw [Finset.mul_sum]
    have hcs_nonneg : 0 ≤ ∑ m ∈ Finset.range (N : ℕ), cellSup b m :=
      Finset.sum_nonneg fun m _ => cellSup_nonneg b m
    calc eLpNorm (fun X : Configuration N => loopArcL s N b X) (ENNReal.ofReal p)
          (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
        ≤ eLpNorm (fun X : Configuration N => 2 * ∑ m ∈ Finset.range (N : ℕ), cellSup b m
          * ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|) (ENNReal.ofReal p)
          (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) := h1
      _ = eLpNorm (∑ m ∈ Finset.range (N : ℕ), (fun X : Configuration N =>
            (2 * cellSup b m) • ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|))
          (ENNReal.ofReal p) (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) := by
          rw [hg]
      _ ≤ ∑ m ∈ Finset.range (N : ℕ), eLpNorm (fun X : Configuration N =>
            (2 * cellSup b m) • ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|)
              (ENNReal.ofReal p) (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) :=
          eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hp)
      _ ≤ ∑ m ∈ Finset.range (N : ℕ), ENNReal.ofReal (2 * C₂ * cellSup b m) :=
          Finset.sum_le_sum hterm
      _ = ENNReal.ofReal (2 * C₂ * ∑ m ∈ Finset.range (N : ℕ), cellSup b m) := by
          rw [hsum_eq, hcs]
      _ ≤ ENNReal.ofReal ((2 * C₂ + C₁) * ∑ m ∈ Finset.range (N : ℕ),
            sSup ((fun z => |deriv b z|) '' Icc (m : ℝ) ((m : ℝ) + 1))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : (0 : ℝ) ≤ C₁ * ∑ m ∈ Finset.range (N : ℕ), cellSup b m :=
            mul_nonneg hC₁ hcs_nonneg
          change 2 * C₂ * ∑ m ∈ Finset.range (N : ℕ), cellSup b m
            ≤ (2 * C₂ + C₁) * ∑ m ∈ Finset.range (N : ℕ), cellSup b m
          nlinarith

end Riesz1

end
end
