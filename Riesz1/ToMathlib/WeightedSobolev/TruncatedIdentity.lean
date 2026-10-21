/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# An almost-everywhere identity on truncated sets

A general limit lemma used to identify the limit of a sequence of pointwise products. Let
`F` be the `L²` limit of `G k`. On a set `S` where `|s| ≤ C`, suppose that `G k - s D` is
controlled by `C |E k|` with `E k → 0` in `L²`. Then `F = s D` almost everywhere on `S`.

This is the mechanism that identifies the Hessian energy of a vector Sobolev limit with
`√(2 χ''_ij(y_j - y_i)) (w_j - w_i)` in `riesz1/HelfferSjostrand/VectorEnergySobolev`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1.WeightedSobolev

/-- On a measurable set `S`, the `L²` limit `F` of `G k` equals `s D` almost everywhere, when
`G k - s D` is controlled by `C |E k|` on `S` and `E k` tends to zero in `L²`. -/
theorem ae_eq_mul_on_of_eLpNorm_tendsto {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F D s : Ω → ℝ} {S : Set Ω} (hS : MeasurableSet S) (hF : AEStronglyMeasurable F μ)
    (hD : AEStronglyMeasurable D μ) (hs : Measurable s) {G E : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hG : Tendsto (fun k => eLpNorm (fun y => G k y - F y) 2 μ) atTop (𝓝 0))
    (hE : Tendsto (fun k => eLpNorm (E k) 2 μ) atTop (𝓝 0))
    (hGE : ∀ k, ∀ᵐ y ∂μ, y ∈ S → ‖G k y - s y * D y‖ ≤ C * ‖E k y‖)
    (hGm : ∀ k, AEStronglyMeasurable (fun y => G k y - F y) μ)
    (hEm : ∀ k, AEStronglyMeasurable (E k) μ) :
    ∀ᵐ y ∂μ, y ∈ S → F y = s y * D y := by
  set R : Ω → ℝ := S.indicator (fun y => F y - s y * D y) with hRdef
  have hRm : AEStronglyMeasurable R μ :=
    AEStronglyMeasurable.indicator (hF.sub (hs.aestronglyMeasurable.mul hD)) hS
  have hbound : ∀ k, eLpNorm R 2 μ ≤
      eLpNorm (fun y => G k y - F y) 2 μ + ‖C‖ₑ * eLpNorm (E k) 2 μ := by
    intro k
    have hpt : ∀ᵐ y ∂μ, ‖R y‖ ≤ ‖G k y - F y‖ + C * ‖E k y‖ := by
      filter_upwards [hGE k] with y hy
      by_cases hyS : y ∈ S
      · have h1 : R y = (G k y - s y * D y) - (G k y - F y) := by
          rw [hRdef, Set.indicator_of_mem hyS]
          ring
        have h2 := norm_sub_le (G k y - s y * D y) (G k y - F y)
        have h3 := hy hyS
        rw [h1]
        linarith
      · rw [hRdef, Set.indicator_of_notMem hyS, norm_zero]
        exact add_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    have hsplit : eLpNorm (fun y => ‖G k y - F y‖ + C * ‖E k y‖) 2 μ ≤
        eLpNorm (fun y => ‖G k y - F y‖) 2 μ + eLpNorm (fun y => C * ‖E k y‖) 2 μ :=
      eLpNorm_add_le (f := fun y => ‖G k y - F y‖) (g := fun y => C * ‖E k y‖) (by norm_num)
    have hnorm : eLpNorm (fun y => ‖G k y - F y‖) 2 μ = eLpNorm (fun y => G k y - F y) 2 μ :=
      eLpNorm_norm _ (hGm k)
    have hscale : eLpNorm (fun y => C * ‖E k y‖) 2 μ = ‖C‖ₑ * eLpNorm (E k) 2 μ := by
      have hfun : (fun y => C * ‖E k y‖) = C • (fun y => ‖E k y‖) := by
        ext y
        simp [smul_eq_mul]
      rw [hfun, eLpNorm_const_smul, eLpNorm_norm _ (hEm k)]
    calc eLpNorm R 2 μ ≤ eLpNorm (fun y => ‖G k y - F y‖ + C * ‖E k y‖) 2 μ :=
          eLpNorm_mono_ae_real hRm hpt
      _ ≤ _ := hsplit
      _ = _ := by rw [hnorm, hscale]
  have hlim : Tendsto (fun k => eLpNorm (fun y => G k y - F y) 2 μ +
      ‖C‖ₑ * eLpNorm (E k) 2 μ) atTop (𝓝 0) := by
    have hE' : Tendsto (fun k => ‖C‖ₑ * eLpNorm (E k) 2 μ) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul hE (a := ‖C‖ₑ) (Or.inr enorm_ne_top)
      simpa using this
    simpa using hG.add hE'
  have hR0 : eLpNorm R 2 μ = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) zero_le
  have hR_ae : R =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff (by norm_num)).mp hR0
  filter_upwards [hR_ae] with y hy hyS
  have h0 : R y = 0 := hy
  rw [hRdef, Set.indicator_of_mem hyS] at h0
  exact sub_eq_zero.mp h0

/-- The pointwise difference of two differences is controlled by the sum of the two
`L²` distances. -/
theorem eLpNorm_sub_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g h k : Ω → ℝ} (hf : AEStronglyMeasurable (fun y => f y - g y) μ)
    (hh : AEStronglyMeasurable (fun y => h y - k y) μ) :
    eLpNorm (fun y => (f y - g y) - (h y - k y)) 2 μ ≤
      eLpNorm (fun y => f y - g y) 2 μ + eLpNorm (fun y => h y - k y) 2 μ := by
  calc eLpNorm (fun y => (f y - g y) - (h y - k y)) 2 μ ≤
        eLpNorm (fun y => ‖f y - g y‖ + ‖h y - k y‖) 2 μ := by
        refine eLpNorm_mono_ae_real ?_ (Filter.Eventually.of_forall fun y => norm_sub_le _ _)
        exact hf.sub hh
    _ ≤ eLpNorm (fun y => ‖f y - g y‖) 2 μ + eLpNorm (fun y => ‖h y - k y‖) 2 μ :=
        eLpNorm_add_le (f := fun y => ‖f y - g y‖) (g := fun y => ‖h y - k y‖) (by norm_num)
    _ = _ := by rw [eLpNorm_norm _ hf, eLpNorm_norm _ hh]

/-- The energy identity along an approximating sequence. If `G k` agrees almost everywhere with
`s (U_j k - U_i k)`, the values `V k` agree with `U k` almost everywhere, and `G k → F`, `V k → V_0`
in `L²`, then `F = s (V_{0,j} - V_{0,i})` almost everywhere. -/
theorem ae_eq_mul_diff_of_eLpNorm_tendsto {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F Vj0 Vi0 s : Ω → ℝ} {G Vj Vi Uj Ui : ℕ → Ω → ℝ}
    (hs : Measurable s) (hs0 : ∀ y, 0 ≤ s y)
    (hF : AEStronglyMeasurable F μ) (hVj0 : AEStronglyMeasurable Vj0 μ)
    (hVi0 : AEStronglyMeasurable Vi0 μ)
    (hGm : ∀ k, AEStronglyMeasurable (G k) μ) (hVjm : ∀ k, AEStronglyMeasurable (Vj k) μ)
    (hVim : ∀ k, AEStronglyMeasurable (Vi k) μ)
    (hG : Tendsto (fun k => eLpNorm (fun y => G k y - F y) 2 μ) atTop (𝓝 0))
    (hVj : Tendsto (fun k => eLpNorm (fun y => Vj k y - Vj0 y) 2 μ) atTop (𝓝 0))
    (hVi : Tendsto (fun k => eLpNorm (fun y => Vi k y - Vi0 y) 2 μ) atTop (𝓝 0))
    (hGu : ∀ k, G k =ᵐ[μ] fun y => s y * (Uj k y - Ui k y))
    (hVju : ∀ k, Vj k =ᵐ[μ] Uj k) (hViu : ∀ k, Vi k =ᵐ[μ] Ui k) :
    ∀ᵐ y ∂μ, F y = s y * (Vj0 y - Vi0 y) := by
  have hE : Tendsto (fun k => eLpNorm (fun y => (Vj k y - Vj0 y) - (Vi k y - Vi0 y)) 2 μ)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hVj.add hVi) (fun k => zero_le) (fun k => ?_)
    exact eLpNorm_sub_sub_le ((hVjm k).sub hVj0) ((hVim k).sub hVi0)
  have hD : AEStronglyMeasurable (fun y => Vj0 y - Vi0 y) μ := hVj0.sub hVi0
  have hall : ∀ n : ℕ, ∀ᵐ y ∂μ, y ∈ {y | s y ≤ n} → F y = s y * (Vj0 y - Vi0 y) := fun n =>
    ae_eq_mul_on_of_eLpNorm_tendsto (measurableSet_le hs measurable_const) hF hD hs
      (Nat.cast_nonneg n) hG hE
      (fun k => by
        filter_upwards [hGu k, hVju k, hViu k] with y hg hvj hvi hyS
        have heq : G k y - s y * (Vj0 y - Vi0 y) = s y * ((Vj k y - Vj0 y) - (Vi k y - Vi0 y)) := by
          rw [hg, hvj, hvi]
          ring
        rw [heq, norm_mul, Real.norm_of_nonneg (hs0 y)]
        exact mul_le_mul_of_nonneg_right hyS (norm_nonneg _))
      (fun k => ((hGm k).sub hF)) (fun k => (((hVjm k).sub hVj0).sub ((hVim k).sub hVi0)))
  filter_upwards [ae_all_iff.mpr hall] with y hy
  obtain ⟨n, hn⟩ := exists_nat_ge (s y)
  exact hy n hn

end Riesz1.WeightedSobolev

end
