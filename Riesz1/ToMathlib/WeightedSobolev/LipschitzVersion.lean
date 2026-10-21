/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.LipschitzVersionMeanValue

/-!
# Lipschitz representative of a Sobolev function with bounded gradient

Let `T` be an open convex set in a finite-dimensional real inner product space `E`. Let
`φ k` be `C¹` on an open set containing `T`, and suppose that `φ k → F` and
`∇(φ k) → G` in `L¹` on every compact subset of `T`, with `‖G‖ ≤ K` almost everywhere on `T`.
Then `F` agrees almost everywhere on `T` with a `K`-Lipschitz function on `E`.

The proof has three steps. Ball averages of `φ k` satisfy the mean value estimate of
`LipschitzVersionMeanValue.lean`, which passes to the limit in `k` for each fixed radius. At
Lebesgue points of `F` the ball averages converge to `F`, so `F` is `K`-Lipschitz on the set of
Lebesgue points in `T`. Finally that Lipschitz function extends to all of `E`.

The extension from the Lebesgue points to all of `E` is `LipschitzOnWith.extend_real`, so no
density argument is needed.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Lebesgue points on a relatively compact open set.** If `U` is open with compact closure
inside `T` and `F` is integrable on that closure, then almost every point of `U` is a Lebesgue
point of `F` in the sense that its ball averages converge to `F`. -/
theorem ae_tendsto_ballAvg_of_isOpen {T U : Set E} {F : E → ℝ}
    (hFloc : ∀ K ⊆ T, IsCompact K → IntegrableOn F K volume) (hU : IsOpen U)
    (hUc : IsCompact (closure U)) (hUT : closure U ⊆ T) :
    ∀ᵐ y ∂(volume : Measure E), y ∈ U →
      Tendsto (fun r => ballAvg F y r) (𝓝[>] (0 : ℝ)) (𝓝 (F y)) := by
  have hint : IntegrableOn F U volume :=
    (hFloc (closure U) hUT hUc).mono_set subset_closure
  have hF₀ : Integrable (U.indicator F) volume :=
    (integrable_indicator_iff hU.measurableSet).mpr hint
  filter_upwards [ae_tendsto_ballAvg hF₀.locallyIntegrable] with y hy hyU
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ballAvg (U.indicator F) y r = ballAvg F y r := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hyU
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    unfold ballAvg
    congr 1
    refine setIntegral_congr_fun measurableSet_closedBall (fun q hq => ?_)
    have hqU : y + q ∈ U := hball (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa [mem_closedBall, dist_eq_norm] using hq) hr.2)
    simp only [indicator_of_mem hqU]
  rw [indicator_of_mem hyU] at hy
  exact hy.congr' (hev.mono fun r hr => hr)

/-- **Lipschitz estimate for ball averages of the limit.** For two points of `T` whose segment
has an `r`-neighbourhood inside `T`, the ball averages of `F` at the two points differ by at most
`K` times their distance. -/
theorem abs_ballAvg_sub_le_of_segment {T : Set E} {K : ℝ}
    {F : E → ℝ} {G : E → E} {φ : ℕ → E → ℝ}
    (hφ : ∀ k, ∃ W : Set E, IsOpen W ∧ T ⊆ W ∧ ContDiffOn ℝ 1 (φ k) W)
    (hFloc : ∀ K ⊆ T, IsCompact K → IntegrableOn F K volume)
    (hGloc : ∀ K ⊆ T, IsCompact K → IntegrableOn G K volume)
    (hF1 : ∀ K ⊆ T, IsCompact K → Tendsto (fun k => ∫ x in K, |φ k x - F x|) atTop (𝓝 0))
    (hG1 : ∀ K ⊆ T, IsCompact K → Tendsto (fun k => ∫ x in K, ‖gradient (φ k) x - G x‖)
      atTop (𝓝 0))
    (hG : ∀ᵐ x ∂(volume : Measure E), x ∈ T → ‖G x‖ ≤ K)
    {x y : E} {r : ℝ} (hr : 0 < r)
    (hrT : cthickening r (segment ℝ x y) ⊆ T) :
    |ballAvg F y r - ballAvg F x r| ≤ K * ‖y - x‖ := by
  set S : Set E := segment ℝ x y with hSdef
  have hSc : IsCompact S := by
    rw [hSdef, segment_eq_image']
    exact isCompact_Icc.image (by fun_prop)
  have hKc : IsCompact (cthickening r S) := hSc.cthickening
  have hKcT : cthickening r S ⊆ T := hrT
  have hpt : ∀ s ∈ Icc (0 : ℝ) 1, closedBall (x + s • (y - x)) r ⊆ cthickening r S := by
    intro s hs
    have hmem : x + s • (y - x) ∈ S := by
      rw [hSdef, segment_eq_image']
      exact ⟨s, hs, rfl⟩
    exact (closedBall_subset_cthickening hmem r)
  -- The mean value estimate for each approximant, passed to the limit `k → ∞`.
  have hest : ∀ k, |ballAvg (φ k) y r - ballAvg (φ k) x r| ≤
      ‖y - x‖ * (K + (volume (closedBall (0 : E) r)).toReal⁻¹ *
        ∫ p in cthickening r S, ‖gradient (φ k) p - G p‖) := by
    intro k
    obtain ⟨W, hW, hTW, hφW⟩ := hφ k
    have hmv := abs_ballAvg_add_sub_le_gradient hW hφW hKc (fun p hp => hTW (hKcT hp))
      (hGloc _ hKcT hKc)
      (by filter_upwards [hG] with p hp hpK using hp (hKcT hpK)) hr
      (fun s hs => hpt s hs)
    rw [add_sub_cancel] at hmv
    simpa using hmv
  -- Convergence of the averages of `φ k` to those of `F` on any ball inside `cthickening r S`.
  have hconv : ∀ z : E, closedBall z r ⊆ cthickening r S →
      Tendsto (fun k => ballAvg (φ k) z r) atTop (𝓝 (ballAvg F z r)) := by
    intro z hz
    have hbd : ∀ k, |ballAvg (φ k) z r - ballAvg F z r| ≤
        (volume (closedBall (0 : E) r)).toReal⁻¹ * ∫ p in cthickening r S, |φ k p - F p| := by
      intro k
      obtain ⟨W, _, hTW, hφW⟩ := hφ k
      have hφint : IntegrableOn (φ k) (cthickening r S) volume :=
        (hφW.continuousOn.mono (hKcT.trans hTW)).integrableOn_compact hKc
      exact abs_ballAvg_sub_le hz hφint (hFloc _ hKcT hKc)
    have h0 : Tendsto (fun k => ballAvg (φ k) z r - ballAvg F z r) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k => (volume (closedBall (0 : E) r)).toReal⁻¹ *
        ∫ p in cthickening r S, |φ k p - F p|) (fun k => ?_) ?_
      · simpa [Real.norm_eq_abs] using hbd k
      · simpa using (hF1 _ hKcT hKc).const_mul ((volume (closedBall (0 : E) r)).toReal⁻¹)
    exact tendsto_sub_nhds_zero_iff.mp h0
  have hx0 : closedBall x r ⊆ cthickening r S := by simpa using hpt 0 ⟨le_rfl, zero_le_one⟩
  have hy1 : closedBall y r ⊆ cthickening r S := by simpa using hpt 1 ⟨zero_le_one, le_rfl⟩
  have hlim : Tendsto (fun k => |ballAvg (φ k) y r - ballAvg (φ k) x r|) atTop
      (𝓝 |ballAvg F y r - ballAvg F x r|) :=
    ((hconv y hy1).sub (hconv x hx0)).abs
  have hub : Tendsto (fun k => ‖y - x‖ * (K + (volume (closedBall (0 : E) r)).toReal⁻¹ *
      ∫ p in cthickening r S, ‖gradient (φ k) p - G p‖)) atTop
      (𝓝 (‖y - x‖ * (K + (volume (closedBall (0 : E) r)).toReal⁻¹ * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul (hG1 _ hKcT hKc)))
  have hfin := le_of_tendsto_of_tendsto hlim hub (Eventually.of_forall hest)
  rw [mul_zero, add_zero, mul_comm] at hfin
  exact hfin

/-- **Lipschitz representative.** Let `T` be an open convex set. Suppose that the `C¹` functions
`φ k` are defined on open sets containing `T`, and that `φ k → F` and `∇(φ k) → G` in `L¹` on every
compact subset of `T`, with `‖G‖ ≤ K` almost everywhere on `T`. Then there is a `K`-Lipschitz
function `g` on `E` with `g = F` almost everywhere on `T`. -/
theorem exists_lipschitzWith_ae_eq {T : Set E} (hT : IsOpen T) (hTc : Convex ℝ T) {K : NNReal}
    {F : E → ℝ} {G : E → E} {φ : ℕ → E → ℝ}
    (hφ : ∀ k, ∃ W : Set E, IsOpen W ∧ T ⊆ W ∧ ContDiffOn ℝ 1 (φ k) W)
    (hFloc : ∀ K ⊆ T, IsCompact K → IntegrableOn F K volume)
    (hGloc : ∀ K ⊆ T, IsCompact K → IntegrableOn G K volume)
    (hF1 : ∀ K ⊆ T, IsCompact K → Tendsto (fun k => ∫ x in K, |φ k x - F x|) atTop (𝓝 0))
    (hG1 : ∀ K ⊆ T, IsCompact K → Tendsto (fun k => ∫ x in K, ‖gradient (φ k) x - G x‖)
      atTop (𝓝 0))
    (hG : ∀ᵐ x ∂(volume : Measure E), x ∈ T → ‖G x‖ ≤ K) :
    ∃ g : E → ℝ, LipschitzWith K g ∧ ∀ᵐ x ∂(volume : Measure E), x ∈ T → g x = F x := by
  -- Step 1: almost every point of `T` is a Lebesgue point of `F`.
  have hLeb : ∀ᵐ x ∂(volume : Measure E), x ∈ T →
      Tendsto (fun r => ballAvg F x r) (𝓝[>] (0 : ℝ)) (𝓝 (F x)) := by
    have hloc : ∀ y ∈ T, ∃ ε : ℝ, 0 < ε ∧ closedBall y ε ⊆ T := by
      intro y hy
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT y hy
      exact ⟨ε / 2, by linarith, (closedBall_subset_ball (by linarith)).trans hball⟩
    choose! ε hεpos hεT using hloc
    obtain ⟨t, htT, htc, htcover⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := T)
      (f := fun y => ball y (ε y))
      (fun y hy => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y (hεpos y hy)))
    have : Countable t := htc.to_subtype
    have hpiece : ∀ y : t, ∀ᵐ z ∂(volume : Measure E), z ∈ ball (y : E) (ε y) →
        Tendsto (fun r => ballAvg F z r) (𝓝[>] (0 : ℝ)) (𝓝 (F z)) := by
      intro y
      have hyT : (y : E) ∈ T := htT y.2
      exact ae_tendsto_ballAvg_of_isOpen hFloc isOpen_ball
        ((isCompact_closedBall _ _).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall)
        (closure_ball_subset_closedBall.trans (hεT _ hyT))
    have hall := ae_all_iff.mpr hpiece
    filter_upwards [hall] with z hz hzT
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (htcover hzT)
    exact hz ⟨y, hy⟩ hzy
  -- Step 2: `F` is `K`-Lipschitz on the set of Lebesgue points in `T`.
  set GS : Set E := {x | x ∈ T ∧ Tendsto (fun r => ballAvg F x r) (𝓝[>] (0 : ℝ)) (𝓝 (F x))}
    with hGS
  have hLip : LipschitzOnWith K F GS := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.dist_eq, dist_eq_norm]
    obtain ⟨hxT, hxL⟩ := hx
    obtain ⟨hyT, hyL⟩ := hy
    have hSc : IsCompact (segment ℝ x y) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    obtain ⟨δ, hδ, hδT⟩ := hSc.exists_thickening_subset_open hT (hTc.segment_subset hxT hyT)
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), |ballAvg F y r - ballAvg F x r| ≤ K * ‖y - x‖ := by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
      exact abs_ballAvg_sub_le_of_segment hφ hFloc hGloc hF1 hG1 hG hr.1
        ((cthickening_subset_thickening' hδ hr.2 _).trans hδT)
    have hlim := (hyL.sub hxL).abs
    have hfin := le_of_tendsto hlim hbound
    rw [abs_sub_comm, norm_sub_rev]
    exact hfin
  -- Step 3: extend from the Lebesgue points to all of `E`, with the same constant.
  obtain ⟨g, hgL, hgeq⟩ := hLip.extend_real
  refine ⟨g, hgL, ?_⟩
  filter_upwards [hLeb] with x hx hxT
  exact (hgeq ⟨hxT, hx hxT⟩).symm

end Riesz1.WeightedSobolev

end

end
