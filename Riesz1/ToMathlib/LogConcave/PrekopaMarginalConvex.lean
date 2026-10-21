/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.PrekopaContinuity
public import Riesz1.ToMathlib.LogConcave.MarginalConcave
public import Riesz1.Frozen.External.PrekopaLeindler

/-!
# Convexity of the negative logarithm of a fiber integral on a bounded open convex set

Let `Q` be a bounded open convex set in `E × EuclideanSpace ℝ (Fin n)` with `0 < n`, and let `V`
be convex on `Q`. The function `z ↦ -log ∫ e^{-V(z, y)} dy` over the fiber of `Q` is convex on
the projection of `Q`. The proof restricts to each segment `t ↦ x + t (y - x)`. On the segment,
the fiber integral becomes the marginal of a jointly log-concave function of `(t, y)`, and the
one-dimensional marginal theorem `Riesz1.marginal_concaveOn_log_of_continuous` applies.
The sole external input is the midpoint Prékopa–Leindler inequality
`External.PrekopaLeindler`, which is taken as a hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology Filter

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The projection of a convex set is convex. -/
theorem convex_fst_image_prod {n : ℕ} {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    (hQc : Convex ℝ Q) : Convex ℝ (Prod.fst '' Q) := by
  have := hQc.linear_image (LinearMap.fst ℝ E (EuclideanSpace ℝ (Fin n)))
  simpa using this

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- Every point of the projection of `Q` has a point of `Q` above it. -/
theorem exists_fiber_of_mem_fst_image {n : ℕ} {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    {z : E} (hz : z ∈ Prod.fst '' Q) : ∃ y, (z, y) ∈ Q := by
  obtain ⟨p, hp, rfl⟩ := hz
  exact ⟨p.2, by simpa using hp⟩

/-- The convexity of the negative logarithm of a fiber integral on a bounded open convex set. -/
theorem convexOn_neg_log_marginal_exp_of_bounded (hPL : External.PrekopaLeindler) {n : ℕ}
    (hn : 0 < n) {Q : Set (E × EuclideanSpace ℝ (Fin n))}
    {V : E × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hQc : Convex ℝ Q) (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V) :
    ConvexOn ℝ (Prod.fst '' Q)
      (fun z => -Real.log (∫ y, Q.indicator (fun p => Real.exp (-V p)) (z, y))) := by
  have hPconv : Convex ℝ (Prod.fst '' Q) := convex_fst_image_prod hQc
  have hex := fun z (hz : z ∈ Prod.fst '' Q) => exists_fiber_of_mem_fst_image hz
  obtain ⟨c, hc⟩ := exists_lower_bound_of_convexOn hQo hQb hV
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall
    (0 : E × EuclideanSpace ℝ (Fin n))).mp hQb
  have hFmeas := measurable_exp_indicator (E := E) hQo hV
  have hFIcc : ∀ p, Q.indicator (fun q => Real.exp (-V q)) p ∈ Icc (0 : ℝ) (Real.exp (-c)) := by
    intro p
    by_cases hp : p ∈ Q
    · rw [indicator_of_mem hp]
      exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (neg_le_neg (hc p hp))⟩
    · rw [indicator_of_notMem hp]
      exact ⟨le_rfl, (Real.exp_pos _).le⟩
  have hJcont := continuousOn_marginal_exp_indicator (E := E) hQo hQc hQb hV
  refine ⟨hPconv, ?_⟩
  intro x hx y hy a b ha hb hab
  dsimp only
  by_cases hxy : x = y
  · subst hxy
    rw [← add_smul, hab, one_smul]
    have hsum : a * -Real.log (∫ w, Q.indicator (fun p => Real.exp (-V p)) (x, w)) +
        b * -Real.log (∫ w, Q.indicator (fun p => Real.exp (-V p)) (x, w)) =
        -Real.log (∫ w, Q.indicator (fun p => Real.exp (-V p)) (x, w)) := by
      rw [← add_mul, hab, one_mul]
    rw [smul_eq_mul, smul_eq_mul]
    linarith
  · -- Nontrivial segment: parametrize `t ↦ x + t • (y - x)` and lift to the joint variable.
    have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (fun h => hxy h.symm))
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ × EuclideanSpace ℝ (Fin n) → E × EuclideanSpace ℝ (Fin n),
        ∀ p, ψ p = (x + p.1 • (y - x), p.2) := ⟨fun p => (x + p.1 • (y - x), p.2), fun p => rfl⟩
    obtain ⟨G, hG⟩ : ∃ G : ℝ × EuclideanSpace ℝ (Fin n) → ℝ,
        ∀ p, G p = Q.indicator (fun q => Real.exp (-V q)) (ψ p) :=
      ⟨fun p => Q.indicator (fun q => Real.exp (-V q)) (ψ p), fun p => rfl⟩
    -- The affine parametrization of the segment in the joint variable.
    have hψmeas : Measurable ψ := by
      have : ψ = fun p => (x + p.1 • (y - x), p.2) := funext hψ
      rw [this]
      fun_prop
    have hGmeas : Measurable G := by
      have : G = (Q.indicator fun q => Real.exp (-V q)) ∘ ψ := funext fun p => hG p
      rw [this]
      exact hFmeas.comp hψmeas
    have hψcomb : ∀ (p1 p2 : ℝ × EuclideanSpace ℝ (Fin n)) (a' b' : ℝ), a' + b' = 1 →
        ψ (a' • p1 + b' • p2) = a' • ψ p1 + b' • ψ p2 := by
      intro p1 p2 a' b' hab'
      obtain rfl : b' = 1 - a' := by linarith
      rw [hψ, hψ, hψ]
      ext
      · simp only [Prod.smul_fst, Prod.fst_add]
        module
      · simp only [Prod.smul_snd, Prod.snd_add]
    have hψQ : ∀ p, ψ p ∈ Q ↔ p ∈ Function.support G := by
      intro p
      rw [Function.mem_support, hG]
      by_cases h : ψ p ∈ Q
      · simp [h]
      · simp [h]
    -- The support of `G` is the preimage of `Q` under `ψ`, which is convex.
    have hsuppconv : Convex ℝ (Function.support G) := by
      intro p1 hp1 p2 hp2 a' b' ha' hb' hab'
      rw [← hψQ] at hp1 hp2 ⊢
      rw [hψcomb p1 p2 a' b' hab']
      exact hQc hp1 hp2 ha' hb' hab'
    have hlog : ConcaveOn ℝ (Function.support G) (fun p => Real.log (G p)) := by
      refine ⟨hsuppconv, fun p1 hp1 p2 hp2 a' b' ha' hb' hab' => ?_⟩
      have hp1' := (hψQ p1).2 hp1
      have hp2' := (hψQ p2).2 hp2
      have hmix := hsuppconv hp1 hp2 ha' hb' hab'
      have hmix' := (hψQ _).2 hmix
      have hlogG : ∀ p, ψ p ∈ Q → Real.log (G p) = -V (ψ p) := by
        intro p hp
        rw [hG, indicator_of_mem hp, Real.log_exp]
      simp only [smul_eq_mul]
      rw [hlogG p1 hp1', hlogG p2 hp2', hlogG _ hmix', hψcomb p1 p2 a' b' hab']
      have hVc := hV.2 hp1' hp2' ha' hb' hab'
      simp only [smul_eq_mul] at hVc
      linarith
    -- Restrict to the segment and apply the one-dimensional marginal theorem.
    obtain ⟨s, hs⟩ : ∃ s : Set ℝ, s = {t : ℝ | x + t • (y - x) ∈ Prod.fst '' Q} :=
      ⟨_, rfl⟩
    have hsconv : Convex ℝ s := by
      intro t1 ht1 t2 ht2 a' b' ha' hb' hab'
      rw [hs] at ht1 ht2 ⊢
      obtain rfl : b' = 1 - a' := by linarith
      have hcomb : x + (a' * t1 + (1 - a') * t2) • (y - x) =
          a' • (x + t1 • (y - x)) + (1 - a') • (x + t2 • (y - x)) := by
        module
      show x + (a' • t1 + (1 - a') • t2) • (y - x) ∈ Prod.fst '' Q
      rw [smul_eq_mul, smul_eq_mul]
      rw [hcomb]
      exact hPconv ht1 ht2 ha' hb' (by ring)
    have hline : ∀ t : ℝ, ∫ w, G (t, w) = ∫ w, Q.indicator (fun p => Real.exp (-V p))
        (x + t • (y - x), w) := by
      intro t
      congr 1
      ext w
      rw [hG, hψ]
    have hs0 : (0 : ℝ) ∈ s := by
      rw [hs]
      show x + (0 : ℝ) • (y - x) ∈ Prod.fst '' Q
      rw [zero_smul, add_zero]
      exact hx
    have hs1 : (1 : ℝ) ∈ s := by
      rw [hs]
      show x + (1 : ℝ) • (y - x) ∈ Prod.fst '' Q
      rw [one_smul, add_sub_cancel]
      exact hy
    -- Boundedness of the support of `G`, using the bound `R` on `Q`.
    have hGbdd : Bornology.IsBounded (Set.range G) := by
      refine (Metric.isBounded_Icc (0 : ℝ) (Real.exp (-c))).subset ?_
      rintro _ ⟨p, rfl⟩
      rw [hG]
      exact hFIcc _
    have hGsupp : Bornology.IsBounded (Function.support G) := by
      refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ × EuclideanSpace ℝ (Fin n))).2
        ⟨|(R + ‖x‖) / ‖y - x‖| + |R|, fun p hp => ?_⟩
      have hpQ : ψ p ∈ Q := (hψQ p).2 hp
      have hpR : ‖ψ p‖ ≤ R := by
        have := hR hpQ
        rwa [mem_closedBall_zero_iff] at this
      have hψ1 : (ψ p).1 = x + p.1 • (y - x) := by rw [hψ]
      have hψ2 : (ψ p).2 = p.2 := by rw [hψ]
      have hfst : ‖x + p.1 • (y - x)‖ ≤ R := by
        rw [← hψ1]
        exact (norm_fst_le _).trans hpR
      have hsnd : ‖p.2‖ ≤ R := by
        rw [← hψ2]
        exact (norm_snd_le _).trans hpR
      have hscale : ‖p.1 • (y - x)‖ ≤ R + ‖x‖ := by
        have e : p.1 • (y - x) = (x + p.1 • (y - x)) - x := by abel
        rw [e]
        exact (norm_sub_le _ _).trans (by linarith)
      have hp1 : |p.1| ≤ (R + ‖x‖) / ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs] at hscale
        rw [le_div_iff₀ hd]
        exact hscale
      rw [mem_closedBall_zero_iff, Prod.norm_def]
      apply max_le
      · rw [Real.norm_eq_abs]
        linarith [le_abs_self ((R + ‖x‖) / ‖y - x‖), abs_nonneg R]
      · linarith [le_abs_self R, abs_nonneg ((R + ‖x‖) / ‖y - x‖)]
    -- The one-dimensional marginal theorem gives concavity of the logarithm along the segment.
    have hGnonneg : ∀ p, 0 ≤ G p := fun p => by
      rw [hG]
      exact (hFIcc _).1
    have hcont : ContinuousOn (fun t => ∫ w, G (t, w)) s := by
      have hfun : (fun t => ∫ w, G (t, w)) = (fun z => ∫ w, Q.indicator
          (fun p => Real.exp (-V p)) (z, w)) ∘ (fun t : ℝ => x + t • (y - x)) := by
        funext t
        exact hline t
      rw [hfun]
      have hcts : Continuous fun t : ℝ => x + t • (y - x) := by fun_prop
      refine ContinuousOn.comp hJcont hcts.continuousOn ?_
      intro t ht
      rw [hs] at ht
      exact ht
    have hpos : ∀ t ∈ s, 0 < ∫ w, G (t, w) := by
      intro t ht
      rw [hline t]
      rw [hs] at ht
      exact marginal_exp_indicator_pos hQo hQb hV (hex _ ht)
    have hcl := marginal_concaveOn_log_of_continuous hPL n hn G hGmeas hGnonneg hGbdd hGsupp
      hlog s hsconv hpos hcont
    have h := hcl.2 hs0 hs1 ha hb hab
    have e0 : ∫ w, G (0, w) = ∫ w, Q.indicator (fun p => Real.exp (-V p)) (x, w) := by
      rw [hline 0, zero_smul, add_zero]
    have e1 : ∫ w, G (1, w) = ∫ w, Q.indicator (fun p => Real.exp (-V p)) (y, w) := by
      rw [hline 1, one_smul, add_sub_cancel]
    have e2 : x + b • (y - x) = a • x + b • y := by
      obtain rfl : a = 1 - b := by linarith
      module
    dsimp only at h
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at h
    rw [e0, e1, hline b, e2] at h
    rw [smul_eq_mul, smul_eq_mul, mul_neg, mul_neg]
    linarith

end Riesz1

end
end
