/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.AssemblyDistance
public import Riesz1.CLT.NondegeneracyRegularized
public import Riesz1.CLT.NondegeneracyMacroscopic
public import Riesz1.CLT.NondegeneracyStatistic
public import Riesz1.CLT.NondegeneracyZero

/-!
# Case analysis of the central limit theorem assembly

The bounded-Lipschitz bound of `Riesz1/CLT/AssemblyDistance.lean` needs the nondegeneracy of the
regularized profile. This file splits the profiles into two cases:

* **nondegenerate**: a compact profile with nonzero zero extension, or a noncompact profile that
  is not constant. Then `clt_nondegeneracy_compact` or `clt_nondegeneracy_macroscopic` bounds the
  regularized variance below for large `Nℓ_N`.
* **degenerate**: a compact profile with zero zero-extension, or a constant noncompact profile.
  Then every normalized statistic vanishes almost surely and every variance is zero, so the
  distance to the (degenerate) Gaussian is zero.

For a noncompact profile every admissible scale sequence is the macroscopic one `ℓ_N = 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace Riesz1.Internal

/-- A mollifier exists. This is the bump of `exists_isMollifier`, stated here so
that the assembly does not import another module. -/
theorem assembly_exists_isMollifier : ∃ ρ : ℝ → ℝ, IsMollifier ρ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.contDiff_normed, b.nonneg_normed,
    b.normed_neg, ?_, b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro x hx
  have hx' : |x| ≤ 1 / 4 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, b] using hx
  constructor <;> linarith [le_abs_self x, neg_le_abs x]

/-- The noncompact admissible scales are macroscopic: `ℓ_N = 1` for every particle number. -/
lemma admissible_macro_of_not_compact {P : Parameters} {p : Profile} {α : ℝ} {d : TestData}
    {ell : Scales} (hadm : Admissible P p ell α d) (hnc : ¬CompactProfile p) :
    (∀ N, (ell N).val = 1) ∧
      PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
      TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1 := by
  rcases hadm.2.2.2.2.2.2 with hmac | hcomp
  · exact hmac
  · exact (hnc hcomp.1).elim

/-- **Nondegenerate case.** If the profile is nondegenerate, the regularized variance is bounded
below by a positive constant for every admissible scale sequence once `Nℓ_N` is large. -/
theorem assembly_nondegenerate_profile (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (hnd : (CompactProfile p ∧ ¬ zeroExtension p =ᵐ[volume] fun _ => 0) ∨
      (¬CompactProfile p ∧ ¬ ∃ c : ℝ, p.val =ᵐ[volume] fun _ => c)) :
    ∃ c K₁ : ℝ, 0 < c ∧ ∀ ell : Scales, Admissible P p ell α d → ∀ N : ℕ+,
      K₁ ≤ (N : ℝ) * (ell N).val →
      cltVariance P (ell N)
          ⟨(fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
            cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩ < ⊤ ∧
        c ≤ Real.sqrt (cltVariance P (ell N)
          ⟨(fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
            cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩).toReal := by
  rcases hnd with ⟨hp, hz⟩ | ⟨hnc, hp⟩
  · -- Compact nondegenerate profile: the full compact assertion of the nondegeneracy lemma.
    obtain ⟨c, C, K₀, hc, -, -, hcomp⟩ := clt_nondegeneracy_compact P p hp α d hz ρ hρ
    refine ⟨c, K₀, hc, fun ell hadm N hN => ?_⟩
    have h := hcomp ell hadm N hN
    dsimp only at h
    exact ⟨h.1, h.2.1⟩
  · -- Noncompact nonconstant profile: only the macroscopic scale is admissible.
    by_cases hex : ∃ ell₀ : Scales, Admissible P p ell₀ α d
    · obtain ⟨ell₀, h₀⟩ := hex
      obtain ⟨hmac₀, hprim₀, hreg₀⟩ := admissible_macro_of_not_compact h₀ hnc
      obtain ⟨cm, Cm, Km, hcm, -, -, hmacro⟩ := clt_nondegeneracy_macroscopic P p d.1 d.2.1
        d.2.2.2.1 d.2.2.2.2 α d.2.2.1 h₀.2.2.1 h₀.2.2.2.2.1.le h₀.2.2.2.2.2.1.le h₀.1 h₀.2.1
        hprim₀ hreg₀ hp ρ hρ
      refine ⟨cm, Km, hcm, fun ell hadm N hN => ?_⟩
      obtain ⟨hmac, -, -⟩ := admissible_macro_of_not_compact hadm hnc
      have ha : ell N = ⟨1, by norm_num⟩ := Subtype.ext (hmac N)
      have hmacN := hmacro N (by
        have h1 : (ell N).val = 1 := hmac N
        rw [h1, mul_one] at hN
        exact hN)
      have key := nondegeneracy_compact_unit_variance P p (ell N) (hmac N) hρ
        (cltDelta_pos P N (ell N))
      rw [key, ha]
      dsimp only at hmacN ⊢
      exact ⟨hmacN.1, hmacN.2.1⟩
    · -- No admissible scale: the statement is vacuous.
      exact ⟨1, 1, one_pos, fun ell hadm => (hex ⟨ell, hadm⟩).elim⟩

/-- **Degenerate case.** If the profile is degenerate, every normalized statistic vanishes almost
surely and every circle variance is zero. -/
theorem assembly_degenerate_profile (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (hdeg : (CompactProfile p ∧ zeroExtension p =ᵐ[volume] fun _ => 0) ∨
      (¬CompactProfile p ∧ ∃ c : ℝ, p.val =ᵐ[volume] fun _ => c))
    (ell : Scales) (hadm : Admissible P p ell α d) (N : ℕ+) :
    (normalizedStatistic P p ell N =ᵐ[gibbsMeasure P N] fun _ => 0) ∧
      circleVariance P p (ell N) = 0 := by
  rcases hdeg with ⟨-, hz⟩ | ⟨hnc, c, hc⟩
  · -- Compact zero profile: every testAtScale vanishes almost everywhere.
    have ht := testAtScale_ae_zero_of_zeroExtension p hz (ell N)
    refine ⟨?_, ?_⟩
    · filter_upwards [fluctuation_ae_zero_of_ae_const P N
        ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩ ht] with X hX
      simp only [normalizedStatistic, hX, mul_zero]
    · have hS : circleSobolevSq ((1 - P.val.2) / 2)
          ⟨(fun x => (testAtScale p (ell N) x : ℂ)), testAtScaleL2 p (ell N)⟩ = 0 :=
        (circleSobolevSq_eq_zero_iff _ _).mpr ⟨0, by
          filter_upwards [ht] with x hx
          simp [hx]⟩
      rw [circleVariance_eq_cltVariance]
      unfold cltVariance
      rw [hS, mul_zero]
  · -- Constant noncompact profile: only the macroscopic scale is admissible.
    have hmac := (admissible_macro_of_not_compact hadm hnc).1
    have hz0 : circleVariance P p ⟨1, by norm_num⟩ = 0 :=
      (clt_nondegeneracy_macroscopic_zero P p).mpr ⟨c, hc⟩
    have ha : ell N = ⟨1, by norm_num⟩ := Subtype.ext (hmac N)
    refine ⟨clt_nondegeneracy_macroscopic_statistic P p hz0 ell hmac N, ?_⟩
    rw [ha]
    exact hz0

/-- **The bounded-Lipschitz bound for every profile.** For `α < s/2`, every `eps > 0` and every
admissible scale sequence, the law of the normalized statistic is within the bounded-Lipschitz
distance `C (Nℓ_N)^{eps + max((s-1)/2, -r)}` of its Gaussian comparison, with `C` independent of
the scale sequence and of `N`. The degenerate profiles give distance zero. -/
theorem assembly_bl_profile (hPL : External.PrekopaLeindler)
    (hErr1 : AssemblyErrorOneConclusion) (hErr2 : AssemblyErrorTwoConclusion)
    (hQVU : QuantitativeVarianceUniformConclusion) (P : Parameters) (p : Profile) (α : ℝ)
    (d : TestData) (hα : α < P.val.2 / 2) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d → ∀ N : ℕ+,
      1 ≤ (N : ℝ) * (ell N).val →
      ∃ law : ProbabilityMeasure ℝ,
        (law : Measure ℝ) = (gibbsMeasure P N).map (normalizedStatistic P p ell N) ∧
        blDistance law ⟨normalLaw (circleVariance P p (ell N)).toNNReal,
          by unfold normalLaw; infer_instance⟩ ≤
          ENNReal.ofReal (C * ((N : ℝ) * (ell N).val) ^
            (eps + max ((P.val.2 - 1) / 2) (-((2 - P.val.2) * (P.val.2 - 2 * α) /
              (2 * (4 + P.val.2)))))) := by
  obtain ⟨ρ, hρ⟩ := assembly_exists_isMollifier
  by_cases hdeg : (CompactProfile p ∧ zeroExtension p =ᵐ[volume] fun _ => 0) ∨
      (¬CompactProfile p ∧ ∃ c : ℝ, p.val =ᵐ[volume] fun _ => c)
  · -- Degenerate: the distance is zero, so any positive constant works.
    refine ⟨1, one_pos, fun ell hadm N _ => ?_⟩
    obtain ⟨hF0, hv0⟩ := assembly_degenerate_profile P p α d hdeg ell hadm N
    have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
    refine ⟨⟨(gibbsMeasure P N).map (normalizedStatistic P p ell N), inferInstance⟩, rfl, ?_⟩
    have hz := blDistance_map_eq_zero_of_ae (gibbsMeasure P N) hF0
      ((circleVariance P p (ell N)).toNNReal) (by rw [hv0]; rfl)
    have hz' : blDistance ⟨(gibbsMeasure P N).map (normalizedStatistic P p ell N), inferInstance⟩
        ⟨normalLaw (circleVariance P p (ell N)).toNNReal, by unfold normalLaw; infer_instance⟩ = 0 := hz
    rw [hz']
    exact zero_le
  · -- Nondegenerate: the regularized variance is bounded below for large `Nℓ_N`.
    have hnondeg : (CompactProfile p ∧ ¬ zeroExtension p =ᵐ[volume] fun _ => 0) ∨
        (¬CompactProfile p ∧ ¬ ∃ c : ℝ, p.val =ᵐ[volume] fun _ => c) := by
      by_cases hc : CompactProfile p
      · exact Or.inl ⟨hc, fun hz => hdeg (Or.inl ⟨hc, hz⟩)⟩
      · exact Or.inr ⟨hc, fun hex => hdeg (Or.inr ⟨hc, hex⟩)⟩
    obtain ⟨c, K₁, hc, hnd⟩ := assembly_nondegenerate_profile P p α d hρ hnondeg
    exact assembly_bl_bound_of_nondegenerate hPL hErr1 hErr2 hQVU P p α d hα hρ eps heps c K₁ hc hnd

end Riesz1.Internal

end
end
