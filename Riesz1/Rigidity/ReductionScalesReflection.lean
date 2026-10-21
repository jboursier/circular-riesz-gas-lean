/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ReductionScalesGaps
public import Riesz1.Rigidity.GapLawReversal
public import Riesz1.Rigidity.GapLawSymmetry

/-!
# Mean zero of the multiscale increment under a symmetric constrained law

This is the mean assertion in the proof of Lemma 4.4, when the block of `G_m` is symmetric
about the particle `i` (`2 k_{m+1} < N`). The argument is a reflection: the gap family of a block
is invariant in law under reversal of its gap order (`map_gapFamily_block_reverse`), the forcing
potential is invariant under that reversal (`forcingFun_reflect`), and the increment is odd under
it (`gapCoefOf_reflect`). Hence the integral of the odd, reversal-invariant integrand vanishes, and
so does the constrained mean.

The main result is `integral_scaleIncrement_symmetric`.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### Gap families of a block -/

/-- Shift invariance of gap families: shifting every label of a family by an integer leaves its law
unchanged. -/
theorem map_gapFamily_add_int {ι : Type*} (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (k : ι → ℤ) (c : ℤ) :
    (gibbsMeasure P N).map (fun X i => gap X (k i + c)) =
      (gibbsMeasure P N).map (fun X i => gap X (k i)) := by
  refine Int.induction_on c ?_ ?_ ?_
  · simp
  · intro n ih
    have h : (gibbsMeasure P N).map (fun X i => gap X (k i + (n : ℤ) + 1)) =
        (gibbsMeasure P N).map (fun X i => gap X (k i + (n : ℤ))) :=
      map_gapFamily_add_one_gibbsMeasure P N hN (fun i => k i + (n : ℤ))
    have e : (fun (X : Configuration N) i => gap X (k i + ((n : ℤ) + 1))) =
        fun X i => gap X (k i + (n : ℤ) + 1) := by
      funext X i
      congr 1
      ring
    rw [e, h, ih]
  · intro n ih
    have h : (gibbsMeasure P N).map (fun X i => gap X (k i + (-(n : ℤ) - 1) + 1)) =
        (gibbsMeasure P N).map (fun X i => gap X (k i + (-(n : ℤ) - 1))) :=
      map_gapFamily_add_one_gibbsMeasure P N hN (fun i => k i + (-(n : ℤ) - 1))
    have e : (fun (X : Configuration N) i => gap X (k i + (-(n : ℤ) - 1) + 1)) =
        fun X i => gap X (k i + -(n : ℤ)) := by
      funext X i
      congr 1
      ring
    rw [e] at h
    rw [← h, ih]

/-- The gaps of the block `[i0, i0 + L]` as a family indexed by `Fin L`, `g_u = gap X (i0 + u)`. -/
noncomputable def blockFam (i0 : ℤ) (L : ℕ) (X : Configuration N) : Fin L → ℝ :=
  fun u => gap X (i0 + ((u : ℕ) : ℤ))

/-- The block gap family is measurable in the configuration. -/
theorem measurable_blockFam (i0 : ℤ) (L : ℕ) : Measurable (blockFam (N := N) i0 L) :=
  measurable_pi_iff.mpr fun _ => measurable_gap _

/-- Reversal of the block gap order leaves the law of the gap family unchanged: the family
`u ↦ gap X (i0 + (L - 1 - u))` has the same law as `u ↦ gap X (i0 + u)`. No symmetry of the block is
needed: reversal of the labels `j ↦ -j - 1` followed by an integer shift is the reversal of any
block. -/
theorem map_blockFam_rev (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i0 : ℤ) (L : ℕ) :
    (gibbsMeasure P N).map (fun X => fun u : Fin L => blockFam i0 L X (Fin.rev u)) =
      (gibbsMeasure P N).map (blockFam i0 L) := by
  have h : (gibbsMeasure P N).map (fun X (u : Fin L) => gap X (-(i0 + ((u : ℕ) : ℤ)) - 1)) =
      (gibbsMeasure P N).map (fun X (u : Fin L) => gap X (i0 + ((u : ℕ) : ℤ))) :=
    map_gapFamily_reverse_gibbsMeasure P N (fun u : Fin L => i0 + ((u : ℕ) : ℤ))
  have hs : (gibbsMeasure P N).map (fun X (u : Fin L) =>
      gap X ((i0 + (((Fin.rev u : Fin L) : ℕ) : ℤ)) + -(2 * i0 + (L : ℤ)))) =
      (gibbsMeasure P N).map (fun X (u : Fin L) => gap X (i0 + (((Fin.rev u : Fin L) : ℕ) : ℤ))) :=
    map_gapFamily_add_int P N hN (fun u : Fin L => i0 + (((Fin.rev u : Fin L) : ℕ) : ℤ))
      (-(2 * i0 + (L : ℤ)))
  have e1 : (fun (X : Configuration N) (u : Fin L) => gap X (-(i0 + ((u : ℕ) : ℤ)) - 1)) =
      fun X (u : Fin L) => gap X ((i0 + (((Fin.rev u : Fin L) : ℕ) : ℤ)) +
        -(2 * i0 + (L : ℤ))) := by
    funext X u
    congr 1
    have hu := u.isLt
    rw [Fin.val_rev]
    omega
  rw [e1, hs] at h
  exact h

/-! ### The integrand in block gap coordinates -/

/-- The gap sequence of a block extended by zero beyond its length. -/
noncomputable def extFin (L : ℕ) (g : Fin L → ℝ) : ℕ → ℝ :=
  fun u => if h : u < L then g ⟨u, h⟩ else 0

/-- The extension agrees with the gap sequence below `L`. -/
theorem extFin_apply_lt {L : ℕ} (g : Fin L → ℝ) {u : ℕ} (hu : u < L) :
    extFin L g u = g ⟨u, hu⟩ := by
  unfold extFin
  rw [dite_eq_left hu]

/-- The integrand of the mean: `(∑_u a_u g_u) exp(-β F_{I,R})` written in the block gaps. -/
noncomputable def reflIntegrand (P : Parameters) (θ : ℝ → ℝ) (L : ℕ) (R : ℝ) (a : Fin L → ℝ)
    (g : Fin L → ℝ) : ℝ :=
  (∑ u, a u * g u) * Real.exp (-P.val.1 * forcingFun θ L R (extFin L g))

/-- The integrand is measurable in the block gaps. -/
theorem measurable_reflIntegrand (P : Parameters) {θ : ℝ → ℝ} (hθ : Continuous θ) (L : ℕ) (R : ℝ)
    (a : Fin L → ℝ) : Measurable (reflIntegrand P θ L R a) := by
  have hext : ∀ u : ℕ, Measurable fun g : Fin L → ℝ => extFin L g u := by
    intro u
    by_cases h : u < L
    · have e : (fun g : Fin L → ℝ => extFin L g u) = fun g => g ⟨u, h⟩ := by
        funext g
        exact extFin_apply_lt g h
      rw [e]
      exact measurable_pi_apply _
    · have e : (fun g : Fin L → ℝ => extFin L g u) = fun _ => 0 := by
        funext g
        unfold extFin
        rw [dite_eq_right h]
      rw [e]
      exact measurable_const
  have hF : Measurable fun g : Fin L → ℝ => forcingFun θ L R (extFin L g) := by
    unfold forcingFun
    refine measurable_const.mul (Finset.measurable_sum _ fun p _ => ?_)
    refine Finset.measurable_sum _ fun q _ => ?_
    refine hθ.measurable.comp ?_
    refine Measurable.div_const ?_ R
    exact Finset.measurable_sum _ fun u _ => hext u
  unfold reflIntegrand
  exact Measurable.mul
    (Finset.measurable_sum _ fun u _ => measurable_const.mul (measurable_pi_apply _))
    (Real.measurable_exp.comp (measurable_const.mul hF))

/-- Reversal of the block gap order negates the integrand, when the coefficients are odd and the
forcing potential is reversal invariant. -/
theorem reflIntegrand_rev (P : Parameters) (θ : ℝ → ℝ) (L : ℕ) (R : ℝ) (a : Fin L → ℝ)
    (ha : ∀ u : Fin L, a (Fin.rev u) = -a u) (g : Fin L → ℝ) :
    reflIntegrand P θ L R a (fun u => g (Fin.rev u)) = -reflIntegrand P θ L R a g := by
  unfold reflIntegrand
  have hsum : ∑ u, a u * g (Fin.rev u) = -∑ u, a u * g u := by
    have h := Equiv.sum_comp Fin.revPerm (fun u => a (Fin.rev u) * g u)
    simp only [Fin.revPerm_apply, Fin.rev_rev] at h
    rw [h, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [ha u]
    ring
  have hexp : forcingFun θ L R (extFin L (fun u => g (Fin.rev u))) =
      forcingFun θ L R (extFin L g) := by
    have h1 : forcingFun θ L R (extFin L (fun u => g (Fin.rev u))) =
        forcingFun θ L R (fun u => extFin L g (L - 1 - u)) := by
      refine forcingFun_congr_lt θ L R fun u hu => ?_
      have hrev : L - 1 - u < L := by omega
      rw [extFin_apply_lt _ hu, extFin_apply_lt g hrev]
      congr 1
      ext
      simp only [Fin.val_rev]
      omega
    rw [h1, forcingFun_reflect]
  rw [hsum, hexp]
  ring

/-! ### Change of measure to the constrained law -/

/-- The expectation under a constrained law is the Gibbs expectation of the density times the
observable, with the normalizer. -/
theorem integral_constrainedLaw_eq (P : Parameters) (N : ℕ+) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    (i0 : ℤ) (L : ℕ) (R : ℝ) (G : Configuration N → ℝ) :
    ∫ X, G X ∂constrainedLaw P N θ i0 L R =
      (constrainedNormalizer P N θ i0 L R)⁻¹ *
        ∫ X, Real.exp (-P.val.1 * forcingPotential θ i0 L R X) * G X ∂gibbsMeasure P N := by
  have hz : 0 ≤ constrainedNormalizer P N θ i0 L R := by
    unfold constrainedNormalizer
    exact integral_nonneg fun X => (Real.exp_pos _).le
  have hdens : Measurable fun X : Configuration N =>
      ENNReal.ofReal ((constrainedNormalizer P N θ i0 L R)⁻¹ *
        Real.exp (-P.val.1 * forcingPotential θ i0 L R X)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul (measurable_forcingPotential hθ i0 L R))))
  unfold constrainedLaw
  rw [integral_withDensity_eq_integral_toReal_smul hdens
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hz) (Real.exp_pos _).le)]
  ring

/-! ### The symmetric mean -/

/-- The constrained mean of an odd block functional vanishes: if the coefficients `a_u` of
`∑_u a_u g_u` are odd under the reversal of the block gaps, then the mean of this functional under the
constrained law of the block is zero. -/
theorem integral_gapSum_constrained_eq_zero (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i0 : ℤ) (L : ℕ) (R : ℝ) (a : Fin L → ℝ)
    (ha : ∀ u : Fin L, a (Fin.rev u) = -a u) :
    ∫ X, (∑ u, a u * blockFam i0 L X u) ∂constrainedLaw P N θ i0 L R = 0 := by
  rw [integral_constrainedLaw_eq P N hθ i0 L R]
  have hpt : ∀ X : Configuration N,
      Real.exp (-P.val.1 * forcingPotential θ i0 L R X) * (∑ u, a u * blockFam i0 L X u) =
        reflIntegrand P θ L R a (blockFam i0 L X) := by
    intro X
    have hF : forcingFun θ L R (extFin L (blockFam i0 L X)) = forcingPotential θ i0 L R X := by
      rw [forcingPotential_eq_forcingFun]
      refine forcingFun_congr_lt θ L R fun u hu => ?_
      rw [extFin_apply_lt _ hu]
      rfl
    unfold reflIntegrand
    rw [hF]
    exact mul_comm _ _
  simp only [hpt]
  have hmeas := measurable_reflIntegrand P hθ.1.continuous L R a
  have hrev_meas : Measurable (fun X : Configuration N => fun u : Fin L => blockFam i0 L X (Fin.rev u)) :=
    measurable_pi_iff.mpr fun u => (measurable_pi_apply (Fin.rev u)).comp (measurable_blockFam i0 L)
  have hcomp : ∫ X, reflIntegrand P θ L R a (fun u => blockFam i0 L X (Fin.rev u))
      ∂gibbsMeasure P N =
      ∫ X, reflIntegrand P θ L R a (blockFam i0 L X) ∂gibbsMeasure P N := by
    rw [← integral_map hrev_meas.aemeasurable hmeas.aestronglyMeasurable,
      map_blockFam_rev P N hN i0 L,
      integral_map (measurable_blockFam i0 L).aemeasurable hmeas.aestronglyMeasurable]
  have hneg : ∫ X, reflIntegrand P θ L R a (fun u => blockFam i0 L X (Fin.rev u))
      ∂gibbsMeasure P N = -∫ X, reflIntegrand P θ L R a (blockFam i0 L X) ∂gibbsMeasure P N := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun X =>
      reflIntegrand_rev P θ L R a ha (blockFam i0 L X))
  have hI : ∫ X, reflIntegrand P θ L R a (blockFam i0 L X) ∂gibbsMeasure P N = 0 := by
    linarith
  rw [hI, mul_zero]

/-! ### Gap form of the increment -/

/-- The increment `G_m` is the odd gap form `∑_u a_u g_u` of `gapCoefOf`, with the lifted coefficients
`scaleCoef`, when `k ≥ 1`, `2k ≤ N` and `m < q`. -/
theorem scaleIncrement_eq_gapSum (N : ℕ+) (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) (X : Configuration N) :
    scaleIncrement i k q m X =
      ∑ u : Fin (cyclicRepSpan N (scaleIndex k q (m + 1))),
        gapCoefOf ((N : ℕ) : ℝ) (scaleCoef N i k q m) (cyclicRepSpan N (scaleIndex k q (m + 1)))
            (u : ℕ) *
          blockFam (cyclicRepStart N (scaleIndex k q (m + 1)) i)
            (cyclicRepSpan N (scaleIndex k q (m + 1))) X u := by
  have hLz : gapCoefOf ((N : ℕ) : ℝ) (scaleCoef N i k q m)
      (cyclicRepSpan N (scaleIndex k q (m + 1))) (cyclicRepSpan N (scaleIndex k q (m + 1))) = 0 := by
    unfold gapCoefOf
    rw [Finset.sum_eq_zero (fun r hr => ite_eq_right (by have := Finset.mem_range.1 hr; omega)),
      mul_zero]
  rw [scaleIncrement_eq_sum_coef i hk hkN hm X,
    sum_coef_cyclicLift_eq_gap X _ (scaleCoef N i k q m) _ (sum_scaleCoef i hk hkN hm),
    Finset.sum_range_succ, hLz, zero_mul, add_zero, Finset.sum_range]
  rfl

/-! ### The symmetric mean of the increment -/

/-- The mean of the increment `G_m` under its constrained law vanishes when the block of `G_m` is
symmetric about `i`, that is, when `2 k_{m+1} < N`. The increment is the odd gap form
`∑_u a_u g_u` of `scaleIncrement_eq_gapSum`, with palindromic lifted coefficients of zero sum. -/
theorem integral_scaleIncrement_symmetric (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (ε : ℝ) (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k)
    (hkN : 2 * k ≤ (N : ℕ)) (hm : m < q) (hsym : 2 * scaleIndex k q (m + 1) < (N : ℕ)) :
    ∫ X, scaleIncrement i k q m X ∂scaleLaw P N θ ε i k q m = 0 := by
  unfold scaleLaw
  have hgap : ∀ X : Configuration N, scaleIncrement i k q m X =
      ∑ u : Fin (cyclicRepSpan N (scaleIndex k q (m + 1))),
        gapCoefOf ((N : ℕ) : ℝ) (scaleCoef N i k q m) (cyclicRepSpan N (scaleIndex k q (m + 1)))
            (u : ℕ) *
          blockFam (cyclicRepStart N (scaleIndex k q (m + 1)) i)
            (cyclicRepSpan N (scaleIndex k q (m + 1))) X u :=
    scaleIncrement_eq_gapSum N i hk hkN hm
  have hpal : ∀ r ≤ cyclicRepSpan N (scaleIndex k q (m + 1)),
      scaleCoef N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)) - r) =
        scaleCoef N i k q m r :=
    fun r hr => scaleCoef_reflect i hk hkN hm hsym hr
  have ha : ∀ u : Fin (cyclicRepSpan N (scaleIndex k q (m + 1))),
      gapCoefOf ((N : ℕ) : ℝ) (scaleCoef N i k q m) (cyclicRepSpan N (scaleIndex k q (m + 1)))
          ((Fin.rev u : Fin _) : ℕ) =
        -gapCoefOf ((N : ℕ) : ℝ) (scaleCoef N i k q m) (cyclicRepSpan N (scaleIndex k q (m + 1)))
          (u : ℕ) := by
    intro u
    rw [Fin.val_rev, show cyclicRepSpan N (scaleIndex k q (m + 1)) - ((u : ℕ) + 1) =
      cyclicRepSpan N (scaleIndex k q (m + 1)) - 1 - (u : ℕ) by omega]
    exact gapCoefOf_reflect _ _ _ hpal (sum_scaleCoef i hk hkN hm) u.isLt
  simp only [hgap]
  exact integral_gapSum_constrained_eq_zero P N hN hθ _ _ _ _ ha

end Riesz1

end
