/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvatureForcedPairs
public import Riesz1.Rigidity.GapLawSymmetry

/-!
# Cyclic transport of the constrained law

Every integer starting label is reduced to an initial block through the
affine relabeling. The identities include the fundamental-region
seam and the actual constrained normalizer.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

namespace Internal

theorem curvature_cyclicLift_add_periods {N : ℕ+} (X : Configuration N) (j q : ℤ) :
    cyclicLift X (j + (N : ℕ) * q) = cyclicLift X j + q := by
  obtain ⟨k, hk, p, rfl⟩ := exists_nat_add_mul (N := N) j
  rw [show (k : ℤ) + (N : ℕ) * p + (N : ℕ) * q =
    (k : ℤ) + (N : ℕ) * (p + q) by ring,
    cyclicLift_add_mul X hk, cyclicLift_add_mul X hk]
  push_cast
  ring

end Internal

/-- Natural cyclic relabeling is exactly the integer lift. -/
theorem hsRelabel_eq_cyclicLift {N : ℕ+} (k : ℕ) (X : Configuration N) (i : Fin (N : ℕ)) :
    hsRelabel N k (WithLp.toLp 2 X.val) i = cyclicLift X ((k + i.val : ℕ) : ℤ) := by
  have he : ((k + i.val : ℕ) : ℤ) =
      (((k + i.val) % (N : ℕ) : ℕ) : ℤ) +
        ((N : ℕ) : ℤ) * (((k + i.val) / (N : ℕ) : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div (k + i.val) (N : ℕ)).symm
  rw [he, cyclicLift_add_mul X (Nat.mod_lt _ N.pos)]
  simp only [hsRelabel, hsCycIdx, hsCycShift, Nat.add_comm, Int.cast_natCast]

/-- The homogeneous Riesz energy is preserved by fundamental cyclic relabeling. -/
theorem energy_hsRelabelConfiguration (s : RieszExponent) (N : ℕ+) (k : ℕ)
    (X : Configuration N) : energy s (hsRelabelConfiguration N k X) = energy s X := by
  have he (i j : Fin (N : ℕ)) :
      rieszRepresentative s (((hsRelabelConfiguration N k X).val i -
        (hsRelabelConfiguration N k X).val j : ℝ) : UnitAddCircle) =
      rieszRepresentative s ((X.val (hsCycIdx N k i) - X.val (hsCycIdx N k j) : ℝ) :
        UnitAddCircle) := by
    have hd : (hsRelabelConfiguration N k X).val i -
        (hsRelabelConfiguration N k X).val j =
        (X.val (hsCycIdx N k i) - X.val (hsCycIdx N k j)) +
          (((hsCycShift N k i : ℤ) - (hsCycShift N k j : ℤ) : ℤ) : ℝ) := by
      change (hsRelabel N k (WithLp.toLp 2 X.val) i - _) -
        (hsRelabel N k (WithLp.toLp 2 X.val) j - _) = _
      simp only [hsRelabel_apply]
      push_cast
      ring
    rw [hd]
    congr 1
    have hper (n : ℤ) : ((n : ℝ) : UnitAddCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
      exact ⟨n, by simp⟩
    rw [AddCircle.coe_add, hper, add_zero]
  unfold energy
  simp_rw [he]
  exact congrArg (fun a : ℝ => (N : ℝ) ^ (-s.val) * a)
    (sum_offDiagonal_equiv (hsCycEquiv N k) (fun i j =>
      rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle)))

/-- Cyclic relabeling preserves the actual Gibbs law. -/
theorem map_hsRelabelConfiguration_gibbsMeasure (P : Parameters) (N : ℕ+) (k : ℕ) :
    (gibbsMeasure P N).map (hsRelabelConfiguration N k) = gibbsMeasure P N := by
  let w := fun X : Configuration N => ENNReal.ofReal
    (Real.exp (-P.val.1 * energy (parametersExponent P) X))
  have hw : Measurable w := (continuous_gibbsDensity P N).measurable
  have he : (fun X => w (hsRelabelConfiguration N k X)) = w := by
    funext X
    dsimp only [w]
    rw [energy_hsRelabelConfiguration]
  unfold gibbsMeasure gibbsWeight
  rw [Measure.map_smul _ (measurable_hsRelabelConfiguration N k).aemeasurable]
  change (partitionFunction P N)⁻¹ • ((configurationVolume N).withDensity w).map _ =
    (partitionFunction P N)⁻¹ • (configurationVolume N).withDensity w
  rw [← he, map_withDensity_comp _ (measurable_hsRelabelConfiguration N k) hw,
    (measurePreserving_hsRelabelConfiguration N k).map_eq]
  rw [he]

/-- The exact block map after any integer number of cyclic periods. -/
theorem liftedBlock_eq_relabel {N : ℕ+} (i0 : ℤ) {k : ℕ} {q : ℤ}
    (hi0 : i0 = (k : ℤ) + (N : ℕ) * q) {L : ℕ} (hL : L < (N : ℕ))
    (X : Configuration N) :
    liftedBlock i0 hL X = liftedBlock 0 hL (hsRelabelConfiguration N k X) := by
  apply Subtype.ext
  funext i
  change Fin (L + 1) at i
  have hr := cyclicLift_natCast (hsRelabelConfiguration N k X)
    (Fin.castLE (Nat.succ_le_of_lt hL) i)
  change cyclicLift (hsRelabelConfiguration N k X) (i.val : ℤ) = _ at hr
  have hk := hsRelabel_eq_cyclicLift k X (Fin.castLE (Nat.succ_le_of_lt hL) i)
  have hk0 := hsRelabel_eq_cyclicLift k X ⟨0, N.pos⟩
  change hsRelabel N k (WithLp.toLp 2 X.val) (Fin.castLE (Nat.succ_le_of_lt hL) i) =
    cyclicLift X ((k : ℤ) + (i.val : ℤ)) at hk
  change hsRelabel N k (WithLp.toLp 2 X.val) ⟨0, N.pos⟩ = cyclicLift X (k : ℤ) at hk0
  change cyclicLift X (i0 + i.val) - (⌊cyclicLift X i0⌋ : ℝ) =
    cyclicLift (hsRelabelConfiguration N k X) (0 + i.val) -
      (⌊cyclicLift (hsRelabelConfiguration N k X) 0⌋ : ℝ)
  rw [zero_add, hr, cyclicLift_zero]
  change _ = (hsRelabel N k (WithLp.toLp 2 X.val) (Fin.castLE (Nat.succ_le_of_lt hL) i) -
      (⌊hsRelabel N k (WithLp.toLp 2 X.val) ⟨0, N.pos⟩⌋ : ℝ)) -
    (⌊(hsRelabel N k (WithLp.toLp 2 X.val) ⟨0, N.pos⟩ -
      (⌊hsRelabel N k (WithLp.toLp 2 X.val) ⟨0, N.pos⟩⌋ : ℝ))⌋ : ℝ)
  rw [hk, hk0, hi0,
    show (k : ℤ) + (N : ℕ) * q + i.val = ((k : ℤ) + i.val) + (N : ℕ) * q by ring,
    Internal.curvature_cyclicLift_add_periods, Internal.curvature_cyclicLift_add_periods,
    Int.floor_add_intCast, Int.floor_sub_intCast]
  push_cast
  ring

/-- The forcing is exactly transported to the initial block. -/
theorem forcingPotential_eq_relabel {N : ℕ+} (i0 : ℤ) {k : ℕ} {q : ℤ}
    (hi0 : i0 = (k : ℤ) + (N : ℕ) * q) {L : ℕ} (hL : L < (N : ℕ))
    (θ : ℝ → ℝ) (R : ℝ) (X : Configuration N) :
    forcingPotential θ i0 L R X =
      forcingPotential θ 0 L R (hsRelabelConfiguration N k X) := by
  rw [forcingPotential_eq_liftedBlock θ i0 hL,
    forcingPotential_eq_liftedBlock θ 0 hL, liftedBlock_eq_relabel i0 hi0 hL]

/-- Cyclic transport includes the actual normalizer. -/
theorem constrainedNormalizer_eq_relabel (P : Parameters) (N : ℕ+) (i0 : ℤ)
    {k : ℕ} {q : ℤ} (hi0 : i0 = (k : ℤ) + (N : ℕ) * q) {L : ℕ}
    (hL : L < (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (R : ℝ) :
    constrainedNormalizer P N θ i0 L R = constrainedNormalizer P N θ 0 L R := by
  unfold constrainedNormalizer
  simp_rw [forcingPotential_eq_relabel i0 hi0 hL]
  have hi := integral_map (μ := gibbsMeasure P N)
    (measurable_hsRelabelConfiguration N k).aemeasurable
    ((Real.measurable_exp.comp ((measurable_forcingPotential hθ 0 L R).const_mul (-P.val.1)))).aestronglyMeasurable
  rw [map_hsRelabelConfiguration_gibbsMeasure] at hi
  exact hi.symm

/-- Every constrained law is carried to the initial constrained law. -/
theorem map_constrainedLaw_relabel (P : Parameters) (N : ℕ+) (i0 : ℤ)
    {k : ℕ} {q : ℤ} (hi0 : i0 = (k : ℤ) + (N : ℕ) * q) {L : ℕ}
    (hL : L < (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (R : ℝ) :
    (constrainedLaw P N θ i0 L R).map (hsRelabelConfiguration N k) =
      constrainedLaw P N θ 0 L R := by
  let w := fun X : Configuration N => ENNReal.ofReal
    ((constrainedNormalizer P N θ 0 L R)⁻¹ * Real.exp (-P.val.1 * forcingPotential θ 0 L R X))
  have hw : Measurable w := ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Real.measurable_exp.comp ((measurable_forcingPotential hθ 0 L R).const_mul _)))
  have he : (fun X : Configuration N => ENNReal.ofReal
      ((constrainedNormalizer P N θ i0 L R)⁻¹ * Real.exp (-P.val.1 * forcingPotential θ i0 L R X))) =
      fun X => w (hsRelabelConfiguration N k X) := by
    funext X
    dsimp only [w]
    rw [constrainedNormalizer_eq_relabel P N i0 hi0 hL hθ R,
      forcingPotential_eq_relabel i0 hi0 hL]
  unfold constrainedLaw
  rw [he, map_withDensity_comp _ (measurable_hsRelabelConfiguration N k) hw,
    map_hsRelabelConfiguration_gibbsMeasure]

end Riesz1

end
