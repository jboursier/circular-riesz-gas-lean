/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.NoExplosionUniformIBP
public import Riesz1.ToMathlib.LogConcave.InverseRecurrence

/-!
# Uniform inverse moments of nearest gaps

Lemma 4.5. Constants are chosen before particle number
and label. The one-particle convention is included.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Internal recurrence for the actual Gibbs inverse moments. -/
theorem gap_inverse_recurrence_internal (hPL : External.PrekopaLeindler)
    (P : Parameters) (n : ℕ) (j : ℤ) {q : ℝ} (hq : 0 < q) :
    let M := fun r : ℝ => ∫ X : Configuration (n + 1).succPNat,
      gap X j ^ (-r) ∂gibbsMeasure P (n + 1).succPNat
    (2 * P.val.1 * P.val.2) * (M (P.val.2 + 1) - M P.val.2) ≤ 1 ∧
    (2 * P.val.1 * P.val.2) * M (q + P.val.2 + 1) ≤
      (2 * P.val.1 * P.val.2) * M q * M (P.val.2 + 1) + q * M (q + 1) := by
  let := (modelWellDefined P (n + 1).succPNat).2.2
  let V := fun t : ℝ => -Real.log (gapMarginalProbabilityDensity P n t) -
    2 * P.val.1 * t ^ (-P.val.2)
  let v := fun t : ℝ => derivWithin V (Ioi t) t
  have h := gap_ibp_gibbs_internal hPL P n j hq
  simp only [show -P.val.2 - 1 = -(P.val.2 + 1) by ring] at h
  exact inverse_covariance_recurrence_internal (fun X => gap X j)
    (fun X => v (gap X j)) (Ioo (0 : ℝ) (n + 2 : ℝ)) v (fun _ ht => ht.1)
    (fun X => ⟨gap_pos X j, by
      have hh := gap_lt_particle_number (by simp) X j
      norm_num only [Nat.succPNat_coe, Nat.cast_succ] at hh
      linarith⟩)
    (fun X => gap_pos X j) (fun _ => rfl)
    (gap_rightDeriv_monotoneOn (convexOn_gapPotential hPL P n)) P.2.2.1 hq
    (integrable_gap P _ j) (integral_gap_gibbsMeasure P _ (by simp) j)
    (fun r hr => integrable_gap_inverse_rpow P n j hr)
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- **No explosion of nearby particles**, Lemma 4.5.
The constant depends only on the model parameters and the positive order.
All particle numbers, including one, and all integer labels are covered. -/
theorem no_explosion_uniform (P : Parameters) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (j : ℤ),
      ∃ _h : Integrable (fun X : Configuration N => gap X j ^ (-p)) (gibbsMeasure P N),
        (∫⁻ X : Configuration N, ENNReal.ofReal (gap X j ^ (-p)) ∂gibbsMeasure P N) ≤
          ENNReal.ofReal C := by
  obtain ⟨C, hC, hbound⟩ := exists_inverse_moment_bound_internal
    (a := 2 * P.val.1 * P.val.2) (mul_pos (mul_pos (by norm_num) P.2.1) P.2.2.1) P.2.2.1 hp
  refine ⟨max C 1, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro hPL N j
  by_cases hN : N = 1
  · subst N
    refine ⟨?_, ?_⟩
    · let := (modelWellDefined P 1).2.2
      simpa only [gap_one_particle, Real.one_rpow] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : Configuration 1 => (1 : ℝ)) (gibbsMeasure P 1))
    · rw [gap_inverse_moment_one_particle]
      exact_mod_cast (show ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (max C 1) from
        ENNReal.ofReal_le_ofReal (le_max_right _ _))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n + 1).succPNat := by
      refine ⟨N.val - 2, ?_⟩
      apply PNat.coe_injective
      have hpos := N.pos
      have hne : N.val ≠ 1 := fun h => hN (PNat.coe_injective h)
      simp only [Nat.succPNat_coe]
      omega
    let := (modelWellDefined P (n + 1).succPNat).2.2
    have hi := integrable_gap_inverse_rpow P n j hp.le
    refine ⟨hi, ?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun X =>
      Real.rpow_nonneg (gap_pos X j).le (-p))]
    apply ENNReal.ofReal_le_ofReal
    apply le_trans _ (le_max_left C 1)
    apply hbound (fun r => ∫ X : Configuration (n + 1).succPNat,
      gap X j ^ (-r) ∂gibbsMeasure P (n + 1).succPNat)
    · intro r _
      exact integral_nonneg fun X => Real.rpow_nonneg (gap_pos X j).le _
    · intro r t hr ht hrt
      exact integral_inverse_rpow_le (fun X => gap_pos X j) hr ht hrt
        (integrable_gap_inverse_rpow P n j hr) (integrable_gap_inverse_rpow P n j ht.le)
    · exact (gap_inverse_recurrence_internal hPL P n j (q := 1) one_pos).1
    · intro q hq
      exact (gap_inverse_recurrence_internal hPL P n j hq).2

end Riesz1

end
