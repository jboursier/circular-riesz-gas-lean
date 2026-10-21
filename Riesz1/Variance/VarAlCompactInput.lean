/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.CompactDecompositionInput
public import Riesz1.Variance.VarAlCompact

/-!
# The complete loop variance input

Proposition 5.9 and the loop component of Theorem 2, on the original test
and both actual convolution families, with all coefficients chosen before
the scale sequence.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology ENNReal

namespace Riesz1.Internal

/-- The compact part of the loop variance input, uniformly before the
scale sequence, particle count, both radii, and transport representative. -/
theorem varAlCompact_optimalScalingTest
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (hp : CompactProfile p) (α : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      ∀ (N : ℕ+) (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (h : ℝ) (hh : 0 < h), 1 ≤ cltK N (ell N) → (cltK N (ell N))⁻¹ ≤ h → h ≤ 1 →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N)) ⟨(fun x => (ψ x : ℂ)),
            complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltRegCircle hρ _ hh f)
                  (cltRegCircle_contDiff hρ _ hh f)) k) →
          ∃ hi : Integrable (loopOnConfiguration (parametersExponent P) N (ell N)
              (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ hi < ⊤ ∧
            (variance (gibbsMeasure P N) _ hi).toReal ≤
              C * cltK N (ell N) ^ (ε + max 1 (2 * (1 - P.val.2 + α))) := by
  obtain ⟨α', hα', hα'2, hαα', hpower⟩ := varAlFinal_interior_exponent P.property.2.2 hα hα2
  obtain ⟨E, hE, hpieces⟩ := compactDecomposition_optimalScalingTest P p hp α α' d
    hα hα2 hαα' hα' hα'2 hη hB hC₀ ρ hρ
  obtain ⟨C, hC, hv⟩ := varAlFinal_finite_pieces hBE hPL P
    ((d.2.2.2.1 : ℕ) + 1) hα'.le hα'2 hE hε
  refine ⟨C, hC, fun ell hell hreg N r v f ht h hh hK hKh hh1 ψ hψ htr => ?_⟩
  obtain ⟨φ, hφ, hsum, henv⟩ := hpieces ell hell hreg N r v f ht h hh hK hKh hh1 ψ hψ htr
  have htrans (j : Fin ((d.2.2.2.1 : ℕ) + 1)) : ∃ a : ℝ,
      (∀ x, |deriv (fun t => φ j (t + a)) x| ≤ E *
        gradWeightOne P.val.2 (1 - P.val.2 + α') (cltK N (ell N)) (ell N).val⁻¹ x) ∧
      (∀ x, |deriv (deriv (fun t => φ j (t + a))) x| ≤ E *
        gradWeightTwo P.val.2 (1 - P.val.2 + α') (cltK N (ell N)) (ell N).val⁻¹ x) := by
    let a : ℝ := Fin.lastCases 0 d.2.2.2.2 j
    refine ⟨a, fun x => ?_, fun x => ?_⟩
    · rw [deriv_comp_add_const]
      simpa only [a, add_sub_cancel_right] using (henv j (x + a)).1
    · rw [show deriv (fun t => φ j (t + a)) = fun t => deriv (φ j) (t + a) from
        funext fun t => deriv_comp_add_const (φ j) a t, deriv_comp_add_const]
      simpa only [a, add_sub_cancel_right] using (henv j (x + a)).2
  obtain ⟨hi, hb⟩ := hv N (ell N).val _ φ (ell N).property.1 (ell N).property.2
    hK hφ hsum htrans
  have hb' : variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal
      (C * cltK N (ell N) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
    rwa [hpower] at hb
  have hfinite : variance (gibbsMeasure P N) _ hi < ⊤ := hb'.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, hfinite, ?_⟩
  exact (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mpr hb' |>.trans
    (ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg (cltK_pos N (ell N)).le _))).le

/-- Proposition 5.9, uniformly over the original test and both
convolution families. This discharges the optimal-variance input. -/
theorem varAlVarianceInput_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) : VarAlVarianceInput := by
  classical
  intro P p α d ρ hρ r _ _ ε hε
  obtain ⟨Cm, hCm, hm⟩ := varAlVarianceInput_macroscopic_of_externals hBE hPL P p α d ρ hρ hε
  by_cases hex : ∃ ell : Scales, Admissible P p ell α d ∧ CompactProfile p
  · obtain ⟨_, hadm₀, hp⟩ := hex
    obtain ⟨Cc, hCc, hc⟩ := varAlCompact_optimalScalingTest hBE hPL P p hp α d
      hadm₀.1 hadm₀.2.1 hadm₀.2.2.1 hadm₀.2.2.2.2.1.le hadm₀.2.2.2.2.2.1.le ρ hρ hε
    refine ⟨max Cm Cc, hCm.trans_le (le_max_left _ _), fun ell hadm N hK v f ht h hh hKh hh1 ψ hψ htr => ?_⟩
    have hpow : 0 ≤ cltK N (ell N) ^ (ε + max 1 (2 * (1 - P.val.2 + α))) :=
      Real.rpow_nonneg (cltK_pos N (ell N)).le _
    rcases hadm.2.2.2.2.2.2 with ⟨hone, _, _⟩ | ⟨_, hell, hreg⟩
    · obtain ⟨hi, hf, hb⟩ := hm ell hadm hone N r v f ht h hh hKh hh1 ψ hψ htr
      exact ⟨hi, hf, hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)⟩
    · obtain ⟨hi, hf, hb⟩ := hc ell hell hreg N r v f ht h hh hK hKh hh1 ψ hψ htr
      exact ⟨hi, hf, hb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)⟩
  · refine ⟨Cm, hCm, fun ell hadm N _ v f ht h hh hKh hh1 ψ hψ htr => ?_⟩
    rcases hadm.2.2.2.2.2.2 with ⟨hone, _, _⟩ | ⟨hp, _, _⟩
    · exact hm ell hadm hone N r v f ht h hh hKh hh1 ψ hψ htr
    · exact False.elim (hex ⟨ell, hadm, hp⟩)

end Riesz1.Internal
