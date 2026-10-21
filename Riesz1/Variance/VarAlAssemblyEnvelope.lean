/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblyVariance
public import Riesz1.Variance.VarAlTransfer
public import Riesz1.Rigidity.ForcingPotential

/-!
# The original loop variance for a single envelope-bounded transport

Proposition 5.9: localization, convexified representation and
measure transfer, with the small exponent chosen before the profile.
This is the strict-exponent single-piece case.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1.Internal

theorem varAlAssembly_frozenVariance_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    variance μ F (hF.integrable one_le_two) = ENNReal.ofReal (ProbabilityTheory.variance F μ) := by
  rw [variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
    ← ProbabilityTheory.ofReal_variance hF]

end Riesz1.Internal

namespace Riesz1

/-- Proposition 5.9, strict-exponent single-piece case, for every
`N ≥ 2` and `K ≥ 1`. The coefficient is chosen before the smooth transport,
particle number and observation scale. -/
theorem varAl_loop_variance_single_envelope
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) {α γ C₀ ε : ℝ} (hα : P.val.2 - 1 < α) (hα2 : α < P.val.2 / 2)
    (hγ : max 4 (2 / P.val.2) ≤ γ) (hγloc : loopLocalizationExponent P.val.2 ≤ γ)
    (hC₀ : 0 < C₀) (hε : 0 < ε) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ),
      0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne P.val.2 (1 - P.val.2 + α)
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo P.val.2 (1 - P.val.2 + α)
        (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
      let N := (n + 1).succPNat
      let K := (N : ℝ) * ℓ
      let F := fun X : Configuration N => loopFunctional P.val.2 (N : ℕ) (loopScaleField ℓ ψ) X.val
      letI := (modelWellDefined P N).2.2
      ∃ hF : MemLp F 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) F (hF.integrable one_le_two) ≤
          ENNReal.ofReal (C * K ^ (ε + max 1 (2 * (1 - P.val.2 + α)))) := by
  obtain ⟨εA, κA, hεA, hκA, haux⟩ := auxiliary_Loop hBE hPL P.val.2 α γ P.2.2.1 P.2.2.2
    hα.le hα2 hγloc
  obtain ⟨εE, κE, hεE, hκE, henergy⟩ := varAl_loop_variance_convexified hBE hPL
    (parametersExponent P) hα hα2 hγ
  have hstar : 0 < min εA (min εE (1 - P.val.2 / 2)) :=
    lt_min hεA (lt_min hεE (by linarith [P.2.2.2]))
  obtain ⟨δ, hδ, hδstar, hloss⟩ := Internal.varAlLoop_choose_epsilon
    hstar (add_pos hκA hκE).le hε
  have hδA : δ < εA := hδstar.trans_le (min_le_left _ _)
  have hδE : δ < εE := hδstar.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδs : δ ≤ 1 - P.val.2 / 2 :=
    (hδstar.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨Ca, hCa, ha⟩ := haux P.val.1 P.2.1 χ hχ hχc hχs hχ1 hχ01 C₀ hC₀.le δ hδ hδA
  obtain ⟨Ce, hCe, he⟩ := henergy P.val.1 P.2.1 C₀ hC₀ χ hχ hχc hχs hχ1 hχ01 δ hδ hδE
  have hγ1 : 1 < γ := by have := (le_max_left _ _).trans hγ; linarith
  obtain ⟨_, Ct, ct, _, hCt, hct, ht⟩ :=
    varAl_transfer hPL P hα hα2 hγ1 hδ hδs hC₀ hχ hχc hχs hχ1 hχ01
  let A := Ca * (Ce + Ct + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2 * A, by positivity, ?_⟩
  intro n ℓ ψ hℓ hℓ1 hK hψ hp h1 h2
  let N := (n + 1).succPNat
  let K := (N : ℝ) * ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  let H := fun y : Fin (n + 1) → ℝ => loopCutoffF χ P.val.2 γ δ N ℓ ψ (anchorVector y)
  let ν := nearestAnchoredLaw P forcingCutoff N K (2 * γ) δ
  let Q := nearestTiltedPairs P N isForcingCutoff_forcingCutoff K (2 * γ) δ (by linarith : 0 < K)
  have := (modelWellDefined P N).2.2
  have := isProbabilityMeasure_anchoredLaw P (n + 1)
  obtain ⟨hF, hH, hlocal⟩ := ha n ℓ ψ hℓ hℓ1 hK hψ hp h1 h2
  obtain ⟨hHQ, hvarQ⟩ := he (n + 1) (by omega) forcingCutoff isForcingCutoff_forcingCutoff
    ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  have hQlaw : anchoredMeasureE Q = ν.map (WithLp.toLp 2) :=
    nearestTiltedPairs_anchoredMeasureE P (by omega) isForcingCutoff_forcingCutoff K (2 * γ) δ
      (by linarith)
  have hHQ' : MemLp (H ∘ WithLp.ofLp) 2 (ν.map (WithLp.toLp 2)) := hQlaw ▸ hHQ
  have hmap := ProbabilityTheory.variance_map hHQ'.aemeasurable
    (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).measurable.aemeasurable
  have hmap' : ProbabilityTheory.variance (H ∘ WithLp.ofLp) (ν.map (WithLp.toLp 2)) =
      ProbabilityTheory.variance H ν := by
    convert hmap using 1
    congr 1
  have hν : ProbabilityTheory.variance H ν ≤ Ce * K ^ (κE * δ) *
      (K + K ^ (2 * (1 - P.val.2 + α))) := by
    rw [← hmap']
    exact hQlaw ▸ hvarQ
  have hμlaw : (gibbsMeasure P N).map (anchorMap N) = anchoredLaw P (n + 1) := by
    rw [show anchorMap N = (fun X : Configuration N => (anchorCoords (n + 1) X.val).2) from
      funext (anchorMap_eq_anchorCoords (n + 1))]
    exact map_snd_gibbsMeasure P (n + 1)
  have htrans := (ht (n + 1) (by omega) forcingCutoff isForcingCutoff_forcingCutoff
    ℓ hℓ hℓ1 hK ψ hψ hp h1 h2).2.2.2
  change |ProbabilityTheory.variance H ((gibbsMeasure P N).map (anchorMap N)) -
    ProbabilityTheory.variance H ν| ≤ Ct * Real.exp (-ct * K ^ δ) at htrans
  have htrans : |ProbabilityTheory.variance H (anchoredLaw P (n + 1)) -
      ProbabilityTheory.variance H ν| ≤ Ct * Real.exp (-ct * K ^ δ) := hμlaw ▸ htrans
  have hμ : ProbabilityTheory.variance H (anchoredLaw P (n + 1)) ≤
      (Ce + Ct) * K ^ (κE * δ) * (K + K ^ (2 * (1 - P.val.2 + α))) := by
    have hpow : 1 ≤ K ^ (κE * δ) := Real.one_le_rpow hK (by positivity)
    have hsum : 1 ≤ K + K ^ (2 * (1 - P.val.2 + α)) := by
      linarith [Real.rpow_nonneg (by linarith : 0 ≤ K) (2 * (1 - P.val.2 + α))]
    have hx : Real.exp (-ct * K ^ δ) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg hK0.le _))
    have herr : Ct * Real.exp (-ct * K ^ δ) ≤
        Ct * K ^ (κE * δ) * (K + K ^ (2 * (1 - P.val.2 + α))) := by
      calc
        _ ≤ Ct * 1 := mul_le_mul_of_nonneg_left hx hCt.le
        _ ≤ _ := by nlinarith [mul_le_mul hpow hsum zero_le_one (by positivity)]
    have hv := le_abs_self (ProbabilityTheory.variance H (anchoredLaw P (n + 1)) -
      ProbabilityTheory.variance H ν)
    nlinarith
  have hvH0 : 0 ≤ ProbabilityTheory.variance H (anchoredLaw P (n + 1)) :=
    ProbabilityTheory.variance_nonneg _ _
  rw [Internal.varAlAssembly_frozenVariance_eq _ hF,
    Internal.varAlAssembly_frozenVariance_eq _ hH,
    ← ENNReal.ofReal_mul (by positivity)] at hlocal
  change ENNReal.ofReal (ProbabilityTheory.variance
      (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ) (loopScaleField ℓ ψ) X.val)
      (gibbsMeasure P N)) ≤
    ENNReal.ofReal (Ca * K ^ (κA * δ) * ProbabilityTheory.variance H (anchoredLaw P (n + 1))) +
      ENNReal.ofReal (Ca * K ^ (κA * δ) * (K + K ^ (2 * (1 - P.val.2 + α)))) at hlocal
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hlocal
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlocal
  have hraw : ProbabilityTheory.variance
      (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ) (loopScaleField ℓ ψ) X.val)
      (gibbsMeasure P N) ≤ A * K ^ ((κA + κE) * δ) *
        (K + K ^ (2 * (1 - P.val.2 + α))) := by
    have hpow : 1 ≤ K ^ (κE * δ) := Real.one_le_rpow hK (by positivity)
    have hcoeff : 0 ≤ Ca * K ^ (κA * δ) := mul_nonneg hCa.le (Real.rpow_nonneg hK0.le _)
    calc
      _ ≤ Ca * K ^ (κA * δ) * ((Ce + Ct) * K ^ (κE * δ) *
          (K + K ^ (2 * (1 - P.val.2 + α)))) +
          Ca * K ^ (κA * δ) * (K + K ^ (2 * (1 - P.val.2 + α))) :=
        hreal.trans (add_le_add (mul_le_mul_of_nonneg_left hμ hcoeff) le_rfl)
      _ ≤ Ca * K ^ (κA * δ) * ((Ce + Ct) * K ^ (κE * δ) *
          (K + K ^ (2 * (1 - P.val.2 + α)))) +
          Ca * K ^ (κA * δ) * (K ^ (κE * δ) * (K + K ^ (2 * (1 - P.val.2 + α)))) := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hpow
      _ = _ := by
        rw [show (κA + κE) * δ = κA * δ + κE * δ by ring, Real.rpow_add hK0]
        dsimp [A]
        ring
  have hfinal := Internal.varAlLoop_absorb (K := K) (b := 1 - P.val.2 + α) (κ := κA + κE)
    (δ := δ) (ε := ε) (A := A) (B := 0) (D := 0) hK hε.le hloss hA.le le_rfl le_rfl
  refine ⟨hF, ?_⟩
  rw [Internal.varAlAssembly_frozenVariance_eq _ hF]
  apply ENNReal.ofReal_le_ofReal
  exact hraw.trans (by simpa only [zero_mul, add_zero] using hfinal)

end Riesz1

end
