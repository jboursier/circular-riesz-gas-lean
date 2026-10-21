/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorOneCases
public import Riesz1.CLT.ErrorOneProduct
public import Riesz1.CLT.ErrorOneStein
public import Riesz1.CLT.ErrorOneCentering
public import Riesz1.CLT.ErrorOneExponents
public import Riesz1.CLT.SmoothingVariance

/-!
# The conclusion of Theorem 3 at one scale (`ErrorOneConclusion`)

`ErrorOneConclusion P p α τ C ℓ N` is the three assertions of Theorem 3 at the scale
`ℓ = ℓ_N` and the particle number `N`, with the constant `C`, for every transport `ψ` of the
regularized profile (`htr`) and every `σ` with `σ² = σ_reg²` (`hσV`):

* `‖q_N‖_∞ ≤ C δ^{-2-α-τ}` and `‖q_N'‖_∞ ≤ C δ^{-2-α-τ}`.
* `Var Fluct_N[q_N(ℓ⁻¹ ·)] ≤ C K^{s+2τ} δ^{-2(2+α+τ)}`, for every lift `qC` of `q_N`.
* `|Error¹_N(u)| ≤ C ‖u'‖_∞ K^{s/2-1+τ} δ^{-2-α-τ}`, for every `u ∈ C¹` with bounded `u, u'`.

Here `δ = δ_N` (`cltDelta`), `K = Nℓ_N` (`cltK`), `s = P.val.2`, and the profile is the periodized
`p` at the scale `ℓ_N` as in `Riesz1.Internal.clt_smoothing_of_variance_uniform`.

`errorOne_conclusion_of_facts` proves it from the analytic facts of `ErrorOneCases` and the
conditional `APrioriConclusion`, with the explicit constant
`C_chain = A + 4 C_V A² + 2 √C_V A`, where `A = C₁C₃ + C₁C₄(1+n) + C₂C₃`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The three assertions of Theorem 3 at scale `ℓ_N`, particle number `N` and constant
`C`, for every transport `ψ` of `ξ_reg` and every `σ` with `σ² = σ_reg²`. -/
def ErrorOneConclusion {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (p : Profile)
    (α τ C : ℝ) (ell : Scales) (N : ℕ+) : Prop :=
  ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength (ell N)))))
    (_htr : ∀ k : ℤ, coeff (loopMasterLength (ell N))
      ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
      transportCoeffs P (loopMasterLength (ell N))
        (loopMasterLengthTest _ (cltReg hρ P N (ell N)
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
          (cltReg_contDiff hρ P N (ell N)
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)) k)
    (σ : ℝ)
    (_hσV : ENNReal.ofReal (σ ^ 2) = cltVariance P (ell N)
      ⟨fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ),
        cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩),
    let R := cltRegLine hρ P N (ell N)
      ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
    let q := errorOneQLine (loopMasterProfile (ell N) ψ hψ).val R
    let δ := cltDelta P N (ell N)
    let K := cltK N (ell N)
    (∀ u : ℝ, |q u| ≤ C * δ ^ (-2 - α - τ)) ∧
    (∀ u : ℝ, |deriv q u| ≤ C * δ ^ (-2 - α - τ)) ∧
    (∀ qC : Circle (observationLength (ell N)) → ℝ,
      (∀ u : ℝ, qC (u : Circle (observationLength (ell N))) = q u) →
      ∃ (hint : Integrable (scaledLift (ell N) qC) volume)
        (h1 : Integrable (fun X => fluctuation ⟨scaledLift (ell N) qC, hint⟩ X)
          (gibbsMeasure P N)),
        variance (gibbsMeasure P N) (fun X => fluctuation ⟨scaledLift (ell N) qC, hint⟩ X) h1 ≤
          ENNReal.ofReal (C * K ^ (P.val.2 + 2 * τ) * δ ^ (-(2 * (2 + α + τ))))) ∧
    (∀ u : ℝ → ℝ, ContDiff ℝ 1 u → (∃ B : ℝ, ∀ x, |u x| ≤ B) → ∀ M : ℝ,
      (∀ x, |deriv u x| ≤ M) →
      |errorOneStein hρ P N (ell N)
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
        ψ hψ σ u| ≤ C * M * K ^ (P.val.2 / 2 - 1 + τ) * δ ^ (-2 - α - τ))

/-- The variance constant of `APrioriConclusion` enters the chain through `CV ≥ 0`. -/
lemma pow_neg_two_mul_eq {δ : ℝ} (hδ : 0 < δ) (α τ : ℝ) :
    (δ ^ (-2 - α - τ)) ^ 2 = δ ^ (-(2 * (2 + α + τ))) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  congr 1
  push_cast
  ring

/-- **The conclusion of Theorem 3 at one scale**, from the analytic facts of the case
(`ErrorOneCases`) and the conditional `APrioriConclusion` (through its variance constant `CV`).
The constant is `A + 4 CV A² + 2 √CV A` with `A = C₁C₃ + C₁C₄(1+n) + C₂C₃`. -/
theorem errorOne_conclusion_of_facts {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters)
    (p : Profile) (α τ : ℝ) (_hτ : 0 < τ) (hα0 : P.val.2 - 1 ≤ α) (_hαs : α < P.val.2 / 2)
    (ell : Scales) (N : ℕ+) (hK : 1 ≤ cltK N (ell N))
    (η : ℝ) (hη : 0 < η) (hητ : η ≤ τ) (hτα : α - P.val.2 + 2 * η ≤ τ)
    (hηs : P.val.2 - 1 < α + η)
    (C₁ C₂ C₃ C₄ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄)
    (n : ℕ) (marks : Fin n → ℝ)
    (ψ0 : Circle (loopMasterLength (ell N)) → ℝ)
    (hψ0m : MemLp (fun x => (ψ0 x : ℂ)) 2 (arclength (loopMasterLength (ell N))))
    (hψ0 : ∀ k : ℤ, coeff (loopMasterLength (ell N))
      ⟨(fun x => (ψ0 x : ℂ)), complexL2Integrable _ _ hψ0m⟩ k =
      transportCoeffs P (loopMasterLength (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k)
    (hH : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
      |deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
          (fun s : ℝ => periodizedProfile p (observationLength (ell N))
            (s : Circle (observationLength (ell N)))) t) x| ≤ C₁ * h ^ (-1 - α - η) ∧
      |deriv (deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
          (fun s : ℝ => periodizedProfile p (observationLength (ell N))
            (s : Circle (observationLength (ell N)))) t)) x| ≤ C₂ * h ^ (-2 - α - η))
    (hsup : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
      |circleMollify ρ (loopMasterLength (ell N)).val h
        (fun t : ℝ => ψ0 (t : Circle (loopMasterLength (ell N)))) x| ≤ C₃)
    (hder : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
      |deriv (fun t : ℝ => circleMollify ρ (loopMasterLength (ell N)).val h
          (fun s : ℝ => ψ0 (s : Circle (loopMasterLength (ell N)))) t) x| ≤
        C₄ * (1 + ∑ j : Fin n,
          max (dist (x : Circle (loopMasterLength (ell N)))
            (marks j : Circle (loopMasterLength (ell N)))) h ^ (-1 + P.val.2 - (α + η))))
    (CV : ℝ) (hCV : 0 ≤ CV)
    (hAP : ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val → ∀ M : ℝ, 0 ≤ M →
      ∀ f : Circle (observationLength ℓ) → ℝ,
        ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength ℓ))) →
        (∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u| ≤
          M * aPrioriEnvelope P.val.2 0 ((N : ℝ) * ℓ.val) 2
            |centralRep (observationLength ℓ) ((u - 0 : ℝ) : Circle (observationLength ℓ))|) →
        ∃ hB : Integrable (plainSum ℓ N f) (gibbsMeasure P N),
          variance (gibbsMeasure P N) (plainSum ℓ N f) hB ≤
            ENNReal.ofReal (CV * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (2 * τ + max (2 * 0) P.val.2)))
    (hvanR : ∀ x : ℝ,
      2 ≤ |centralRep (observationLength (ell N)) (x : Circle (observationLength (ell N)))| →
      deriv (cltRegLine hρ P N (ell N)
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩) x = 0 ∧
      deriv (deriv (cltRegLine hρ P N (ell N)
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)) x = 0)
    (C : ℝ)
    (hCC : (C₁ * C₃ + C₁ * C₄ * (1 + n) + C₂ * C₃) +
        4 * CV * (C₁ * C₃ + C₁ * C₄ * (1 + n) + C₂ * C₃) ^ 2 +
        2 * Real.sqrt CV * (C₁ * C₃ + C₁ * C₄ * (1 + n) + C₂ * C₃) ≤ C) :
    ErrorOneConclusion hρ P p α τ C ell N := by
  intro ψ hψ htr σ hσV R q δ K
  set ξ : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength (ell N)))} :=
    ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ with hξdef
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hδ0 : 0 < δ := cltDelta_pos P N (ell N)
  have hδ1 : δ ≤ 1 := cltDelta_le_one P N (ell N) hK
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hKdef : K = (N : ℝ) * (ell N).val := rfl
  have hΨc : ContDiff ℝ ∞ (loopMasterProfile (ell N) ψ hψ).val := hψ
  have hRc : ContDiff ℝ ∞ R := cltRegLine_contDiff hρ P N (ell N) _
  have hRd : Continuous (deriv R) := (contDiff_infty_iff_deriv.1 hRc).2.continuous
  have hqc : ContDiff ℝ ∞ q := hΨc.mul (contDiff_infty_iff_deriv.1 hRc).2
  obtain ⟨hR1, hR2, hΨb, hΨ'b⟩ := errorOne_bounds_of_facts hρ P N (ell N) p α η C₁ C₂ C₃ C₄ n
    marks hα0 hη hηs hC₁ hC₂ hC₃ hC₄ hH ψ0 hψ0m hψ0 hsup hder ψ hψ htr hδ1
  have hdq : ∀ u, deriv q u = deriv (loopMasterProfile (ell N) ψ hψ).val u * deriv R u +
      (loopMasterProfile (ell N) ψ hψ).val u * deriv (deriv R) u :=
    fun u => errorOneQLine_deriv hΨc hRc u
  obtain ⟨hq0, hq1⟩ := errorOne_q_sup (n := (n : ℝ)) hδ0 hδ1 hη.le hητ hτα hC₁ hC₂ hC₃ hC₄
    (Nat.cast_nonneg n) hR1 hR2 hΨb hΨ'b hdq
  set Aq := C₁ * C₃ + C₁ * C₄ * (1 + (n : ℝ)) + C₂ * C₃ with hAq
  have hAq0 : 0 ≤ Aq := by positivity
  have hXnn : 0 ≤ δ ^ (-2 - α - τ) := Real.rpow_nonneg hδ0.le _
  have hsqCV : 0 ≤ Real.sqrt CV := Real.sqrt_nonneg CV
  have hCch : Aq ≤ C := by
    have h1 : 0 ≤ 4 * CV * Aq ^ 2 := by positivity
    have h2 : 0 ≤ 2 * Real.sqrt CV * Aq := by positivity
    linarith
  have hC4 : 4 * CV * Aq ^ 2 ≤ C := by
    have h2 : 0 ≤ 2 * Real.sqrt CV * Aq := by positivity
    linarith
  -- The periodic lift of `q` to the circle of length `ℓ⁻¹`.
  have hqper : Function.Periodic q (observationLength (ell N)).val :=
    errorOneQLine_periodic (loopMasterProfile (ell N) ψ hψ).property.1
      (cltRegLine_periodic hρ P N (ell N) _)
  obtain ⟨qC, hqC⟩ : ∃ qC : Circle (observationLength (ell N)) → ℝ,
      ∀ u : ℝ, qC (u : Circle (observationLength (ell N))) = q u :=
    ⟨hqper.lift, fun u => Function.Periodic.lift_coe hqper u⟩
  -- The fluctuation variance for any lift of `q`.
  have hVar : ∀ qC' : Circle (observationLength (ell N)) → ℝ,
      (∀ u : ℝ, qC' (u : Circle (observationLength (ell N))) = q u) →
      ∃ (hint : Integrable (scaledLift (ell N) qC') volume)
        (h1 : Integrable (fun X => fluctuation ⟨scaledLift (ell N) qC', hint⟩ X)
          (gibbsMeasure P N)),
        variance (gibbsMeasure P N) (fun X => fluctuation ⟨scaledLift (ell N) qC', hint⟩ X) h1 ≤
          ENNReal.ofReal (4 * CV * (Aq * δ ^ (-2 - α - τ)) ^ 2 *
            ((N : ℝ) * (ell N).val) ^ (2 * τ + P.val.2)) := by
    intro qC' hqC'
    have hfun' : (fun u : ℝ => qC' (u : Circle (observationLength (ell N)))) = q := funext hqC'
    have hcont' : Continuous qC' :=
      continuous_circle_of_lift _ (by rw [hfun']; exact hqc.continuous)
    have hC1' : ContDiff ℝ 1 (fun u : ℝ => qC' (u : Circle (observationLength (ell N)))) := by
      rw [hfun']; exact hqc.of_le (by exact_mod_cast le_top)
    have hb' : ∀ u : ℝ, |deriv (fun t : ℝ => qC' (t : Circle (observationLength (ell N)))) u| ≤
        Aq * δ ^ (-2 - α - τ) := by
      intro u; rw [hfun']; exact hq1 u
    have hv' : ∀ u : ℝ, 2 ≤ |centralRep (observationLength (ell N))
        ((u - 0 : ℝ) : Circle (observationLength (ell N)))| →
        deriv (fun t : ℝ => qC' (t : Circle (observationLength (ell N)))) u = 0 := by
      intro u hu
      rw [hfun']
      rw [sub_zero] at hu
      rw [hdq u, (hvanR u hu).1, (hvanR u hu).2]
      simp
    exact errorOne_fluct_variance P (ell N) N (2 * τ) CV hCV hAP hK qC' hcont' hC1'
      (Aq * δ ^ (-2 - α - τ)) (mul_nonneg hAq0 hXnn) hb' hv'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    exact (hq0 u).trans (mul_le_mul_of_nonneg_right hCch hXnn)
  · intro u
    exact (hq1 u).trans (mul_le_mul_of_nonneg_right hCch hXnn)
  · intro qC' hqC'
    obtain ⟨hint', h1', hv⟩ := hVar qC' hqC'
    refine ⟨hint', h1', hv.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    rw [hKdef, mul_pow, pow_neg_two_mul_eq hδ0]
    have hcomm : (2 * τ + P.val.2) = P.val.2 + 2 * τ := by ring
    rw [hcomm]
    have hY : 0 ≤ ((N : ℝ) * (ell N).val) ^ (P.val.2 + 2 * τ) :=
      Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (ell N).property.1.le) _
    have hD : 0 ≤ δ ^ (-(2 * (2 + α + τ))) := Real.rpow_nonneg hδ0.le _
    calc 4 * CV * (Aq ^ 2 * δ ^ (-(2 * (2 + α + τ)))) *
          ((N : ℝ) * (ell N).val) ^ (P.val.2 + 2 * τ)
        = (4 * CV * Aq ^ 2) * ((N : ℝ) * (ell N).val) ^ (P.val.2 + 2 * τ) *
            δ ^ (-(2 * (2 + α + τ))) := by ring
      _ ≤ C * ((N : ℝ) * (ell N).val) ^ (P.val.2 + 2 * τ) * δ ^ (-(2 * (2 + α + τ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4 hY) hD
  · intro u hu hbu M hM
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    unfold errorOneStein
    have hFeq : ∀ X, cltPairingSum (N := N) (ell N) (loopMasterProfile (ell N) ψ hψ) R X =
        plainSum (ell N) N qC X := by
      intro X
      unfold plainSum cltPairingSum
      exact Finset.sum_congr rfl fun k _ => (hqC _).symm
    have hΨcont : Continuous (loopMasterProfile (ell N) ψ hψ).val := hψ.continuous
    have hcontF : Continuous (cltPairingSum (N := N) (ell N) (loopMasterProfile (ell N) ψ hψ) R) :=
      continuous_cltPairingSum (N := N) (ell N) (loopMasterProfile (ell N) ψ hψ) hΨcont hRd
    have hbdF : ∀ X, |cltPairingSum (N := N) (ell N) (loopMasterProfile (ell N) ψ hψ) R X| ≤
        (N : ℝ) * (Aq * δ ^ (-2 - α - τ)) := by
      intro X
      unfold cltPairingSum
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => hq0 _).trans ?_
      simp
    have hF : MemLp (cltPairingSum (N := N) (ell N) (loopMasterProfile (ell N) ψ hψ) R) 2
        (gibbsMeasure P N) :=
      MemLp.of_bound hcontF.aestronglyMeasurable _
        (ae_of_all _ fun X => by rw [Real.norm_eq_abs]; exact hbdF X)
    have hcent := clt_pairing_centering P hρ N (ell N) ξ ψ hψ htr σ hσV
    have hBnn : 0 ≤ 4 * CV * (Aq * δ ^ (-2 - α - τ)) ^ 2 *
        ((N : ℝ) * (ell N).val) ^ (2 * τ + P.val.2) := by
      have h1 : 0 ≤ 4 * CV := by linarith
      have h3 : 0 ≤ ((N : ℝ) * (ell N).val) ^ (2 * τ + P.val.2) :=
        Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (ell N).property.1.le) _
      exact mul_nonneg (mul_nonneg h1 (sq_nonneg _)) h3
    have hqcont : Continuous qC := by
      refine continuous_circle_of_lift _ ?_
      have hfq : (fun u : ℝ => qC (u : Circle (observationLength (ell N)))) = q := funext hqC
      rw [hfq]
      exact hqc.continuous
    have hvarF : variance (gibbsMeasure P N)
        (cltPairingSum (N := N) (ell N) (loopMasterProfile (ell N) ψ hψ) R) (hF.integrable one_le_two) ≤
        ENNReal.ofReal (4 * CV * (Aq * δ ^ (-2 - α - τ)) ^ 2 *
          ((N : ℝ) * (ell N).val) ^ (2 * τ + P.val.2)) := by
      obtain ⟨hint, h1, hv⟩ := hVar qC hqC
      have heq := variance_fluctuation_scaledLift_eq P (ell N) N hqcont hint h1
      have hvarP : variance (gibbsMeasure P N)
          (cltPairingSum (N := N) (ell N) (loopMasterProfile (ell N) ψ hψ) R) (hF.integrable one_le_two) =
          variance (gibbsMeasure P N) (fun X => fluctuation ⟨scaledLift (ell N) qC, hint⟩ X) h1 := by
        rw [heq]
        unfold variance
        simp only [hFeq]
      rw [hvarP]
      exact hv
    have hstein := abs_integral_stein_le (μ := gibbsMeasure P N)
      (F := cltPairingSum (N := N) (ell N) (loopMasterProfile (ell N) ψ hψ) R)
      (g := fun X => deriv u (cltStat P N (ell N)
        (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N)) ξ) X))
      hK0 hM0 hBnn hF hcent (fun X => hM _) hvarF
    refine hstein.trans ?_
    set X := δ ^ (-2 - α - τ) with hX
    set Y := ((N : ℝ) * (ell N).val) ^ (2 * τ + P.val.2) with hYdef
    have hYnn : 0 ≤ Y := Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (ell N).property.1.le) _
    have hYK : Y = K ^ (P.val.2 + 2 * τ) := by
      rw [hYdef, hKdef]
      congr 1
      ring
    have hsqrtB : Real.sqrt (4 * CV * (Aq * X) ^ 2 * Y) ≤
        2 * Real.sqrt CV * Aq * X * Real.sqrt Y := by
      have e : (2 * Real.sqrt CV * Aq * X * Real.sqrt Y) ^ 2 = 4 * CV * (Aq * X) ^ 2 * Y := by
        have h1 := Real.sq_sqrt hCV
        have h2 := Real.sq_sqrt hYnn
        calc (2 * Real.sqrt CV * Aq * X * Real.sqrt Y) ^ 2
            = 4 * (Real.sqrt CV) ^ 2 * (Aq * X) ^ 2 * (Real.sqrt Y) ^ 2 := by ring
          _ = 4 * CV * (Aq * X) ^ 2 * Y := by rw [h1, h2]
      have hnn : 0 ≤ 2 * Real.sqrt CV * Aq * X * Real.sqrt Y :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsqCV) hAq0) hXnn)
          (Real.sqrt_nonneg _)
      exact le_of_eq (by rw [← e, Real.sqrt_sq hnn])
    have hKinv : K⁻¹ * M * (2 * Real.sqrt CV * Aq * X * Real.sqrt Y) =
        (2 * Real.sqrt CV * Aq) * M * X * (K⁻¹ * (K ^ (P.val.2 + 2 * τ)) ^ (1 / 2 : ℝ)) := by
      rw [← hYK]
      simp only [Real.sqrt_eq_rpow]
      ring
    have hkey := inv_mul_sqrt_rpow (K := K) (s := P.val.2) (τ := τ) hK0
    have hc2 : 2 * Real.sqrt CV * Aq ≤ C := by
      have h1 : 0 ≤ 4 * CV * Aq ^ 2 := by positivity
      linarith
    have hMK : 0 ≤ M * K ^ (P.val.2 / 2 - 1 + τ) := mul_nonneg hM0 (Real.rpow_nonneg hK0.le _)
    calc K⁻¹ * M * Real.sqrt (4 * CV * (Aq * X) ^ 2 * Y)
        ≤ K⁻¹ * M * (2 * Real.sqrt CV * Aq * X * Real.sqrt Y) :=
          mul_le_mul_of_nonneg_left hsqrtB (by positivity)
      _ = (2 * Real.sqrt CV * Aq) * M * X * (K⁻¹ * (K ^ (P.val.2 + 2 * τ)) ^ (1 / 2 : ℝ)) :=
          hKinv
      _ = (2 * Real.sqrt CV * Aq) * M * X * K ^ (P.val.2 / 2 - 1 + τ) := by rw [hkey]
      _ = (2 * Real.sqrt CV * Aq) * (M * K ^ (P.val.2 / 2 - 1 + τ)) * X := by ring
      _ ≤ C * (M * K ^ (P.val.2 / 2 - 1 + τ)) * X :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 hMK) hXnn
      _ = C * M * K ^ (P.val.2 / 2 - 1 + τ) * X := by
          ring


end Riesz1.Internal

end
end
