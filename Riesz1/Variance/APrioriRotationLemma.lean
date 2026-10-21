/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriRotationTranslationL2
public import Riesz1.Variance.APrioriRotationExteriorTail
public import Riesz1.Variance.APrioriRotationOriginL2
public import Riesz1.Variance.APrioriRotationJoint
public import Riesz1.Variance.APrioriRotationVariance

/-!
# The rotation part of Lemma 5.2, complete statement

The rotation part of Lemma 5.2, with its claims assembled from the preceding results:

1. (joint law) for every `N ≥ 2` and every jointly measurable `φ`, the origin integral equals the
   integral against `μ*` over `0 < D < w(y)`, with `w(y) = N y_1`.
2. (mass) `E_{μ*} w = 1`.
3. (variance) for every bounded measurable anchored `T` and every `κ > 0`, the size-biased
   variance satisfies `Var_{wμ*}(T) ≤ κ Var_{μ*}(T) + 4 ‖T‖²_∞ E[w 1_{w>κ}]`. The paper takes
   `κ = K^ε`.
4. (exterior tail) for every `p ≥ 2`, every `ε > 0` and every `γ ≥ γ₀`, the anchored exterior sum
   has `L^p` norm at most a constant.
5. (`L²`) for every `ε > 0` and every `γ ≥ γ₀`, the joint exterior sum has second moment at most the
   square of that constant.
6. (translation error) for every `γ > 1`, the squared translation error has joint integral at most
   `C K^{c ε} (1 + K^{2λ})`, with `c` independent of `ε`.

The threshold `γ₀` is chosen before `ε`. Claims 4 and 5 hold for every
`γ ≥ (2 - s)/(1 - s)` and every `ε > 0` (`exterior_tail_eLpNorm_le_of_ge` and
`jointExteriorSum_lintegral_sq_le_of_ge`), so the threshold depends only on `s`. The statement
asserts its existence, and the proof takes `γ₀ = (2 - s)/(1 - s)`, which exceeds `1`. The constant
`c` of claim 6 is chosen before `ε`, depending on `λ` and `γ`.

The constants `C` of claims 4 to 6 are one constant, `C = C_4 + C_5 + C_6`. The Bakry–Émery
criterion `External.BakryEmery` and the Prékopa–Leindler inequality `External.PrekopaLeindler`
are explicit hypotheses. Claim 6 uses them through the rigidity conclusion, and claims 4 and 5
use `PrekopaLeindler` only.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Finset

namespace Riesz1

/-- **The rotation part of Lemma 5.2, complete statement.** See the module documentation for the
claims and the threshold scope note. -/
theorem a_priori_rotation (P : Parameters) (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) {lam p : ℝ} (hlam : 0 ≤ lam) (hp : 2 ≤ p) :
    (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      (∀ φ : ℝ → (Fin (N : ℕ) → ℝ) → ENNReal,
        Measurable (fun q : ℝ × (Fin (N : ℕ) → ℝ) => φ q.1 q.2) →
          ∫⁻ X, φ (originD X) (originPos X) ∂(gibbsMeasure P N) =
            ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y), φ D y) ∂(rotAnchoredLaw P N)) ∧
      ∫ y, sizeBiasWeight N hN y ∂(rotAnchoredLaw P N) = 1 ∧
      (∀ (T : (Fin (N : ℕ) → ℝ) → ℝ) (M : ℝ), Measurable T → (∀ y, |T y| ≤ M) →
        ∀ κ : ℝ, 0 < κ →
          variance T ((rotAnchoredLaw P N).withDensity
              fun y => ENNReal.ofReal (sizeBiasWeight N hN y)) ≤
            κ * variance T (rotAnchoredLaw P N) + 4 * M ^ 2 *
              ∫ y in {y | κ < sizeBiasWeight N hN y}, sizeBiasWeight N hN y ∂(rotAnchoredLaw P N))) ∧
    ∃ γ₀ : ℝ, 1 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ → ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ+) (ℓ : ℝ) (hN : 2 ≤ (N : ℕ)), 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) → f (1 / ℓ / 2) = 0 →
        (∀ u ∈ Set.Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
          |deriv f u| ≤ (if |u| ≤ 2 then 1 / (max |u| (((N : ℕ) : ℝ) * ℓ)⁻¹) ^ (1 + lam) else 0) +
            (if 2 ≤ |u| then 1 / |u| ^ (3 - P.val.2) else 0)) →
        eLpNorm (exteriorSum N ℓ γ f) (ENNReal.ofReal p) (gibbsMeasure P N) ≤ ENNReal.ofReal C ∧
        ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
            ENNReal.ofReal (jointExteriorSum N ℓ γ f D y ^ 2)) ∂(rotAnchoredLaw P N) ≤
          ENNReal.ofReal (C ^ 2) ∧
        ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
            ENNReal.ofReal (translationError N ℓ γ f D y ^ 2)) ∂(rotAnchoredLaw P N) ≤
          ENNReal.ofReal (C * (((N : ℕ) : ℝ) * ℓ) ^ (c * ε) *
            (1 + (((N : ℕ) : ℝ) * ℓ) ^ (2 * lam))) := by
  refine ⟨fun N hN => ⟨fun φ hφ => joint_law_rotAnchoredLaw P N hN φ hφ,
    integral_sizeBiasWeight_rotAnchoredLaw P N hN,
    fun T M hT hTM κ hκ => variance_sizeBiased_anchored P N hN hT hTM hκ⟩, ?_⟩
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hγ0 : 1 < (2 - P.val.2) / (1 - P.val.2) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  refine ⟨(2 - P.val.2) / (1 - P.val.2), hγ0, fun γ hγ => ?_⟩
  have hγ1 : 1 < γ := lt_of_lt_of_le hγ0 hγ
  obtain ⟨c, hc, hT⟩ := translation_lintegral_sq_le P hBE hPL hlam hγ1
  refine ⟨c, hc, fun ε hε => ?_⟩
  obtain ⟨Ce, hCe, hce⟩ := exterior_tail_eLpNorm_le_of_ge P hPL hlam hε hp γ hγ
  obtain ⟨CL, hCL, hcl⟩ := jointExteriorSum_lintegral_sq_le_of_ge P hPL hlam hε γ hγ
  obtain ⟨CT, hCT, hct⟩ := hT ε hε
  refine ⟨Ce + CL + CT, by linarith, fun N ℓ hN hℓ hℓ1 hK f hf hper hzero hder => ?_⟩
  have hCe' : Ce ≤ Ce + CL + CT := by linarith
  have hCL' : CL ≤ Ce + CL + CT := by linarith
  have hCT' : CT ≤ Ce + CL + CT := by linarith
  refine ⟨(hce N ℓ hN hℓ hℓ1 hK f hf hper hzero hder).trans
      (ENNReal.ofReal_le_ofReal hCe'), ?_, ?_⟩
  · refine (hcl N ℓ hN hℓ hℓ1 hK f hf hper hzero hder).trans (ENNReal.ofReal_le_ofReal ?_)
    exact pow_le_pow_left₀ hCL hCL' 2
  · refine (hct N ℓ hN hℓ hℓ1 hK f hf hper hzero hder).trans (ENNReal.ofReal_le_ofReal ?_)
    have hK0 : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (c * ε) := Real.rpow_nonneg (by linarith) _
    have hw : 0 ≤ 1 + (((N : ℕ) : ℝ) * ℓ) ^ (2 * lam) := by
      have := Real.rpow_nonneg (show (0 : ℝ) ≤ ((N : ℕ) : ℝ) * ℓ by linarith) (2 * lam)
      linarith
    have h1 : CT * (((N : ℕ) : ℝ) * ℓ) ^ (c * ε) * (1 + (((N : ℕ) : ℝ) * ℓ) ^ (2 * lam)) ≤
        (Ce + CL + CT) * (((N : ℕ) : ℝ) * ℓ) ^ (c * ε) * (1 + (((N : ℕ) : ℝ) * ℓ) ^ (2 * lam)) := by
      apply mul_le_mul_of_nonneg_right _ hw
      exact mul_le_mul_of_nonneg_right hCT' hK0
    exact h1

end Riesz1
