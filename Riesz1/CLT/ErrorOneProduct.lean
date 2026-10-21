/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorOneCases
public import Riesz1.CLT.ErrorOneEnvelope
public import Riesz1.CLT.ErrorOneFluctuation
public import Riesz1.CLT.ErrorOneExponents
public import Riesz1.CLT.ErrorOneBridge
public import Riesz1.Variance.APrioriConclusion

/-!
# The product `q_N` and its variance (Theorem 3, first two assertions)

`q_N = ψ_reg · ξ_reg'` is a function on the circle of length `ℓ⁻¹`. This file:

* proves its sup bounds `‖q_N‖_∞, ‖q_N'‖_∞ ≤ C δ^{-2-α-τ}` from the four analytic bounds
  (`errorOne_q_sup`).
* shows that `q_N'` vanishes at circle distance at least two from the origin in the compact case
  (`errorOne_deriv_vanish`), so that the envelope of Lemma 5.2 applies with `R = 2`.
* proves the variance bound of `Fluct_N[q_N(ℓ⁻¹ ·)]` from the conditional `APrioriConclusion`
  (`errorOne_fluct_variance`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The line function `q = Ψ · R'`, with `Ψ = ψ_reg` and `R = ξ_reg`. -/
def errorOneQLine (Ψ R : ℝ → ℝ) : ℝ → ℝ := fun u => Ψ u * deriv R u

/-- The product `q` is periodic when `Ψ` and `R` are. -/
lemma errorOneQLine_periodic {c : ℝ} {Ψ R : ℝ → ℝ} (hΨ : Function.Periodic Ψ c)
    (hR : Function.Periodic R c) : Function.Periodic (errorOneQLine Ψ R) c := by
  intro u
  unfold errorOneQLine
  rw [hΨ u, deriv_periodic_of hR u]

/-- The derivative of `q = Ψ · R'`, by the product rule. -/
lemma errorOneQLine_deriv {Ψ R : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hR : ContDiff ℝ ∞ R) (u : ℝ) :
    deriv (errorOneQLine Ψ R) u = deriv Ψ u * deriv R u + Ψ u * deriv (deriv R) u := by
  have h1 : DifferentiableAt ℝ Ψ u := (hΨ.differentiable (by simp)) u
  have h2 : DifferentiableAt ℝ (deriv R) u :=
    ((contDiff_infty_iff_deriv.1 hR).2.differentiable (by simp)) u
  unfold errorOneQLine
  exact deriv_mul h1 h2

/-- The exponent comparison behind `errorOne_q_sup`: the product of the two smoothing powers
`δ^{-b-η} δ^{-1-α-η}` is at most `δ^{-2-α-τ}` when `α - s + 2η ≤ τ`. -/
lemma errorOne_exponent_product {δ s α η τ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (h : α - s + 2 * η ≤ τ) :
    δ ^ (-(1 - s + α) - η) * δ ^ (-1 - α - η) ≤ δ ^ (-2 - α - τ) := by
  rw [← Real.rpow_add hδ0]
  exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)

/-- **The sup bounds of `q_N`.** Let `C₁, C₂, C₃, C₄, n ≥ 0` be the constants of the four analytic
bounds, and let `δ ∈ (0,1]`. If `q = Ψ · R'`, `q' = Ψ' R' + Ψ R''` and
`|R'| ≤ C₁ δ^{-1-α-η}`, `|R''| ≤ C₂ δ^{-2-α-η}`, `|Ψ| ≤ C₃`, `|Ψ'| ≤ C₄ (1 + n) δ^{-b-η}`
(`b = 1 - s + α`), with `α - s + 2η ≤ τ`, then both `|q|` and `|q'|` are at most
`A δ^{-2-α-τ}` with `A = C₁C₃ + C₁C₄(1+n) + C₂C₃`. -/
lemma errorOne_q_sup {Ψ R : ℝ → ℝ} {δ s α η τ C₁ C₂ C₃ C₄ n : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (_hη : 0 ≤ η) (hητ : η ≤ τ) (hτ : α - s + 2 * η ≤ τ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) (hn : 0 ≤ n)
    (hR1 : ∀ u, |deriv R u| ≤ C₁ * δ ^ (-1 - α - η))
    (hR2 : ∀ u, |deriv (deriv R) u| ≤ C₂ * δ ^ (-2 - α - η))
    (hΨ : ∀ u, |Ψ u| ≤ C₃)
    (hΨ' : ∀ u, |deriv Ψ u| ≤ C₄ * (1 + n) * δ ^ (-(1 - s + α) - η))
    (hder : ∀ u, deriv (errorOneQLine Ψ R) u = deriv Ψ u * deriv R u + Ψ u * deriv (deriv R) u) :
    (∀ u, |errorOneQLine Ψ R u| ≤
        (C₁ * C₃ + C₁ * C₄ * (1 + n) + C₂ * C₃) * δ ^ (-2 - α - τ)) ∧
    (∀ u, |deriv (errorOneQLine Ψ R) u| ≤
        (C₁ * C₃ + C₁ * C₄ * (1 + n) + C₂ * C₃) * δ ^ (-2 - α - τ)) := by
  have hpow1 : δ ^ (-1 - α - η) ≤ δ ^ (-2 - α - τ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hpow2 : δ ^ (-2 - α - η) ≤ δ ^ (-2 - α - τ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  have hprod := errorOne_exponent_product hδ0 hδ1 hτ
  have hpos : 0 ≤ δ ^ (-2 - α - τ) := Real.rpow_nonneg hδ0.le _
  set T := δ ^ (-2 - α - τ) with hT
  constructor
  · intro u
    have hq : |errorOneQLine Ψ R u| ≤ C₃ * (C₁ * T) := by
      unfold errorOneQLine
      rw [abs_mul]
      calc |Ψ u| * |deriv R u| ≤ C₃ * (C₁ * δ ^ (-1 - α - η)) :=
            mul_le_mul (hΨ u) (hR1 u) (abs_nonneg _) hC₃
        _ ≤ C₃ * (C₁ * T) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow1 hC₁) hC₃
    have hA : 0 ≤ C₁ * C₄ * (1 + n) * T := by positivity
    have hB : 0 ≤ C₂ * C₃ * T := by positivity
    have hC : C₃ * (C₁ * T) = C₁ * C₃ * T := by ring
    have hD : (C₁ * C₃ + C₁ * C₄ * (1 + n) + C₂ * C₃) * T =
        C₁ * C₃ * T + C₁ * C₄ * (1 + n) * T + C₂ * C₃ * T := by ring
    rw [hD]
    linarith
  · intro u
    rw [hder u]
    have h1 : |deriv Ψ u * deriv R u| ≤
        (C₄ * (1 + n) * δ ^ (-(1 - s + α) - η)) * (C₁ * δ ^ (-1 - α - η)) := by
      rw [abs_mul]
      exact mul_le_mul (hΨ' u) (hR1 u) (abs_nonneg _) (by positivity)
    have h2 : |Ψ u * deriv (deriv R) u| ≤ C₃ * (C₂ * T) := by
      rw [abs_mul]
      calc |Ψ u| * |deriv (deriv R) u| ≤ C₃ * (C₂ * δ ^ (-2 - α - η)) :=
            mul_le_mul (hΨ u) (hR2 u) (abs_nonneg _) hC₃
        _ ≤ C₃ * (C₂ * T) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow2 hC₂) hC₃
    have h3 : (C₄ * (1 + n) * δ ^ (-(1 - s + α) - η)) * (C₁ * δ ^ (-1 - α - η)) ≤
        C₄ * (1 + n) * C₁ * T := by
      have e : (C₄ * (1 + n) * δ ^ (-(1 - s + α) - η)) * (C₁ * δ ^ (-1 - α - η)) =
          (C₄ * (1 + n) * C₁) * (δ ^ (-(1 - s + α) - η) * δ ^ (-1 - α - η)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    have hD : (C₁ * C₃ + C₁ * C₄ * (1 + n) + C₂ * C₃) * T =
        C₁ * C₃ * T + C₄ * (1 + n) * C₁ * T + C₂ * C₃ * T := by ring
    have hE : 0 ≤ C₁ * C₃ * T := by positivity
    have hF : C₃ * (C₂ * T) = C₂ * C₃ * T := by ring
    have htri := abs_add_le (deriv Ψ u * deriv R u) (Ψ u * deriv (deriv R) u)
    rw [hD]
    linarith

/-- In the compact case the regularized profile `ξ_reg` and its first two derivatives vanish at
circle distance larger than `r + δ/2` from the origin, with `δ = δ_N` and `r` the support margin
of `p`. Hence `q_N'` vanishes at circle distance at least two. -/
lemma errorOne_vanish_of_compact {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (p : Profile) {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ᵐ y : ℝ, r ≤ |y| → zeroExtension p y = 0)
    (hmargin : cltDelta P N ℓ < 1 / 2 - r) (x : ℝ)
    (hx : 2 ≤ |centralRep (observationLength ℓ) (x : Circle (observationLength ℓ))|) :
    deriv (cltRegLine hρ P N ℓ ⟨periodizedProfile p (observationLength ℓ),
        periodizedProfileL2 p ℓ⟩) x = 0 ∧
    deriv (deriv (cltRegLine hρ P N ℓ ⟨periodizedProfile p (observationLength ℓ),
        periodizedProfileL2 p ℓ⟩)) x = 0 := by
  have hδ0 : 0 < cltDelta P N ℓ := cltDelta_pos P N ℓ
  have hL1 : 1 ≤ (observationLength ℓ).val := by
    show 1 ≤ (ℓ.val)⁻¹
    exact (one_le_inv₀ ℓ.property.1).2 ℓ.property.2
  have hmar : r + cltDelta P N ℓ / 2 < 1 / 2 := by linarith
  have hc : ∀ z : ℝ, r + cltDelta P N ℓ / 2 < |z| → |z| ≤ (observationLength ℓ).val / 2 →
      cltRegLine hρ P N ℓ ⟨periodizedProfile p (observationLength ℓ),
        periodizedProfileL2 p ℓ⟩ z = 0 := by
    intro z hz hzL
    rw [cltRegLine_eq_circleMollify hρ P N ℓ p z,
      circleMollify_periodized_eq_line_central hρ p (observationLength ℓ) hL1 hδ0 hmar hsupp hzL]
    exact mollifyLine_zeroExtension_eq_zero hρ p hδ0 hsupp hz.le
  have hxc : r + cltDelta P N ℓ / 2 < circDist (observationLength ℓ).val x := by
    rw [errorOne_circDist_centralRep x]
    linarith
  exact errorOne_zero_near_of_far (observationLength ℓ).property
    (cltRegLine_periodic hρ P N ℓ ⟨periodizedProfile p (observationLength ℓ),
      periodizedProfileL2 p ℓ⟩) hc x hxc

/-- The variance of `Fluct_N[f(ℓ⁻¹ ·)]` for a continuous `f` on `ℓ⁻¹ 𝕋` with a bounded derivative
that vanishes at circle distance at least two from the origin: the conditional
`APrioriConclusion` (Lemma 5.2, with radius two and the envelope with factor `2A`) bounds
it by `C A² (Nℓ)^{ε + s}`, the form of the variance bound of Theorem 3. -/
lemma errorOne_fluct_variance (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (N : ℕ+) (ε : ℝ)
    (CV : ℝ) (_hCV : 0 ≤ CV)
    (hAP : ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val → ∀ M : ℝ, 0 ≤ M →
      ∀ f : Circle (observationLength ℓ) → ℝ,
        ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength ℓ))) →
        (∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u| ≤
          M * aPrioriEnvelope P.val.2 0 ((N : ℝ) * ℓ.val) 2
            |centralRep (observationLength ℓ) ((u - 0 : ℝ) : Circle (observationLength ℓ))|) →
        ∃ hB : Integrable (plainSum ℓ N f) (gibbsMeasure P N),
          variance (gibbsMeasure P N) (plainSum ℓ N f) hB ≤
            ENNReal.ofReal (CV * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * 0) P.val.2)))
    (hK : 1 ≤ (N : ℝ) * ℓ.val)
    (f : Circle (observationLength ℓ) → ℝ) (hf : Continuous f)
    (hfC1 : ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength ℓ))))
    (A : ℝ) (hA0 : 0 ≤ A)
    (hbound : ∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u| ≤ A)
    (hvan : ∀ u : ℝ, 2 ≤ |centralRep (observationLength ℓ)
        ((u - 0 : ℝ) : Circle (observationLength ℓ))| →
      deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u = 0) :
    ∃ (hint : Integrable (scaledLift ℓ f) volume)
      (h1 : Integrable (fun X => fluctuation ⟨scaledLift ℓ f, hint⟩ X) (gibbsMeasure P N)),
      variance (gibbsMeasure P N) (fun X => fluctuation ⟨scaledLift ℓ f, hint⟩ X) h1 ≤
        ENNReal.ofReal (4 * CV * A ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + P.val.2)) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hbd := deriv_le_aPrioriEnvelope P.val.2 ((N : ℝ) * ℓ.val) A 0 (observationLength ℓ)
    (fun t : ℝ => f (t : Circle (observationLength ℓ))) hK hA0 hbound hvan
  obtain ⟨hB, hBV⟩ := hAP N ℓ hK (2 * A) (by positivity) f hfC1 hbd
  have hint : Integrable (scaledLift ℓ f) volume := (memLp_scaledLift ℓ hf).integrable one_le_two
  have h1 : Integrable (fun X => fluctuation ⟨scaledLift ℓ f, hint⟩ X) (gibbsMeasure P N) := by
    have heq : (fun X => fluctuation ⟨scaledLift ℓ f, hint⟩ X) =
        fun X => plainSum ℓ N f X - (N : ℝ) * ∫ x, scaledLift ℓ f x :=
      funext fun X => fluctuation_scaledLift_eq ℓ N f X
    rw [heq]
    exact (integrable_plainSum P ℓ N hf).sub (integrable_const _)
  have hmax : max (2 * (0 : ℝ)) P.val.2 = P.val.2 :=
    max_eq_right (by linarith [P.property.2.1])
  refine ⟨hint, h1, ?_⟩
  rw [variance_fluctuation_scaledLift_eq P ℓ N hf hint h1]
  refine hBV.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hmax]
  have e : CV * (2 * A) ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + P.val.2) =
      4 * CV * A ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + P.val.2) := by ring
  exact le_of_eq e

end Riesz1.Internal

end
end
