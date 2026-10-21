/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.PowerVariance
public import Riesz1.Kernel.ExplicitFormulasPower
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Bridge: the power-law energy in the `powerVariance` form

The theorem `explicit_formulas_power` (the power case of Lemma 2.3) writes the variance with
`riemannZeta` at the point `1 + s - 2α`. The definition `powerVariance` writes it with
`HurwitzZeta.hurwitzZeta 0` at the same point. The two agree by `HurwitzZeta.hurwitzZeta_zero`.

Main results:
* `explicit_formulas_power_powerVariance`: the energy identity, with `powerVariance` on
  the right-hand side.
* `powerVariance_pos`: the variance is positive for every admissible exponent.
-/

public section

open MeasureTheory

namespace Riesz1

/-- The power-law energy identity in the `powerVariance` form. For an exponent `0 < α < s/2`, the
Riesz representative `g_α` lies in `L²(𝕋)`, has mean zero, and for every `L²` proof `hg` its
seminorm is finite and satisfies `(2π)^{1-s}/(2βc_s) ‖g_α‖² = powerVariance P α`. -/
theorem explicit_formulas_power_powerVariance (P : Parameters) (alpha : PowerExponent P) :
    MemLp (fun x : UnitAddCircle => (rieszRepresentative (powerRieszExponent P alpha) x : ℂ))
        2 volume ∧
    (∫ x : UnitAddCircle, rieszRepresentative (powerRieszExponent P alpha) x = 0) ∧
    ∀ hg : MemLp (fun x : UnitAddCircle => (rieszRepresentative (powerRieszExponent P alpha) x : ℂ))
        2 volume,
      circleSobolevSq ((1 - P.val.2) / 2)
          ⟨fun x : UnitAddCircle => (rieszRepresentative (powerRieszExponent P alpha) x : ℂ), hg⟩ ≠ ⊤ ∧
      (2 * Real.pi) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P)) *
          (circleSobolevSq ((1 - P.val.2) / 2)
            ⟨fun x : UnitAddCircle => (rieszRepresentative (powerRieszExponent P alpha) x : ℂ),
              hg⟩).toReal =
        powerVariance P alpha := by
  obtain ⟨h1, h2, h3⟩ := explicit_formulas_power (parametersExponent P)
    (powerRieszExponent P alpha) alpha.property.2 P.val.1 P.property.1
  refine ⟨h1, h2, fun hg => ?_⟩
  obtain ⟨h4, h5⟩ := h3 hg
  refine ⟨h4, h5.trans ?_⟩
  unfold powerVariance
  rw [HurwitzZeta.hurwitzZeta_zero]
  rfl

/-- The power-law variance is positive. Each factor is positive: the powers of `2π`, the squared
Riesz constant, `β`, the Riesz constant `c_s`, and `Re ζ(1 + s - 2α)`, since `1 + s - 2α > 1`. -/
theorem powerVariance_pos (P : Parameters) (alpha : PowerExponent P) :
    0 < powerVariance P alpha := by
  have hrc : ∀ s : RieszExponent, 0 < rieszConstant s := by
    intro s
    have h0 := s.2.1
    have h1 := s.2.2
    unfold rieszConstant
    apply div_pos
    · apply mul_pos
      · apply mul_pos
        · positivity
        · exact Real.sqrt_pos.mpr Real.pi_pos
      · exact Real.Gamma_pos_of_pos (by linarith)
    · exact Real.Gamma_pos_of_pos (by linarith)
  have hz : 0 < (riemannZeta ((1 + P.val.2 - 2 * alpha.val : ℝ) : ℂ)).re :=
    riemannZeta_re_pos_of_one_lt (by linarith [alpha.property.2])
  have hpow : 0 < (2 * Real.pi) ^ (-1 + 2 * alpha.val - P.val.2) := by positivity
  unfold powerVariance
  rw [HurwitzZeta.hurwitzZeta_zero]
  exact mul_pos (div_pos (mul_pos hpow (pow_pos (hrc _) 2))
    (mul_pos P.property.1 (hrc (parametersExponent P)))) hz

end Riesz1

end
