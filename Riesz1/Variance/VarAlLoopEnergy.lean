/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlSingular
public import Riesz1.Variance.VarAlGap
public import Riesz1.Variance.AuxiliaryLoopComplete
public import Riesz1.Variance.VarAlLoopRepresentation

/-!
# The combined inverse-energy estimate for the loop

The three actual fields in Proposition 5.9 have a common uniform
inverse-energy bound. Sobolev membership of the cutoff-loop observable is
not asserted here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- Proposition 5.9, the combined field bound following
equation (5.28). The loss and its threshold precede beta and epsilon, and
the coefficient precedes the particle number, scale and transport. -/
theorem varAlLoop_three_fields_energy
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (s : RieszExponent) {α γ : ℝ} (hα : s.val - 1 < α) (hα2 : α < s.val / 2)
    (hγ : max 4 (2 / s.val) ≤ γ) :
    ∃ εstar κ : ℝ, 0 < εstar ∧ 0 < κ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (C₀ : ℝ), 0 < C₀ →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ε < εstar → ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ)
          (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → ∀ (hK : 1 ≤ (n.succPNat : ℝ) * ℓ),
        ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s.val (1 - s.val + α)
            ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s.val (1 - s.val + α)
            ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          let P : Parameters := ⟨(β, s.val), hβ, s.property⟩
          let K := (n.succPNat : ℝ) * ℓ
          let Q := nearestTiltedPairs P n.succPNat hθ K (2 * γ) ε (by linarith)
          let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
            loopCutoff s.val γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
              gradVfield s.val (loopTransport χ n.succPNat ℓ γ ψ)
                n.succPNat ℓ γ (anchorVector (WithLp.ofLp y)) i.succ
          let w := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
            loopCutoff s.val γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
              gradWfield s.val (loopTransport χ n.succPNat ℓ γ ψ)
                n.succPNat ℓ γ (anchorVector (WithLp.ofLp y)) i.succ
          let d := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
            gradLoop s.val (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
                (anchorVector (WithLp.ofLp y)) *
              fderiv ℝ (fun z => loopCutoff s.val γ ε n.succPNat ℓ (anchorVector z))
                (WithLp.ofLp y) (Pi.single i (1 : ℝ))
          ∃ hv : MemLp v 2 (anchoredMeasureE Q),
            ∃ hw : MemLp w 2 (anchoredMeasureE Q),
              ∃ hd : MemLp d 2 (anchoredMeasureE Q),
                anchoredInverseEnergy Q
                  (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
                  (hv.toLp v + hw.toLp w + hd.toLp d) ≤
                    C * K ^ (κ * ε) * (K + K ^ (2 * (1 - s.val + α))) := by
  have hγ1 : 1 < γ := by have := (le_max_left _ _).trans hγ; linarith
  obtain ⟨εv, κv, hεv, hκv, hvbound⟩ := varAl_singular hBE hPL s hα hα2 hγ
  obtain ⟨κw, hκw, hwbound⟩ := varAl_gap hBE hPL s.property.1 s.property.2 hα hα2 hγ1
  let εw := min (1 / 8 : ℝ) ((1 - s.val / 2) / 8)
  have hεw : 0 < εw := lt_min (by norm_num) (by linarith [s.property.2])
  refine ⟨min εv εw, κv + κw, lt_min hεv hεw, add_pos hκv hκw, ?_⟩
  intro β hβ C₀ hC₀ χ hχ hχc hχs hχ1 hχ01 ε hε hεstar
  obtain ⟨Cv, hCv, hvC⟩ := hvbound β hβ C₀ hC₀ χ hχ hχc hχs hχ1 hχ01 ε hε
    (hεstar.trans_le (min_le_left _ _))
  obtain ⟨Cw, hCw, hwC⟩ := hwbound β hβ C₀ hC₀ χ hχ hχc hχs hχ1 hχ01 ε hε
    (hεstar.trans_le (min_le_right _ _))
  refine ⟨4 * Cv + 6 * Cw, by positivity, ?_⟩
  intro n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  obtain ⟨hv, hvE⟩ := hvC n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  obtain ⟨hw, hd, hwE, hdE⟩ := hwC n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  refine ⟨hv, hw, hd, ?_⟩
  let P : Parameters := ⟨(β, s.val), hβ, s.property⟩
  let K := (n.succPNat : ℝ) * ℓ
  let Q := nearestTiltedPairs P n.succPNat hθ K (2 * γ) ε (by linarith : 0 < K)
  have hq : 0 ≤ (κv + κw) * ε := mul_nonneg (add_pos hκv hκw).le hε.le
  have hmono (q : ℝ) (hq' : q ≤ κv + κw) :
      K ^ (q * ε) ≤ K ^ ((κv + κw) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hK (mul_le_mul_of_nonneg_right hq' hε.le)
  have hvE' := hvE.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hmono κv (by linarith)) hCv.le) (by positivity))
  have hwE' := hwE.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hmono κw (by linarith)) hCw.le) (by positivity))
  have hsplit := (anchoredInverse_symmetry_positivity_subadditivity Q
    (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))).2.2.2.2
      (hv.toLp _) (hw.toLp _) (hd.toLp _)
  have hfinal := Internal.varAlLoop_combine_energies hK hq hCw.le hsplit hvE' hwE' hdE
  convert hfinal using 1; ring

end Riesz1

end
