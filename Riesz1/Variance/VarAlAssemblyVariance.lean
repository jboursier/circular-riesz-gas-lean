/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblyGradient
public import Riesz1.Variance.VarAlLoopEnergy
public import Riesz1.Variance.APrioriComparisonAdmissible

/-!
# The convexified cutoff-loop variance estimate

Proposition 5.9, equation (5.28) and its energy bound.
Sobolev membership is proved for the actual function and fields.
The coefficient is chosen before the transport, particle number and scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

theorem varAlAssembly_variance_eq_energy {n : ℕ} {c : ℝ}
    (Q : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hPL : External.PrekopaLeindler) (hn : 0 < n) {C : ℝ} (hadm : HsAdmissible Q C)
    {F : AnchoredEuclidean n → ℝ} {v w d : AnchoredEuclidean n → AnchoredEuclidean n}
    (hv : MemLp v 2 (anchoredMeasureE Q)) (hw : MemLp w 2 (anchoredMeasureE Q))
    (hd : MemLp d 2 (anchoredMeasureE Q))
    (hH : IsAnchoredH1 Q F (fun y => v y + w y + d y)) :
    ProbabilityTheory.variance F (anchoredMeasureE Q) =
      anchoredInverseEnergy Q hc (hv.toLp v + hw.toLp w + hd.toLp d) := by
  have := isProbabilityMeasure_anchoredMeasureE Q hc
  have hg : MemLp (fun y => v y + w y + d y) 2 (anchoredMeasureE Q) := (hv.add hw).add hd
  let S : AnchoredSobolev Q := ⟨(hH.1.toLp F, hg.toLp _),
    WeightedSobolev.IsWeightedH1.congr hH hH.1.coeFn_toLp.symm hg.coeFn_toLp.symm⟩
  have hgrad : S.val.2 = hv.toLp v + hw.toLp w + hd.toLp d := by
    change ((hv.add hw).add hd).toLp _ = _
    rw [(hv.add hw).toLp_add hd, hv.toLp_add hw]
  calc
    _ = ProbabilityTheory.variance S.val.1 (anchoredMeasureE Q) :=
      ProbabilityTheory.variance_congr hH.1.coeFn_toLp.symm
    _ = _ := by rw [anchored_variance_eq_inverseEnergy Q hc hPL hn hadm S, hgrad]

end Riesz1.Internal

namespace Riesz1

/-- Proposition 5.9, the complete convexified anchored cutoff-loop
bound, uniformly over all transports satisfying the two envelopes. -/
theorem varAl_loop_variance_convexified
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
          let F := fun y : AnchoredEuclidean n =>
            loopCutoffF χ s.val γ ε n.succPNat ℓ ψ (anchorVector (WithLp.ofLp y))
          ∃ _hF : MemLp F 2 (anchoredMeasureE Q),
            ProbabilityTheory.variance F (anchoredMeasureE Q) ≤
              C * K ^ (κ * ε) * (K + K ^ (2 * (1 - s.val + α))) := by
  obtain ⟨εE, κ, hεE, hκ, hbound⟩ := varAlLoop_three_fields_energy hBE hPL s hα hα2 hγ
  have hγ1 : 1 ≤ γ := by have := (le_max_left _ _).trans hγ; linarith
  refine ⟨min εE (1 - s.val / 2), κ,
    lt_min hεE (by linarith [s.property.2]), hκ, ?_⟩
  intro β hβ C₀ hC₀ χ hχ hχc hχs hχ1 hχ01 ε hε hεstar
  obtain ⟨C, hC, hE⟩ := hbound β hβ C₀ hC₀ χ hχ hχc hχs hχ1 hχ01 ε hε
    (hεstar.trans_le (min_le_left _ _))
  refine ⟨C, hC, ?_⟩
  intro n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  obtain ⟨hv, hw, hd, he⟩ := hE n hn θ hθ ℓ hℓ hℓ1 hK ψ hψ hp h1 h2
  let P : Parameters := ⟨(β, s.val), hβ, s.property⟩
  let K := (n.succPNat : ℝ) * ℓ
  let Q := nearestTiltedPairs P n.succPNat hθ K (2 * γ) ε (by linarith : 0 < K)
  have hmem := varAlAssembly_loopCutoffF_h1 Q
    (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P)) hn
    s.property.1 s.property.2 hγ1 hε.le
    (hεstar.trans_le (min_le_right _ _)).le hℓ hK hχ hχs hψ hp
  obtain ⟨D, hadm⟩ := APrioriComparison.nearestTiltedPairs_admissible P n.succPNat
    (by simpa using hn) hθ K (2 * γ) ε (by linarith)
  refine ⟨hmem.1, ?_⟩
  rw [Internal.varAlAssembly_variance_eq_energy Q
    (hsRieszPairPotentials_curvature_pos n.succPNat P.2.1 (parametersExponent P))
    hPL (by omega) hadm hv hw hd hmem]
  exact he

end Riesz1

end
