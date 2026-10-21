/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Unconditional.LoopMoments
public import Riesz1.Unconditional.LoopMomentsArcsNull

/-!
# Moments of counts and discrepancies on arcs of every endpoint type

The moment bounds of Lemma 5.8, for every deterministic arc `J` of length `r ≤ N`: the open,
closed and half-open arcs alike. The theorem `Riesz1.auxiliary_Loop_moments` covers open arcs
`microArc N a r` only, and this file extends it to every `J` with `IsMicroArc N r J`.

The main theorem is `Riesz1.auxiliary_Loop_moments_arcs`. Its constants are those of
`Riesz1.auxiliary_Loop_moments`, chosen before `N` and the arc. A deterministic arc of length
`r` and the open arc with the same endpoints differ at most in their two endpoint images, which
are almost surely unoccupied (`IsMicroArc.exists_ae_agree`). Hence every count, energy sum and
discrepancy on `J` equals its open counterpart almost surely, and the `L^p` norms agree.

The externals `hBE` and `hPL` enter only through `Riesz1.auxiliary_Loop_moments`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- Counts on an arc `J` and on the open arc `microArc N a r` agree at a configuration whose particles
have the same membership in both. -/
theorem arcLoopCount_eq_of_agree {N : ℕ+} {J K : Set (AddCircle (N : ℝ))} {X : Configuration N}
    (h : ∀ i : Fin (N : ℕ), loopPos X i ∈ J ↔ loopPos X i ∈ K) :
    arcLoopCount J X = arcLoopCount K X := by
  unfold arcLoopCount
  exact Finset.sum_congr rfl fun i _ => by simp only [h i]

/-- The energy sums over particles in an arc `J` and in an arc `K` agree at a configuration whose
particles have the same membership in both. -/
theorem energy_sum_eq_of_agree {N : ℕ+} (s : ℝ) {J K : Set (AddCircle (N : ℝ))}
    {X : Configuration N} (h : ∀ i : Fin (N : ℕ), loopPos X i ∈ J ↔ loopPos X i ∈ K) :
    ∑ i : Fin (N : ℕ), (if loopPos X i ∈ J then rootedEnergy s X i else 0) =
      ∑ i : Fin (N : ℕ), (if loopPos X i ∈ K then rootedEnergy s X i else 0) :=
  Finset.sum_congr rfl fun i _ => by simp only [h i]

/-- The discrepancy on an arc `J` equals the discrepancy on the open arc `microArc N a r` at a
configuration whose particles have the same membership in both, when the two arcs have the same
Haar measure. -/
theorem arcLoopDiscrepancy_eq_of_agree {N : ℕ+} {J : Set (AddCircle (N : ℝ))} {a r : ℝ}
    {X : Configuration N} (hvol : volume J = volume (microArc N a r))
    (h : ∀ i : Fin (N : ℕ), loopPos X i ∈ J ↔ loopPos X i ∈ microArc N a r) :
    arcLoopDiscrepancy J X = loopDiscrepancy a r X := by
  unfold arcLoopDiscrepancy loopDiscrepancy
  rw [hvol, arcLoopCount_eq_of_agree h]
  rfl

/-- The moment bounds of Lemma 5.8, for every deterministic arc `J` of length `r`, with the
externals `hBE` and `hPL` as hypotheses. The four conclusions are those of the theorem
`Riesz1.auxiliary_Loop_moments`, with the open arc `microArc N a r` replaced by `J`:

* the count `M_J` of particles on `J` has `L^p` norm at most `C (1 + r)`, for `N ≥ 2`, `0 < r ≤ N`.
* the rooted energies `E_i` have bounded `L^p` norm, for every label `i`.
* for `r ≤ 3`, the sum of `E_i` over the particles on `J` has bounded `L^p` norm.
* for `0 < δ < min (s / 2) ε₀`, the discrepancy `ν(J) = M_J - |J|` on an arc with `1 ≤ r ≤ N / 2` has
  `L^p` norm at most `C r^(s/2 + δ)`, and the block deviation `S_{i,k} - k` has `L^p` norm at most
  `C k^(s/2 + δ)`.

The constant `ε₀` and the constants `C` are those of `Riesz1.auxiliary_Loop_moments`. -/
theorem auxiliary_Loop_moments_arcs (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+),
        2 ≤ (N : ℕ) → ∀ (r : ℝ) (J : Set (AddCircle (N : ℝ))), 0 < r → r ≤ N →
          IsMicroArc N r J →
          eLpNorm (fun X : Configuration N => arcLoopCount J X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (1 + r))) ∧
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (i : Fin (N : ℕ)),
        eLpNorm (fun X : Configuration N => rootedEnergy s X i) (ENNReal.ofReal p)
          (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤ ENNReal.ofReal C) ∧
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+),
        2 ≤ (N : ℕ) → ∀ (r : ℝ) (J : Set (AddCircle (N : ℝ))), 0 < r → r ≤ 3 → r ≤ N →
          IsMicroArc N r J →
          eLpNorm (fun X : Configuration N => ∑ i : Fin (N : ℕ),
            if loopPos X i ∈ J then rootedEnergy s X i else 0) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤ ENNReal.ofReal C) ∧
    (∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      (∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (r : ℝ) (J : Set (AddCircle (N : ℝ))), 1 ≤ r → r ≤ (N : ℝ) / 2 →
          IsMicroArc N r J →
          eLpNorm (fun X : Configuration N => arcLoopDiscrepancy J X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * r ^ (s / 2 + δ))) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
          eLpNorm (fun X : Configuration N => blockLength X (i : ℕ) k - k) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ)))) := by
  obtain ⟨hA, hB, hC, hD⟩ := auxiliary_Loop_moments hBE hPL beta s hbeta hs hs1
  refine ⟨fun p hp => ?_, hB, fun p hp => ?_, ?_⟩
  · obtain ⟨C, hC', h⟩ := hA p hp
    refine ⟨C, hC', fun N hN r J hr hrN hJ => ?_⟩
    obtain ⟨a, -, hae⟩ := IsMicroArc.exists_ae_agree (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) hJ
    refine (eLpNorm_congr_ae ?_).trans_le (h N hN a r hr hrN)
    filter_upwards [hae] with X hX
    exact arcLoopCount_eq_of_agree hX
  · obtain ⟨C, hC', h⟩ := hC p hp
    refine ⟨C, hC', fun N hN r J hr hr3 hrN hJ => ?_⟩
    obtain ⟨a, -, hae⟩ := IsMicroArc.exists_ae_agree (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) hJ
    refine (eLpNorm_congr_ae ?_).trans_le (h N hN a r hr hr3 hrN)
    filter_upwards [hae] with X hX
    exact energy_sum_eq_of_agree s hX
  · obtain ⟨eps0, heps0, h⟩ := hD
    refine ⟨eps0, heps0, fun δ hδ hδs p hp => ?_⟩
    obtain ⟨⟨C₁, hC₁, h₁⟩, ⟨C₂, hC₂, h₂⟩⟩ := h δ hδ hδs p hp
    refine ⟨⟨C₁, hC₁, fun N hN r J hr hrN hJ => ?_⟩, ⟨C₂, hC₂, h₂⟩⟩
    obtain ⟨a, hvol, hae⟩ := IsMicroArc.exists_ae_agree (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) hJ
    refine (eLpNorm_congr_ae ?_).trans_le (h₁ N hN a r hr hrN)
    filter_upwards [hae] with X hX
    exact arcLoopDiscrepancy_eq_of_agree hvol hX

end Riesz1

end
end
