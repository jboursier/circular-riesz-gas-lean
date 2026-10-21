/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblyFactors
public import Riesz1.Variance.VarAlGapCutoffBridge

/-!
# Anchored Sobolev membership of the good-event cutoff

Every actual scalar factor is in the completed graph. The reciprocal
factors are identified on the positive-gap domain with the clamped
construction, so their total values outside that domain are irrelevant.
This proves membership of the cutoff itself, not of the singular loop
multiplied by it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace Riesz1.Internal

variable {n : ℕ} {c : ℝ} (Q : HsPairPotentials n.succPNat c) (hc : 0 < c)

include hc

theorem varAlAssembly_anchored_pair_factor (s K γ ε : ℝ) (hK : 0 < K)
    (p : Fin (n.succPNat : ℕ) × ℤ)
    (hp : p ∈ cutoffPairs n.succPNat (window n.succPNat K γ)) :
    let F := fun y : AnchoredEuclidean n => scalarCutoff
      (2 * |gapPairDev n.succPNat (anchoredGapVector n (WithLp.ofLp y)) p| / pairScale s K ε p)
    IsAnchoredH1 Q F (gradient F) ∧
      ∀ᵐ y ∂anchoredMeasureE Q, DifferentiableAt ℝ F y := by
  have hF : ContDiff ℝ ∞ (fun y : AnchoredEuclidean n =>
      gapPairDev n.succPNat (anchoredGapVector n (WithLp.ofLp y)) p) := by
    have heq : (fun y : AnchoredEuclidean n =>
        gapPairDev n.succPNat (anchoredGapVector n (WithLp.ofLp y)) p) =
        fun y => (((n : ℝ) + 1) •
          (anchorCoord n (labelOf n.succPNat (((p.1 : ℕ) : ℤ) + p.2)) - anchorCoord n p.1))
          (WithLp.ofLp y) +
          (((n : ℝ) + 1) * (((((p.1 : ℕ) : ℤ) + p.2) / (n.succPNat : ℕ) : ℤ) : ℝ) - p.2) :=
      funext fun y => gapPairDev_anchoredGapVector n (WithLp.ofLp y) p
    rw [heq]
    exact (((((n : ℝ) + 1) •
      (anchorCoord n (labelOf n.succPNat (((p.1 : ℕ) : ℤ) + p.2)) - anchorCoord n p.1)).contDiff).comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).contDiff).add contDiff_const
  exact varAlAssembly_pair_factor Q hc hF (fun t => varAlAssembly_pair_ne Q hp t)
    (pairScale_pos_of_mem_cutoffPairs hK hp)

theorem varAlAssembly_anchored_near_factor (hn : 1 ≤ n) (K ε : ℝ)
    (hκ : 1 ≤ K ^ ε) (e : Fin (n.succPNat : ℕ)) :
    let F := fun y : AnchoredEuclidean n =>
      scalarCutoff (2 * anchoredGapVector n (WithLp.ofLp y) e / K ^ ε) *
        scalarCutoff (2 / (K ^ ε * anchoredGapVector n (WithLp.ofLp y) e))
    IsAnchoredH1 Q F (gradient F) ∧
      ∀ᵐ y ∂anchoredMeasureE Q, DifferentiableAt ℝ F y := by
  have hF : ContDiff ℝ ∞ (fun y : AnchoredEuclidean n =>
      anchoredGapVector n (WithLp.ofLp y) e) := by
    have he : (fun y : AnchoredEuclidean n => anchoredGapVector n (WithLp.ofLp y) e) =
        fun y => ((n : ℝ) + 1) * (edgeForm n e (WithLp.ofLp y) + wrapOffset n e) :=
      funext fun y => anchoredGapAt_label n (WithLp.ofLp y) e
    rw [he]
    exact contDiff_const.mul (((edgeForm n e).contDiff.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).contDiff).add contDiff_const)
  have hpos : ∀ᵐ y ∂anchoredMeasureE Q, 0 < anchoredGapVector n (WithLp.ofLp y) e := by
    filter_upwards [ae_mem_anchoredSimplex Q] with y hy
    let X : Configuration n.succPNat := ⟨anchorVector (WithLp.ofLp y), varAl_anchorVector_mem hy⟩
    rw [← vectorGap_anchoredLift_eq, anchoredLift_eq_anchorVector]
    exact gap_pos X (e : ℕ)
  exact varAlAssembly_nearest_factor Q hc hF hpos (fun t => varAlAssembly_gap_ne Q hn e t) hκ

theorem varAlAssembly_anchoredCutoff_h1 (hn : 1 ≤ n) (s K γ ε : ℝ)
    (hK : 1 ≤ K) (hε : 0 ≤ ε) :
    IsAnchoredH1 Q (fun y => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y))
      (gradient (fun y => anchoredCutoff n.succPNat s K γ ε (WithLp.ofLp y))) := by
  classical
  let N := n.succPNat
  let μ := anchoredMeasureE Q
  let I := cutoffPairs N (window N K γ)
  let J := nearestPairs N (window N K γ)
  let A := fun (p : Fin (N : ℕ) × ℤ) (y : AnchoredEuclidean n) =>
    scalarCutoff (2 * |gapPairDev N (anchoredGapVector n (WithLp.ofLp y)) p| / pairScale s K ε p)
  let B := fun (e : Fin (N : ℕ)) (y : AnchoredEuclidean n) =>
    scalarCutoff (2 * anchoredGapVector n (WithLp.ofLp y) e / K ^ ε) *
      scalarCutoff (2 / (K ^ ε * anchoredGapVector n (WithLp.ofLp y) e))
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hpair (p : Fin (N : ℕ) × ℤ) (hp : p ∈ I) :
      IsAnchoredH1 Q (A p) (gradient (A p)) ∧
        ∀ᵐ y ∂μ, DifferentiableAt ℝ (A p) y := by
    exact varAlAssembly_anchored_pair_factor Q hc s K γ ε hK0 p hp
  have hnear (e : Fin (N : ℕ)) :
      IsAnchoredH1 Q (B e) (gradient (B e)) ∧
        ∀ᵐ y ∂μ, DifferentiableAt ℝ (B e) y := by
    exact varAlAssembly_anchored_near_factor Q hc hn K ε (Real.one_le_rpow hK hε) e
  have hAbound (p : Fin (N : ℕ) × ℤ) (_hp : p ∈ I) (y : AnchoredEuclidean n) :
      A p y ∈ Icc (0 : ℝ) 1 := ⟨scalarCutoff_nonneg _, scalarCutoff_le_one _⟩
  have hBbound (e : Fin (N : ℕ)) (_he : e ∈ J) (y : AnchoredEuclidean n) :
      B e y ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (scalarCutoff_nonneg _) (scalarCutoff_nonneg _), ?_⟩
    exact (mul_le_mul_of_nonneg_right (scalarCutoff_le_one _) (scalarCutoff_nonneg _)).trans
      (by simpa only [one_mul] using scalarCutoff_le_one _)
  obtain ⟨hA, hdA, hbA⟩ := varAlAssembly_prod_bundle Q hc I A hpair hAbound
  obtain ⟨hB, hdB, hbB⟩ := varAlAssembly_prod_bundle Q hc J B (fun e _ => hnear e) hBbound
  have hfinal := varAlAssembly_mul_classical Q hc hA hB hdA hdB zero_le_one zero_le_one
    (Eventually.of_forall fun y => by rw [abs_of_nonneg (hbA y).1]; exact (hbA y).2)
    (Eventually.of_forall fun y => by rw [abs_of_nonneg (hbB y).1]; exact (hbB y).2)
  rw [anchoredCutoff_eq_comp_gapVector]
  exact hfinal

end Riesz1.Internal

namespace Riesz1

/-- Proposition 5.9, domain preparation: the actual loop cutoff
belongs to the anchored Sobolev completion with its classical gradient.
This includes all `K ≥ 1` and every nonnegative cutoff exponent. -/
theorem varAlAssembly_loopCutoff_h1 {n : ℕ} {c : ℝ}
    (Q : HsPairPotentials n.succPNat c) (hc : 0 < c) (hn : 1 ≤ n)
    (s γ ε ℓ : ℝ) (hK : 1 ≤ (n.succPNat : ℝ) * ℓ) (hε : 0 ≤ ε) :
    IsAnchoredH1 Q
      (fun y => loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)))
      (gradient (fun y => loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)))) := by
  have h := Internal.varAlAssembly_anchoredCutoff_h1 Q hc hn s
    ((n.succPNat : ℝ) * ℓ) (2 * γ) ε hK hε
  have heq {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) :
      loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) =
        anchoredCutoff n.succPNat s ((n.succPNat : ℝ) * ℓ) (2 * γ) ε (WithLp.ofLp y) :=
    varAlGap_loopCutoff_eq_anchoredCutoff hn hK s ε hy
  apply h.congr
  · filter_upwards [ae_mem_anchoredSimplex Q] with y hy
    exact (heq hy).symm
  · filter_upwards [ae_mem_anchoredSimplex Q] with y hy
    have hev : (fun z : AnchoredEuclidean n =>
        loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp z))) =ᶠ[𝓝 y]
        (fun z => anchoredCutoff n.succPNat s ((n.succPNat : ℝ) * ℓ) (2 * γ) ε (WithLp.ofLp z)) := by
      filter_upwards [(isOpen_anchoredSimplex n).mem_nhds hy] with z hz
      exact heq hz
    exact congrArg (InnerProductSpace.toDual ℝ (AnchoredEuclidean n)).symm hev.fderiv_eq.symm

end Riesz1

end
