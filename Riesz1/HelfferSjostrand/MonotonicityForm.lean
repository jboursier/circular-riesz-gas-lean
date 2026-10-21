/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredInverse

/-!
# Coordinates and algebra of the anchored vector form

Supporting facts for Lemma 3.4, anchored part. The
value vector `(u_1, …, u_n)` of an element of `𝒱_μ` has as its `i`-th coordinate the `i`-th
scalar value of the element, almost everywhere. The anchored vector form `q_μ` is additive in
its first argument and symmetric.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The `i`-th coordinate of the value vector of `w ∈ 𝒱_μ` is the `i`-th scalar value of `w`,
almost everywhere. -/
theorem anchoredVectorValues_coord_ae (χ : HsPairPotentials n.succPNat c)
    (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ] (w : AnchoredVectorSobolev χ μ)
    (i : Fin n) :
    (fun y => anchoredVectorValues μ χ w y i) =ᵐ[μ]
      fun y => (anchoredJetValue μ i (w : Lp (AnchoredJetPoint n) 2 μ) :
        AnchoredEuclidean n → ℝ) y := by
  have hv : anchoredVectorValues μ χ w = anchoredInverseValues μ (w : Lp (AnchoredJetPoint n) 2 μ) :=
    rfl
  rw [hv]
  unfold anchoredInverseValues anchoredJetValue
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (WithLp.fstL 2 ℝ (AnchoredEuclidean n) (AnchoredJetPair n)) (w : Lp (AnchoredJetPoint n) 2 μ),
    ContinuousLinearMap.coeFn_compLpL (jetValueL i) (w : Lp (AnchoredJetPoint n) 2 μ)]
    with y h1 h2
  rw [h1, h2]
  rfl

/-- The anchored vector form is additive in its first argument. -/
theorem anchoredVectorSobolevForm_sub_left (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (Ψ Φ Θ : Lp (AnchoredJetPoint n) 2 μ) :
    anchoredVectorSobolevForm μ (Ψ - Φ) Θ =
      anchoredVectorSobolevForm μ Ψ Θ - anchoredVectorSobolevForm μ Φ Θ := by
  unfold anchoredVectorSobolevForm
  simp only [map_sub, inner_sub_left, Finset.sum_sub_distrib]
  ring

/-- The anchored vector form is symmetric. -/
theorem anchoredVectorSobolevForm_comm (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]
    (Ψ Φ : Lp (AnchoredJetPoint n) 2 μ) :
    anchoredVectorSobolevForm μ Ψ Φ = anchoredVectorSobolevForm μ Φ Ψ := by
  unfold anchoredVectorSobolevForm
  congr 1
  · exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  · exact real_inner_comm _ _

end Riesz1

end
