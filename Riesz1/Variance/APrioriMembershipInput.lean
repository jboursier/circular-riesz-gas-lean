/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffField
public import Riesz1.HelfferSjostrand.AnchoredLawSobolev

/-!
# The completion-membership obligation in the a priori argument

This internal proposition records only membership of the literal cutoff
product, together with its literal product-rule gradient, in the
Sobolev completion. It assumes no energy estimate or variance conclusion.
Intermediate results in the proof of Lemma 5.2 take it as an explicit hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory InnerProductSpace

namespace Riesz1.Internal

/-- Cutoff products of localized `C¹` statistics belong to the actual
anchored Sobolev completion, under the actual nearest-neighbour tilt.
The cutoff-gradient term uses `anchoredCutoffField`, whose
coordinates are defined by the differential on the original carrier. -/
def APrioriMembershipInput : Prop :=
  ∀ (P : Parameters) (n : ℕ), 1 ≤ n →
    ∀ (θ : ℝ → ℝ) (hθ : IsForcingCutoff θ) (ℓ : ℝ), 0 < ℓ →
    ∀ hK : 1 ≤ ((n : ℝ) + 1) * ℓ,
    ∀ γ ε : ℝ, 1 < γ → 0 < ε →
    ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
    let K := ((n : ℝ) + 1) * ℓ
    let χ := nearestTiltedPairs P n.succPNat hθ K γ ε (by linarith)
    let F := fun y : Fin n → ℝ =>
      ∑ j ∈ window n.succPNat K γ, f (anchorVector y j / ℓ)
    let η := fun y : AnchoredEuclidean n =>
      anchoredCutoff n.succPNat P.val.2 K γ ε (WithLp.ofLp y)
    IsAnchoredH1 χ (fun y => η y * F (WithLp.ofLp y))
      (fun y => η y • gradient (fun z => F (WithLp.ofLp z)) y +
        anchoredCutoffField n P.val.2 K γ ε F y)

end Riesz1.Internal

end
