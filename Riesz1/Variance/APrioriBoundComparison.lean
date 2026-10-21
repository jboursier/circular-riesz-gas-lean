/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriBoundInput
public import Riesz1.Variance.APrioriComparisonLemma

/-!
# Discharging the comparison input

The full comparison lemma (the comparison part of Lemma 5.2) implies the proposition used by
the a priori bound. The Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler` are explicit hypotheses. The comparison is proved here.
-/

public section

open MeasureTheory

namespace Riesz1.Internal

/-- The comparison input follows from the complete comparison lemma, with threshold
`ε₀ = 1`. -/
theorem a_priori_comparison_input (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) : APrioriComparisonInput := by
  intro P lam γ hlam hγ
  obtain ⟨κ, hκ, hsum, henergy⟩ := a_priori_comparison hBE hPL P lam γ hlam hγ
  refine ⟨κ, 1, hκ, zero_lt_one, ?_, ?_⟩
  · intro ε hε hε1
    obtain ⟨C, hC, hb⟩ := hsum ε hε hε1
    exact ⟨C, hC, fun n _ K hK _ J hJ => hb n.succPNat K hK J hJ⟩
  · intro a ha
    obtain ⟨κ₁, hκ₁, hb⟩ := henergy a ha
    refine ⟨κ₁, hκ₁, ?_⟩
    intro ε hε hε1 M hM
    obtain ⟨C, hC, hc⟩ := hb ε hε hε1 M hM
    refine ⟨C, hC, ?_⟩
    intro n hn θ hθ K hK _ J hJ w hw
    dsimp only
    intro v hvm hz hv
    apply hc n hn θ hθ K hK J hJ w hw v hvm
    · exact fun i => hz.mono fun _ hy => hy i
    · intro i
      filter_upwards [hv] with y hy
      simpa only [mul_assoc] using hy i

end Riesz1.Internal
