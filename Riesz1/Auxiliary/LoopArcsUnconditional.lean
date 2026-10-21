/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCrude
public import Riesz1.Rigidity.RigidityTheorem

/-!
# Arc representation and crude loop bounds with explicit external inputs

The arcs and crude parts of Lemma 5.8.
Rigidity is supplied through the external inputs `External.BakryEmery` and
`External.PrekopaLeindler`. The tests may be any periodic `C¹`
functions, and the crude bound includes the one-particle case.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The arcs part of Lemma 5.8: integrability, the exact arc identity,
and uniform cell moments, with constants chosen before the particle number. -/
theorem auxiliary_Loop_arcs
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {beta s : ℝ} (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (b : ℝ → ℝ), ContDiff ℝ 1 b → Function.Periodic b (N : ℝ) →
        ∀ (m : ℕ), m < N →
          (∀ X : Configuration N, IntegrableOn (fun t => loopArcLambda s N X t)
            (Ioc (0 : ℝ) N)) ∧
          (∀ X : Configuration N, loopArcL s N b X =
            -2 * ∫ t in (0 : ℝ)..(N : ℝ), deriv b t * loopArcLambda s N X t) ∧
          eLpNorm (fun X : Configuration N =>
            ∫ t in Ioc (m : ℝ) ((m : ℝ) + 1), |loopArcLambda s N X t|)
            (ENNReal.ofReal p) (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N)
            ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, h⟩ := loopArc_complete_of_rigidity hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) hp
  exact ⟨C, hC, h hPL⟩

/-- The crude part of Lemma 5.8, including `N = 1`, with a strictly
positive constant and only the Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler` as additional inputs. -/
theorem auxiliary_Loop_crude
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    {beta s : ℝ} (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (b : ℝ → ℝ),
      ContDiff ℝ 1 b → Function.Periodic b (N : ℝ) →
        eLpNorm (fun X : Configuration N => loopArcL s N b X) (ENNReal.ofReal p)
          (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
          ENNReal.ofReal (C * ∑ m ∈ Finset.range (N : ℕ),
            sSup ((fun z => |deriv b z|) '' Icc (m : ℝ) ((m : ℝ) + 1))) := by
  obtain ⟨C, hC, h⟩ := loopArc_crude_of_rigidity hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) hp
  refine ⟨C + 1, by linarith, fun N b hb hp => (h hPL N b hb hp).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by linarith)
    (Finset.sum_nonneg fun m _ => cellSup_nonneg b m)

end Riesz1

end
