/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Configuration
public import Riesz1.Auxiliary.LoopCutoffInvariance
public import Riesz1.Auxiliary.GradientSplittingGapIdentity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Regularity of the anchored cutoff

The cutoff from the cutoff data part of Lemma 5.8 is locally Lipschitz on the
ordered lift domain and Lipschitz on every compact subset of that domain. The reciprocal
gap factors are considered only at positive gaps.
-/

public section

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace Riesz1

private lemma local_mul {A : Type*} [PseudoEMetricSpace A] {f g : A → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => f x * g x) := by
  have h : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * p.2) :=
    contDiff_fst.mul contDiff_snd
  exact h.locallyLipschitz.comp (hf.prodMk hg)

private lemma local_prod {A ι : Type*} [PseudoEMetricSpace A] (S : Finset ι)
    (f : ι → A → ℝ) (hf : ∀ i ∈ S, LocallyLipschitz (f i)) :
    LocallyLipschitz (fun x => ∏ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using (LocallyLipschitz.const (1 : ℝ) : LocallyLipschitz (fun _ : A => (1 : ℝ)))
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact local_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private lemma local_restrict {d : ℕ} {S : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ}
    (hf : ∀ x ∈ S, ContDiffAt ℝ 1 f x) : LocallyLipschitz (fun x : S => f x.val) := by
  apply locallyLipschitzOn_iff_restrict.mp
  intro x hx
  obtain ⟨K, U, hU, hK⟩ := (hf x hx).exists_lipschitzOnWith
  exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hK⟩

private lemma smooth_lift (N : ℕ+) (j : ℤ) :
    ContDiff ℝ 1 (fun X : Fin (N : ℕ) → ℝ => gradLift N X j) := by
  unfold gradLift
  exact (contDiff_apply ℝ (fun _ : Fin (N : ℕ) => ℝ) (gradIndex N j)).add contDiff_const

private lemma local_profile : LocallyLipschitz cutoffC := by
  have h : ContDiff ℝ 1 (fun r : ℝ => 2 - r) := contDiff_const.sub contDiff_id
  exact (LocallyLipschitz.const 1).min ((LocallyLipschitz.const 0).max h.locallyLipschitz)

/-- The cutoff data part of Lemma 5.8: local Lipschitz continuity of `η`.
No rigidity or restrictions on the cutoff exponents are needed. -/
theorem loopCutoff_locallyLipschitzOn (s γ ε : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    LocallyLipschitzOn (orderedDomain N) (loopCutoff s γ ε N ℓ) := by
  classical
  apply locallyLipschitzOn_iff_restrict.mpr
  have hK : 0 < (N : ℝ) * ℓ := mul_pos (by exact_mod_cast N.pos) hℓ
  have hlift (j : ℤ) := smooth_lift N j
  have hp (i k : ℤ) : LocallyLipschitz (fun X : Configuration N =>
      cutoffC (2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
        (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2)))) := by
    have ha : ContDiff ℝ 1 (fun X : Fin (N : ℕ) → ℝ =>
        (N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k) :=
      (contDiff_const.mul ((hlift _).sub (hlift _))).sub contDiff_const
    have hb : ContDiff ℝ 1 (fun r : ℝ =>
        2 * r / (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))) :=
      (contDiff_const.mul contDiff_id).div_const _
    exact local_profile.comp (hb.locallyLipschitz.comp
      ((lipschitzWith_one_norm : LipschitzWith 1 (fun x : ℝ => |x|)).locallyLipschitz.comp (local_restrict fun X _ => ha.contDiffAt)))
  have he (i : ℤ) : LocallyLipschitz (fun X : Configuration N =>
      cutoffC (2 * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)) /
        ((N : ℝ) * ℓ) ^ ε) *
      cutoffC (2 / (((N : ℝ) * ℓ) ^ ε *
        ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i))))) := by
    have ha : ContDiff ℝ 1 (fun X : Fin (N : ℕ) → ℝ =>
        2 * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i)) /
          ((N : ℝ) * ℓ) ^ ε) := by
      exact (contDiff_const.mul (contDiff_const.mul ((hlift _).sub (hlift _)))).div_const _
    have hb : ∀ X ∈ orderedDomain N, ContDiffAt ℝ 1
        (fun X : Fin (N : ℕ) → ℝ => 2 / (((N : ℝ) * ℓ) ^ ε *
          ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i)))) X := by
      intro X hX
      apply contDiffAt_const.div
        (contDiffAt_const.mul (contDiffAt_const.mul ((hlift _).contDiffAt.sub (hlift _).contDiffAt)))
      exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos hK _)
        (mul_pos (by exact_mod_cast N.pos) (sub_pos.mpr (gradLift_lt_succ hX i))))
    exact local_mul (local_profile.comp (local_restrict fun X _ => ha.contDiffAt))
      (local_profile.comp (local_restrict hb))
  unfold loopCutoff
  apply local_mul
  · apply local_prod
    intro i _
    apply local_prod
    intro k _
    by_cases h : k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k)
    · simpa only [ite_eq_left h] using hp i k
    · simp only [ite_eq_right h]
      exact LocallyLipschitz.const 1
  · apply local_prod
    intro i _
    by_cases h : gradInWindow N ℓ (2 * γ) (i + 1)
    · simpa only [ite_eq_left h] using he i
    · simp only [ite_eq_right h]
      exact LocallyLipschitz.const 1

/-- The cutoff data part of Lemma 5.8: `η` is Lipschitz on every compact subset
of the ordered domain. The Lipschitz bound may depend on that compact subset. -/
theorem loopCutoff_lipschitzOn_compact (s γ ε : ℝ) (N : ℕ+) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {S : Set (Fin (N : ℕ) → ℝ)} (hS : IsCompact S) (hSD : S ⊆ orderedDomain N) :
    ∃ C : ℝ≥0, LipschitzOnWith C (loopCutoff s γ ε N ℓ) S :=
  ((loopCutoff_locallyLipschitzOn s γ ε N hℓ).mono hSD).exists_lipschitzOnWith_of_compact hS

end Riesz1

end
