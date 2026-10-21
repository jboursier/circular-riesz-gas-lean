/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlTransferBounds
public import Riesz1.Variance.VarAlLoopDifferential

/-!
# Selected collisions are excluded on the relative cutoff support

The larger-window good event is closed in the ambient anchored chart.
Its lower gap bounds exclude zero separation. Its partial-window
upper bound and full-window complementary arc bound exclude winding
collisions. No strict ordering of the other particles is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace Riesz1.Internal

theorem varAlAssembly_coe_ne_zero_of_abs {r : ℝ} (h0 : 0 < |r|) (h1 : |r| < 1) :
    (r : UnitAddCircle) ≠ 0 := by
  apply coe_ne_zero_of_forall_ne_int
  intro m hm
  have hm1 : |m| < (1 : ℤ) := by exact_mod_cast (hm ▸ h1)
  have hm0 : m = 0 := by have := abs_lt.mp hm1; omega
  simp only [hm0, Int.cast_zero] at hm
  simp only [hm, abs_zero, lt_self_iff_false] at h0

/-- All pairs used by the localized loop remain noncolliding on the
ambient larger-window good event, even at exterior collision faces. -/
theorem varAlAssembly_good_pair_noncollision {s γ ε ℓ : ℝ} {N : ℕ+}
    (hs0 : 0 < s) (hs1 : s < 1) (hγ : 1 ≤ γ) (hεs : ε ≤ 1 - s / 2)
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) {X : Fin (N : ℕ) → ℝ}
    (hev : gradEvent s (2 * γ) ε N ℓ X) {i j : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) (hij : i ≠ j) :
    ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0 := by
  let k := j - i
  have hik : i + k = j := by dsimp [k]; ring
  have hkn : k ≠ 0 := sub_ne_zero.mpr hij.symm
  have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hkn)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hq : 0 < ((N : ℝ) * ℓ) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hw := loop_pair_window_two hK (by linarith : 0 ≤ γ)
    (i := i) (j := i + k) (Or.inr ⟨hi, by rw [hik]; exact hj⟩)
  have hlow := gradEvent_sep_lower hev i k hw
  rw [hik, abs_mul, abs_of_pos hN] at hlow
  have hsep0 : 0 < |gradLift N X j - gradLift N X i| := by
    have := mul_pos hq hkpos
    nlinarith
  apply varAlAssembly_coe_ne_zero_of_abs hsep0
  by_cases hP : GradPartial N ℓ γ
  · have hu := loopPartial_sep_le hs0 hs1 hγ hεs hℓ hK hev i k hP
      ⟨hi, by rw [hik]; exact hj⟩ (gradLabels_partial_two_abs_le hP hi hj)
    rw [hik, abs_mul, abs_of_pos hN] at hu
    nlinarith
  · have hkN : |k| < (N : ℤ) := gradLabels_abs_sub_lt hi hj
    have hu := gradEvent_sep_complement hev hℓ
      (not_partial_two_of_not_partial hK (by linarith) hP) i k hkN.le
    rw [hik] at hu
    have hkR : |(k : ℝ)| < (N : ℝ) := by exact_mod_cast hkN
    have := mul_pos hq (sub_pos.mpr hkR)
    nlinarith

/-- Closure of the nonzero physical cutoff is contained in the ambient
good event. This is the support notion needed for smooth extension. -/
theorem varAlAssembly_relative_support_good {n : ℕ} {s γ ε ℓ : ℝ} (hℓ : 0 < ℓ)
    {y : AnchoredEuclidean n}
    (hy : y ∈ closure {z : AnchoredEuclidean n | z ∈ anchoredSimplex n ∧
      loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp z)) ≠ 0}) :
    gradEvent s (2 * γ) ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) := by
  have ha : Continuous (fun z : AnchoredEuclidean n => anchorVector (WithLp.ofLp z)) :=
    (continuous_pi fun k => continuous_anchorVector_apply k).comp (PiLp.continuous_ofLp 2 _)
  apply closure_minimal (t := {z : AnchoredEuclidean n |
    gradEvent s (2 * γ) ε n.succPNat ℓ (anchorVector (WithLp.ofLp z))}) ?_
    ((varAl_isClosed_gradEvent s (2 * γ) ε ℓ n.succPNat).preimage ha) hy
  intro z hz
  have hpos : 0 < loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp z)) :=
    lt_of_le_of_ne (loopCutoff_mem_Icc s γ ε ℓ _).1 (Ne.symm hz.2)
  exact gradEvent_of_loopCutoff_pos hℓ
    (⟨anchorVector (WithLp.ofLp z), varAl_anchorVector_mem hz.1⟩ : Configuration n.succPNat) hpos

end Riesz1.Internal

end
