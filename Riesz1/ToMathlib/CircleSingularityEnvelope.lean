/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Riesz1.ToMathlib.PuncturedOscillatoryFinite

/-!
# An interval envelope for circular power singularities

On one fundamental interval, a negative power of the circular distance is bounded by
the real singularity at the mark's representative and by singularities at the two
endpoints. This reduces circular derivative bounds to a finite real singular set.
-/

public section

open Set MeasureTheory

namespace Riesz1.CircleSingularity

/-- The nearest lift of a mark is either its representative in `[0,T)` or lies beyond
one of the endpoints. The estimate also holds at a mark with Mathlib's real-power value. -/
theorem dist_rpow_le_interval_envelope {T e : ℝ} (hT : 0 < T) (he : e ≤ 0)
    {x r : ℝ} (hx : x ∈ Ioo 0 T) (hr : r ∈ Ico 0 T) :
    dist (x : AddCircle T) (r : AddCircle T) ^ e ≤
      x ^ e + (T - x) ^ e + |x - r| ^ e := by
  have h₁ : 0 ≤ x ^ e := Real.rpow_nonneg hx.1.le _
  have h₂ : 0 ≤ (T - x) ^ e := Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _
  have h₃ : 0 ≤ |x - r| ^ e := by positivity
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq]
  let n : ℤ := round (T⁻¹ * (x - r))
  change |x - r - n * T| ^ e ≤ _
  by_cases hn : n = 0
  · simp only [hn, Int.cast_zero, zero_mul, sub_zero]
    linarith
  · rcases lt_or_gt_of_ne hn with hn | hn
    · have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
      have hl : r + n * T ≤ 0 := by nlinarith [hr.1, hr.2, mul_le_mul_of_nonneg_right hn' hT.le]
      have hp : (x - (r + n * T)) ^ e ≤ x ^ e :=
        Real.rpow_le_rpow_of_nonpos hx.1 (by linarith) he
      rw [show x - r - n * T = x - (r + n * T) by ring,
        abs_of_pos (by linarith [hx.1])]
      exact hp.trans (by linarith)
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hl : T ≤ r + n * T := by nlinarith [hr.1, hr.2, mul_le_mul_of_nonneg_right hn' hT.le]
      have hp : (r + n * T - x) ^ e ≤ (T - x) ^ e :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hx.2]) (by linarith) he
      rw [abs_of_neg (by linarith [hx.2]), show -(x - r - n * T) = r + n * T - x by ring]
      exact hp.trans (by linarith)

/-- A derivative bound with finitely many circular singularities supplies a power
oscillatory estimate on a full period. Constants may depend on this fixed period. -/
theorem oscillatory_bound_of_deriv_bound {T b C : ℝ} (hT : 0 < T)
    (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C) {ι : Type*} [Fintype ι]
    (marks : ι → AddCircle T) {q : ℝ → ℝ}
    (hq : ∀ x ∈ Ioo 0 T, (∀ j, (x : AddCircle T) ≠ marks j) → DifferentiableAt ℝ q x)
    (hbound : ∀ x ∈ Ioo 0 T, (∀ j, (x : AddCircle T) ≠ marks j) →
      |deriv q x| ≤ C * (1 + ∑ j, dist (x : AddCircle T) (marks j) ^ (-1 - b))) :
    IntervalIntegrable q volume 0 T ∧
      ∃ K W : ℝ, 0 ≤ K ∧ 1 ≤ W ∧
        ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
          (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
          ‖∫ t in (0 : ℝ)..T, (q t : ℂ) * χ t‖ ≤ K * ‖c‖ ^ (b - 1) := by
  classical
  have : Fact (0 < T) := ⟨hT⟩
  let r : ι → ℝ := fun j => (AddCircle.equivIco T 0 (marks j)).val
  let S : Finset ℝ := Finset.univ.image r
  have hr : ∀ j, r j ∈ Ico 0 T := by
    intro j
    simpa [r] using (AddCircle.equivIco T 0 (marks j)).property
  have hrepr : ∀ j, (r j : AddCircle T) = marks j := fun j => AddCircle.coe_equivIco
  have hn : ∀ x ∈ Ioo 0 T \ (S : Set ℝ), ∀ j, (x : AddCircle T) ≠ marks j := by
    intro x hx j he
    have heq : x = r j := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show x ∈ Ico 0 (0 + T) by simpa using ⟨hx.1.1.le, hx.1.2⟩)
      (show r j ∈ Ico 0 (0 + T) by simpa using hr j)).mp (he.trans (hrepr j).symm)
    apply hx.2
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩
  apply PuncturedDerivative.oscillatory_bound_of_finite_deriv_bound hb hb1 S
    (C := C * (T ^ (1 + b) + Fintype.card ι)) (by positivity) hT
    (fun x hx => hq x hx.1 (hn x hx))
  intro x hx
  let E := (x - 0) ^ (-1 - b) + (T - x) ^ (-1 - b) +
    ∑ y ∈ S, |x - y| ^ (-1 - b)
  have hxp : 0 < x := hx.1.1
  have hTx : 0 < T - x := sub_pos.mpr hx.1.2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hsum : (∑ j, dist (x : AddCircle T) (marks j) ^ (-1 - b)) ≤
      (Fintype.card ι : ℝ) * E := by
    calc _ ≤ ∑ _j : ι, E := by
          apply Finset.sum_le_sum
          intro j _
          rw [← hrepr j]
          have hs : |x - r j| ^ (-1 - b) ≤ ∑ y ∈ S, |x - y| ^ (-1 - b) :=
            Finset.single_le_sum (s := S) (f := fun y : ℝ => |x - y| ^ (-1 - b)) (fun _ _ => by positivity)
              (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
          exact (dist_rpow_le_interval_envelope hT (by linarith) hx.1 (hr j)).trans
            (by dsimp [E]; simp only [sub_zero]; linarith)
      _ = (Fintype.card ι : ℝ) * E := by simp
  have hpow : T ^ (1 + b) * T ^ (-1 - b) = 1 := by
    rw [← Real.rpow_add hT, show 1 + b + (-1 - b) = 0 by ring, Real.rpow_zero]
  have hlow : T ^ (-1 - b) ≤ E := by
    have hp : T ^ (-1 - b) ≤ x ^ (-1 - b) :=
      Real.rpow_le_rpow_of_nonpos hx.1.1 hx.1.2.le (by linarith)
    dsimp [E]
    simp only [sub_zero]
    have ht : 0 ≤ (T - x) ^ (-1 - b) := Real.rpow_nonneg hTx.le _
    have hs : 0 ≤ ∑ y ∈ S, |x - y| ^ (-1 - b) := by positivity
    linarith
  have hone : 1 ≤ T ^ (1 + b) * E := by
    calc 1 = T ^ (1 + b) * T ^ (-1 - b) := hpow.symm
      _ ≤ T ^ (1 + b) * E := mul_le_mul_of_nonneg_left hlow (by positivity)
  have ho := hbound x hx.1 (hn x hx)
  change |deriv q x| ≤ C * (T ^ (1 + b) + Fintype.card ι) * E
  nlinarith [mul_le_mul_of_nonneg_left hsum hC, mul_le_mul_of_nonneg_left hone hC]

end Riesz1.CircleSingularity
