/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleFourierUniqueness
public import Riesz1.ToMathlib.FiniteMarkMollify
public import Riesz1.Frozen.Coeff
public import Riesz1.Frozen.ComplexL2Integrable
public import Riesz1.Frozen.Arclength

/-!
# Uniqueness of continuous circle functions and separation of finitely many points

Two continuous real functions on a circle with the same Fourier coefficients agree everywhere.
Used to identify the transport `ψ` of a test profile with the transports produced by the
regularization theorems. Also: finitely many distinct points of a metric space are uniformly
separated, and the distance of two points of a circle is the circular distance of their difference.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter

namespace Riesz1

/-- Continuous real functions on a circle with equal Fourier coefficients are equal. -/
theorem continuous_eq_of_coeff_eq {L : Length} {f g : Circle L → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfL : MemLp (fun x => (f x : ℂ)) 2 (arclength L))
    (hgL : MemLp (fun x => (g x : ℂ)) 2 (arclength L))
    (h : ∀ k : ℤ, coeff L ⟨fun x => (f x : ℂ), complexL2Integrable L _ hfL⟩ k =
      coeff L ⟨fun x => (g x : ℂ), complexL2Integrable L _ hgL⟩ k) : f = g := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hvol : arclength L = volume := rfl
  have hfv : MemLp (fun x => (f x : ℂ)) 2 volume := by
    rw [← hvol]
    exact hfL
  have hgv : MemLp (fun x => (g x : ℂ)) 2 volume := by
    rw [← hvol]
    exact hgL
  have hae : (fun x => (f x : ℂ)) =ᵐ[volume] (fun x => (g x : ℂ)) :=
    CircleFourier.ae_eq_of_coeff_eq hfv hgv (fun k => h k)
  have hae' : f =ᵐ[volume] g := by
    filter_upwards [hae] with x hx
    exact Complex.ofReal_injective hx
  exact (Continuous.ae_eq_iff_eq volume hf hg).mp hae'

/-- Finitely many distinct points of a metric space are separated by a fixed positive distance. -/
theorem exists_pos_le_dist_of_injective {ι X : Type*} [Fintype ι] [MetricSpace X]
    {f : ι → X} (hf : Function.Injective f) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i k, i ≠ k → δ ≤ dist (f i) (f k) := by
  classical
  let S : Finset (ι × ι) := Finset.univ.filter (fun q => q.1 ≠ q.2)
  by_cases hS : S.Nonempty
  · obtain ⟨q, hq, hmin⟩ := S.exists_min_image (fun q => dist (f q.1) (f q.2)) hS
    refine ⟨dist (f q.1) (f q.2), ?_, ?_⟩
    · have hne : q.1 ≠ q.2 := (Finset.mem_filter.mp hq).2
      exact dist_pos.mpr (fun h => hne (hf h))
    · intro i k hik
      exact hmin (i, k) (by simp [S, hik])
  · refine ⟨1, one_pos, fun i k hik => ?_⟩
    exact absurd ⟨(i, k), by simp [S, hik]⟩ hS

/-- On a circle of length `L > 0`, the distance of two classes is the circular distance of the
difference of their representatives. -/
theorem dist_coe_eq_circDist_sub {L : ℝ} (hL : 0 < L) (x y : ℝ) :
    dist (x : AddCircle L) (y : AddCircle L) = circDist L (x - y) := by
  have : Fact (0 < L) := ⟨hL⟩
  rw [← dist_sub_right (x : AddCircle L) (y : AddCircle L) (y : AddCircle L), sub_self,
    ← AddCircle.coe_sub, dist_coe_zero_eq_circDist]

end Riesz1

end
