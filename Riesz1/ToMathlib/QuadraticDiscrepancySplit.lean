/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Tactic.Ring

/-!
# Splitting a symmetric empirical discrepancy pairing

The exterior-exterior kernel vanishes when a transport is supported in the
interior. The remaining difference is twice the signed cross pairing.
-/

public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- Exact expansion of a symmetric quadratic discrepancy pairing across a
finite label partition and a background measure partition. -/
theorem quadratic_discrepancy_split {Ω ι : Type*} [MeasurableSpace Ω]
    [DecidableEq ι] (I E : Finset ι) (hIE : Disjoint I E) (z : ι → Ω)
    (μ ν : Measure Ω) [SFinite μ] [SFinite ν] (k : Ω → Ω → ℝ)
    (hsym : ∀ x y, k x y = k y x)
    (hslice : ∀ x, Integrable (k x) μ ∧ Integrable (k x) ν)
    (hBB : Integrable (fun p : Ω × Ω => k p.1 p.2) (μ.prod μ))
    (hBC : Integrable (fun p : Ω × Ω => k p.1 p.2) (μ.prod ν))
    (hCC : Integrable (fun p : Ω × Ω => k p.1 p.2) (ν.prod ν))
    (hEE : ∀ i ∈ E, ∀ j ∈ E, k (z i) (z j) = 0)
    (hEC : ∀ i ∈ E, ∀ᵐ u ∂ν, k (z i) u = 0)
    (hCC0 : ∀ᵐ x ∂ν, ∀ᵐ u ∂ν, k x u = 0) :
    ((∑ i ∈ I ∪ E, ∑ j ∈ I ∪ E, k (z i) (z j)) -
      2 * (∑ i ∈ I ∪ E, ∫ u, k (z i) u ∂(μ + ν)) +
      ∫ x, ∫ u, k x u ∂(μ + ν) ∂(μ + ν)) -
    ((∑ i ∈ I, ∑ j ∈ I, k (z i) (z j)) -
      2 * (∑ i ∈ I, ∫ u, k (z i) u ∂μ) +
      ∫ x, ∫ u, k x u ∂μ ∂μ) =
    2 * ((∑ i ∈ I, ((∑ j ∈ E, k (z i) (z j)) - (∫ u, k (z i) u ∂ν))) -
      ∫ x, ((∑ j ∈ E, k x (z j)) - (∫ u, k x u ∂ν)) ∂μ) := by
  have hCB : Integrable (fun p : Ω × Ω => k p.1 p.2) (ν.prod μ) := by
    exact hBC.swap.congr (Filter.Eventually.of_forall fun p => hsym p.2 p.1)
  have hsum : (∑ i ∈ I ∪ E, ∑ j ∈ I ∪ E, k (z i) (z j)) =
      (∑ i ∈ I, ∑ j ∈ I, k (z i) (z j)) +
        2 * (∑ i ∈ I, ∑ j ∈ E, k (z i) (z j)) := by
    simp_rw [Finset.sum_union hIE, Finset.sum_add_distrib]
    have hz : (∑ i ∈ E, ∑ j ∈ E, k (z i) (z j)) = 0 := by
      exact Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => hEE i hi j hj))
    have hc : (∑ i ∈ E, ∑ j ∈ I, k (z i) (z j)) =
        ∑ i ∈ I, ∑ j ∈ E, k (z i) (z j) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hsym _ _))
    rw [hz, hc]
    ring
  have hsingle : (∑ i ∈ I ∪ E, ∫ u, k (z i) u ∂(μ + ν)) =
      (∑ i ∈ I, ∫ u, k (z i) u ∂μ) + (∑ i ∈ I, ∫ u, k (z i) u ∂ν) +
        ∑ j ∈ E, ∫ x, k x (z j) ∂μ := by
    simp_rw [integral_add_measure (hslice _).1 (hslice _).2]
    rw [Finset.sum_union hIE, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hz : (∑ i ∈ E, ∫ u, k (z i) u ∂ν) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact integral_eq_zero_of_ae (hEC i hi)
    have hc : (∑ i ∈ E, ∫ u, k (z i) u ∂μ) = ∑ j ∈ E, ∫ x, k x (z j) ∂μ := by
      exact Finset.sum_congr rfl (fun i _ => integral_congr_ae
        (Filter.Eventually.of_forall fun x => hsym _ _))
    rw [hz, hc]
    ring
  have hdouble : (∫ x, ∫ u, k x u ∂(μ + ν) ∂(μ + ν)) =
      (∫ x, ∫ u, k x u ∂μ ∂μ) + 2 * ∫ x, ∫ u, k x u ∂ν ∂μ := by
    simp_rw [integral_add_measure (hslice _).1 (hslice _).2]
    have he := integral_add_measure (hBB.integral_prod_left.add hBC.integral_prod_left)
      (hCB.integral_prod_left.add hCC.integral_prod_left)
    have hm := integral_add hBB.integral_prod_left hBC.integral_prod_left
    have hn := integral_add hCB.integral_prod_left hCC.integral_prod_left
    simp only [Pi.add_apply] at he hm hn
    rw [he, hm, hn]
    have hc : (∫ x, ∫ u, k x u ∂μ ∂ν) = ∫ x, ∫ u, k x u ∂ν ∂μ := by
      rw [integral_integral_swap hCB]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
        integral_congr_ae (Filter.Eventually.of_forall fun u => hsym _ _))
    have hz : (∫ x, ∫ u, k x u ∂ν ∂ν) = 0 := by
      exact integral_eq_zero_of_ae (hCC0.mono fun x hx => integral_eq_zero_of_ae hx)
    rw [hc, hz]
    ring
  have hr : (∫ x, ((∑ j ∈ E, k x (z j)) - (∫ u, k x u ∂ν)) ∂μ) =
      (∑ j ∈ E, ∫ x, k x (z j) ∂μ) - ∫ x, ∫ u, k x u ∂ν ∂μ := by
    have hi (j : ι) : Integrable (fun x => k x (z j)) μ :=
      (hslice (z j)).1.congr (Filter.Eventually.of_forall fun x => hsym _ _)
    rw [integral_sub (integrable_finsetSum _ (fun j _ => hi j)) hBC.integral_prod_left,
      integral_finsetSum _ (fun j _ => hi j)]
  rw [hsum, hsingle, hdouble, hr, Finset.sum_sub_distrib]
  ring

end Riesz1

end
