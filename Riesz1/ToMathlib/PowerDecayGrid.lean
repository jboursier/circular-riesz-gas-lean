/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.Complex.Basic

/-!
# Integrable power decay on every frequency mesh

The mesh times the sum over its nonzero points is bounded independently of
the mesh. This is useful for Fourier bounds on circles of unbounded length.
-/

public section

open MeasureTheory Set

namespace Riesz1.FourierGrid

/-- A decreasing integrable power has a uniform Riemann-sum bound on every
positive mesh, with the zero mode removed. -/
theorem power_decay_mesh_bound {q : ℝ} (hq : q < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else (1 + δ * |(k : ℝ)|) ^ q) ∧
      δ * (∑' k : ℤ, if k = 0 then (0 : ℝ) else (1 + δ * |(k : ℝ)|) ^ q) ≤ C := by
  let F := fun x : ℝ => (1 + x) ^ q
  let I := ∫ x in Ioi (0 : ℝ), F x
  have hI : IntegrableOn F (Ioi 0) := by
    simpa only [F, add_comm] using integrableOn_add_rpow_Ioi_of_lt hq
      (by norm_num : -(1 : ℝ) < 0)
  have hI0 : 0 ≤ I := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    dsimp [F]
    exact Real.rpow_nonneg (by linarith [show 0 < x from hx]) q
  refine ⟨2 * I + 1, by positivity, fun δ hδ => ?_⟩
  let G := fun x : ℝ => F (δ * x)
  have hGi : IntegrableOn G (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff F 0 hδ).mpr (by simpa only [mul_zero] using hI)
  have hGa : AntitoneOn G (Ici 0) := by
    intro x hx y hy hxy
    change (1 + δ * y) ^ q ≤ (1 + δ * x) ^ q
    exact Real.rpow_le_rpow_of_nonpos (by nlinarith [show 0 ≤ x from hx])
      (by nlinarith) (by linarith)
  have hGn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ G x := by
    intro x hx
    change 0 ≤ (1 + δ * x) ^ q
    exact Real.rpow_nonneg (by nlinarith [show 0 < x from hx]) q
  have hs : Summable (fun n : ℕ => G (n : ℝ)) :=
    hGa.summable_of_integrableOn_Ioi_zero hGi hGn
  have hs' : Summable (fun n : ℕ => G ((n + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff 1).mpr hs
  have hb : (∑' n : ℕ, G ((n + 1 : ℕ) : ℝ)) ≤ δ⁻¹ * I := by
    have hi := integral_comp_mul_left_Ioi F 0 hδ
    simp only [mul_zero, smul_eq_mul] at hi
    exact (hGa.tsum_add_one_le_integral hGi hGn).trans_eq hi
  let A := fun k : ℤ => if k = 0 then (0 : ℝ) else (1 + δ * |(k : ℝ)|) ^ q
  have hpos (n : ℕ) : A (n : ℤ) = if n = 0 then 0 else G (n : ℝ) := by
    simp only [A, G, F, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ _),
      Int.natCast_eq_zero]
  have hneg (n : ℕ) : A (-(n + 1 : ℤ)) = G ((n + 1 : ℕ) : ℝ) := by
    dsimp only [A]
    rw [ite_eq_right (by omega), Int.cast_neg, Int.cast_add, Int.cast_natCast,
      Int.cast_one, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    simp only [G, F, Nat.cast_add, Nat.cast_one]
  have hps : Summable (fun n : ℕ => A (n : ℤ)) := by
    apply hs.congr_cofinite
    filter_upwards [Filter.eventually_cofinite_ne (0 : ℕ)] with n hn
    rw [hpos n, ite_eq_right hn]
  have hns : Summable (fun n : ℕ => A (-(n + 1 : ℤ))) := by
    simpa only [hneg] using hs'
  have hAs : Summable A := hps.of_nat_of_neg_add_one hns
  have hsum : (∑' k : ℤ, A k) = 2 * ∑' n : ℕ, G ((n + 1 : ℕ) : ℝ) := by
    rw [tsum_of_nat_of_neg_add_one hps hns, hps.tsum_eq_zero_add]
    have hz : A (0 : ℤ) = 0 := by simp only [A, ite_true]
    simp only [Int.natCast_zero, hz, zero_add]
    simp_rw [hpos, Nat.add_one_ne_zero, ite_false, hneg]
    ring
  refine ⟨hAs, ?_⟩
  change δ * (∑' k : ℤ, A k) ≤ _
  rw [hsum]
  have ht := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * δ)
  have hc : 2 * δ * (δ⁻¹ * I) = 2 * I := by field_simp
  rw [hc] at ht
  linarith

end Riesz1.FourierGrid
