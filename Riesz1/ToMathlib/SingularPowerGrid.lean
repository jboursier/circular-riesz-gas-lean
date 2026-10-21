/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PowerDecayGrid
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Frequency meshes with an integrable singularity at zero

The absolute differentiated Fourier sum in Lemma 5.1
can have a negative exponent strictly above minus one. The zero frequency
is omitted, and the mesh bound retains that singularity.
-/

public section

open MeasureTheory Set

namespace Riesz1.FourierGrid

/-- The integral test also applies when the decreasing function is unbounded
at zero. Its value at zero is never sampled. -/
theorem summable_add_one_le_integral_of_antitoneOn_Ioi {F : ℝ → ℝ}
    (ha : AntitoneOn F (Ioi 0)) (hi : IntegrableOn F (Ioi 0))
    (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ F x) :
    Summable (fun n : ℕ => F ((n + 1 : ℕ) : ℝ)) ∧
      (∑' n : ℕ, F ((n + 1 : ℕ) : ℝ)) ≤ ∫ x in Ioi (0 : ℝ), F x := by
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, F ((n + 1 : ℕ) : ℝ)) ≤
      ∫ x in Ioi (0 : ℝ), F x := by
    have hic : IntegrableOn F (Icc 0 (N : ℝ)) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact hi.mono_set Ioc_subset_Ioi_self
    have hh := (ha.mono (show Ioc (0 : ℝ) (0 + N) ⊆ Ioi 0 from
      fun _ hx => hx.1)).sum_le_integral_of_integrableOn (by simpa using hic)
    simp only [zero_add] at hh
    refine hh.trans ?_
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
    exact setIntegral_mono_set hi (ae_restrict_of_forall_mem measurableSet_Ioi hn)
      Ioc_subset_Ioi_self.eventuallySubset
  have hs := summable_of_sum_range_le (fun n => hn _ (show (0 : ℝ) < (n + 1 : ℕ) by positivity)) hb
  refine ⟨hs, ?_⟩
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall hb)

/-- Nonzero samples of any decreasing integrable positive envelope have a
length independent mesh bound, even if the envelope is singular at zero. -/
theorem antitone_integrable_mesh_bound {F : ℝ → ℝ}
    (ha : AntitoneOn F (Ioi 0)) (hi : IntegrableOn F (Ioi 0))
    (hn : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ F x) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else F (δ * |(k : ℝ)|)) ∧
      δ * (∑' k : ℤ, if k = 0 then (0 : ℝ) else F (δ * |(k : ℝ)|)) ≤ C := by
  let I := ∫ x in Ioi (0 : ℝ), F x
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi hn
  refine ⟨2 * I + 1, by positivity, fun δ hδ => ?_⟩
  let G := fun x : ℝ => F (δ * x)
  have hGi : IntegrableOn G (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff F 0 hδ).mpr (by simpa using hi)
  have hGa : AntitoneOn G (Ioi 0) := by
    intro x hx y hy hxy
    exact ha (mul_pos hδ hx) (mul_pos hδ hy) (mul_le_mul_of_nonneg_left hxy hδ.le)
  obtain ⟨hs, hb⟩ := summable_add_one_le_integral_of_antitoneOn_Ioi hGa hGi
    (fun x hx => hn _ (mul_pos hδ hx))
  have hb' : (∑' n : ℕ, G ((n + 1 : ℕ) : ℝ)) ≤ δ⁻¹ * I := by
    have hh := integral_comp_mul_left_Ioi F 0 hδ
    simp only [mul_zero, smul_eq_mul] at hh
    exact hb.trans_eq hh
  let A := fun k : ℤ => if k = 0 then (0 : ℝ) else F (δ * |(k : ℝ)|)
  have hp (n : ℕ) : A ((n + 1 : ℕ) : ℤ) = G ((n + 1 : ℕ) : ℝ) := by
    simp only [A, G, Int.natCast_eq_zero, Nat.add_one_ne_zero, ite_false,
      Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (n + 1) : (0 : ℝ) ≤ _)]
  have hneg (n : ℕ) : A (-(n + 1 : ℤ)) = G ((n + 1 : ℕ) : ℝ) := by
    simp only [A, G, show -(n + 1 : ℤ) ≠ 0 by omega, ite_false, Int.cast_neg,
      abs_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
  have hps : Summable (fun n : ℕ => A (n : ℤ)) := by
    rw [← summable_nat_add_iff 1]
    simpa only [hp] using hs
  have hns : Summable (fun n : ℕ => A (-(n + 1 : ℤ))) := by
    simpa only [hneg] using hs
  have hAs : Summable A := hps.of_nat_of_neg_add_one hns
  have he : (∑' k : ℤ, A k) = 2 * ∑' n : ℕ, G ((n + 1 : ℕ) : ℝ) := by
    rw [tsum_of_nat_of_neg_add_one hps hns, hps.tsum_eq_zero_add]
    have hz : A 0 = 0 := by simp only [A, ite_true]
    simp only [Int.natCast_zero, hz, zero_add]
    simp_rw [hp, hneg]
    ring
  refine ⟨hAs, ?_⟩
  change δ * (∑' k : ℤ, A k) ≤ _
  rw [he]
  have ht := mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ 2 * δ)
  have hc : 2 * δ * (δ⁻¹ * I) = 2 * I := by field_simp
  rw [hc] at ht
  linarith

/-- A locally integrable power singularity multiplied by a sufficiently
strong decreasing tail is uniformly summable on every nonzero mesh. -/
theorem singular_power_mesh_bound {q r : ℝ} (hq : -1 < q) (hq0 : q ≤ 0)
    (hr : r ≤ 0) (hqr : q + r < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
        (δ * |(k : ℝ)|) ^ q * (1 + δ * |(k : ℝ)|) ^ r) ∧
      δ * (∑' k : ℤ, if k = 0 then (0 : ℝ) else
        (δ * |(k : ℝ)|) ^ q * (1 + δ * |(k : ℝ)|) ^ r) ≤ C := by
  let F := fun x : ℝ => x ^ q * (1 + x) ^ r
  have hn (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : 0 ≤ F x := by
    have hx0 : 0 < x := hx
    dsimp [F]
    positivity
  have ha : AntitoneOn F (Ioi 0) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hx hxy hq0)
      (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1 + x) (by linarith) hr)
      (by positivity) (by positivity)
  have hc : ContinuousOn F (Ioi 0) := by
    exact (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))).mul
      ((continuousOn_const.add continuousOn_id).rpow_const
        (fun x hx => Or.inl (by have hx0 : 0 < x := hx; linarith : 1 + x ≠ 0)))
  have hi0 : IntegrableOn F (Ioc 0 1) := by
    have hp : IntegrableOn (fun x : ℝ => x ^ q) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr hq
    apply hp.mono' ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx0 : 0 < x := hx.1
    rw [Real.norm_of_nonneg (hn x hx.1)]
    exact mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hx.1]) hr)
  have hi1 : IntegrableOn F (Ioi 1) := by
    apply (integrableOn_Ioi_rpow_of_lt hqr (by norm_num : (0 : ℝ) < 1)).mono'
      ((hc.mono (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 < x := hx
    rw [Real.norm_of_nonneg (hn x (show 0 < x by linarith))]
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x) (by linarith) hr)
      (by positivity)).trans_eq (Real.rpow_add (by linarith : 0 < x) q r).symm
  apply antitone_integrable_mesh_bound ha _ hn
  have hu : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  rw [← hu]
  exact hi0.union hi1

/-- The same mesh bound for every locally integrable exponent, including
positive powers, with sufficient decay at infinity. -/
theorem power_product_mesh_bound {q r : ℝ} (hq : -1 < q)
    (hr : r ≤ 0) (hqr : q + r < -1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ →
      Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
        (δ * |(k : ℝ)|) ^ q * (1 + δ * |(k : ℝ)|) ^ r) ∧
      δ * (∑' k : ℤ, if k = 0 then (0 : ℝ) else
        (δ * |(k : ℝ)|) ^ q * (1 + δ * |(k : ℝ)|) ^ r) ≤ C := by
  by_cases hq0 : q ≤ 0
  · exact singular_power_mesh_bound hq hq0 hr hqr
  obtain ⟨C, hC, hmesh⟩ := power_decay_mesh_bound hqr
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨hs, hb⟩ := hmesh δ hδ
  have hm (k : ℤ) :
      (if k = 0 then (0 : ℝ) else
        (δ * |(k : ℝ)|) ^ q * (1 + δ * |(k : ℝ)|) ^ r) ≤
      (if k = 0 then (0 : ℝ) else (1 + δ * |(k : ℝ)|) ^ (q + r)) := by
    split_ifs with hk
    · exact le_rfl
    have hu : 0 ≤ δ * |(k : ℝ)| := mul_nonneg hδ.le (abs_nonneg _)
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hu (by linarith) (le_of_not_ge hq0))
      (by positivity)).trans_eq (Real.rpow_add (by linarith) q r).symm
  have hn (k : ℤ) : 0 ≤ (if k = 0 then (0 : ℝ) else
      (δ * |(k : ℝ)|) ^ q * (1 + δ * |(k : ℝ)|) ^ r) := by
    split_ifs <;> positivity
  have hs' := Summable.of_norm_bounded hs (fun k => by
    rw [Real.norm_of_nonneg (hn k)]
    exact hm k)
  exact ⟨hs', (mul_le_mul_of_nonneg_left (hs'.tsum_le_tsum hm hs) hδ.le).trans hb⟩

end Riesz1.FourierGrid
