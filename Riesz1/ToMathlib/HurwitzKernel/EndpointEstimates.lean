/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.DerivativeBounds

/-!
# Endpoint estimates for the periodic Riesz kernel

Quantitative one-dimensional ingredients for the endpoint analysis.
All statements use `hurwitzKernel`. No kernel is defined here.
-/

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Riesz1

theorem contDiffOn_hurwitzKernel_unit (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ContDiffOn ℝ ∞ (hurwitzKernel s) (Ioo 0 1) := by
  intro x hx
  exact (contDiffAt_const.mul
    (contDiffAt_hurwitzZetaEven_re_of_mem_Ioo s hs0 hs1 x hx.1 hx.2)).contDiffWithinAt

/-- A uniform, strictly positive pair curvature, not merely pointwise positivity. -/
theorem hurwitzKernel_curvature_lower (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    s * (s + 1) ≤ deriv (deriv (hurwitzKernel s)) r := by
  rw [(hasDerivAt_deriv_hurwitzKernel_unit s hs0 hs1 r hr.1 hr.2).deriv]
  apply le_mul_of_one_le_right (by positivity : 0 ≤ s * (s + 1))
  have hsum := (summable_and_tsum_int_abs_rpow (-s - 2) (by linarith) r hr.1 hr.2).1
  have hterm := hsum.le_tsum (0 : ℤ) (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)
  simp only [Int.cast_zero, sub_zero, abs_of_pos hr.1] at hterm
  exact (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr.1 hr.2.le
    (by linarith)).trans hterm

theorem tendsto_hurwitzKernel_left (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (hurwitzKernel s) (𝓝[>] 0) atTop :=
  (tendsto_hurwitzZetaEven_re_at_zero s hs0 hs1).mono_left
    (nhdsWithin_mono _ (fun _ hx => ne_of_gt hx))

theorem hurwitzKernel_one_sub (s r : ℝ) :
    hurwitzKernel s (1 - r) = hurwitzKernel s r := by
  unfold hurwitzKernel
  have hcoe : ((1 - r : ℝ) : UnitAddCircle) = -(r : UnitAddCircle) := by
    rw [AddCircle.coe_sub]
    have hz : ((1 : ℝ) : UnitAddCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨1, by simp⟩
    rw [hz, zero_sub]
  rw [hcoe, HurwitzZeta.hurwitzZetaEven_neg]

theorem tendsto_hurwitzKernel_right (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (hurwitzKernel s) (𝓝[<] 1) atTop := by
  have h : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hlim : Tendsto (fun r : ℝ => 1 - r) (𝓝 1) (𝓝 (1 - 1 : ℝ)) :=
        (continuous_const.sub continuous_id).tendsto 1
      rw [sub_self] at hlim
      exact hlim.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr hr
  simpa only [Function.comp_def, hurwitzKernel_one_sub] using
    (tendsto_hurwitzKernel_left s hs0 hs1).comp h

theorem deriv_hurwitzKernel_unit (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    deriv (hurwitzKernel s) r =
      -s * r ^ (-s - 1) + s * (1 - r) ^ (-s - 1) -
        s * (shiftPowSum (s + 1) r).re +
          s * (shiftPowSum (s + 1) ((1 - r : ℝ) : ℂ)).re := by
  exact ((hasDerivAt_kernel_euler s hs0 hs1 r hr.1 hr.2).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds hr.1 hr.2)
      (fun x hx => hurwitzKernel_eq_euler s hs0 hs1 x hx.1 hx.2))).deriv

/-- The tail after deleting the two endpoint singularities is uniformly bounded. -/
theorem hurwitzKernel_deriv_remainder_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ r ∈ Ioo (0 : ℝ) 1,
      |deriv (hurwitzKernel s) r + s * r ^ (-s - 1) -
        s * (1 - r) ^ (-s - 1)| ≤ K := by
  let M : ℝ := ∑' n : ℕ, (2 : ℝ) ^ (s + 1) * ((n : ℝ) + 1) ^ (-(s + 1))
  refine ⟨2 * s * |M| + 1, by positivity, ?_⟩
  intro r hr
  have hb (w : ℝ) (hw : 0 < w) : |(shiftPowSum (s + 1) w).re| ≤ |M| :=
    ((Complex.abs_re_le_norm _).trans (norm_shiftPowSum_le (s + 1) (by linarith)
      (w : ℂ) (by simp; linarith))).trans (le_abs_self M)
  have h₁ := abs_le.mp (hb r hr.1)
  have h₂ := abs_le.mp (hb (1 - r) (sub_pos.mpr hr.2))
  rw [deriv_hurwitzKernel_unit s hs0 hs1 hr, abs_le]
  constructor <;> nlinarith

/-- The once differentiated series has a bounded error at the left endpoint. -/
theorem hurwitzKernel_deriv_left_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      |deriv (hurwitzKernel s) r + s * r ^ (-s - 1)| ≤ K := by
  obtain ⟨K, hK, hbound⟩ := hurwitzKernel_deriv_remainder_bound s hs0 hs1
  refine ⟨K + s * 2 ^ (s + 1), by positivity, ?_⟩
  intro r hr0 hr1
  have hr : r ∈ Ioo (0 : ℝ) 1 := ⟨hr0, by linarith⟩
  have hp : (1 - r) ^ (-s - 1) ≤ 2 ^ (s + 1) := by
    rw [← rpow_half_neg_eq, show -(s + 1) = -s - 1 by ring]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have hh := abs_le.mp (hbound r hr)
  have hp0 : 0 ≤ (1 - r) ^ (-s - 1) := Real.rpow_nonneg (by linarith) _
  rw [abs_le]
  constructor <;> nlinarith

namespace Internal

/-- Absorb the less singular power into an arbitrarily small multiple of the next power. -/
theorem rpow_absorb_endpoint {s ε t : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) (ht : 0 < t) :
    t ^ (-s) ≤ ε * t ^ (-s - 1) + ε ^ (-s) := by
  have he : t * t ^ (-s - 1) = t ^ (-s) := by
    nth_rw 1 [← Real.rpow_one t]
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rcases le_or_gt t ε with h | h
  · have hh := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg ht.le (-s - 1))
    rw [he] at hh
    linarith [Real.rpow_nonneg hε.le (-s)]
  · have hh := Real.rpow_le_rpow_of_nonpos hε h.le (neg_nonpos.mpr hs)
    linarith [mul_nonneg hε.le (Real.rpow_nonneg ht.le (-s - 1))]

end Internal

/-- The force paired with displacement from a uniformly interior separation is coercive
at both endpoints. This is the one-pair estimate. -/
theorem hurwitzKernel_force_coercive (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ b B : ℝ, 0 < b ∧ 0 ≤ B ∧ ∀ a r : ℝ, η ≤ a → a ≤ 1 - η →
      r ∈ Ioo (0 : ℝ) 1 →
      b * (r ^ (-s - 1) + (1 - r) ^ (-s - 1)) - B ≤
        deriv (hurwitzKernel s) r * (r - a) := by
  obtain ⟨K, hK, hbound⟩ := hurwitzKernel_deriv_remainder_bound s hs0 hs1
  refine ⟨s * (η / 2), 2 * s * (η / 2) ^ (-s) + K, by positivity, by positivity, ?_⟩
  intro a r ha₀ ha₁ hr
  have ha : 0 < a ∧ a < 1 := ⟨lt_of_lt_of_le hη ha₀, by linarith⟩
  have hdist : |r - a| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  have herr : -(K : ℝ) ≤ (deriv (hurwitzKernel s) r + s * r ^ (-s - 1) -
      s * (1 - r) ^ (-s - 1)) * (r - a) := by
    have hh := calc
      |(deriv (hurwitzKernel s) r + s * r ^ (-s - 1) -
          s * (1 - r) ^ (-s - 1)) * (r - a)|
          = |deriv (hurwitzKernel s) r + s * r ^ (-s - 1) -
              s * (1 - r) ^ (-s - 1)| * |r - a| := abs_mul _ _
      _ ≤ K * 1 := mul_le_mul (hbound r hr) hdist (abs_nonneg _) hK.le
      _ = K := mul_one _
    exact (abs_le.mp hh).1
  have hpow (t : ℝ) (ht : 0 < t) : t * t ^ (-s - 1) = t ^ (-s) := by
    nth_rw 1 [← Real.rpow_one t]
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have h₁ := Internal.rpow_absorb_endpoint hs0.le (by positivity : 0 < η / 2) hr.1
  have h₂ := Internal.rpow_absorb_endpoint hs0.le (by positivity : 0 < η / 2)
    (sub_pos.mpr hr.2)
  have hp₁ := hpow r hr.1
  have hp₂ := hpow (1 - r) (sub_pos.mpr hr.2)
  have hm₁ := mul_nonneg (sub_nonneg.mpr ha₀)
    (Real.rpow_nonneg hr.1.le (-s - 1))
  have hm₂ := mul_nonneg (sub_nonneg.mpr ha₁)
    (Real.rpow_nonneg (sub_nonneg.mpr hr.2.le) (-s - 1))
  nlinarith

/-- A second-derivative bound using any lower bound on both endpoint distances. -/
theorem hurwitzKernel_deriv2_gap_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ r δ : ℝ, r ∈ Ioo (0 : ℝ) 1 → 0 < δ →
      δ ≤ r → δ ≤ 1 - r →
      deriv (deriv (hurwitzKernel s)) r ≤ D * δ ^ (-s - 2) := by
  let M : ℝ := ∑' n : ℕ, (2 : ℝ) ^ (s + 2) * ((n : ℝ) + 1) ^ (-(s + 2))
  refine ⟨s * (s + 1) * (2 + 2 * |M|), by positivity, ?_⟩
  intro r δ hr hδ hδr hδr'
  have hb (w : ℝ) (hw : 0 < w) : (shiftPowSum (s + 2) w).re ≤ |M| :=
    ((Complex.re_le_norm _).trans (norm_shiftPowSum_le (s + 2) (by linarith)
      (w : ℂ) (by simp; linarith))).trans (le_abs_self M)
  have h₂ := hb r hr.1
  have h₃ := hb (1 - r) (sub_pos.mpr hr.2)
  have he := (summable_and_tsum_int_abs_rpow (-s - 2) (by linarith) r hr.1 hr.2).2
  have hre₁ := shiftPowSum_re_ofReal (s + 2) r hr.1.le
  have hre₂ := shiftPowSum_re_ofReal (s + 2) (1 - r) (sub_nonneg.mpr hr.2.le)
  rw [show -(s + 2) = -s - 2 by ring] at hre₁ hre₂
  rw [(hasDerivAt_deriv_hurwitzKernel_unit s hs0 hs1 r hr.1 hr.2).deriv,
    he, ← hre₁, ← hre₂]
  have hp₁ := Real.rpow_le_rpow_of_nonpos hδ hδr (by linarith : -s - 2 ≤ 0)
  have hp₂ := Real.rpow_le_rpow_of_nonpos hδ hδr' (by linarith : -s - 2 ≤ 0)
  have hp₃ : 1 ≤ δ ^ (-s - 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ (by linarith [hr.2]) (by linarith)
  have hm : 2 * |M| ≤ 2 * |M| * δ ^ (-s - 2) :=
    le_mul_of_one_le_right (by positivity) hp₃
  have hsum : r ^ (-s - 2) + (1 - r) ^ (-s - 2) +
      (shiftPowSum (s + 2) r).re + (shiftPowSum (s + 2) ((1 - r : ℝ) : ℂ)).re ≤
        (2 + 2 * |M|) * δ ^ (-s - 2) := by linarith
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ s * (s + 1))).trans_eq
    (by ring)

end Riesz1

end
