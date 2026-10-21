/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopScaleIntegrability
public import Riesz1.Variance.LoopIBPPairs
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceKernel

/-!
# Size bounds for the loop functional on a Lipschitz profile

Proposition 5.5, moment clause. For a Lipschitz
profile `f` of period one, the loop kernel `(f(a) - f(b)) g_s'(a - b)` is bounded by a constant
multiple of `dist(a - b, ℤ)^(-s)`, and each particle-background integral is bounded uniformly
in the particle position. Summing these bounds gives a bound on the loop functional by a
constant times `1 + ∑ₖ gapₖ^{-s}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology UnitAddCircle

namespace Riesz1

/-- The kernel is bounded by a constant multiple of `dist(a - b, ℤ)^(-s)` off the diagonal
of the circle. The constant depends on the Lipschitz constant of `f` and on `s`, not on `a, b`. -/
lemma exists_loopKernel_le (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, ((a - b : ℝ) : UnitAddCircle) ≠ 0 →
      |loopKernel s.val f a b| ≤ K * dist ((a - b : ℝ) : UnitAddCircle) 0 ^ (-s.val) := by
  obtain ⟨C, hC, hgb⟩ := deriv_hurwitzKernel_bound s.val s.property.1 s.property.2
  refine ⟨C * M, mul_nonneg hC.le M.property, fun a b hab => ?_⟩
  set d := dist ((a - b : ℝ) : UnitAddCircle) 0 with hd
  have hdpos : 0 < d := dist_pos.mpr hab
  have hψ : |f a - f b| ≤ (M : ℝ) * d := by
    have h := loopScale_lipschitz_increment hf hp b (a - b)
    rwa [show b + (a - b) = a by ring] at h
  have hk : |deriv (hurwitzKernel s.val) (a - b)| ≤ C * d ^ (-s.val - 1) := hgb (a - b) hab
  have he : d ^ (-s.val - 1) * d = d ^ (-s.val) := by
    rw [Real.rpow_sub_one hdpos.ne', div_mul_cancel₀ _ hdpos.ne']
  unfold loopKernel
  rw [abs_mul]
  calc |f a - f b| * |deriv (hurwitzKernel s.val) (a - b)|
      ≤ ((M : ℝ) * d) * (C * d ^ (-s.val - 1)) :=
        mul_le_mul hψ hk (abs_nonneg _) (by positivity)
    _ = (C * M) * (d ^ (-s.val - 1) * d) := by ring
    _ = (C * M) * d ^ (-s.val) := by rw [he]

/-- Each particle-background integral is bounded uniformly in the particle position. -/
lemma exists_background_le (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : ℝ, |∫ y in (0 : ℝ)..1, loopKernel s.val f a y| ≤ B := by
  obtain ⟨K, hK0, hK⟩ := loopScale_abs_pvIntegrand_le s hf hp
  have hmaj : IntervalIntegrable (fun u : ℝ => K * (u ^ (-s.val) + (1 - u) ^ (-s.val)))
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact (integrableOn_rpow_majorant s.property.2).const_mul K
  have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 1 := by
    rw [ae_iff]
    simp
  refine ⟨∫ u in (0 : ℝ)..1, K * (u ^ (-s.val) + (1 - u) ^ (-s.val)),
    intervalIntegral.integral_nonneg zero_le_one
      (fun u hu => mul_nonneg hK0 (add_nonneg (Real.rpow_nonneg hu.1 _)
        (Real.rpow_nonneg (by linarith [hu.2]) _))), fun a => ?_⟩
  rw [loopScale_integral_kernel_eq s.val hp a, abs_neg]
  have hbound : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ioc (0 : ℝ) 1 →
      ‖pvIntegrand s.val f a u‖ ≤ K * (u ^ (-s.val) + (1 - u) ^ (-s.val)) := by
    filter_upwards [hae] with u hu1 hu
    rw [Real.norm_eq_abs]
    exact hK a u hu.1 (lt_of_le_of_ne hu.2 hu1)
  have := intervalIntegral.norm_integral_le_of_norm_le zero_le_one hbound hmaj
  rw [Real.norm_eq_abs] at this
  exact this

/-- The double background integral is bounded. -/
lemma exists_double_background_le (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ B : ℝ, 0 ≤ B ∧ |∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s.val f u v| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := exists_background_le s hf hp
  refine ⟨B, hB0, ?_⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun u : ℝ => ∫ v in (0 : ℝ)..1, loopKernel s.val f u v)
    (C := B) (fun u _ => by rw [Real.norm_eq_abs]; exact hB u)
  rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h
  exact h

/-- The particle-background integral is symmetric in its two arguments, so the integral over the
first argument is bounded by the same constant. -/
lemma integral_kernel_left_eq (s : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    (∫ u in (0 : ℝ)..1, loopKernel s f u x) = ∫ y in (0 : ℝ)..1, loopKernel s f x y := by
  congr 1
  funext u
  exact loopScale_kernel_symm s f u x

/-- The kernel is jointly measurable for a continuous profile. -/
lemma measurable_loopKernel_pair (s : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun p : ℝ × ℝ => loopKernel s f p.1 p.2) := by
  unfold loopKernel
  exact ((hf.measurable.comp measurable_fst).sub (hf.measurable.comp measurable_snd)).mul
    ((measurable_deriv (hurwitzKernel s)).comp (measurable_fst.sub measurable_snd))

/-- The particle-background integral is measurable in the particle position. -/
lemma measurable_background (s : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun x : ℝ => ∫ y in (0 : ℝ)..1, loopKernel s f x y) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact (((measurable_loopKernel_pair s hf).stronglyMeasurable).integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

/-- The loop functional of a Lipschitz profile is bounded by a constant multiple of
`1 + ∑ₖ gapₖ^{-s}` on every configuration. The particle-particle sum uses the pair bound, and the
three background terms are bounded uniformly in the particle positions. -/
theorem exists_loopFunctional_le (s : RieszExponent) (N : ℕ+) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Configuration N,
      |loopFunctional s.val (N : ℕ) f X.val| ≤ C * (1 + gapPowerSum s.val X) := by
  obtain ⟨K, hK0, hK⟩ := exists_loopKernel_le s hf hp
  obtain ⟨B, hB0, hB⟩ := exists_background_le s hf hp
  obtain ⟨D, hD0, hD⟩ := exists_double_background_le s hf hp
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hs0 : 0 ≤ s.val := s.property.1.le
  have hNs : (0 : ℝ) ≤ (N : ℝ) ^ (-s.val) := (Real.rpow_pos_of_pos hNpos _).le
  have hNr : (0 : ℝ) ≤ (N : ℝ) ^ s.val := (Real.rpow_pos_of_pos hNpos _).le
  have ha₁ : 0 ≤ (N : ℝ) ^ (-s.val) * ((N : ℝ) ^ 2 * K * (N : ℝ) ^ s.val) :=
    mul_nonneg hNs (mul_nonneg (mul_nonneg (sq_nonneg _) hK0) hNr)
  have hb₁ : 0 ≤ (N : ℝ) ^ (-s.val) * (2 * (N : ℝ) ^ 2 * B + (N : ℝ) ^ 2 * D) :=
    mul_nonneg hNs (add_nonneg (mul_nonneg (by positivity) hB0) (mul_nonneg (by positivity) hD0))
  refine ⟨(N : ℝ) ^ (-s.val) * ((N : ℝ) ^ 2 * K * (N : ℝ) ^ s.val) +
      (N : ℝ) ^ (-s.val) * (2 * (N : ℝ) ^ 2 * B + (N : ℝ) ^ 2 * D), add_nonneg ha₁ hb₁,
    fun X => ?_⟩
  have hG0 : 0 ≤ gapPowerSum s.val X := by
    unfold gapPowerSum
    exact Finset.sum_nonneg fun k _ => Real.rpow_nonneg (gap_pos X _).le _
  -- The particle-particle sum.
  have hc : ∀ i j : Fin (N : ℕ),
      |(if j = i then (0 : ℝ) else loopKernel s.val f (X.val i) (X.val j))| ≤
        K * (N : ℝ) ^ s.val * gapPowerSum s.val X := by
    intro i j
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte, abs_zero]
      exact mul_nonneg (mul_nonneg hK0 hNr) hG0
    · simp only [hji, ↓reduceIte]
      have hij : i ≠ j := fun h => hji h.symm
      calc |loopKernel s.val f (X.val i) (X.val j)|
          ≤ K * dist ((X.val i - X.val j : ℝ) : UnitAddCircle) 0 ^ (-s.val) :=
            hK _ _ (coe_sub_ne_zero X hij)
        _ ≤ K * ((N : ℝ) ^ s.val * gapPowerSum s.val X) :=
            mul_le_mul_of_nonneg_left (dist_rpow_le_gapPowerSum X hij hs0) hK0
        _ = K * (N : ℝ) ^ s.val * gapPowerSum s.val X := by ring
  have hA : |∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
      (if j = i then (0 : ℝ) else loopKernel s.val f (X.val i) (X.val j))| ≤
      (N : ℝ) ^ 2 * (K * (N : ℝ) ^ s.val * gapPowerSum s.val X) := by
    calc _ ≤ ∑ i : Fin (N : ℕ), |∑ j : Fin (N : ℕ),
          (if j = i then (0 : ℝ) else loopKernel s.val f (X.val i) (X.val j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
          K * (N : ℝ) ^ s.val * gapPowerSum s.val X :=
          Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => hc i j)
      _ = (N : ℝ) ^ 2 * (K * (N : ℝ) ^ s.val * gapPowerSum s.val X) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- The particle-background sums.
  have hSI : |∑ i : Fin (N : ℕ), ∫ y in (0 : ℝ)..1, loopKernel s.val f (X.val i) y| ≤
      (N : ℝ) * B := by
    calc _ ≤ ∑ i : Fin (N : ℕ), |∫ y in (0 : ℝ)..1, loopKernel s.val f (X.val i) y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin (N : ℕ), B := Finset.sum_le_sum fun i _ => hB _
      _ = (N : ℝ) * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hSJ : |∑ j : Fin (N : ℕ), ∫ u in (0 : ℝ)..1, loopKernel s.val f u (X.val j)| ≤
      (N : ℝ) * B := by
    have e : (∑ j : Fin (N : ℕ), ∫ u in (0 : ℝ)..1, loopKernel s.val f u (X.val j)) =
        ∑ j : Fin (N : ℕ), ∫ y in (0 : ℝ)..1, loopKernel s.val f (X.val j) y :=
      Finset.sum_congr rfl fun j _ => integral_kernel_left_eq s.val f (X.val j)
    rw [e]
    calc _ ≤ ∑ j : Fin (N : ℕ), |∫ y in (0 : ℝ)..1, loopKernel s.val f (X.val j) y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin (N : ℕ), B := Finset.sum_le_sum fun j _ => hB _
      _ = (N : ℝ) * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Assemble the four terms.
  have hDD : |∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s.val f u v| ≤ D := hD
  have hE : |(∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
        (if j = i then (0 : ℝ) else loopKernel s.val f (X.val i) (X.val j)))
      - (N : ℝ) * (∑ i : Fin (N : ℕ), ∫ y in (0 : ℝ)..1, loopKernel s.val f (X.val i) y)
      - (N : ℝ) * (∑ j : Fin (N : ℕ), ∫ u in (0 : ℝ)..1, loopKernel s.val f u (X.val j))
      + (N : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, loopKernel s.val f u v| ≤
      (N : ℝ) ^ 2 * (K * (N : ℝ) ^ s.val * gapPowerSum s.val X) +
        (N : ℝ) * ((N : ℝ) * B) + (N : ℝ) * ((N : ℝ) * B) + (N : ℝ) ^ 2 * D := by
    have h1 := abs_le.mp hA
    have h2 := abs_le.mp (show |(N : ℝ) * (∑ i : Fin (N : ℕ),
        ∫ y in (0 : ℝ)..1, loopKernel s.val f (X.val i) y)| ≤ (N : ℝ) * ((N : ℝ) * B) by
      rw [abs_mul, abs_of_nonneg hNpos.le]
      exact mul_le_mul_of_nonneg_left hSI hNpos.le)
    have h3 := abs_le.mp (show |(N : ℝ) * (∑ j : Fin (N : ℕ),
        ∫ u in (0 : ℝ)..1, loopKernel s.val f u (X.val j))| ≤ (N : ℝ) * ((N : ℝ) * B) by
      rw [abs_mul, abs_of_nonneg hNpos.le]
      exact mul_le_mul_of_nonneg_left hSJ hNpos.le)
    have h4 := abs_le.mp (show |(N : ℝ) ^ 2 * ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1,
        loopKernel s.val f u v| ≤ (N : ℝ) ^ 2 * D by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left hDD (sq_nonneg _))
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  unfold loopFunctional
  have hfin := mul_le_mul_of_nonneg_left hE (show (0 : ℝ) ≤ (N : ℝ) ^ (-s.val) from hNs)
  rw [abs_mul, abs_of_nonneg hNs]
  calc (N : ℝ) ^ (-s.val) * |_| ≤ _ := hfin
    _ = (N : ℝ) ^ (-s.val) * ((N : ℝ) ^ 2 * K * (N : ℝ) ^ s.val) * gapPowerSum s.val X +
        (N : ℝ) ^ (-s.val) * (2 * (N : ℝ) ^ 2 * B + (N : ℝ) ^ 2 * D) := by ring
    _ ≤ _ := by nlinarith [mul_nonneg ha₁ hG0, mul_nonneg hb₁ hG0]

end Riesz1

end
