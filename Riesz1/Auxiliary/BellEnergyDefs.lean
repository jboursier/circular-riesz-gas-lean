/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellQuadrature
public import Riesz1.Variance.LoopScaleIntegrability

/-!
# The quadratic loop energy

The carrier is generalized to the periodic
Lipschitz profiles. The definition is the four empirical/background terms
of the signed fluctuation integral, with the particle diagonal omitted.
The scale factor is included in `loopScaleField`, so the squared difference
is exactly `ℓ² (ψ(x/ℓ) - ψ(y/ℓ))²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The unnormalized quadratic pair kernel. Its value on the diagonal is zero
because the squared difference is zero. No branch is used. -/
def bellPairKernel (s : ℝ) (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  iteratedDeriv 2 (hurwitzKernel s) (x - y) * (f x - f y) ^ 2

/-- The same kernel in the displacement variable used for background integrals. -/
def bellPairIntegrand (s : ℝ) (f : ℝ → ℝ) (x u : ℝ) : ℝ :=
  iteratedDeriv 2 (hurwitzKernel s) u * (f (x - u) - f x) ^ 2

/-- The quadratic loop energy, on its full periodic Lipschitz carrier. -/
def bellQuadraticLoop (s : RieszExponent) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) : ℝ :=
  (N : ℝ) ^ (-s.val) *
    ((∑ p ∈ (Finset.univ : Finset (Fin (N : ℕ))).offDiag,
        bellPairKernel s.val (loopScaleField ℓ.val ψ.val) (X.val p.1) (X.val p.2)) -
      (N : ℝ) * (∑ i : Fin (N : ℕ), ∫ y in (0 : ℝ)..1,
        bellPairKernel s.val (loopScaleField ℓ.val ψ.val) (X.val i) y) -
      (N : ℝ) * (∑ j : Fin (N : ℕ), ∫ x in (0 : ℝ)..1,
        bellPairKernel s.val (loopScaleField ℓ.val ψ.val) x (X.val j)) +
      (N : ℝ) ^ 2 * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        bellPairKernel s.val (loopScaleField ℓ.val ψ.val) x y))

lemma bellPairKernel_symm (s : ℝ) (f : ℝ → ℝ) (x y : ℝ) :
    bellPairKernel s f x y = bellPairKernel s f y x := by
  unfold bellPairKernel
  rw [show y - x = -(x - y) by ring, iteratedDeriv_two_neg]
  ring

lemma bellPairKernel_diag (s : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    bellPairKernel s f x x = 0 := by simp [bellPairKernel]

/-- Joint measurability of the quadratic kernel. -/
lemma measurable_bellPairKernel (s : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun p : ℝ × ℝ => bellPairKernel s f p.1 p.2) := by
  unfold bellPairKernel
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact ((measurable_deriv (deriv (hurwitzKernel s))).comp
    (measurable_fst.sub measurable_snd)).mul
      (((hf.measurable.comp measurable_fst).sub (hf.measurable.comp measurable_snd)).pow_const 2)

/-- The particle-background integral is a measurable function of its anchor. -/
lemma measurable_bellPair_background (s : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun x : ℝ => ∫ y in (0 : ℝ)..1, bellPairKernel s f x y) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  exact (((measurable_bellPairKernel s hf).stronglyMeasurable).integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable

/-- The displacement integrand is bounded by an integrable endpoint majorant. -/
lemma bellPair_majorant (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ x y : ℝ, ((x - y : ℝ) : UnitAddCircle) ≠ 0 →
        |bellPairKernel s.val f x y| ≤ K * dist ((x - y : ℝ) : UnitAddCircle) 0 ^ (-s.val)) ∧
      (∀ x u : ℝ, 0 < u → u < 1 →
        |bellPairIntegrand s.val f x u| ≤ K * (u ^ (-s.val) + (1 - u) ^ (-s.val))) := by
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_hurwitzKernel_bound s.val s.2.1 s.2.2 2
  let K := C * (M : ℝ) ^ 2
  have hK : 0 ≤ K := mul_nonneg hC.le (sq_nonneg _)
  have hpoint (x y : ℝ) (hne : ((x - y : ℝ) : UnitAddCircle) ≠ 0) :
      |bellPairKernel s.val f x y| ≤ K * dist ((x - y : ℝ) : UnitAddCircle) 0 ^ (-s.val) := by
    let d := dist ((x - y : ℝ) : UnitAddCircle) 0
    have hd : 0 < d := dist_pos.mpr hne
    have hdiff : |f x - f y| ≤ (M : ℝ) * d := by
      simpa only [show y + (x - y) = x by ring] using loopScale_lipschitz_increment hf hp y (x - y)
    have hder := hb (x - y) hne
    norm_num only [Nat.cast_ofNat] at hder
    unfold bellPairKernel
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f x - f y))]
    calc _ ≤ (C * d ^ (-s.val - 2)) * ((M : ℝ) * d) ^ 2 := by
          apply mul_le_mul hder _ (sq_nonneg _) (by positivity)
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdiff 2
      _ = K * (d ^ (-s.val - 2) * d ^ 2) := by dsimp [K]; ring
      _ = _ := by rw [rpow_mul_sq_two hd]
  refine ⟨K, hK, hpoint, ?_⟩
  intro x u hu0 hu1
  have he : bellPairIntegrand s.val f x u = bellPairKernel s.val f x (x - u) := by
    unfold bellPairIntegrand bellPairKernel
    rw [sub_sub_cancel]
    ring
  rw [he]
  have hne : ((x - (x - u) : ℝ) : UnitAddCircle) ≠ 0 := by
    rw [sub_sub_cancel]
    exact coe_ne_zero_of_mem_Ioo01 hu0 hu1
  refine (hpoint x (x - u) hne).trans ?_
  rw [sub_sub_cancel]
  exact mul_le_mul_of_nonneg_left (dist_rpow_le_majorant hu0 hu1) hK

end Riesz1

end
