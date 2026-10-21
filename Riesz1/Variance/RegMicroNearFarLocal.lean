/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroNearFarCutoffs
public import Riesz1.Variance.RegMicroVarianceLocal
public import Riesz1.ToMathlib.CircleDilationSupport

/-!
# The actual bounded near error at microscopic scale

The `4h` support of `microNearError` becomes a union of arcs of length
eight on `N𝕋` when `h=(Nℓ)⁻¹`. The local variance lemma therefore applies
to the actual cutoff product. Constants precede the error, scale, marks
and particle number. In particular the result includes `N=1`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The bounded-envelope near step of Lemma 5.3, for
the literal cutoff product on the original profile circle. -/
theorem micro_near_variance_of_bound (P : Parameters) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (ℓ : Scale),
      1 ≤ (N : ℝ)*ℓ.val →
      let L := observationLength ℓ
      let K := (N : ℝ)*ℓ.val
      ∀ (a : Fin m → ℝ),
        (∀ i j, i ≠ j → 8*K⁻¹ ≤ dist (a i : Circle L) (a j : Circle L)) →
      ∀ (A : ℝ), 0 ≤ A → ∀ e : Circle L → ℝ, Measurable e →
        (∀ x, |e x| ≤ A) →
      ∃ hF : Integrable (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) hF ≤
            ENNReal.ofReal (C*A^2) := by
  obtain ⟨C, hC, hb⟩ := reg_micro_bounded_near_variance P 8 (by norm_num) m
  refine ⟨C, hC, fun hPL N ℓ hK => ?_⟩
  let L := observationLength ℓ
  let K := (N : ℝ)*ℓ.val
  have hN : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < K := mul_pos hN ℓ.property.1
  have hKL : K*L.val = (N : ℝ) := by
    dsimp [K, L, observationLength]
    field_simp [ℓ.property.1.ne']
  have hratio : L.val / (N : ℝ) = K⁻¹ := by
    dsimp [L, K, observationLength]
    rw [mul_inv_rev, div_eq_mul_inv]
  dsimp only
  intro a hsep A hA e he heA
  let d := AddCircle.equivAddCircle (N : ℝ) L.val hN.ne' L.property.ne'
  let g := microNearError L.val K⁻¹ a e
  let f : AddCircle (N : ℝ) → ℝ := fun u => g (d u)
  have hd : Continuous d := AddCircle.continuous_equivAddCircle ..
  have hgc : Measurable g := by
    exact (microCutoffSum_measurable L.property (2*K⁻¹) a).mul he
  have hf : Measurable f := hgc.comp hd.measurable
  have hfa (u : AddCircle (N : ℝ)) : |f u| ≤ A :=
    (microNearError_abs_le (inv_pos.mpr hK0) a hsep e (d u)).trans (heA _)
  have hcenter (j : Fin m) : d ((K*a j : ℝ) : AddCircle (N : ℝ)) = (a j : Circle L) := by
    rw [show d = AddCircle.equivAddCircle (N : ℝ) L.val hN.ne' L.property.ne' from rfl,
      AddCircle.equivAddCircle_apply_mk]
    congr 1
    field_simp
    linear_combination (a j)*hKL
  have hsupp (u : AddCircle (N : ℝ))
      (hu : u ∉ ⋃ j, (fun t : ℝ => (t : AddCircle (N : ℝ))) '' Icc (K*a j-4) (K*a j+4)) :
      f u = 0 := by
    apply microNearError_eq_zero_of_far (inv_pos.mpr hK0) a e
    intro j
    have hn : u ∉ Metric.closedBall ((K*a j : ℝ) : AddCircle (N : ℝ)) 4 := by
      rw [circle_closedBall_eq_image_interval]
      exact fun hj => hu (mem_iUnion.mpr ⟨j, hj⟩)
    have hdist : 4 ≤ dist u ((K*a j : ℝ) : AddCircle (N : ℝ)) :=
      (lt_of_not_ge hn).le
    rw [← hcenter j, circleDilation_dist hN L.property, hratio]
    nlinarith [mul_le_mul_of_nonneg_left hdist (inv_pos.mpr hK0).le]
  have : Fact (0 < (N : ℝ)) := ⟨hN⟩
  obtain ⟨hF, hv⟩ := hb hPL N (fun j => K*a j-4) (fun j => K*a j+4)
    (fun j => by ring_nf; norm_num) A hA f hf hfa hsupp
  have heval (X : Configuration N) : (∑ i : Fin (N : ℕ), f ((N : ℝ)*X.val i)) =
      ∑ i : Fin (N : ℕ), g ((X.val i/ℓ.val : ℝ) : Circle L) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f, d]
    rw [AddCircle.equivAddCircle_apply_mk]
    congr 1
    congr 1
    dsimp [L, observationLength]
    field_simp
  simp_rw [heval] at hF hv
  exact ⟨hF, hv⟩

/-- Restoring the smoothing envelope gives exactly the near-piece power
`K^(2α)`. The exponent is unrestricted in this algebraic consequence. -/
theorem micro_near_rate_of_bound (P : Parameters) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (ℓ : Scale),
      1 ≤ (N : ℝ)*ℓ.val →
      let L := observationLength ℓ
      let K := (N : ℝ)*ℓ.val
      ∀ (a : Fin m → ℝ),
        (∀ i j, i ≠ j → 8*K⁻¹ ≤ dist (a i : Circle L) (a j : Circle L)) →
      ∀ (α M : ℝ), 0 ≤ M → ∀ e : Circle L → ℝ, Measurable e →
        (∀ x, |e x| ≤ M*K⁻¹^(-α)) →
      ∃ hF : Integrable (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) hF ≤
            ENNReal.ofReal (C*M^2*K^(2*α)) := by
  obtain ⟨C, hC, hb⟩ := micro_near_variance_of_bound P m
  refine ⟨C, hC, fun hPL N ℓ hK => ?_⟩
  dsimp only
  intro a hsep α M hM e he hbound
  let K := (N : ℝ)*ℓ.val
  have hK0 : 0 < K := by dsimp [K]; linarith
  obtain ⟨hF, hv⟩ := hb hPL N ℓ hK a hsep (M*K⁻¹^(-α)) (by positivity) e he hbound
  have hp : (K⁻¹ ^ (-α))^2 = K^(2*α) := by
    rw [Real.inv_rpow hK0.le, ← Real.rpow_neg hK0.le, neg_neg,
      ← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    congr 1
    ring
  refine ⟨hF, ?_⟩
  simpa only [mul_pow, hp, mul_assoc] using hv

end Riesz1.Internal

end
