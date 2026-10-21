/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroPositiveLocal

/-!
# The actual near cutoff for positive exponents

Changing from profile coordinates to `u=Nx` converts each distance power
by exactly `K^α`. Local square integrability is proved in the predecessor
module. The statement includes every particle number and every `K ≥ 1`.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The positive-exponent near step of Lemma 5.3.
Only the kernel's pointwise envelope is required of the error representative. -/
theorem micro_near_positive_of_envelope (P : Parameters) (m : ℕ) (α : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1/2) :
    ∃ D : ℝ, 0 < D ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (ℓ : Scale),
      1 ≤ (N : ℝ)*ℓ.val →
      let L := observationLength ℓ
      let K := (N : ℝ)*ℓ.val
      ∀ a : Fin m → ℝ,
        (∀ i j, i ≠ j → 8*K⁻¹ ≤ dist (a i : Circle L) (a j : Circle L)) →
      ∀ A : ℝ, 0 ≤ A → ∀ e : Circle L → ℝ, Measurable e →
        (∀ x, (∀ j, x ≠ (a j : Circle L)) →
          |e x| ≤ A*(K⁻¹^(-α) + ∑ j, dist x (a j : Circle L)^(-α))) →
      ∃ hF : Integrable (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) hF ≤
            ENNReal.ofReal (D*A^2*K^(2*α)) := by
  classical
  obtain ⟨D, hD, hb⟩ := reg_micro_positive_local_variance P m α hα0 hα1
  refine ⟨D, hD, fun hPL N ℓ hK => ?_⟩
  dsimp only
  intro a hsep A hA e he hbound
  let L := observationLength ℓ
  let K := (N : ℝ)*ℓ.val
  have hN : 0 < (N : ℝ) := by exact_mod_cast N.pos
  let : Fact (0 < (N : ℝ)) := ⟨hN⟩
  let : NeZero (N : ℝ) := ⟨hN.ne'⟩
  have : NullSingletonClass (volume : Measure (AddCircle (N : ℝ))) := ⟨fun x => by
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    simp only [mul_zero, min_eq_right hN.le, ENNReal.ofReal_zero]⟩
  have hK0 : 0 < K := mul_pos hN ℓ.property.1
  have hh : 0 < K⁻¹ := inv_pos.mpr hK0
  have hKL : K*L.val = (N : ℝ) := by
    dsimp [K, L, observationLength]
    field_simp [ℓ.property.1.ne']
  have hratio : L.val/(N : ℝ) = K⁻¹ := by
    dsimp [L, K, observationLength]
    rw [mul_inv_rev, div_eq_mul_inv]
  let d := AddCircle.equivAddCircle (N : ℝ) L.val hN.ne' L.property.ne'
  let g := microNearError L.val K⁻¹ a e
  let f : AddCircle (N : ℝ) → ℝ := fun u => g (d u)
  have hd : Continuous d := AddCircle.continuous_equivAddCircle ..
  have hf : Measurable f :=
    ((microCutoffSum_measurable L.property (2*K⁻¹) a).mul he).comp hd.measurable
  have hcenter (j : Fin m) : d ((K*a j : ℝ) : AddCircle (N : ℝ)) = (a j : Circle L) := by
    rw [show d = AddCircle.equivAddCircle (N : ℝ) L.val hN.ne' L.property.ne' from rfl,
      AddCircle.equivAddCircle_apply_mk]
    congr 1
    field_simp
    linear_combination (a j)*hKL
  have hscale (u : AddCircle (N : ℝ)) (j : Fin m) :
      dist (d u) (a j : Circle L) = K⁻¹ * dist u ((K*a j : ℝ) : AddCircle (N : ℝ)) := by
    rw [← hcenter j, circleDilation_dist hN L.property, hratio]
  have henv : ∀ᵐ u : AddCircle (N : ℝ) ∂volume,
      |f u| ≤ (A*K^α) * (1 + ∑ j, dist u ((K*a j : ℝ) : AddCircle (N : ℝ))^(-α)) := by
    filter_upwards [(Set.countable_range (fun j => ((K*a j : ℝ) : AddCircle (N : ℝ)))).ae_notMem volume]
      with u hu
    have hnot (j : Fin m) : d u ≠ (a j : Circle L) := by
      intro hj
      have huj : u = ((K*a j : ℝ) : AddCircle (N : ℝ)) := d.injective (hj.trans (hcenter j).symm)
      exact hu ⟨j, huj.symm⟩
    have hen := (microNearError_abs_le hh a hsep e (d u)).trans (hbound _ hnot)
    have hp : K⁻¹^(-α) = K^α := by
      rw [Real.inv_rpow hK0.le, ← Real.rpow_neg hK0.le, neg_neg]
    have heq : A*(K⁻¹^(-α) + ∑ j, dist (d u) (a j : Circle L)^(-α)) =
        (A*K^α) * (1 + ∑ j, dist u ((K*a j : ℝ) : AddCircle (N : ℝ))^(-α)) := by
      simp_rw [hscale, Real.mul_rpow hh.le dist_nonneg, hp]
      rw [← Finset.mul_sum]
      ring
    exact hen.trans_eq heq
  have hsupp (u : AddCircle (N : ℝ))
      (hu : u ∉ ⋃ j, Metric.closedBall ((K*a j : ℝ) : AddCircle (N : ℝ)) 4) : f u = 0 := by
    apply microNearError_eq_zero_of_far hh a e
    intro j
    have hn : u ∉ Metric.closedBall ((K*a j : ℝ) : AddCircle (N : ℝ)) 4 :=
      fun hj => hu (mem_iUnion.mpr ⟨j, hj⟩)
    have hdist : 4 ≤ dist u ((K*a j : ℝ) : AddCircle (N : ℝ)) := (lt_of_not_ge hn).le
    rw [hscale]
    nlinarith [mul_le_mul_of_nonneg_left hdist hh.le]
  obtain ⟨hF, hv⟩ := hb hPL N (fun j => K*a j) (A*K^α) (by positivity) f hf henv hsupp
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
  have hp : (K^α)^2 = K^(2*α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    congr 1
    ring
  refine ⟨hF, ?_⟩
  simpa only [mul_pow, hp, mul_assoc] using hv

end Riesz1.Internal
