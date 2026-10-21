/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFinalEnvelopes
public import Riesz1.Variance.RegMicroFinalStatistics
public import Riesz1.Variance.RegMicroVarianceFar

/-!
# Applying the proved a priori theorem to the actual far pieces

The variance step for the fixed marked cutoffs and smooth remainder of
Lemma 5.3. This internal calculus-to-variance helper
consumes derivative bounds, never a probabilistic conclusion. Both
the Bakry–Émery criterion and the Prékopa–Leindler inequality are explicit
hypotheses, and every constant precedes `N` and the
observation scale.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- The far half of the microscopic decomposition, including its actual
cutoff support and the smooth remainder. Its derivative hypotheses are
the conclusions of `regMicro_far_derivatives_of_kernel`. -/
theorem regMicro_far_variance_of_derivatives
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (α ε : ℝ) (hα : P.val.2-1 ≤ α) (hε : 0 < ε)
    (n : ℕ+) (r₀ R A B : ℝ) (hr₀ : 0 < r₀) (hr1 : 2*r₀ ≤ 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ)*ℓ.val →
      let L := observationLength ℓ
      let K := (N : ℝ)*ℓ.val
      ∀ (a : Fin (n : ℕ) → ℝ) (e : Circle L → ℝ),
        (∀ j, ContDiff ℝ 1 (fun x : ℝ => microFarError L.val r₀ K⁻¹ a e j (x : Circle L))) →
        ContDiff ℝ 1 (fun x : ℝ => microFarRemainder L.val r₀ K⁻¹ a e (x : Circle L)) →
        (L.val/2 ≤ R ∨ (∀ z, R ≤ dist z 0 → microFarRemainder L.val r₀ K⁻¹ a e z = 0)) →
        (∀ j x, |deriv (fun t : ℝ => microFarError L.val r₀ K⁻¹ a e j (t : Circle L)) x| ≤
          A*K⁻¹^(1-P.val.2)*(max (dist (x : Circle L) (a j : Circle L)) K⁻¹)^(-(2-P.val.2+α))) →
        (∀ x, |deriv (fun t : ℝ => microFarRemainder L.val r₀ K⁻¹ a e (t : Circle L)) x| ≤
          B*K⁻¹^(1-P.val.2)) →
      ∃ hF : Integrable (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          ((∑ j, microFarError L.val r₀ K⁻¹ a e j ((X.val i/ℓ.val : ℝ) : Circle L)) +
            microFarRemainder L.val r₀ K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)))
          (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hF ≤
          ENNReal.ofReal (C*K^ε*(K^(2*α)+K^(3*P.val.2-2))) := by
  let lam := 1-P.val.2+α
  let T := (max R 2)^(1+lam)+(max R 2)^(3-P.val.2)
  let M := A+B*T+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hAM : A ≤ M := by dsimp [M]; nlinarith
  have hBM : B*T ≤ M := by dsimp [M]; linarith
  obtain ⟨D, hD, hb⟩ := reg_micro_far_rate_of_input
    (regMicroAPrioriInput_of_externals hBE hPL) P α ε hα hε (n.val+1)
  refine ⟨D*M^2, by positivity, fun N ℓ hK => ?_⟩
  dsimp only
  intro a e hc hr hsupp hd hdr
  let L := observationLength ℓ
  let K := (N : ℝ)*ℓ.val
  have hK0 : 0 < K := by dsimp [K]; linarith
  let f : Fin (n.val+1) → Circle L → ℝ :=
    Fin.cases (microFarRemainder L.val r₀ K⁻¹ a e) (microFarError L.val r₀ K⁻¹ a e)
  let c : Fin (n.val+1) → ℝ := Fin.cases 0 a
  have hfc : ∀ j, ContDiff ℝ 1 (fun x : ℝ => f j (x : Circle L)) :=
    Fin.forall_fin_succ.mpr ⟨hr, hc⟩
  have hfd : ∀ j x, |deriv (fun t : ℝ => f j (t : Circle L)) x| ≤
      (M*K⁻¹^(1-P.val.2))*cutoffMajorant P.val.2 lam K
        |centralRep L ((x-c j : ℝ) : Circle L)| := by
    refine Fin.forall_fin_succ.mpr ⟨?_, ?_⟩
    · intro x
      have hrem := hsupp
      have hh := regMicro_bounded_to_majorant L K R P.val.2 lam (B*K⁻¹^(1-P.val.2))
        hK (by dsimp [lam]; linarith) (by linarith [P.property.2.2]) (by positivity)
        (microFarRemainder L.val r₀ K⁻¹ a e) hrem hdr x
      dsimp only [f, c, Fin.cases_zero]
      simp only [sub_zero]
      apply hh.trans
      have hm : B*K⁻¹^(1-P.val.2)*T ≤ M*K⁻¹^(1-P.val.2) := by
        nlinarith [mul_le_mul_of_nonneg_right hBM (Real.rpow_nonneg (inv_nonneg.mpr hK0.le) (1-P.val.2))]
      exact mul_le_mul_of_nonneg_right hm (cutoffMajorant_nonneg hK0 _)
    · intro j x
      have hh := regMicro_power_to_majorant L K lam P.val.2 (A*K⁻¹^(1-P.val.2))
        (a j) hK0 (by positivity) (microFarError L.val r₀ K⁻¹ a e j)
        (fun z hz => microFarError_eq_zero_of_far hr₀ a e j (hr1.trans hz))
        (by simpa only [lam, show 1+(1-P.val.2+α)=2-P.val.2+α by ring] using hd j) x
      dsimp only [f, c, Fin.cases_succ]
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAM (by positivity)) (cutoffMajorant_nonneg hK0 _))
  obtain ⟨hFi, hv⟩ := hb N ℓ hK M hM.le c f hfc hfd
  have heq : (fun X : Configuration N => ∑ j, ∑ i : Fin (N : ℕ),
      f j ((X.val i/ℓ.val : ℝ) : Circle L)) =
      fun X : Configuration N => ∑ i : Fin (N : ℕ),
        ((∑ j, microFarError L.val r₀ K⁻¹ a e j ((X.val i/ℓ.val : ℝ) : Circle L))+
          microFarRemainder L.val r₀ K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)) := by
    funext X
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succ]
    dsimp only [f, Fin.cases_zero, Fin.cases_succ]
    exact add_comm _ _
  refine ⟨hFi.congr (Eventually.of_forall (congrFun heq)), ?_⟩
  exact (auxiliary_variance_congr _ hFi (Eventually.of_forall (congrFun heq.symm))).trans_le hv

end Riesz1.Internal
