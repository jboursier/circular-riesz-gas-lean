/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriBoundEnvelope
public import Riesz1.Variance.APrioriBoundLocalization
public import Riesz1.Variance.APrioriComparisonLemma

/-!
# The localized gradient in the a priori bound

The literal Euclidean gradient of the localized statistic has the
coordinate bound required by Lemma 5.2.
The estimate includes every scale `K ≥ 1`, and its constants are chosen
before the particle number, scale and test function.
-/

public section

noncomputable section

open MeasureTheory Set InnerProductSpace Classical

namespace Riesz1.Internal

/-- A periodic derivative bound on the half period gives the bound at
the circular distance, for every real argument. -/
theorem a_priori_periodic_derivative {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f : ℝ → ℝ} (hper : Function.Periodic f (1 / ℓ))
    {g : ℝ → ℝ}
    (hder : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2), |deriv f u| ≤ g |u|)
    (x : ℝ) : |deriv f (x / ℓ)| ≤ g (circDist 1 x / ℓ) := by
  have hdper : Function.Periodic (deriv f) (1 / ℓ) := by
    intro u
    have h := deriv_comp_add_const f (1 / ℓ) u
    rw [show (fun v => f (v + 1 / ℓ)) = f from funext hper] at h
    exact h.symm
  let q : ℤ := round x
  let u := (x - (q : ℝ)) / ℓ
  have he : u = x / ℓ - (q : ℝ) * (1 / ℓ) := by dsimp [u]; ring
  have hdist : |u| = circDist 1 x / ℓ := by
    rw [APG.circDist_one_eq_abs_sub_round]
    dsimp [u, q]
    rw [abs_div, abs_of_pos hℓ]
  have hu : |u| ≤ 1 / ℓ / 2 := by
    dsimp [u, q]
    rw [abs_div, abs_of_pos hℓ, show 1 / ℓ / 2 = (1 / 2) / ℓ by ring]
    exact div_le_div_of_nonneg_right (abs_sub_round x) hℓ.le
  have hb := hder u ⟨by linarith [neg_abs_le u], (le_abs_self u).trans hu⟩
  rw [he, hdper.sub_int_mul_eq q, ← he, hdist] at hb
  exact hb

/-- The exact Euclidean gradient of the localized statistic. -/
theorem localizedStatistic_gradient_apply (n : ℕ) (ℓ : ℝ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (I : Finset (Fin (n + 1)))
    (y : AnchoredEuclidean n) (i : Fin n) :
    gradient (fun z : AnchoredEuclidean n =>
      ∑ j ∈ I, f (anchorVector (WithLp.ofLp z) j / ℓ)) y i =
        if i.succ ∈ I then deriv f (y i / ℓ) / ℓ else 0 := by
  let F := fun z : AnchoredEuclidean n => ∑ j ∈ I, f (anchorVector (WithLp.ofLp z) j / ℓ)
  have hd := (localizedStatistic_hasFDerivAt n ℓ f hf I (WithLp.ofLp y)).comp y
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).hasFDerivAt
  have he := hd.differentiableAt.hasGradientAt.fderiv_apply (y := EuclideanSpace.single i 1)
  rw [hd.fderiv] at he
  have hinner : inner ℝ (gradient F y) (EuclideanSpace.single i 1) = gradient F y i := by
    rw [EuclideanSpace.inner_single_right]
    simp only [RCLike.conj_to_real, one_mul]
  change _ = inner ℝ (gradient F y) (EuclideanSpace.single i 1) at he
  rw [hinner] at he
  rw [← he]
  change (∑ j ∈ I, (deriv f (anchorVector (WithLp.ofLp y) j / ℓ) / ℓ) • anchorCoord n j)
    (WithLp.ofLp (EuclideanSpace.single i 1)) = _
  rw [sum_apply]
  simp only [smul_apply, smul_eq_mul]
  have hc (j : Fin (n + 1)) (z : Fin n → ℝ) : anchorCoord n j z = anchorVector z j :=
    anchorCoord_apply n z j
  simp only [hc]
  let b : Fin (n + 1) → ℝ := fun j => deriv f (anchorVector (WithLp.ofLp y) j / ℓ) / ℓ
  change (∑ j ∈ I, b j * anchorVector (WithLp.ofLp (EuclideanSpace.single i 1)) j) = _
  have ha (j : Fin (n + 1)) :
      anchorVector (WithLp.ofLp (EuclideanSpace.single i (1 : ℝ))) j =
        if j = i.succ then 1 else 0 := by
    induction j using Fin.cases with
    | zero =>
      have hz : (0 : Fin (n + 1)) ≠ i.succ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      change 0 = if (0 : Fin (n + 1)) = i.succ then 1 else 0
      rw [ite_eq_right hz]
    | succ j => simp [anchorVector, Pi.single_apply, eq_comm]
  simp only [ha, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [b, anchorVector_succ]

/-- The spatial-to-label derivative estimate on the good event, with
the augmented weight. This proves the pointwise estimate in the proof
of Lemma 5.2, uniformly also for bounded `K`. -/
theorem a_priori_derivative_on_good (s lam γ ε : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hlam : 0 ≤ lam) (hγ : 1 < γ)
    (hε : 0 < ε) (hεs : ε ≤ (1 - s / 2) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 0 < ℓ →
      1 ≤ ((N : ℕ) : ℝ) * ℓ → ∀ f : ℝ → ℝ, Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ cutoffMajorant s lam (((N : ℕ) : ℝ) * ℓ) |u|) →
      ∀ X : Configuration N, X ∈ goodEvent N s (((N : ℕ) : ℝ) * ℓ) γ ε →
      ∀ i : Fin (N : ℕ), i ∈ window N (((N : ℕ) : ℝ) * ℓ) γ → i ≠ ⟨0, N.pos⟩ →
        |deriv f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)| / ℓ ≤
          C * (((N : ℕ) : ℝ) * ℓ) ^ ((3 + lam) * ε) *
            (((N : ℕ) : ℝ) * augmentedComparisonWeight N (((N : ℕ) : ℝ) * ℓ) s lam ε i) := by
  obtain ⟨C, hC, hb⟩ := a_priori_envelope s lam γ ε hs hs1 hlam (by linarith) hε hεs
  refine ⟨C, hC, fun N ℓ hℓ hK f hper hder X hX i hi hi0 => ?_⟩
  let K := ((N : ℕ) : ℝ) * ℓ
  let t := circDist 1 (X.val i - X.val ⟨0, N.pos⟩) / ℓ
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hd : 1 ≤ (labelDistToOne N i : ℝ) := by
    have h : 1 ≤ labelDistToOne N i := APrioriComparison.distance_pos hi0
    exact_mod_cast h
  have hz : (⟨0, N.pos⟩ : Fin (N : ℕ)) ∈ window N K γ := origin_mem_window N hK
  have he : K * t = ((N : ℕ) : ℝ) * circDist 1 (X.val i - X.val ⟨0, N.pos⟩) := by
    dsimp [K, t]
    field_simp
  have hlow : K ^ (-ε) * (labelDistToOne N i : ℝ) ≤ K * t := by
    rw [he]
    have h := APG.lower_comparison X hs hs1 hK (by linarith)
      (by nlinarith) hX hz hi
    simpa only [labelDistToOne, cyclicIndexDistance, Nat.dist_comm] using h
  have herr : |K * t - (labelDistToOne N i : ℝ)| ≤
      K ^ ε * (labelDistToOne N i : ℝ) ^ (s / 2) := by
    rw [he]
    exact (a_priori_circular_error X i).trans (APG.anchored_error X hK hX hi)
  have hbound := hb N K hK i hi hd t hlow herr
  have hf := a_priori_periodic_derivative hℓ hper hder (X.val i - X.val ⟨0, N.pos⟩)
  have hN : 0 < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hr : ℓ⁻¹ = ((N : ℕ) : ℝ) * K⁻¹ := by dsimp [K]; field_simp
  calc
    _ ≤ cutoffMajorant s lam K t / ℓ := div_le_div_of_nonneg_right hf hℓ.le
    _ = ((N : ℕ) : ℝ) * (K⁻¹ * cutoffMajorant s lam K t) := by rw [div_eq_mul_inv, hr]; ring
    _ ≤ ((N : ℕ) : ℝ) * (C * K ^ ((3 + lam) * ε) * augmentedComparisonWeight N K s lam ε i) :=
      mul_le_mul_of_nonneg_left hbound hN.le
    _ = _ := by ring

end Riesz1.Internal

end
