/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlTransferBounds
public import Riesz1.Variance.ConvexificationEnergyLaw
public import Riesz1.Variance.ConvexificationVariance
public import Riesz1.Auxiliary.LoopCutoffRegularity
public import Riesz1.ToMathlib.VarianceTransferOn

/-!
# Measure transfer for the localized loop

Proposition 5.9. The anchored observable is
`loopCutoffF` evaluated at the vector `(0,y)`. Estimates restrict
the ambient total formula to the physical anchored domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff

namespace Riesz1

theorem varAl_anchorVector_mem {n : ℕ} {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) :
    anchorVector y ∈ orderedDomain n.succPNat := by
  rw [mem_orderedDomain_iff]
  simpa only [anchorVector_zero, anchorVector_succ, sub_zero] using
    (show (0 ≤ (0 : ℝ) ∧ (0 : ℝ) < 1) ∧
      (∀ j, 0 < y j ∧ y j < 1) ∧ StrictMono y from ⟨⟨le_rfl, zero_lt_one⟩, hy⟩)

/-- Every anchored law is carried by the physical anchored domain. -/
theorem varAl_ae_anchoredDomain (n : ℕ) (μ : Measure (Configuration n.succPNat)) :
    ∀ᵐ y ∂μ.map (anchorMap n.succPNat), y ∈ anchoredDomain n := by
  apply (ae_map_iff (measurable_anchorMap n.succPNat).aemeasurable
    (p := fun y => y ∈ anchoredDomain n) (measurableSet_anchoredDomain n)).2
  apply ae_of_all
  intro X
  rw [anchorMap_eq_anchorCoords]
  exact (mem_orderedDomain_iff n X.val).mp X.property |>.2

/-- Polynomial bounds and transfer, Proposition 5.9. The explicit polynomial
exponent and the coefficient are uniform in the particle number, scale and
profile. Only the Prékopa--Leindler inequality `External.PrekopaLeindler` is
needed for this proposition. -/
theorem varAl_transfer (hPL : External.PrekopaLeindler) (P : Parameters)
    {α γ ε C₀ : ℝ} (hα : P.val.2 - 1 < α) (hα2 : α < P.val.2 / 2)
    (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε ≤ 1 - P.val.2 / 2) (hC₀ : 0 < C₀)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ B C c : ℝ, 0 < B ∧ 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (θ : ℝ → ℝ), IsForcingCutoff θ →
        ∀ (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (n.succPNat : ℝ) * ℓ →
          ∀ (ψ : ℝ → ℝ), ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤
            C₀ * gradWeightOne P.val.2 (1 - P.val.2 + α) ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤
            C₀ * gradWeightTwo P.val.2 (1 - P.val.2 + α) ((n.succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          let K := (n.succPNat : ℝ) * ℓ
          let F := fun y : Fin n → ℝ => loopCutoffF χ P.val.2 γ ε n.succPNat ℓ ψ (anchorVector y)
          (∀ y ∈ anchoredDomain n, |F y| ≤ C * K ^ B) ∧
          (∀ y ∈ anchoredDomain n, y ∈ closure {z : Fin n → ℝ |
              z ∈ anchoredDomain n ∧
              fderiv ℝ (fun z => loopCutoff P.val.2 γ ε n.succPNat ℓ (anchorVector z)) z ≠ 0} →
            |gradLoop P.val.2 (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
              (anchorVector y)| ≤ C * K ^ B) ∧
          totalVariation (gibbsMeasure P n.succPNat)
            (nearestLaw P θ n.succPNat K (2 * γ) ε) ≤ C * Real.exp (-c * K ^ ε) ∧
          |variance F ((gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)) -
            variance F (nearestAnchoredLaw P θ n.succPNat K (2 * γ) ε)| ≤
              C * Real.exp (-c * K ^ ε) := by
  obtain ⟨Cf, hCf, hf⟩ := loopCutoffF_explicit_bound P.2.2.1 P.2.2.2 hα.le hα2 hγ hε hεs
    hχ hχc hχs hχ1 hχ01
  obtain ⟨Cl, hCl, hl⟩ := varAl_loop_good_bound P.2.2.1 P.2.2.2 hα.le hα2 hγ hε hεs
    hχ hχc hχs hχ1 hχ01
  obtain ⟨⟨ct, Ct, hct, hCt, ht⟩, -⟩ :=
    a_priori_convexity hPL (γ := 2 * γ) (by linarith) hε
  let B := (1 - P.val.2 + α) + 2 * γ + ε * (P.val.2 + 1)
  let M := (Cf + Cl + 1) * C₀
  have hb : 0 < 1 - P.val.2 + α := by linarith
  have hs : 0 < P.val.2 + 1 := by linarith [P.2.2.1]
  have hB : 0 < B := by dsimp [B]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨Ca, hCa, ha⟩ := rpow_mul_exp_neg_le_half (D := 2 * B) hε hct
  let C := M + Ct + 6 * M ^ 2 * Ct * Ca
  have hC : 0 < C := by dsimp [C]; nlinarith [show 0 ≤ 6 * M ^ 2 * Ct * Ca by positivity]
  have hMC : M ≤ C := by dsimp [C]; nlinarith [show 0 ≤ 6 * M ^ 2 * Ct * Ca by positivity]
  have hTC : Ct ≤ C := by dsimp [C]; nlinarith [show 0 ≤ 6 * M ^ 2 * Ct * Ca by positivity]
  have hAC : 6 * M ^ 2 * Ct * Ca ≤ C := by dsimp [C]; nlinarith [show 0 ≤ 6 * M ^ 2 * Ct * Ca by positivity]
  refine ⟨B, C, ct / 2, hB, hC, by linarith, ?_⟩
  intro n hn θ hθ ℓ hℓ _hℓ1 hK ψ hψ hp h1 h2
  let K := (n.succPNat : ℝ) * ℓ
  let F := fun y : Fin n → ℝ => loopCutoffF χ P.val.2 γ ε n.succPNat ℓ ψ (anchorVector y)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hN : 2 ≤ (n.succPNat : ℕ) := by simpa using hn
  have hfb : ∀ y ∈ anchoredDomain n, |F y| ≤ M * K ^ B := by
    intro y hy
    exact (hf C₀ n.succPNat ℓ ψ (anchorVector y) hC₀.le hN hℓ hK hψ hp h1 h2
      (varAl_anchorVector_mem hy) (anchorVector_zero y)).trans
        (mul_le_mul_of_nonneg_right (by dsimp [M]; nlinarith) (Real.rpow_nonneg hK0.le _))
  have hav : Continuous (anchorVector : (Fin n → ℝ) → Fin (n.succPNat : ℕ) → ℝ) :=
    continuous_pi fun k => continuous_anchorVector_apply k
  have hcut : ContinuousOn (loopCutoff P.val.2 γ ε n.succPNat ℓ) (orderedDomain n.succPNat) :=
    (loopCutoff_locallyLipschitzOn P.val.2 γ ε n.succPNat hℓ).continuousOn
  have hsupp : GradPartial n.succPNat ℓ γ → ∀ y : ℝ,
      (∀ m : ℤ, gradT n.succPNat ℓ γ / 4 ≤ |y - m|) →
      loopTransport χ n.succPNat ℓ γ ψ (y / ℓ) = 0 := by
    intro _hpart y hy
    unfold loopTransport
    simp only [_hpart, ↓reduceIte]
    have ht : 0 < gradT n.succPNat ℓ γ := by
      unfold gradT
      rw [ite_eq_left _hpart]
      exact div_pos (Real.rpow_pos_of_pos hK0 γ) (by positivity)
    have hrep := hy ⌊y + 1 / 2⌋
    have heq : ℓ * loopCircleRep ℓ (y / ℓ) = y - (⌊y + 1 / 2⌋ : ℤ) := by
      unfold loopCircleRep
      field_simp
    have hfar : 1 / 4 ≤ |ℓ * loopCircleRep ℓ (y / ℓ) / gradT n.succPNat ℓ γ| := by
      rw [heq, abs_div, abs_of_pos ht, le_div_iff₀ ht]
      linarith
    have hn : ℓ * loopCircleRep ℓ (y / ℓ) / gradT n.succPNat ℓ γ ∉ tsupport χ := by
      intro hh
      have := abs_lt.mpr (hχs hh)
      linarith
    rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]
  have hloop := (gradient_splitting_identity (contDiff_loopTransport hχ hψ hχs n.succPNat hℓ γ)
    hℓ (by simpa only [one_div] using
      loopTransport_periodic (N := n.succPNat) (γ := γ) hℓ χ hp) P.2.2.1 P.2.2.2 hsupp).1.continuousOn
  have hFc : ContinuousOn F (anchoredDomain n) :=
    (hcut.mul hloop).comp hav.continuousOn (fun _ hy => varAl_anchorVector_mem hy)
  have hTV := ht P θ hθ n.succPNat hN K hK
  have hTV' : totalVariation (gibbsMeasure P n.succPNat)
      (nearestLaw P θ n.succPNat K (2 * γ) ε) ≤ Ct * Real.exp (-(ct / 2) * K ^ ε) :=
    hTV.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg hK0.le ε])) hCt.le)
  refine ⟨fun y hy => (hfb y hy).trans (mul_le_mul_of_nonneg_right hMC (by positivity)),
    ?_, hTV'.trans (mul_le_mul_of_nonneg_right hTC (Real.exp_nonneg _)), ?_⟩
  · intro y _hy hys
    have hev : gradEvent P.val.2 (2 * γ) ε n.succPNat ℓ (anchorVector y) := by
      have hclosed := (varAl_isClosed_gradEvent P.val.2 (2 * γ) ε ℓ n.succPNat).preimage hav
      apply closure_minimal (t := {z : Fin n → ℝ |
        gradEvent P.val.2 (2 * γ) ε n.succPNat ℓ (anchorVector z)}) ?_ hclosed hys
      intro z hz
      have hpos : 0 < loopCutoff P.val.2 γ ε n.succPNat ℓ (anchorVector z) := by
        have hnonneg := (loopCutoff_mem_Icc P.val.2 γ ε ℓ (anchorVector z)).1
        apply lt_of_le_of_ne hnonneg
        intro heq
        apply hz.2
        apply IsLocalMin.fderiv_eq_zero
        exact Filter.Eventually.of_forall fun w => by
          change loopCutoff P.val.2 γ ε n.succPNat ℓ (anchorVector z) ≤
            loopCutoff P.val.2 γ ε n.succPNat ℓ (anchorVector w)
          rw [← heq]
          exact (loopCutoff_mem_Icc P.val.2 γ ε ℓ (anchorVector w)).1
      exact gradEvent_of_loopCutoff_pos hℓ ⟨_, varAl_anchorVector_mem hz.1⟩ hpos
    exact (hl C₀ n.succPNat ℓ ψ hC₀.le hℓ hK hψ hp h1 h2 _ hev (anchorVector_zero y)).trans
      (mul_le_mul_of_nonneg_right
        (show Cl * C₀ ≤ C from (by dsimp [M] at hMC; nlinarith)) (by positivity))
  · have := isProbabilityMeasure_gibbsMeasure P n.succPNat
    have := isProbabilityMeasure_nearestLaw (P := P) (N := n.succPNat) (K := K)
      (γ := 2 * γ) (ε := ε) hθ hK0
    let μ : Measure (Fin n → ℝ) := (gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)
    let ν : Measure (Fin n → ℝ) := nearestAnchoredLaw P θ n.succPNat K (2 * γ) ε
    have hμ : IsProbabilityMeasure μ :=
      (Measure.isProbabilityMeasure_map_iff (measurable_anchorMap n.succPNat).aemeasurable).2
        (isProbabilityMeasure_gibbsMeasure P n.succPNat)
    have hν : IsProbabilityMeasure ν :=
      isProbabilityMeasure_nearestAnchoredLaw P θ n.succPNat K (2 * γ) ε hθ hK0
    have hv := abs_variance_sub_le_on μ ν
      (measurableSet_anchoredDomain n) (varAl_ae_anchoredDomain n _)
      (varAl_ae_anchoredDomain n _) hFc (mul_nonneg hM.le (by positivity)) hfb
    have hmap := totalVariation_map_le (gibbsMeasure P n.succPNat)
      (nearestLaw P θ n.succPNat K (2 * γ) ε) (measurable_anchorMap _)
    calc |variance F ((gibbsMeasure P n.succPNat).map (anchorMap n.succPNat)) -
        variance F (nearestAnchoredLaw P θ n.succPNat K (2 * γ) ε)|
        ≤ 6 * (M * K ^ B) ^ 2 * (Ct * Real.exp (-ct * K ^ ε)) :=
          hv.trans (mul_le_mul_of_nonneg_left (hmap.trans hTV) (by positivity))
      _ = (6 * M ^ 2 * Ct) * (K ^ (2 * B) * Real.exp (-ct * K ^ ε)) := by
        rw [rpow_two_mul_eq_sq_rpow hK0.le]
        ring
      _ ≤ (6 * M ^ 2 * Ct) * (Ca * Real.exp (-(ct / 2) * K ^ ε)) :=
        mul_le_mul_of_nonneg_left (ha K hK) (by positivity)
      _ ≤ C * Real.exp (-(ct / 2) * K ^ ε) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hAC (Real.exp_nonneg _)

end Riesz1

end
