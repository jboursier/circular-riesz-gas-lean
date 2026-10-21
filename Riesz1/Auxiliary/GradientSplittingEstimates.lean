/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingEstimatesPacking
public import Riesz1.Auxiliary.GradientSplittingEstimatesStructure
public import Riesz1.Auxiliary.GradientSplittingEstimatesDisplacement

/-!
# Gradient splitting estimates, conditional only on quadrature

The estimates part of Lemma 5.7. The quadrature input is an
internal proposition giving precisely the quadrature part of Lemma 5.7
on the fields from earlier results. Its constants are chosen before `N`, `ℓ`, `C₀` and `ψ`.
The support premise uses circular distance, expressed using all integer
translates, as in the localized-loop identity.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1.Internal

noncomputable section

/-- The quadrature part of Lemma 5.7, on the objects from earlier results.
The exponent and smallness threshold are independent of `ε`. The multiplicative
constant can depend on `ε`. -/
def GradientSplittingQuadratureConclusion (s α γ : ℝ) : Prop :=
  ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₀ →
      ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (GradPartial N ℓ γ → ∀ y : ℝ,
        (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
      ∀ X ∈ orderedDomain N, gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε →
      ∀ i ∈ gradLabels N ℓ γ,
        |gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i| ≤
          C * C₀ * ((N : ℝ) * ℓ) ^ (κ * ε) *
            (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
              (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
                (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2))

/-- The three estimates (A2), (A3), and the translation derivative bound,
at one configuration. The structural conclusions are stated separately. -/
def GradientSplittingEstimatesAt (s α γ ε C κ C₀ ℓ : ℝ) (N : ℕ+)
    (ψ : ℝ → ℝ) (X : Fin (N : ℕ) → ℝ) : Prop :=
  (∀ i ∈ gradLabels N ℓ γ, |gradVlab s ψ N ℓ γ X i| ≤
    C * C₀ * ((N : ℝ) * ℓ) ^ (κ * ε) *
      (ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
        (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
          (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2))) ∧
  (∑ e ∈ Finset.Ico (0 : ℤ) N, (gradWgap s ψ N ℓ γ X e) ^ 2 ≤
    C * C₀ ^ 2 * ((N : ℝ) * ℓ) ^ (κ * ε) *
      ((N : ℝ) * ℓ + ((N : ℝ) * ℓ) ^ (2 * (1 - s + α)))) ∧
  |∑ k : Fin (N : ℕ), fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1)| ≤
    C * C₀ * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε)

/-- Increasing the constant and power preserves a nonnegative weighted bound. -/
lemma gradEst_bound_mono {A B F R K p q : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (hF : 0 ≤ F) (hR : 0 ≤ R) (hK : 1 ≤ K) (hpq : p ≤ q) :
    A * F * K ^ p * R ≤ B * F * K ^ q * R := by
  apply mul_le_mul_of_nonneg_right _ hR
  exact mul_le_mul (mul_le_mul_of_nonneg_right hAB hF)
    (Real.rpow_le_rpow_of_exponent_le hK hpq) (Real.rpow_nonneg (by linarith) _)
    (mul_nonneg (hA.trans hAB) hF)

/-- All assertions of the estimates part of Lemma 5.7, conditional
only on the full quadrature conclusion. Translation uniformity holds for every
common translation staying in the ordered lift chart and satisfying the anchor
bound. No restriction on its size is needed. -/
theorem gradient_splitting_estimates_of_quadrature {s α γ : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hα0 : s - 1 ≤ α) (hα1 : α < s / 2)
    (hγ : max 4 (2 / s) ≤ γ) (hquad : GradientSplittingQuadratureConclusion s α γ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
        2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₀ →
        ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
        (GradPartial N ℓ γ → ∀ y : ℝ,
          (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) →
        ContDiffOn ℝ ∞ (gradLoop s ψ N ℓ γ) (orderedDomain N) ∧
        (∀ X ∈ orderedDomain N,
          (∀ k : Fin (N : ℕ), fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1) =
            gradVfield s ψ N ℓ γ X k + gradWfield s ψ N ℓ γ X k) ∧
          (∀ k : Fin (N : ℕ), (∀ i ∈ gradLabels N ℓ γ, gradIndex N i ≠ k) →
            gradVfield s ψ N ℓ γ X k = 0 ∧ gradWfield s ψ N ℓ γ X k = 0) ∧
          (∀ e ∈ Finset.Ico (0 : ℤ) N,
            (¬∃ i ∈ gradLabels N ℓ γ, gradInWindow N ℓ γ (i + 1) ∧ i % (N : ℤ) = e) →
            gradWgap s ψ N ℓ γ X e = 0) ∧
          (∀ U : Fin (N : ℕ) → ℝ,
            ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k * U k =
              -∑ e ∈ Finset.Ico (0 : ℤ) N,
                gradWgap s ψ N ℓ γ X e * (N : ℝ) * gradEdgeDiff N U e) ∧
          ∑ k : Fin (N : ℕ), gradWfield s ψ N ℓ γ X k = 0) ∧
        (∀ X ∈ orderedDomain N, gradEvent s γ ε N ℓ X →
          |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε →
          GradientSplittingEstimatesAt s α γ ε C κ C₀ ℓ N ψ X) ∧
        (∀ X ∈ orderedDomain N, gradEvent s γ ε N ℓ X → ∀ c : ℝ,
          (fun k => X k + c) ∈ orderedDomain N →
          |(N : ℝ) * gradLift N (fun k => X k + c) 0| ≤ ((N : ℝ) * ℓ) ^ ε →
          GradientSplittingEstimatesAt s α γ ε C κ C₀ ℓ N ψ (fun k => X k + c)) := by
  have hγ4 : 4 ≤ γ := (le_max_left _ _).trans hγ
  have hγ1 : 1 < γ := by linarith
  have ha0 : 0 ≤ 1 - s + α := by linarith
  have ha : 1 - s + α < 1 - s / 2 := by linarith
  obtain ⟨εd, hεd, κd, hκd, hd⟩ := gradEst_displacement hs0 hs1 hα0 hα1 hγ4
  obtain ⟨εq, hεq, κq, hκq, hq⟩ := hquad
  obtain ⟨κw, hκw, hw⟩ := gradient_splitting_gap hs0 hs1 hα0 hα1 hγ1
  let εstar := min εd (min εq (min (1 / 8) ((1 - s / 2) / 8)))
  let κv := κd + κq
  let κ := κv + κw + 2
  have hκv : 0 < κv := by dsimp [κv]; linarith
  have hκ : 0 < κ := by dsimp [κ]; linarith
  refine ⟨εstar, by
    have : 0 < (1 - s / 2) / 8 := by linarith
    dsimp [εstar]
    positivity, κ, hκ, fun ε hε hεs => ?_⟩
  have hεd' : ε < εd := hεs.trans_le (min_le_left _ _)
  have hεrest := hεs.trans_le (min_le_right _ _)
  have hεq' : ε < εq := hεrest.trans_le (min_le_left _ _)
  have hεw : ε < min (1 / 8) ((1 - s / 2) / 8) := hεrest.trans_le (min_le_right _ _)
  have hεp : ε < (1 - s / 2) / 8 := hεw.trans_le (min_le_right _ _)
  obtain ⟨Cd, hCd, hd'⟩ := hd ε hε hεd'
  obtain ⟨Cq, hCq, hq'⟩ := hq ε hε hεq'
  obtain ⟨Cw, hCw, hw'⟩ := hw ε hε hεw
  obtain ⟨Cp, hCp, hp'⟩ := gradEst_sum_envelope hs0 hs1 ha0 ha hγ1 ε hε hεp
  let Cv := Cd + Cq
  let C := Cv * Cp + Cv + Cw + 1
  have hCv : 0 < Cv := by dsimp [Cv]; linarith
  have hC : 0 < C := by dsimp [C]; positivity
  have hvC : Cv ≤ C := by dsimp [C]; nlinarith [mul_pos hCv hCp]
  have hwC : Cw ≤ C := by dsimp [C]; nlinarith [mul_pos hCv hCp]
  have htC : Cv * Cp ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hper h1 h2 hsupp => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hid := gradient_splitting_identity hψ hℓ (by simpa only [one_div] using hper) hs0 hs1 hsupp
  have hbound : ∀ X ∈ orderedDomain N, gradEvent s γ ε N ℓ X →
      |(N : ℝ) * gradLift N X 0| ≤ ((N : ℝ) * ℓ) ^ ε →
      GradientSplittingEstimatesAt s α γ ε C κ C₀ ℓ N ψ X := by
    intro X hXD hX hanchor
    let R (i : ℤ) := ℓ⁻¹ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
      (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α) /
        (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)
    have hR (i : ℤ) : 0 ≤ R i := by
      have := gradWeightTwo_nonneg_unconditional s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
      have := circDist_nonneg 1 (gradLift N X i)
      dsimp [R]
      positivity
    have hv (i : ℤ) (hi : i ∈ gradLabels N ℓ γ) :
        |gradVlab s ψ N ℓ γ X i| ≤ Cv * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε) * R i := by
      have hdisp := hd' C₀ hC₀ N ℓ X ψ i hN hℓ hℓ1 hK hψ hper h1 h2 hX hanchor hi
      have hquad' := hq' N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hper h1 h2 hsupp X hXD hX hanchor i hi
      have hdisp' := hdisp.trans (gradEst_bound_mono hCd.le (le_refl Cd) hC₀ (hR i) hK
        (mul_le_mul_of_nonneg_right (by dsimp [κv]; linarith : κd ≤ κv) hε.le))
      have hquad'' := hquad'.trans (gradEst_bound_mono hCq.le (le_refl Cq) hC₀ (hR i) hK
        (mul_le_mul_of_nonneg_right (by dsimp [κv]; linarith : κq ≤ κv) hε.le))
      calc |gradVlab s ψ N ℓ γ X i| = |gradV1lab s ψ N ℓ γ X i +
          (gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i)| := by rw [gradV1lab]; ring_nf
        _ ≤ |gradV1lab s ψ N ℓ γ X i| + |gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i| := abs_add_le _ _
        _ ≤ Cd * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε) * R i +
            Cq * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε) * R i := add_le_add hdisp' hquad''
        _ = _ := by dsimp [Cv]; ring
    have hgap := (hw' N ℓ C₀ ψ X hN hℓ hℓ1 hK hC₀ hψ hper h1 hXD hX).2.2.2
    refine ⟨fun i hi => (hv i hi).trans (gradEst_bound_mono hCv.le hvC hC₀ (hR i) hK
      (mul_le_mul_of_nonneg_right (by dsimp [κ]; linarith : κv ≤ κ) hε.le)),
      hgap.trans (gradEst_bound_mono hCw.le hwC (sq_nonneg _) (by positivity) hK
        (mul_le_mul_of_nonneg_right (by dsimp [κ]; linarith : κw ≤ κ) hε.le)), ?_⟩
    have hsum : ∑ k : Fin (N : ℕ), fderiv ℝ (gradLoop s ψ N ℓ γ) X (Pi.single k 1) =
        ∑ i ∈ gradLabels N ℓ γ, gradVlab s ψ N ℓ γ X i := by
      simp_rw [hid.2.1 X hXD]
      rw [Finset.sum_add_distrib, gradWfield_sum_eq_zero hs0 hs1 hper hXD, add_zero,
        gradEst_sum_Vfield]
    have hp := hp' N ℓ X hN hℓ hℓ1 hK hX
    change ∑ i ∈ gradLabels N ℓ γ, R i ≤ _ at hp
    have hpow : ((N : ℝ) * ℓ) ^ (κv * ε) * ((N : ℝ) * ℓ) ^ (1 - s + α + 2 * ε) =
        ((N : ℝ) * ℓ) ^ (1 - s + α + (κv + 2) * ε) := by
      rw [← Real.rpow_add hK0]
      congr 1
      ring
    rw [hsum]
    calc |∑ i ∈ gradLabels N ℓ γ, gradVlab s ψ N ℓ γ X i|
        ≤ ∑ i ∈ gradLabels N ℓ γ, |gradVlab s ψ N ℓ γ X i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ gradLabels N ℓ γ, Cv * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε) * R i := Finset.sum_le_sum hv
      _ = (Cv * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε)) * ∑ i ∈ gradLabels N ℓ γ, R i := by rw [Finset.mul_sum]
      _ ≤ (Cv * C₀ * ((N : ℝ) * ℓ) ^ (κv * ε)) * (Cp * (N : ℝ) * ((N : ℝ) * ℓ) ^ (1 - s + α + 2 * ε)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (Cv * Cp) * (C₀ * (N : ℝ)) * ((N : ℝ) * ℓ) ^ (1 - s + α + (κv + 2) * ε) * 1 := by
          calc _ = (Cv * Cp) * (C₀ * (N : ℝ)) *
              (((N : ℝ) * ℓ) ^ (κv * ε) * ((N : ℝ) * ℓ) ^ (1 - s + α + 2 * ε)) := by ring
            _ = _ := by rw [hpow]; ring
      _ ≤ C * (C₀ * (N : ℝ)) * ((N : ℝ) * ℓ) ^ (1 - s + α + κ * ε) * 1 :=
          gradEst_bound_mono (mul_nonneg hCv.le hCp.le) htC (mul_nonneg hC₀ hN0.le)
            zero_le_one hK (by dsimp [κ]; nlinarith)
      _ = _ := by ring
  refine ⟨hid.1, ?_, hbound, ?_⟩
  · intro X hX
    exact ⟨hid.2.1 X hX, fun k hk => gradEst_fields_support ψ X k hk,
      fun e he hout => gradEst_gap_support ψ X he hout,
      gradient_splitting_gap_identity hs0 hs1 hper hX,
      gradWfield_sum_eq_zero hs0 hs1 hper hX⟩
  · intro X _ hX c hY hanchor
    exact hbound _ hY ((gradEst_event_translate_iff s γ ε N ℓ X c).mpr hX) hanchor

end

end Riesz1.Internal
