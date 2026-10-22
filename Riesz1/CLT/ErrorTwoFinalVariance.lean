/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoPieces
public import Riesz1.Variance.VarAlPiecesDerivativeCutoffs
public import Riesz1.Variance.APrioriConclusion
import all Riesz1.Variance.LoopForce

/-!
# Variance assembly for pieces of the transport derivative

The transport derivative is a sum of fixed periodic cutoff pieces and
a regular remainder. Apply the a priori estimate with the singular
exponent to each cutoff piece and with exponent zero to the remainder.
The centers, cutoff radius and number of pieces precede the observation scale.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The a priori maximum power is bounded by the required sum. -/
theorem errorTwo_cutoff_power {K : ℝ} (hK : 1 ≤ K) (s b ε : ℝ) :
    K ^ (ε + max (2 * b) s) ≤ K ^ ε * (K ^ s + K ^ (2 * b)) := by
  rw [Real.rpow_add (by linarith : 0 < K)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
  rcases le_total (2 * b) s with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_right (Real.rpow_nonneg (by linarith) _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_left (Real.rpow_nonneg (by linarith) _)

/-- A-priori variance for a periodic `C¹` function with a translated
single-center derivative bound. Integrability is concluded. -/
theorem errorTwo_fluctuation_piece_of_input (hAP : APrioriConclusion)
    (P : Parameters) (b ε c : ℝ) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), 1 ≤ (N : ℝ) * a.val →
      ∀ (M : ℝ), 0 ≤ M → ∀ f : ℝ → ℝ,
        ContDiff ℝ 1 f → Function.Periodic f a.val⁻¹ →
        (∀ u, |deriv f u| ≤
          M * gradWeightTwo P.val.2 b ((N : ℝ) * a.val) a.val⁻¹ (u - c)) →
        ∃ hF : Integrable (fun X : Configuration N =>
          fluctIntegral (fun u => f (u / a.val)) N X.val) (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ hF ≤
            ENNReal.ofReal (C * M ^ 2 * (((N : ℝ) * a.val) ^ ε *
              (((N : ℝ) * a.val) ^ P.val.2 + ((N : ℝ) * a.val) ^ (2 * b)))) := by
  obtain ⟨C, hC, hbound⟩ := hAP P b hb ε hε 1 one_pos c
  refine ⟨C, hC, fun N a hK M hM f hf hp hd => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  let g : Circle (observationLength a) → ℝ := hp.lift
  have hg : (fun u : ℝ => g (u : Circle (observationLength a))) = f := by
    funext u
    exact hp.lift_coe u
  have hgc : ContDiff ℝ 1 (fun u : ℝ => g (u : Circle (observationLength a))) := by
    rwa [hg]
  have hgd : ∀ u : ℝ, |deriv (fun t : ℝ => g (t : Circle (observationLength a))) u| ≤
      M * aPrioriEnvelope P.val.2 b ((N : ℝ) * a.val) 1
        |centralRep (observationLength a) ((u - c : ℝ) : Circle (observationLength a))| := by
    intro u
    rw [hg]
    have hh := (hd u).trans (mul_le_mul_of_nonneg_left
      (errorTwo_weightTwo_le P.val.2 b ((N : ℝ) * a.val) a.val⁻¹ (u - c)) hM)
    rw [← show (observationLength a).val = a.val⁻¹ from rfl] at hh
    simpa only [aPrioriEnvelope, errorTwo_circDist_centralRep] using hh
  obtain ⟨hS, hSV⟩ := (hbound N a hK M hM g hgc hgd).2
  let m : ℝ := (N : ℝ) * ∫ t in (0 : ℝ)..1, f (t / a.val)
  have he : (fun X : Configuration N => fluctIntegral (fun u => f (u / a.val)) N X.val) =
      fun X => plainSum a N g X - m := by
    funext X
    unfold fluctIntegral plainSum
    congr 1
  rw [he]
  refine ⟨hS.sub (integrable_const m), ?_⟩
  rw [frozenVariance_sub_const hS m]
  apply hSV.trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_left (errorTwo_cutoff_power hK P.val.2 b ε)
    (by positivity)

/-- Sum a finite family of variance bounds with individually chosen exponents.
Each exponent is nonnegative and bounded by the prescribed singular exponent. -/
theorem errorTwo_fluctuation_pieces_of_input (hAP : APrioriConclusion)
    (P : Parameters) (b ε : ℝ) (hε : 0 < ε)
    (m : ℕ) (c lam : Fin m → ℝ) (hlam0 : ∀ j, 0 ≤ lam j) (hlamb : ∀ j, lam j ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), 1 ≤ (N : ℝ) * a.val →
      ∀ (M : ℝ), 0 ≤ M → ∀ φ : Fin m → ℝ → ℝ,
        (∀ j, ContDiff ℝ 1 (φ j)) →
        (∀ j, Function.Periodic (φ j) a.val⁻¹) →
        (∀ j u, |deriv (φ j) u| ≤
          M * gradWeightTwo P.val.2 (lam j) ((N : ℝ) * a.val) a.val⁻¹ (u - c j)) →
        ∃ hF : Integrable (fun X : Configuration N =>
          fluctIntegral (fun u => ∑ j, φ j (u / a.val)) N X.val) (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ hF ≤
            ENNReal.ofReal (C * M ^ 2 * (((N : ℝ) * a.val) ^ ε *
              (((N : ℝ) * a.val) ^ P.val.2 + ((N : ℝ) * a.val) ^ (2 * b)))) := by
  classical
  choose D hD hbound using fun j : Fin m =>
    errorTwo_fluctuation_piece_of_input hAP P (lam j) ε (c j) (hlam0 j) hε
  have hDsum : 0 ≤ ∑ j, D j := Finset.sum_nonneg fun j _ => (hD j).le
  refine ⟨1 + (m : ℝ) * ∑ j, D j, by positivity, fun N a hK M hM φ hφ hp hd => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  let R := ((N : ℝ) * a.val) ^ ε * (((N : ℝ) * a.val) ^ P.val.2 + ((N : ℝ) * a.val) ^ (2 * b))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let F : Fin m → Configuration N → ℝ := fun j X =>
    fluctIntegral (fun u => φ j (u / a.val)) N X.val
  have hmem : ∀ j, MemLp (F j) 2 (gibbsMeasure P N) := by
    intro j
    apply errorTwo_memLp_fluctIntegral P N ((hφ j).continuous.comp (continuous_id.div_const _))
    intro u
    change φ j ((u + 1) / a.val) = φ j (u / a.val)
    rw [add_div, one_div, hp j]
  have hV : ∀ j, variance (gibbsMeasure P N) (F j) ((hmem j).integrable one_le_two) ≤
      ENNReal.ofReal (D j * M ^ 2 * R) := by
    intro j
    apply (hbound j N a hK M hM (φ j) (hφ j) (hp j) (hd j)).choose_spec.trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hp : ((N : ℝ) * a.val) ^ (2 * lam j) ≤ ((N : ℝ) * a.val) ^ (2 * b) :=
      Real.rpow_le_rpow_of_exponent_le hK (by linarith [hlamb j])
    have hp' : ((N : ℝ) * a.val) ^ P.val.2 + ((N : ℝ) * a.val) ^ (2 * lam j) ≤
        ((N : ℝ) * a.val) ^ P.val.2 + ((N : ℝ) * a.val) ^ (2 * b) := by linarith
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hp' (Real.rpow_nonneg (by linarith : 0 ≤ (N : ℝ) * a.val) _))
      (mul_nonneg (hD j).le (sq_nonneg M))
  have he : (fun X : Configuration N =>
      fluctIntegral (fun u => ∑ j, φ j (u / a.val)) N X.val) = fun X => ∑ j, F j X := by
    funext X
    dsimp only [F]
    unfold fluctIntegral
    rw [Finset.sum_comm, intervalIntegral.integral_finsetSum,
      Finset.sum_sub_distrib, Finset.mul_sum]
    intro j _
    exact ((hφ j).continuous.comp (continuous_id.div_const _)).intervalIntegrable _ _
  rw [he]
  obtain ⟨hS, hSV⟩ := variance_finsetSum_le (gibbsMeasure P N) m F hmem
  refine ⟨hS, hSV.trans ?_⟩
  calc
    _ ≤ (m : ℝ≥0∞) * ∑ j, ENNReal.ofReal (D j * M ^ 2 * R) :=
      mul_le_mul_right (Finset.sum_le_sum fun j _ => hV j) _
    _ = ENNReal.ofReal ((m : ℝ) * (∑ j, D j) * M ^ 2 * R) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
          mul_nonneg (mul_nonneg (hD j).le (sq_nonneg M)) hR),
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
      congr 1
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      dsimp only [R]
      nlinarith [mul_nonneg (sq_nonneg M) hR])

/-- Apply the a priori estimate with the singular exponent near each mark
and exponent zero on the regular remainder, then sum the variances. -/
theorem errorTwo_variance_of_envelopes (hAP : APrioriConclusion)
    (P : Parameters) (n : ℕ) (marks : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (b ε : ℝ) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (a : Scale), 1 ≤ (N : ℝ) * a.val →
      (∀ i k, i ≠ k → δ ≤ circDist a.val⁻¹ (marks i - marks k)) →
      ∀ (h A : ℝ), 0 < h → ((N : ℝ) * a.val)⁻¹ ≤ h → 0 ≤ A →
      ∀ F : ℝ → ℝ, ContDiff ℝ ∞ F → Function.Periodic F a.val⁻¹ →
      (∀ x, |F x| ≤ A * (1 + ∑ j,
        max (circDist a.val⁻¹ (x - marks j)) h ^ (-b))) →
      (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
        max (circDist a.val⁻¹ (x - marks j)) h ^ (-1 - b))) →
      (∀ x, 2 ≤ circDist a.val⁻¹ x →
        |F x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 2) ∧
          |deriv F x| ≤ A * circDist a.val⁻¹ x ^ (P.val.2 - 3)) →
      ∃ hF : Integrable (fun X : Configuration N =>
        fluctIntegral (fun u => F (u / a.val)) N X.val) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hF ≤
          ENNReal.ofReal (C * A ^ 2 * (((N : ℝ) * a.val) ^ ε *
            (((N : ℝ) * a.val) ^ P.val.2 + ((N : ℝ) * a.val) ^ (2 * b)))) := by
  obtain ⟨D, hD, hsplit⟩ := varAlPieces_derivative_cutoffs n marks
    (by linarith [P.property.2.2] : P.val.2 < 3) hb hδ
  let lam : Fin (n + 1) → ℝ := Fin.lastCases 0 (fun _ => b)
  have hlam0 (j : Fin (n + 1)) : 0 ≤ lam j := by
    refine Fin.lastCases ?_ (fun _ => ?_) j <;>
      simp only [lam, Fin.lastCases_last, Fin.lastCases_castSucc]
    · exact le_rfl
    · exact hb
  have hlamb (j : Fin (n + 1)) : lam j ≤ b := by
    refine Fin.lastCases ?_ (fun _ => ?_) j <;>
      simp only [lam, Fin.lastCases_last, Fin.lastCases_castSucc]
    · exact hb
    · exact le_rfl
  obtain ⟨V, hV, hvariance⟩ := errorTwo_fluctuation_pieces_of_input hAP P b ε hε
    (n + 1) (Fin.lastCases 0 marks) lam hlam0 hlamb
  refine ⟨V * D ^ 2, by positivity, fun N a hK hsep h A hh hhK hA F hF hp hfv hfd ht => ?_⟩
  obtain ⟨φ, hφ, hsum, hd⟩ := hsplit a.val⁻¹ ((N : ℝ) * a.val) h A
    ((one_le_inv₀ a.property.1).mpr a.property.2) hsep hK hhK hA F hF hp hfv hfd
    (fun x hx => (ht x (by linarith)).2)
  obtain ⟨hi, hbnd⟩ := hvariance N a hK (D * A) (mul_nonneg hD.le hA) φ
    (fun j => (hφ j).1.of_le (by simp)) (fun j => (hφ j).2) hd
  have he : (fun u => ∑ j, φ j (u / a.val)) = fun u => F (u / a.val) :=
    funext fun u => hsum (u / a.val)
  have hstatement : ∃ hi : Integrable (fun X : Configuration N =>
      fluctIntegral (fun u => ∑ j, φ j (u / a.val)) N X.val) (gibbsMeasure P N),
      variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal
        (V * (D * A) ^ 2 * (((N : ℝ) * a.val) ^ ε *
          (((N : ℝ) * a.val) ^ P.val.2 + ((N : ℝ) * a.val) ^ (2 * b)))) := ⟨hi, hbnd⟩
  rw [he] at hstatement
  obtain ⟨hi', hbnd'⟩ := hstatement
  refine ⟨hi', hbnd'.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))⟩
  ring

end Riesz1.Internal
