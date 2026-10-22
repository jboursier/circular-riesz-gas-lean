/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.CompactDecompositionProfile
public import Riesz1.Variance.RegUniformFamilyTransportBounds
public import Riesz1.ToMathlib.MollifyPowerTailIterated

/-!
# Compact decomposition uniform over both convolution families

Proposition 5.9. Near-mark bounds come
from the family theorem. A second convolution preserves the
compact tails outside radius four, for the entire interval `0 < t ≤ 1`.
The decomposition coefficient precedes the scale sequence and both radii.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- The two actual transport families admit a common compact
decomposition on every observation circle. Both Fourier multipliers
and both function identities are retained. -/
theorem compactDecomposition_transport_families
    (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B C₀ : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2) (hαα' : α ≤ α')
    (hα' : P.val.2 - 1 < α') (hα'2 : α' < P.val.2 / 2)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ c : Scale, ∀ i k, i ≠ k →
      δ ≤ circDist c.val⁻¹ (marks i - marks k))
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) →
      ∀ N : ℕ+,
        ∃ q : {g : Circle (observationLength (ell N)) → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength (observationLength (ell N)))},
          Continuous q.val ∧
          (∀ k, coeff (observationLength (ell N)) ⟨(fun x => (q.val x : ℂ)),
            complexL2Integrable _ _ q.property⟩ k = transportCoeffs P (observationLength (ell N))
              ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k) ∧
          ∀ t : ℝ, 0 < t → t ≤ 1 →
            ∃ φ χ : {g : Circle (observationLength (ell N)) → ℝ //
              MemLp (fun x => (g x : ℂ)) 2 (arclength (observationLength (ell N)))},
              (∀ x : ℝ, φ.val (x : Circle (observationLength (ell N))) =
                circleMollify ρ (ell N).val⁻¹ t
                  (fun y : ℝ => q.val (y : Circle (observationLength (ell N)))) x) ∧
              (∀ x, χ.val x = q.val x - φ.val x) ∧
              (∀ k, coeff (observationLength (ell N)) ⟨(fun x => (φ.val x : ℂ)),
                complexL2Integrable _ _ φ.property⟩ k = transportCoeffs P (observationLength (ell N))
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k *
                    (mollifierFT ρ (t * k / (ell N).val⁻¹) : ℂ)) ∧
              (∀ k, coeff (observationLength (ell N)) ⟨(fun x => (χ.val x : ℂ)),
                complexL2Integrable _ _ χ.property⟩ k = transportCoeffs P (observationLength (ell N))
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k -
                  transportCoeffs P (observationLength (ell N))
                    ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k *
                    (mollifierFT ρ (t * k / (ell N).val⁻¹) : ℂ)) ∧
              ∀ v, (v = φ ∨ v = χ) → ∀ h : ℝ,
                1 ≤ (N : ℝ) * (ell N).val → ((N : ℝ) * (ell N).val)⁻¹ ≤ h → h ≤ 1 →
                ∃ f : Fin ((n : ℕ) + 1) → ℝ → ℝ,
                  (∀ j, ContDiff ℝ ∞ (f j) ∧ Function.Periodic (f j) (ell N).val⁻¹) ∧
                  (∀ x, circleMollify ρ (ell N).val⁻¹ h
                    (fun y : ℝ => v.val (y : Circle (observationLength (ell N)))) x = ∑ j, f j x) ∧
                  (∀ j x,
                    |deriv (f j) x| ≤ C * gradWeightOne P.val.2 (1 - P.val.2 + α')
                      ((N : ℝ) * (ell N).val) (ell N).val⁻¹ (x - Fin.lastCases 0 marks j) ∧
                    |deriv (deriv (f j)) x| ≤ C * gradWeightTwo P.val.2 (1 - P.val.2 + α')
                      ((N : ℝ) * (ell N).val) (ell N).val⁻¹ (x - Fin.lastCases 0 marks j)) := by
  obtain ⟨Cf, hCf, hfamily⟩ := regUniform_familyTransport_compact P p hp η B n marks α α' C₀
    hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  obtain ⟨Ct, hCt, hTails⟩ := regUniform_transportTails_compact P p hp η B n marks α α' C₀
    hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  let A := Cf + Ct * (1 + 2 ^ (2 - P.val.2) + 2 ^ (3 - P.val.2))
  have hA : 0 < A := by dsimp [A]; positivity
  have hCfA : Cf ≤ A := le_add_of_nonneg_right (by positivity)
  have htA : Ct ≤ A := by
    dsimp [A]
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 - P.val.2),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3 - P.val.2)]
  have hsumA (e : ℝ) (he : e = 2 - P.val.2 ∨ e = 3 - P.val.2) : Ct + Ct * 2 ^ e ≤ A := by
    rcases he with rfl | rfl <;> dsimp [A] <;>
      nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 - P.val.2),
        Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (3 - P.val.2)]
  obtain ⟨E, hE, hsplit⟩ := varAlPieces_fixed_uniform (n : ℕ) marks
    P.property.2.2 (by linarith : 0 < 1 - P.val.2 + α') hCf.le hA.le hδ
  refine ⟨E, hE, fun ell hell hreg N => ?_⟩
  let a := ell N
  let L := observationLength a
  obtain ⟨q, hqc, hqf, hqfamily⟩ := hfamily ell hell hreg a (hreg N).1 (hreg N).2
  obtain ⟨qt, hqtc, hqtm, hqtf, hqtails⟩ := hTails ell hell hreg a (hreg N).1 (hreg N).2
  have heqt : qt = q.val := continuous_eq_of_coeff_eq hqtc hqc hqtm q.property
    (fun k => (hqtf k).trans (hqf k).symm)
  let Q := fun x : ℝ => q.val (x : Circle L)
  have hQp : Function.Periodic Q L.val := by intro x; simp only [Q, AddCircle.coe_add_period]
  have hQi : LocallyIntegrable Q volume := (hqc.comp (AddCircle.continuous_mk' L.val)).locallyIntegrable
  have hbase (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (x : ℝ) (hx : 2 ≤ circDist L.val x) :
      |deriv (circleMollify ρ L.val r Q) x| ≤ Ct * circDist L.val x ^ (P.val.2 - 2) ∧
      |deriv (deriv (circleMollify ρ L.val r Q)) x| ≤ Ct * circDist L.val x ^ (P.val.2 - 3) := by
    have hc (y : ℝ) (hy : 2 ≤ |y|) (hyL : |y| ≤ L.val / 2) := hqtails r hr hr1 y hy hyL
    rw [heqt] at hc
    exact tail_of_central L.property (circleMollify_periodic hρ L.property hr hQi hQp) hc x hx
  refine ⟨q, hqc, hqf, fun t ht ht1 => ?_⟩
  obtain ⟨φ, χ, hφv, hχv, hφf, hχf, hbounds⟩ := hqfamily t ht ht1
  refine ⟨φ, χ, hφv, hχv, ?_, ?_, fun v hv h hK hh hh1 => ?_⟩
  · intro k
    have hf := hφf k
    rw [hqf] at hf
    simpa only [observationLength] using hf
  · intro k
    have hf := hχf k
    rw [hφf, hqf] at hf
    simpa only [observationLength] using hf
  have hh0 : 0 < h := lt_of_lt_of_le (inv_pos.mpr (mul_pos (by positivity) a.property.1)) hh
  let G := circleMollify ρ L.val t Q
  have hG : ContDiff ℝ ∞ G := contDiff_circleMollify hρ L.property ht hQi hQp
  have hGp : Function.Periodic G L.val := circleMollify_periodic hρ L.property ht hQi hQp
  have hGφ : (fun x : ℝ => φ.val (x : Circle L)) = G := funext hφv
  have hdiff : (fun x : ℝ => χ.val (x : Circle L)) = fun x => Q x - G x := by
    funext x; rw [hχv, hφv]
  have hdistance (y z : ℝ) : circDist L.val y ≤ circDist L.val z + |y - z| :=
    circDist_le_add_abs L.property y z
  have hdouble (x : ℝ) (hx : 4 ≤ circDist L.val x) :
      |deriv (circleMollify ρ L.val h G) x| ≤
        Ct * 2 ^ (2 - P.val.2) * circDist L.val x ^ (P.val.2 - 2) ∧
      |deriv (deriv (circleMollify ρ L.val h G)) x| ≤
        Ct * 2 ^ (3 - P.val.2) * circDist L.val x ^ (P.val.2 - 3) := by
    constructor
    · simpa only [iteratedDeriv_one, show -(P.val.2 - 2) = 2 - P.val.2 by ring] using
        circleMollify_iterated_power_tail_from_two hρ L.property hh0 hh1 hCt.le
          (by linarith [P.property.2.2] : P.val.2 - 2 ≤ 0) 1 hG hGp hdistance
          (fun y hy => by simpa only [G, iteratedDeriv_one] using (hbase t ht ht1 y hy).1) hx
    · simpa only [iteratedDeriv_succ, iteratedDeriv_zero,
        show -(P.val.2 - 3) = 3 - P.val.2 by ring] using
        circleMollify_iterated_power_tail_from_two hρ L.property hh0 hh1 hCt.le
          (by linarith [P.property.2.2] : P.val.2 - 3 ≤ 0) 2 hG hGp hdistance
          (fun y hy => by simpa only [G, iteratedDeriv_succ, iteratedDeriv_zero] using (hbase t ht ht1 y hy).2) hx
  obtain ⟨hvc, _, hb⟩ := hbounds v hv
  let F := circleMollify ρ L.val h (fun x : ℝ => v.val (x : Circle L))
  have hvi : LocallyIntegrable (fun x : ℝ => v.val (x : Circle L)) volume :=
    (hvc.comp (AddCircle.continuous_mk' L.val)).locallyIntegrable
  have hvp : Function.Periodic (fun x : ℝ => v.val (x : Circle L)) L.val := by
    intro x; simp only [AddCircle.coe_add_period]
  have hF : ContDiff ℝ ∞ F := contDiff_circleMollify hρ L.property hh0 hvi hvp
  have hFp : Function.Periodic F L.val := circleMollify_periodic hρ L.property hh0 hvi hvp
  have h1 (x : ℝ) : |deriv F x| ≤ A * (1 + ∑ j,
      max (circDist L.val (x - marks j)) h ^ (-(1 - P.val.2 + α'))) := by
    have hh' := (hb h hh0 hh1 x).2.1
    simp only [dist_coe_eq_circDist_sub L.property,
      show -1 + P.val.2 - α' = -(1 - P.val.2 + α') by ring] at hh'
    exact hh'.trans (mul_le_mul_of_nonneg_right hCfA (by positivity))
  have h2 (x : ℝ) : |deriv (deriv F) x| ≤ A * (1 + ∑ j,
      max (circDist L.val (x - marks j)) h ^ (-1 - (1 - P.val.2 + α'))) := by
    have hh' := (hb h hh0 hh1 x).2.2
    simp only [dist_coe_eq_circDist_sub L.property,
      show -2 + P.val.2 - α' = -1 - (1 - P.val.2 + α') by ring] at hh'
    exact hh'.trans (mul_le_mul_of_nonneg_right hCfA (by positivity))
  have htail (x : ℝ) (hx : 4 ≤ circDist L.val x) :
      |deriv F x| ≤ A * circDist L.val x ^ (P.val.2 - 2) ∧
        |deriv (deriv F) x| ≤ A * circDist L.val x ^ (P.val.2 - 3) := by
    have h0 := hbase h hh0 hh1 x (by linarith)
    have hD := hdouble x hx
    rcases hv with rfl | rfl
    · change |deriv (circleMollify ρ L.val h _) x| ≤ _ ∧
        |deriv (deriv (circleMollify ρ L.val h _)) x| ≤ _
      rw [hGφ]
      exact ⟨hD.1.trans (mul_le_mul_of_nonneg_right
        (by linarith [hsumA _ (Or.inl rfl)]) (by positivity)),
        hD.2.trans (mul_le_mul_of_nonneg_right
          (by linarith [hsumA _ (Or.inr rfl)]) (by positivity))⟩
    · have he : F = fun y => circleMollify ρ L.val h Q y - circleMollify ρ L.val h G y := by
        dsimp [F]
        rw [hdiff]
        exact circleMollify_sub hρ L.property hh0 hQi hG.continuous.locallyIntegrable hQp hGp
      have hH : ContDiff ℝ ∞ (circleMollify ρ L.val h Q) :=
        contDiff_circleMollify hρ L.property hh0 hQi hQp
      have hI : ContDiff ℝ ∞ (circleMollify ρ L.val h G) :=
        contDiff_circleMollify hρ L.property hh0 hG.continuous.locallyIntegrable hGp
      rw [he, deriv_fun_sub (hH.differentiable (by simp) x) (hI.differentiable (by simp) x),
        secondDeriv_sub_of_contDiffAt (hH.contDiffAt.of_le (by simp)) (hI.of_le (by simp))]
      constructor
      · calc
          _ ≤ |deriv (circleMollify ρ L.val h Q) x| +
              |deriv (circleMollify ρ L.val h G) x| := abs_sub _ _
          _ ≤ Ct * circDist L.val x ^ (P.val.2 - 2) +
              (Ct * 2 ^ (2 - P.val.2)) * circDist L.val x ^ (P.val.2 - 2) := add_le_add h0.1 hD.1
          _ = (Ct + Ct * 2 ^ (2 - P.val.2)) * circDist L.val x ^ (P.val.2 - 2) := by ring
          _ ≤ A * circDist L.val x ^ (P.val.2 - 2) := mul_le_mul_of_nonneg_right
            (hsumA _ (Or.inl rfl)) (Real.rpow_nonneg (circDist_nonneg _ _) _)
      · calc
          _ ≤ |deriv (deriv (circleMollify ρ L.val h Q)) x| +
              |deriv (deriv (circleMollify ρ L.val h G)) x| := abs_sub _ _
          _ ≤ Ct * circDist L.val x ^ (P.val.2 - 3) +
              (Ct * 2 ^ (3 - P.val.2)) * circDist L.val x ^ (P.val.2 - 3) := add_le_add h0.2 hD.2
          _ = (Ct + Ct * 2 ^ (3 - P.val.2)) * circDist L.val x ^ (P.val.2 - 3) := by ring
          _ ≤ A * circDist L.val x ^ (P.val.2 - 3) := mul_le_mul_of_nonneg_right
            (hsumA _ (Or.inr rfl)) (Real.rpow_nonneg (circDist_nonneg _ _) _)
  exact hsplit L.val ((N : ℝ) * a.val) h
    ((one_le_inv₀ a.property.1).mpr a.property.2) (hsep a) hK hh F hF hFp
    (fun x => (hb h hh0 hh1 x).1) h1 h2 htail

end Riesz1.Internal
