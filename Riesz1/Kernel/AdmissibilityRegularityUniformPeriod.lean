/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityUniformTails
public import Riesz1.Kernel.AdmissibilityRegularityUniformLocal
public import Riesz1.ToMathlib.OscillatoryTwoTails

/-!
# A uniform full-period estimate for the compact transport

The bounded central region and both kernel tails concern the same continuous
representative. Their constants precede every observation scale. This proves the
large-circle, high-frequency integral step.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- The full-period derivative estimate, with constants depending only on fixed profile
and admissibility data. Neither derivative integrability nor a Fourier estimate is assumed. -/
theorem exists_uniform_large_circle_transport_estimate (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (m : ℕ+) (marks : Fin (m : ℕ) → ℝ) (α C δ : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hδ1 : δ < P.val.2 - α) :
    ∃ D W L0 : ℝ, 0 < D ∧ 1 ≤ W ∧ 1 ≤ L0 ∧ ∀ a : Scale,
      L0 ≤ (observationLength a).val →
      PrimitiveRegularity (observationLength a) η P.val.2 B
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
      TransportRegularity P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ m marks α C →
      ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
          (∀ k : ℤ, coeff (observationLength a)
            ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
              transportCoeffs P (observationLength a)
                ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
          LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) volume ∧
          (∀ x : ℝ, (∀ j, (x : Circle (observationLength a)) ≠
              (marks j : Circle (observationLength a))) →
            DifferentiableAt ℝ (fun t : ℝ => ψ (t : Circle (observationLength a))) x) ∧
          ∀ (χ : ℝ → ℂ) (c : ℂ), W ≤ ‖c‖ →
            (∀ t : ℝ, HasDerivAt χ (c * χ t) t) → (∀ t : ℝ, ‖χ t‖ = 1) →
            ‖∫ t in (-(observationLength a).val / 2)..((observationLength a).val / 2),
              ((deriv (fun u : ℝ => ψ (u : Circle (observationLength a))) t : ℝ) : ℂ) * χ t‖ ≤
              D * ‖c‖ ^ (α - P.val.2 + δ) := by
  classical
  obtain ⟨M, hM, hregular⟩ := exists_uniform_regular_transport P η B hη hB
  let R := 1 + ∑ j, |marks j|
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun j _ => abs_nonneg (marks j))]
  have hmarks : ∀ j, |marks j| ≤ R := by
    intro j
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => |marks i|) (fun i _ => abs_nonneg (marks i)) (Finset.mem_univ j)
    dsimp [R]
    linarith
  obtain ⟨K, W, hK, hW, hlocal⟩ := Internal.uniform_local_oscillatory_of_transport_bounds
    P m marks α C δ M R hα0 hδ hδ1 hC hM hR hmarks
  obtain ⟨M1, C2, hM1, hC2, htail⟩ := Internal.uniform_transport_derivative_tails P p hp
  let A := 2 * M1 + C2 / (-(P.val.2 - 3) - 1) * R ^ ((P.val.2 - 3) + 1)
  have hA : 0 ≤ A := add_nonneg (mul_nonneg (by norm_num) hM1)
    (mul_nonneg (div_nonneg hC2 (by linarith [P.property.2.2])) (Real.rpow_nonneg (by linarith) _))
  refine ⟨K + 2 * A + 1, W, 4 * R, by linarith, hW, by linarith,
    fun a ha hprim hreg => ?_⟩
  let L := observationLength a
  obtain ⟨ψ, hc, hψ, hcoeff, hb, hpoint⟩ := hregular L _ m marks α C hprim hreg
  have hi := Internal.locallyIntegrable_deriv_of_transport_bound P L marks α C
    hα0 hα1 hC _ hpoint
  obtain ⟨hic, hosc⟩ := hlocal L ha (fun t : ℝ => ψ (t : Circle L))
    (fun t => hb (t : Circle L)) hpoint
  refine ⟨ψ, hc, hψ, hcoeff, hi,
    fun x hx => (hpoint x hx).1.differentiableAt (by norm_num), fun χ c hw hχ hn => ?_⟩
  have ht := htail a ψ hc hψ hcoeff
  have hh := PuncturedDerivative.norm_oscillatory_two_tails_le
    (q := deriv (fun t : ℝ => ψ (t : Circle L)))
    (R := R) (z := L.val / 2) (M := M1) (C := C2) (e := P.val.2 - 3)
    (g := α - P.val.2 + δ) (K := K) (W := W)
    (by linarith) (by change 4 * R ≤ L.val at ha; linarith) hM1 hC2
    (by linarith [P.property.2.2]) (by linarith) hW hic
    (fun t htR htL => (ht t (hR.trans htR) htL).1)
    (fun t htR htL => (ht t (hR.trans htR) htL).2.1)
    (fun t htR htL => (ht t (hR.trans htR) htL).2.2)
    hw hχ hn (hosc χ c hw hχ hn)
  change ‖∫ t in (-L.val / 2)..(L.val / 2), _‖ ≤ _
  rw [← neg_div] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith)
    (Real.rpow_nonneg (norm_nonneg c) _))

end Riesz1
