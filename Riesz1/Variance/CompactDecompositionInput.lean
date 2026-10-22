/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.CompactDecompositionFamilies
public import Riesz1.Variance.VarAlFinalMacroInput

/-!
# The compact decomposition on the original and both actual test families

Proposition 5.9, on the exact
`OptimalScalingTest` relation. This standalone theorem supplies periodic
transport pieces to the loop variance and the two auxiliary estimates.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- One compact decomposition coefficient for the original test and
both families, before the scale sequence and both smoothing radii.
The smooth transport representative is arbitrary with the prescribed coefficients. -/
theorem compactDecomposition_optimalScalingTest
    (P : Parameters) (p : Profile) (hp : CompactProfile p) (α α' : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2) (hαα' : α ≤ α')
    (hα' : P.val.2 - 1 < α') (hα'2 : α' < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (C : ℝ), 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      ∀ (N : ℕ+) (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (h : ℝ) (hh : 0 < h), 1 ≤ cltK N (ell N) → (cltK N (ell N))⁻¹ ≤ h → h ≤ 1 →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N)) ⟨(fun x => (ψ x : ℂ)),
            complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltRegCircle hρ _ hh f)
                  (cltRegCircle_contDiff hρ _ hh f)) k) →
          ∃ φ : Fin ((n : ℕ) + 1) → ℝ → ℝ,
            (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) (ell N).val⁻¹) ∧
            (∀ x : ℝ, ψ (x : Circle (loopMasterLength (ell N))) = ∑ j, φ j x) ∧
            (∀ j x,
              |deriv (φ j) x| ≤ C * gradWeightOne P.val.2 (1 - P.val.2 + α')
                (cltK N (ell N)) (ell N).val⁻¹ (x - Fin.lastCases 0 marks j) ∧
              |deriv (deriv (φ j)) x| ≤ C * gradWeightTwo P.val.2 (1 - P.val.2 + α')
                (cltK N (ell N)) (ell N).val⁻¹ (x - Fin.lastCases 0 marks j)) := by
  obtain ⟨n, marks, D, δ, hD, hδ, hsep, hreplace, _⟩ := regMicro_compact_family_marks
    P p hp d.1 d.2.1 d.2.2.1 α d.2.2.2.1 d.2.2.2.2 hη hB hC₀ hα hα2
  have hsepc (c : Scale) (i k : Fin (n : ℕ)) (hik : i ≠ k) :
      δ ≤ circDist c.val⁻¹ (marks i - marks k) := by
    have ht := hsep c i k hik
    rw [dist_coe_eq_circDist_sub (observationLength c).property,
      show (observationLength c).val = c.val⁻¹ from rfl] at ht
    exact ht
  obtain ⟨Co, hCo, ho⟩ := compactDecomposition_profile P p hp d.1 d.2.1 D
    n marks α α' hη hB hD.le hα hα2 hαα' hα' hα'2 δ hδ hsepc ρ hρ
  obtain ⟨Cf, hCf, hfam⟩ := compactDecomposition_transport_families P p hp d.1 d.2.1 D
    n marks α α' hη hB hD.le hα hα2 hαα' hα' hα'2 δ hδ hsepc ρ hρ
  let C := max Co Cf
  have hC : 0 < C := hCo.trans_le (le_max_left _ _)
  refine ⟨n, marks, C, hC, fun ell hell hdata N r v f hv h hh hK hKh hh1 ψ hψ htr => ?_⟩
  have hreg : ∀ N,
      PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
      TransportRegularity P (observationLength (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n marks α D :=
    fun N => ⟨(hdata N).1, hreplace ell hell hdata (ell N) (hdata N).1⟩
  let a := ell N
  let L := loopMasterLength a
  let ξ := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  obtain ⟨q, _, hq, hfamily⟩ := hfam ell hell hreg N
  have htransfer (q₀ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)})
      (hcoef : ∀ k, coeff L ⟨(fun x => (q₀.val x : ℂ)), complexL2Integrable _ _ q₀.property⟩ k =
        transportCoeffs P L f k) {B : ℝ} (hBC : B ≤ C)
      (hb : ∃ φ : Fin ((n : ℕ) + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) a.val⁻¹) ∧
        (∀ x, circleMollify ρ a.val⁻¹ h (fun y : ℝ => q₀.val (y : Circle L)) x = ∑ j, φ j x) ∧
        (∀ j x,
          |deriv (φ j) x| ≤ B * gradWeightOne P.val.2 (1 - P.val.2 + α') (cltK N a)
            a.val⁻¹ (x - Fin.lastCases 0 marks j) ∧
          |deriv (deriv (φ j)) x| ≤ B * gradWeightTwo P.val.2 (1 - P.val.2 + α') (cltK N a)
            a.val⁻¹ (x - Fin.lastCases 0 marks j))) :
      ∃ φ : Fin ((n : ℕ) + 1) → ℝ → ℝ,
        (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) a.val⁻¹) ∧
        (∀ x : ℝ, ψ (x : Circle L) = ∑ j, φ j x) ∧
        (∀ j x,
          |deriv (φ j) x| ≤ C * gradWeightOne P.val.2 (1 - P.val.2 + α') (cltK N a)
            a.val⁻¹ (x - Fin.lastCases 0 marks j) ∧
          |deriv (deriv (φ j)) x| ≤ C * gradWeightTwo P.val.2 (1 - P.val.2 + α') (cltK N a)
            a.val⁻¹ (x - Fin.lastCases 0 marks j)) := by
    have heq (x : ℝ) : ψ (x : Circle L) =
        circleMollify ρ a.val⁻¹ h (fun y : ℝ => q₀.val (y : Circle L)) x :=
      errorOne_eq_circleMollify_of_coeff P L hρ hh f q₀.val q₀.property hcoef
        (loopMasterLengthTest _ (cltRegCircle hρ _ hh f) (cltRegCircle_contDiff hρ _ hh f))
        (fun x => cltRegCircle_coe hρ _ hh f x) (loopMasterLengthTest _ ψ hψ)
        (continuous_circle_of_lift _ hψ.continuous) htr x
    obtain ⟨φ, hφ, hsum, henv⟩ := hb
    refine ⟨φ, hφ, fun x => (heq x).trans (hsum x), fun j x => ⟨?_, ?_⟩⟩
    · exact (henv j x).1.trans (mul_le_mul_of_nonneg_right hBC (by
        unfold gradWeightOne
        split_ifs
        · exact Real.rpow_nonneg (le_max_of_le_left (circDist_nonneg _ _)) _
        · exact Real.rpow_nonneg (circDist_nonneg _ _) _))
    · exact (henv j x).2.trans (mul_le_mul_of_nonneg_right hBC (by
        unfold gradWeightTwo
        split_ifs
        · exact Real.rpow_nonneg (le_max_of_le_left (circDist_nonneg _ _)) _
        · exact Real.rpow_nonneg (circDist_nonneg _ _) _))
  rcases hv with ⟨_, rfl⟩ | ⟨t, ht, ht1, _, hcases⟩
  · exact htransfer q hq (le_max_left _ _) (ho ell hell hreg N h hK hKh hh1 q hq)
  · obtain ⟨φ, χ, _, _, hφf, hχf, hpieces⟩ := hfamily t ht ht1
    let g := loopMasterLengthTest L (cltRegCircle hρ L ht ξ) (cltRegCircle_contDiff hρ L ht ξ)
    have hg (k : ℤ) : transportCoeffs P L g k = transportCoeffs P L ξ k *
        (mollifierFT ρ (t * k / a.val⁻¹) : ℂ) :=
      errorOne_transportCoeffs_smooth P L hρ ht ξ g (fun x => cltRegCircle_coe hρ L ht ξ x) k
    rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact htransfer φ (fun k => (hφf k).trans (hg k).symm) (le_max_right _ _)
        (hpieces φ (Or.inl rfl) h hK hKh hh1)
    · have hc (k : ℤ) : coeff L ⟨(fun x => (χ.val x : ℂ)), complexL2Integrable _ _ χ.property⟩ k =
          transportCoeffs P L (subCircleL2 ξ g) k := by
        rw [varAlFinal_transport_sub, hg]
        exact hχf k
      exact htransfer χ hc (le_max_right _ _) (hpieces χ (Or.inr rfl) h hK hKh hh1)

end Riesz1.Internal
