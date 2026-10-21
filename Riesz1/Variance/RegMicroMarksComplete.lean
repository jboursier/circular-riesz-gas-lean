/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroMarksRegularity
public import Riesz1.Variance.QuantitativeVarianceInput

/-!
# Uniformly separated compact marks with complete regularity

Exterior real marks are removed before choosing
the cutoff radius. The same fixed marked set is separated on every
observation circle, hence for the original test and every member of both
actual `OptimalScalingTest` families, independently of its radius.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace Riesz1.Internal

/-- Fixed compact data admit a replacement marked family with complete
transport regularity and unconditional uniform circle separation.
All choices precede the sequence and every smoothing parameter. -/
theorem regMicro_compact_marks
    (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B C₀ α : ℝ) (n : ℕ+) (a : Fin (n : ℕ) → ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα : P.val.2-1 ≤ α) (hα2 : α < P.val.2/2) :
    ∃ (m : ℕ+) (b : Fin (m : ℕ) → ℝ) (C δ : ℝ), 0 < C ∧ 0 < δ ∧
      (∀ L : ℝ, 1 ≤ L → ∀ i j, i ≠ j →
        δ ≤ dist (b i : AddCircle L) (b j : AddCircle L)) ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n a α C₀) →
        ∀ c : Scale, PrimitiveRegularity (observationLength c) η P.val.2 B
          ⟨periodizedProfile p (observationLength c), periodizedProfileL2 p c⟩ →
          TransportRegularity P (observationLength c)
            ⟨periodizedProfile p (observationLength c), periodizedProfileL2 p c⟩ m b α C := by
  obtain ⟨r, hr, hrhalf, hsupp⟩ := hp
  let q := (r+1/2)/2
  have hrq : r < q := by dsimp [q]; linarith
  have hq : q < 1/2 := by dsimp [q]; linarith
  obtain ⟨m, b, δ, hδ, hb, hbin, _, hcover, _, hsep⟩ :=
    regMicro_select_inner_marks a (by linarith : 0 ≤ q) hq
  obtain ⟨C, hC, hreg⟩ := regMicro_remove_exterior_marks P p hr hrq hq hsupp
    η B C₀ α n a hη hB hC₀ hα hα2 m b hb hbin hcover
  exact ⟨m, b, C, δ, hC, hδ, hsep, hreg⟩

/-- A universally separated fixed family discharges the separation
premise on the original test and both actual families. This geometric
statement is independent of family admissibility and of `t`. -/
theorem regMicro_marks_separation_optimalScalingTest
    (m : ℕ+) (b : Fin (m : ℕ) → ℝ) (δ : ℝ)
    (hsep : ∀ L : ℝ, 1 ≤ L → ∀ i j, i ≠ j →
      δ ≤ dist (b i : AddCircle L) (b j : AddCircle L))
    (p : Profile) (ell : Scales) (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (r : ℝ) (v : Profile)
    (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))})
    (_hf : OptimalScalingTest p ell N hρ r v f) :
    ∀ i j, i ≠ j → δ ≤ dist (b i : Circle (loopMasterLength (ell N)))
      (b j : Circle (loopMasterLength (ell N))) :=
  hsep (ell N).val⁻¹ ((one_le_inv₀ (ell N).property.1).mpr (ell N).property.2)

/-- One replacement marked set for the original test and both actual
families, chosen before `ell`, `N`, the mollifier and its extra radius.
The transport predicate for the original profile is preserved in full.
The geometric conclusion holds on every member of `OptimalScalingTest`.
Family analytic estimates can therefore reuse this same marked set. -/
theorem regMicro_compact_family_marks
    (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B C₀ α : ℝ) (n : ℕ+) (a : Fin (n : ℕ) → ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα : P.val.2-1 ≤ α) (hα2 : α < P.val.2/2) :
    ∃ (m : ℕ+) (b : Fin (m : ℕ) → ℝ) (C δ : ℝ), 0 < C ∧ 0 < δ ∧
      (∀ c : Scale, ∀ i j, i ≠ j →
        δ ≤ dist (b i : Circle (observationLength c)) (b j : Circle (observationLength c))) ∧
      (∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k+1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n a α C₀) →
        ∀ c : Scale, PrimitiveRegularity (observationLength c) η P.val.2 B
          ⟨periodizedProfile p (observationLength c), periodizedProfileL2 p c⟩ →
          TransportRegularity P (observationLength c)
            ⟨periodizedProfile p (observationLength c), periodizedProfileL2 p c⟩ m b α C) ∧
      ∀ (ell : Scales) (N : ℕ+) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ)
        (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ i j, i ≠ j → δ ≤ dist (b i : Circle (loopMasterLength (ell N)))
          (b j : Circle (loopMasterLength (ell N))) := by
  obtain ⟨m, b, C, δ, hC, hδ, hsep, hreg⟩ := regMicro_compact_marks
    P p hp η B C₀ α n a hη hB hC₀ hα hα2
  exact ⟨m, b, C, δ, hC, hδ,
    fun c => hsep c.val⁻¹ ((one_le_inv₀ c.property.1).mpr c.property.2), hreg,
    fun ell N ρ hρ r v f hf => regMicro_marks_separation_optimalScalingTest
      m b δ hsep p ell N hρ r v f hf⟩

end Riesz1.Internal
