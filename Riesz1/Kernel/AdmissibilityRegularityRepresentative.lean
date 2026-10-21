/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityContinuous
public import Riesz1.ToMathlib.CircleFourierUniqueness
public import Riesz1.Frozen.TransportRegularity

/-!
# The continuous transport inherits (A2) and (A3)

The Hölder primitive supplies a continuous representative.
Fourier uniqueness identifies it almost everywhere with the representative in (A2)–(A3).
On the complement of the marks, continuity upgrades this to local pointwise equality.
Both derivatives and their bounds therefore transfer to the continuous transport.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace Riesz1

/-- The complement of finitely many marked circle points is open in the real lift. -/
theorem isOpen_unmarked_lift {L : Length} {ι : Type*} [Finite ι]
    (marks : ι → ℝ) : IsOpen {x : ℝ | ∀ j, (x : Circle L) ≠ (marks j : Circle L)} := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have : {x : ℝ | ∀ j, (x : Circle L) ≠ (marks j : Circle L)} =
      ⋂ j, (fun x : ℝ => (x : Circle L)) ⁻¹' ({(marks j : Circle L)}ᶜ) := by
    ext x
    simp
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isClosed_singleton.isOpen_compl.preimage (AddCircle.continuous_mk' L.val)

/-- A continuous circle representative agrees locally with an a.e. equal representative
wherever the latter has a continuous real lift. -/
theorem eventuallyEq_lift_of_ae_eq {L : Length} {f g : Circle L → ℝ}
    (hc : Continuous f) (hae : f =ᵐ[arclength L] g)
    {U : Set ℝ} (hU : IsOpen U)
    (hg : ContinuousOn (fun t : ℝ => g (t : Circle L)) U) {x : ℝ} (hx : x ∈ U) :
    (fun t : ℝ => f (t : Circle L)) =ᶠ[𝓝 x]
      (fun t : ℝ => g (t : Circle L)) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  let V := U ∩ Ioo (x - L.val / 2) (x + L.val / 2)
  have hV : IsOpen V := hU.inter isOpen_Ioo
  have hxV : x ∈ V := ⟨hx, by constructor <;> linarith [L.property]⟩
  have heq := CircleFourier.eqOn_lift_of_ae_eq (T := L.val) (a := x - L.val / 2)
    (show f =ᵐ[volume] g from hae) hV
    (show V ⊆ Ioc (x - L.val / 2) (x - L.val / 2 + L.val) from
      fun t ht => ⟨ht.2.1, by linarith [ht.2.2]⟩)
    (hc.comp (AddCircle.continuous_mk' L.val)).continuousOn
    (hg.mono inter_subset_left)
  exact Filter.eventuallyEq_of_mem (hV.mem_nhds hxV) heq

/-- The continuous representative furnished by (A1) satisfies (A2) and (A3) itself.
This is the representative-identification step, with no regularity
conclusion added as a hypothesis. -/
theorem exists_continuous_transport_with_regularity (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (p : ℕ+) (marks : Fin (p : ℕ) → ℝ) (α C : ℝ)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f p marks α C) :
    ∃ ψ : Circle L → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L),
        (∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
          transportCoeffs P L f k) ∧
        ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x ∧
          |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤ C *
            ((if dist (x : Circle L) 0 ≤ 1 then
                ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α)
              else 0) +
             (if 1 ≤ dist (x : Circle L) 0 then
                dist (x : Circle L) 0 ^ (-3 + P.val.2) else 0)) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hψ, hcoef⟩ :=
    exists_continuous_transport_of_primitiveRegularity P L η B hη hB f hprim
  obtain ⟨_, g, hgcoef, hg⟩ := hreg
  have haeC : (fun x => (ψ x : ℂ)) =ᵐ[arclength L] (fun x => (g.val x : ℂ)) := by
    apply CircleFourier.ae_eq_of_coeff_eq hψ g.property
    intro k
    exact (hcoef k).trans (hgcoef k).symm
  have hae : ψ =ᵐ[arclength L] g.val := by
    filter_upwards [haeC] with x hx
    exact Complex.ofReal_injective hx
  refine ⟨ψ, hc, hψ, hcoef, fun x hx => ?_⟩
  have heq := eventuallyEq_lift_of_ae_eq hc hae (isOpen_unmarked_lift marks)
    (fun t ht => (hg t ht).1.continuousAt.continuousWithinAt) hx
  exact ⟨(hg x hx).1.congr_of_eventuallyEq heq,
    heq.deriv.deriv.eq_of_nhds ▸ (hg x hx).2⟩

end Riesz1
