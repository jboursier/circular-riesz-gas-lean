/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorOneBounds
public import Riesz1.CLT.ErrorOneTransfer
public import Riesz1.Variance.RegUniformComplete
public import Riesz1.Frozen.Admissible

/-!
# The analytic facts of each case of the first error bound in Theorem 3

Lemma 5.1 (`Riesz1.regUniform_complete` and its named clauses) gives, with constants
chosen before the scale sequence, the bounds on the mollified profile and on the mollified
transport that `errorOne_bounds_of_facts` consumes. Two cases occur, as in
`Admissible`:

* the compact case (`CompactProfile p`, scales tending to zero), where each scale is a
  circle of length `a⁻¹ ≥ 1`.
* the macroscopic case (`a = 1` for every `N`), where the regularity data are those of the unit
  circle, transferred to length one by `ErrorOneTransfer`.

Each lemma provides, for every admissible scale and every `N` with `Nℓ_N ≥ 1`, a transport `ψ0`
of the periodized profile with the four facts of `errorOne_bounds_of_facts`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- The analytic facts of the compact case, with the constants of Lemma 5.1. -/
lemma errorOne_compact_facts {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (α η : ℝ) (d : TestData)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hη : 0 < η)
    (hηα : α + η < P.val.2 / 2) (hηs : P.val.2 - 1 < α + η)
    (hd1 : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1) :
    ∃ C₁ C₂ C₃ C₄ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 ≤ C₄ ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
        ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
          ∃ (ψ0 : Circle (loopMasterLength (ell N)) → ℝ)
            (hψ0m : MemLp (fun x => (ψ0 x : ℂ)) 2 (arclength (loopMasterLength (ell N)))),
            (∀ k : ℤ, coeff (loopMasterLength (ell N))
              ⟨(fun x => (ψ0 x : ℂ)), complexL2Integrable _ _ hψ0m⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
                  k) ∧
            (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
                  (fun s : ℝ => periodizedProfile p (observationLength (ell N))
                    (s : Circle (observationLength (ell N)))) t) x| ≤ C₁ * h ^ (-1 - α - η) ∧
              |deriv (deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
                  (fun s : ℝ => periodizedProfile p (observationLength (ell N))
                    (s : Circle (observationLength (ell N)))) t)) x| ≤ C₂ * h ^ (-2 - α - η)) ∧
            (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |circleMollify ρ (loopMasterLength (ell N)).val h
                (fun t : ℝ => ψ0 (t : Circle (loopMasterLength (ell N)))) x| ≤ C₃) ∧
            (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |deriv (fun t : ℝ => circleMollify ρ (loopMasterLength (ell N)).val h
                  (fun s : ℝ => ψ0 (s : Circle (loopMasterLength (ell N)))) t) x| ≤
                C₄ * (1 + ∑ j : Fin (d.2.2.2.1 : ℕ),
                  max (dist (x : Circle (loopMasterLength (ell N)))
                    (d.2.2.2.2 j : Circle (loopMasterLength (ell N)))) h ^
                    (-1 + P.val.2 - (α + η)))) := by
  obtain ⟨Cd, hCd, hd⟩ := regUniform_derivatives_compact P p hp d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α
    d.2.2.1 η hd1 hB hC₀ hα0 hα1 hη ρ hρ
  obtain ⟨Cs, hCs, hs⟩ := regUniform_smoothed_transport P d.1 d.2.1 hd1 hB
  obtain ⟨Ct, hCt, ht⟩ := regUniform_complete.2.2.2.2.2.2.1 P p hp d.1 d.2.1 d.2.2.2.1
    d.2.2.2.2 α (α + η) d.2.2.1 hd1 hB hC₀ hα0 hα1 (le_add_of_nonneg_right hη.le) hηs hηα ρ hρ
  refine ⟨Cd, Cd, Cs, Ct, hCd.le, hCd.le, hCs.le, hCt.le, fun ell hT hadm N hN => ?_⟩
  have hadmN := hadm N
  -- The derivative bounds of the periodized profile at this scale.
  have hH : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
      |deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
          (fun s : ℝ => periodizedProfile p (observationLength (ell N))
            (s : Circle (observationLength (ell N)))) t) x| ≤ Cd * h ^ (-1 - α - η) ∧
      |deriv (deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
          (fun s : ℝ => periodizedProfile p (observationLength (ell N))
            (s : Circle (observationLength (ell N)))) t)) x| ≤ Cd * h ^ (-2 - α - η) := by
    intro h hh hh1 x
    obtain ⟨ph, -, -, hph, hd1', hd2'⟩ := hd ell hT hadm (ell N) h hh hh1
    have hfun : (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
        (fun s : ℝ => periodizedProfile p (observationLength (ell N))
          (s : Circle (observationLength (ell N)))) t) =
        fun t : ℝ => ph.val (t : Circle (observationLength (ell N))) :=
      funext fun t => (hph t).symm
    rw [hfun]
    exact ⟨hd1' x, hd2' x⟩
  -- The smoothed transport: its sup bound and the derivative bound of the transport `ψ7`
  -- coincide, because both are continuous transports of the same coefficients.
  obtain ⟨ψ5, hψ5c, hψ5coef, hψ5sup⟩ :=
    hs (observationLength (ell N)) ⟨periodizedProfile p (observationLength (ell N)),
      periodizedProfileL2 p (ell N)⟩ hadmN.1
  obtain ⟨ψ7, hψ7c, hψ7mem, hψ7coef, hψ7d⟩ := ht ell hT hadm (ell N) hadmN.1 hadmN.2
  have huniq : ψ5.val = ψ7 :=
    continuous_eq_of_coeff_eq hψ5c hψ7c ψ5.property hψ7mem
      (fun k => (hψ5coef k).trans (hψ7coef k).symm)
  refine ⟨ψ5.val, ψ5.property, fun k => hψ5coef k, hH, ?_, ?_⟩
  · intro h hh hh1 x
    obtain ⟨g, ψh, -, hψhpt, -, -, hψhb⟩ := hψ5sup ρ hρ h hh
    have hb := hψhb (x : Circle (observationLength (ell N)))
    rw [hψhpt x] at hb
    exact hb
  · intro h hh hh1 x
    rw [huniq]
    exact hψ7d h hh hh1 x

/-- The analytic facts of the macroscopic case: every scale is one, and the unit-circle regularity
data transfer to length one. -/
lemma errorOne_macro_facts {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (p : Profile)
    (α η : ℝ) (d : TestData)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hη : 0 < η)
    (hηα : α + η < P.val.2 / 2) (hηs : P.val.2 - 1 < α + η)
    (hd1 : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (hprim : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ d.2.2.2.1 d.2.2.2.2 α d.2.2.1) :
    ∃ C₁ C₂ C₃ C₄ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 ≤ C₄ ∧
      ∀ ell : Scales, (∀ N, (ell N).val = 1) →
        ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
          ∃ (ψ0 : Circle (loopMasterLength (ell N)) → ℝ)
            (hψ0m : MemLp (fun x => (ψ0 x : ℂ)) 2 (arclength (loopMasterLength (ell N)))),
            (∀ k : ℤ, coeff (loopMasterLength (ell N))
              ⟨(fun x => (ψ0 x : ℂ)), complexL2Integrable _ _ hψ0m⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
                  k) ∧
            (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
                  (fun s : ℝ => periodizedProfile p (observationLength (ell N))
                    (s : Circle (observationLength (ell N)))) t) x| ≤ C₁ * h ^ (-1 - α - η) ∧
              |deriv (deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
                  (fun s : ℝ => periodizedProfile p (observationLength (ell N))
                    (s : Circle (observationLength (ell N)))) t)) x| ≤ C₂ * h ^ (-2 - α - η)) ∧
            (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |circleMollify ρ (loopMasterLength (ell N)).val h
                (fun t : ℝ => ψ0 (t : Circle (loopMasterLength (ell N)))) x| ≤ C₃) ∧
            (∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |deriv (fun t : ℝ => circleMollify ρ (loopMasterLength (ell N)).val h
                  (fun s : ℝ => ψ0 (s : Circle (loopMasterLength (ell N)))) t) x| ≤
                C₄ * (1 + ∑ j : Fin (d.2.2.2.1 : ℕ),
                  max (dist (x : Circle (loopMasterLength (ell N)))
                    (d.2.2.2.2 j : Circle (loopMasterLength (ell N)))) h ^
                    (-1 + P.val.2 - (α + η)))) := by
  obtain ⟨Cd, hCd, hd⟩ := regUniform_derivatives_macroscopic P p d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α
    d.2.2.1 η hd1 hB hC₀ hα0 hα1 hη hprim hreg ρ hρ
  obtain ⟨Cs, hCs, hs⟩ := regUniform_smoothed_transport P d.1 d.2.1 hd1 hB
  obtain ⟨Ct, hCt, ψ6, hψ6c, hψ6mem, hψ6coef, hψ6d⟩ :=
    regUniform_complete.2.2.2.2.2.1 P p d.1 d.2.1 d.2.2.2.1 d.2.2.2.2 α (α + η) d.2.2.1 hd1 hB
      hC₀ hα0 hα1 (le_add_of_nonneg_right hη.le) hηs hηα hprim hreg ρ hρ
  obtain ⟨ψ5, hψ5c, hψ5coef, hψ5sup⟩ := hs unitLength ⟨p.val, p.property⟩ hprim
  have huniq : ψ5.val = ψ6 :=
    continuous_eq_of_coeff_eq hψ5c hψ6c ψ5.property hψ6mem
      (fun k => (hψ5coef k).trans (hψ6coef k).symm)
  refine ⟨Cd, Cd, Cs, Ct, hCd.le, hCd.le, hCs.le, hCt.le, fun ell hone N hN => ?_⟩
  have hL : (observationLength (ell N)).val = 1 := by
    show (ell N).val⁻¹ = 1
    rw [hone N, inv_one]
  have hL' : (loopMasterLength (ell N)).val = 1 := by
    show (ell N).val⁻¹ = 1
    rw [hone N, inv_one]
  -- The derivative bounds of the periodized profile, transferred from the unit circle.
  have hH : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
      |deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
          (fun s : ℝ => periodizedProfile p (observationLength (ell N))
            (s : Circle (observationLength (ell N)))) t) x| ≤ Cd * h ^ (-1 - α - η) ∧
      |deriv (deriv (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
          (fun s : ℝ => periodizedProfile p (observationLength (ell N))
            (s : Circle (observationLength (ell N)))) t)) x| ≤ Cd * h ^ (-2 - α - η) := by
    intro h hh hh1 x
    obtain ⟨ph, -, -, hph, hd1', hd2'⟩ := hd h hh hh1
    have hfun : (fun t : ℝ => circleMollify ρ (observationLength (ell N)).val h
        (fun s : ℝ => periodizedProfile p (observationLength (ell N))
          (s : Circle (observationLength (ell N)))) t) =
        fun t : ℝ => ph.val (t : UnitAddCircle) :=
      funext fun t => (errorOne_circleMollify_periodized_eq_unit p (observationLength (ell N)) hL
        ρ h t).trans (hph t).symm
    rw [hfun]
    exact ⟨hd1' x, hd2' x⟩
  -- The transport on the length-`ℓ⁻¹` circle, transferred from the unit transport `ψ6`.
  obtain ⟨ψ0, hψ0pt, -, hψ0coef⟩ :=
    exists_transfer_of_val_one (loopMasterLength (ell N)) hL' ⟨ψ6, hψ6mem⟩
  refine ⟨ψ0.val, ψ0.property, ?_, hH, ?_, ?_⟩
  · intro k
    exact (hψ0coef k).trans ((hψ6coef k).trans
      (transportCoeffs_periodizedProfile_eq_unit P p (observationLength (ell N)) hL
        (periodizedProfileL2 p (ell N)) k).symm)
  · intro h hh hh1 x
    have hmoll : circleMollify ρ (loopMasterLength (ell N)).val h
        (fun t : ℝ => ψ0.val (t : Circle (loopMasterLength (ell N)))) x =
        circleMollify ρ 1 h (fun t : ℝ => ψ6 (t : Circle unitLength)) x :=
      circleMollify_eq_of_val_one ρ (loopMasterLength (ell N)) hL' h ψ0.val ψ6
        (fun y => hψ0pt y) x
    rw [hmoll, ← huniq]
    obtain ⟨g, ψh, -, hψhpt, -, -, hψhb⟩ := hψ5sup ρ hρ h hh
    have hb := hψhb (x : Circle unitLength)
    rw [hψhpt x] at hb
    exact hb
  · intro h hh hh1 x
    have hfun : (fun t : ℝ => circleMollify ρ (loopMasterLength (ell N)).val h
        (fun s : ℝ => ψ0.val (s : Circle (loopMasterLength (ell N)))) t) =
        fun t : ℝ => circleMollify ρ 1 h (fun s : ℝ => ψ6 (s : Circle unitLength)) t :=
      funext fun t => circleMollify_eq_of_val_one ρ (loopMasterLength (ell N)) hL' h ψ0.val ψ6
        (fun y => hψ0pt y) t
    rw [hfun]
    simp only [dist_circle_eq_of_val_one (loopMasterLength (ell N)) hL']
    exact hψ6d h hh hh1 x

end Riesz1.Internal

end
end
