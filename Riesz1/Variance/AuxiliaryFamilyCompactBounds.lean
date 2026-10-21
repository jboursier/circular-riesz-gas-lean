/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyCompactTails
public import Riesz1.Variance.RegUniformFamilyTransportBounds
public import Riesz1.Variance.RegUniformTails
public import Riesz1.CLT.ErrorTwoFinalCompact
import all Riesz1.Variance.AuxiliaryMixed
import all Riesz1.Variance.LoopMaster

/-!
# Actual compact family transports with uniform envelopes and tails

The analytic hypotheses used in both auxiliary estimates are proved
on all three branches of `OptimalScalingTest`. Constants precede the
shrinking sequence and the entire permitted extra-radius interval.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- The two smooth transport tails add under subtraction. -/
theorem auxiliary_family_sub_transport_tails {U V : ℝ → ℝ} {L s B D : ℝ}
    (hU : ContDiff ℝ ∞ U) (hV : ContDiff ℝ ∞ V)
    (hu : ∀ x, 2 ≤ circDist L x →
      |deriv U x| ≤ B * circDist L x ^ (s - 2) ∧
      |deriv (deriv U) x| ≤ B * circDist L x ^ (s - 3))
    (hv : ∀ x, 2 ≤ circDist L x →
      |deriv V x| ≤ D * circDist L x ^ (s - 2) ∧
      |deriv (deriv V) x| ≤ D * circDist L x ^ (s - 3)) :
    ∀ x, 2 ≤ circDist L x →
      |deriv (fun y => U y - V y) x| ≤ (B + D) * circDist L x ^ (s - 2) ∧
      |deriv (deriv (fun y => U y - V y)) x| ≤ (B + D) * circDist L x ^ (s - 3) := by
  intro x hx
  rw [deriv_fun_sub (hU.differentiable (by simp) x) (hV.differentiable (by simp) x),
    secondDeriv_sub_of_contDiffAt (hU.of_le (by simp)).contDiffAt (hV.of_le (by simp))]
  constructor
  · exact (abs_sub _ _).trans ((add_le_add (hu x hx).1 (hv x hx).1).trans_eq (by ring))
  · exact (abs_sub _ _).trans ((add_le_add (hu x hx).2 (hv x hx).2).trans_eq (by ring))

/-- Uniform near-mark bounds and both tails for the actual microscopic
transport of every compact family test. -/
theorem auxiliary_family_compact_transport_bounds
    (P : Parameters) (p : Profile) (hp : CompactProfile p) (α α' : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hαα' : α ≤ α') (hα' : P.val.2 - 1 < α') (hα'2 : α' < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 ≤ d.2.1) (hC₀ : 0 ≤ d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ A : ℝ, 0 < A ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (nhds 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) d.1 P.val.2 d.2.1
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            d.2.2.2.1 d.2.2.2.2 α d.2.2.1) →
      ∀ N : ℕ+, 1 ≤ cltK N (ell N) → ∀ r : ℝ, 0 < r →
      ∀ (v : Profile) (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
        MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N)) ⟨(fun x => (ψ x : ℂ)),
            complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N)) (mixedReg hρ N (ell N) f) k) →
          let F := fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N)))
          (∀ x, |deriv F x| ≤ A * (1 + ∑ j,
            max (circDist (ell N).val⁻¹ (x - d.2.2.2.2 j)) (cltK N (ell N))⁻¹ ^
              (-(1 - P.val.2 + α')))) ∧
          (∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ j,
            max (circDist (ell N).val⁻¹ (x - d.2.2.2.2 j)) (cltK N (ell N))⁻¹ ^
              (-1 - (1 - P.val.2 + α')))) ∧
          (∀ x, 2 ≤ circDist (ell N).val⁻¹ x →
            |deriv F x| ≤ A * circDist (ell N).val⁻¹ x ^ (P.val.2 - 2) ∧
            |deriv (deriv F) x| ≤ A * circDist (ell N).val⁻¹ x ^ (P.val.2 - 3)) := by
  obtain ⟨C₁, hC₁, hT1⟩ := regUniform_firstTransport_compact P p hp d.1 d.2.1
    d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  obtain ⟨C₂, hC₂, hT2⟩ := regUniform_secondTransport_compact P p hp d.1 d.2.1
    d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  obtain ⟨Ct, hCt, hTail⟩ := regUniform_transportTails_compact P p hp d.1 d.2.1
    d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  obtain ⟨B, hBp, hFam⟩ := regUniform_familyTransport_compact P p hp d.1 d.2.1
    d.2.2.2.1 d.2.2.2.2 α α' d.2.2.1 hη hB hC₀ hα hα2 hαα' hα' hα'2 ρ hρ
  obtain ⟨T, hT, hFTail⟩ := auxiliary_family_compact_transport_tails P p hρ
  let A := C₁ + C₂ + Ct + B + T
  have hA : 0 < A := by dsimp [A]; positivity
  have h₁ : C₁ ≤ A := by dsimp [A]; linarith
  have h₂ : C₂ ≤ A := by dsimp [A]; linarith
  have htA : Ct ≤ A := by dsimp [A]; linarith
  have hBA : B ≤ A := by dsimp [A]; linarith
  have hTA : T ≤ A := by dsimp [A]; linarith
  have htTA : Ct + T ≤ A := by dsimp [A]; linarith
  refine ⟨A, hA, fun ell hell hdata N hK r hr v f hv ψ hψ htr => ?_⟩
  dsimp only
  let a := ell N
  let L := observationLength a
  let ξ := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  let h := (cltK N a)⁻¹
  have hh : 0 < h := inv_pos.mpr (cltK_pos N a)
  have hh1 : h ≤ 1 := inv_le_one_of_one_le₀ hK
  obtain ⟨ψ₁, hc₁, hm₁, hf₁, hb₁⟩ := hT1 ell hell hdata a (hdata N).1 (hdata N).2
  obtain ⟨ψ₂, hc₂, hm₂, hf₂, hb₂⟩ := hT2 ell hell hdata a (hdata N).1 (hdata N).2
  obtain ⟨ψt, hct, hmt, hft, hbt⟩ := hTail ell hell hdata a (hdata N).1 (hdata N).2
  obtain ⟨ψ₀, hc₀, hf₀, hfamily⟩ := hFam ell hell hdata a (hdata N).1 (hdata N).2
  have he₂ : ψ₂ = ψ₁ := continuous_eq_of_coeff_eq hc₂ hc₁ hm₂ hm₁
    (fun k => (hf₂ k).trans (hf₁ k).symm)
  have het : ψt = ψ₁ := continuous_eq_of_coeff_eq hct hc₁ hmt hm₁
    (fun k => (hft k).trans (hf₁ k).symm)
  have he₀ : ψ₀.val = ψ₁ := continuous_eq_of_coeff_eq hc₀ hc₁ ψ₀.property hm₁
    (fun k => (hf₀ k).trans (hf₁ k).symm)
  let U := circleMollify ρ L.val h (fun x : ℝ => ψ₁ (x : Circle L))
  have hp₁ : Function.Periodic (fun x : ℝ => ψ₁ (x : Circle L)) L.val := by
    intro x; simp only [AddCircle.coe_add_period]
  have hUi : LocallyIntegrable (fun x : ℝ => ψ₁ (x : Circle L)) volume :=
    (hc₁.comp (AddCircle.continuous_mk' L.val)).locallyIntegrable
  have hUs : ContDiff ℝ ∞ U := contDiff_circleMollify hρ L.property hh hUi hp₁
  have hUp : Function.Periodic U L.val := circleMollify_periodic hρ L.property hh hUi hp₁
  have hUtail (x : ℝ) (hx : 2 ≤ circDist L.val x) :
      |deriv U x| ≤ Ct * circDist L.val x ^ (P.val.2 - 2) ∧
      |deriv (deriv U) x| ≤ Ct * circDist L.val x ^ (P.val.2 - 3) := by
    have hcentral := fun y hy hyL => hbt h hh hh1 y hy hyL
    simp only [het] at hcentral
    exact tail_of_central L.property hUp hcentral x hx
  have hnotMacro : ¬ ∀ M, (ell M).val = 1 := by
    intro hone
    have hc : Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (nhds (1 : ℝ)) := by
      have he := funext fun k : ℕ => hone ⟨k + 1, Nat.succ_pos k⟩
      rw [he]
      exact tendsto_const_nhds
    have he := tendsto_nhds_unique hc hell
    norm_num at he
  have hdist (x m : ℝ) : dist (x : Circle L) (m : Circle L) =
      circDist L.val (x - m) := dist_coe_eq_circDist_sub L.property x m
  rcases hv with ⟨_, rfl⟩ | ⟨t, ht, ht1, hdom, hcases⟩
  · have he := auxiliary_family_transport_eq P N a hρ ξ ⟨ψ₁, hm₁⟩ hf₁ ψ hψ htr
    rw [he]
    have h1 := fun x => hb₁ h hh hh1 x
    have h2 := fun x => hb₂ h hh hh1 x
    simp only [he₂, hdist,
      show -1 + P.val.2 - α' = -(1 - P.val.2 + α') by ring,
      show -2 + P.val.2 - α' = -1 - (1 - P.val.2 + α') by ring] at h1 h2
    have hsum (x e : ℝ) : 0 ≤ 1 + ∑ j,
        max (circDist L.val (x - d.2.2.2.2 j)) h ^ e := by
      apply add_nonneg zero_le_one
      exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (le_max_of_le_right hh.le) _
    exact ⟨fun x => (h1 x).trans (mul_le_mul_of_nonneg_right h₁ (hsum x _)),
      fun x => (h2 x).trans (mul_le_mul_of_nonneg_right h₂ (hsum x _)),
      fun x hx => ⟨(hUtail x hx).1.trans (mul_le_mul_of_nonneg_right htA (Real.rpow_nonneg (circDist_nonneg _ _) _)),
        (hUtail x hx).2.trans (mul_le_mul_of_nonneg_right htA (Real.rpow_nonneg (circDist_nonneg _ _) _))⟩⟩
  · have hd := hdom.resolve_left hnotMacro
    have hsupp := hd.1
    have hmargin : r + t / 2 < 1 / 2 := by linarith [hd.2]
    obtain ⟨φ, χ, hφv, hχv, hfφ, hfχ, hb⟩ := hfamily t ht ht1
    let g := loopMasterLengthTest L (cltRegCircle hρ L ht ξ)
      (cltRegCircle_contDiff hρ L ht ξ)
    have hg (k : ℤ) : transportCoeffs P L g k =
        transportCoeffs P L ξ k * (mollifierFT ρ (t * k / L.val) : ℂ) :=
      errorOne_transportCoeffs_smooth P L hρ ht ξ g
        (fun x => cltRegCircle_coe hρ L ht ξ x) k
    have hφcoef (k : ℤ) : coeff L ⟨(fun x => (φ.val x : ℂ)),
        complexL2Integrable _ _ φ.property⟩ k = transportCoeffs P L g k := by
      rw [hfφ k, hf₀ k, hg k]
    have hp₀ : Function.Periodic (fun x : ℝ => ψ₀.val (x : Circle L)) L.val := by
      intro x; simp only [AddCircle.coe_add_period]
    have hφs : ContDiff ℝ ∞ (fun x : ℝ => φ.val (x : Circle L)) := by
      rw [funext hφv]
      exact contDiff_circleMollify hρ L.property ht
        (hc₀.comp (AddCircle.continuous_mk' L.val)).locallyIntegrable hp₀
    let V := circleMollify ρ L.val h (fun x : ℝ => φ.val (x : Circle L))
    have hpφ : Function.Periodic (fun x : ℝ => φ.val (x : Circle L)) L.val := by
      intro x; simp only [AddCircle.coe_add_period]
    have hVi : LocallyIntegrable (fun x : ℝ => φ.val (x : Circle L)) volume :=
      hφs.continuous.locallyIntegrable
    have hVs : ContDiff ℝ ∞ V := contDiff_circleMollify hρ L.property hh hVi hpφ
    have hVtail := hFTail a r t hr ht hmargin hsupp φ hφs hφcoef h hh hh1
    have hnear (q : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
        (hq : q = φ ∨ q = χ) := (hb q hq).2.2 h hh hh1
    have hbounds (q : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
        (hq : q = φ ∨ q = χ) :
        (∀ x, |deriv (circleMollify ρ L.val h (fun y : ℝ => q.val (y : Circle L))) x| ≤
          A * (1 + ∑ j, max (circDist L.val (x - d.2.2.2.2 j)) h ^ (-(1 - P.val.2 + α')))) ∧
        (∀ x, |deriv (deriv (circleMollify ρ L.val h (fun y : ℝ => q.val (y : Circle L)))) x| ≤
          A * (1 + ∑ j, max (circDist L.val (x - d.2.2.2.2 j)) h ^ (-1 - (1 - P.val.2 + α')))) := by
      have hn := hnear q hq
      simp only [hdist,
        show -1 + P.val.2 - α' = -(1 - P.val.2 + α') by ring,
        show -2 + P.val.2 - α' = -1 - (1 - P.val.2 + α') by ring] at hn
      have hsum (x e : ℝ) : 0 ≤ 1 + ∑ j,
          max (circDist L.val (x - d.2.2.2.2 j)) h ^ e :=
        add_nonneg zero_le_one (Finset.sum_nonneg fun j _ =>
          Real.rpow_nonneg (le_max_of_le_right hh.le) _)
      exact ⟨fun x => (hn x).2.1.trans (mul_le_mul_of_nonneg_right hBA (hsum x _)),
        fun x => (hn x).2.2.trans (mul_le_mul_of_nonneg_right hBA (hsum x _))⟩
    have hχcoef (k : ℤ) : coeff L ⟨(fun x => (χ.val x : ℂ)),
        complexL2Integrable _ _ χ.property⟩ k = transportCoeffs P L (subCircleL2 ξ g) k := by
      rw [hfχ k, hf₀ k, hφcoef k, varAlFinal_transport_sub]
    have heχ : (fun x : ℝ => χ.val (x : Circle L)) =
        fun x : ℝ => ψ₁ (x : Circle L) - φ.val (x : Circle L) := by
      funext x
      rw [hχv, he₀]
    have heχsm : circleMollify ρ L.val h (fun x : ℝ => χ.val (x : Circle L)) =
        fun x => U x - V x := by
      rw [heχ]
      exact circleMollify_sub hρ L.property hh hUi hVi hp₁ hpφ
    have hχtail := auxiliary_family_sub_transport_tails hUs hVs hUtail hVtail
    rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have he := auxiliary_family_transport_eq P N a hρ g φ hφcoef ψ hψ htr
      obtain ⟨h1, h2⟩ := hbounds φ (Or.inl rfl)
      refine ⟨fun x => ?_, fun x => ?_, fun x hx => ⟨?_, ?_⟩⟩
      · exact (congrArg (fun F : ℝ → ℝ => |deriv F x|) he).trans_le (h1 x)
      · exact (congrArg (fun F : ℝ → ℝ => |deriv (deriv F) x|) he).trans_le (h2 x)
      · exact (congrArg (fun F : ℝ → ℝ => |deriv F x|) he).trans_le
          ((hVtail x hx).1.trans (mul_le_mul_of_nonneg_right hTA (Real.rpow_nonneg (circDist_nonneg _ _) _)))
      · exact (congrArg (fun F : ℝ → ℝ => |deriv (deriv F) x|) he).trans_le
          ((hVtail x hx).2.trans (mul_le_mul_of_nonneg_right hTA (Real.rpow_nonneg (circDist_nonneg _ _) _)))
    · have he := auxiliary_family_transport_eq P N a hρ (subCircleL2 ξ g) χ hχcoef ψ hψ htr
      obtain ⟨h1, h2⟩ := hbounds χ (Or.inr rfl)
      have he' := he.trans heχsm
      refine ⟨fun x => ?_, fun x => ?_, fun x hx => ⟨?_, ?_⟩⟩
      · exact (congrArg (fun F : ℝ → ℝ => |deriv F x|) he).trans_le (h1 x)
      · exact (congrArg (fun F : ℝ → ℝ => |deriv (deriv F) x|) he).trans_le (h2 x)
      · exact (congrArg (fun F : ℝ → ℝ => |deriv F x|) he').trans_le
          ((hχtail x hx).1.trans (mul_le_mul_of_nonneg_right htTA (Real.rpow_nonneg (circDist_nonneg _ _) _)))
      · exact (congrArg (fun F : ℝ → ℝ => |deriv (deriv F) x|) he').trans_le
          ((hχtail x hx).2.trans (mul_le_mul_of_nonneg_right htTA (Real.rpow_nonneg (circDist_nonneg _ _) _)))

end Riesz1.Internal

end
