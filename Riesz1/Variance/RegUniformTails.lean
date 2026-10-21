/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.FiniteMarkMollify
public import Riesz1.ToMathlib.MollifyPowerTail
public import Riesz1.ToMathlib.CircleLiftTranslation
public import Riesz1.ToMathlib.CircleMollifyWeakDerivative
public import Riesz1.Variance.RegTransportBoundsFixedCircle
public import Riesz1.Variance.RegTransportBoundsCompact

/-!
# Compact transport tails after smoothing

The first and second derivative tails in Lemma 5.1,
with constants chosen before every enlarged observation circle.
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace Riesz1
namespace Internal

/-- Extend the central transport tails to every real lift and retain smoothness. -/
theorem compact_transport_tails_all_lifts (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (a : Scale) (ψ : Circle (observationLength a) → ℝ)
    (hc : Continuous ψ)
    (hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)))
    (hcoeff : ∀ k : ℤ, coeff (observationLength a)
      ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
        transportCoeffs P (observationLength a)
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k)
    (C : ℝ)
    (htail : ∀ x : ℝ, 1 ≤ |x| → |x| ≤ (observationLength a).val / 2 →
      |deriv (fun t : ℝ => ψ (t : Circle (observationLength a))) x| ≤ C * |x| ^ (P.val.2 - 2) ∧
      |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
        C * |x| ^ (P.val.2 - 3)) :
    ∀ x : ℝ, 1 ≤ dist (x : Circle (observationLength a)) 0 →
      ContDiffAt ℝ ∞ (fun t : ℝ => ψ (t : Circle (observationLength a))) x ∧
      |deriv (fun t : ℝ => ψ (t : Circle (observationLength a))) x| ≤
        C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 2) ∧
      |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
        C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 3) := by
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨r, hr, hrhalf, hsupp⟩ := hp
  obtain ⟨D, _, hoff⟩ := uniform_transport_deriv_off_support P 1 le_rfl
  intro x hx
  let z := centralRep L (x : Circle L)
  have hzx : (z : Circle L) = (x : Circle L) := AddCircle.coe_equivIco
  have hzL : |z| ≤ L.val / 2 := by
    have hm := centralRep_mem_Ico L (x : Circle L)
    exact abs_le.mpr ⟨hm.1, hm.2.le⟩
  have hdist : dist (x : Circle L) 0 = |z| := by
    rw [← hzx]
    simpa only [AddCircle.coe_zero, sub_zero] using
      CircleSingularity.dist_coe_eq_abs_sub L.property (x := z) (y := 0) (by simpa using hzL)
  have hz1 : 1 ≤ |z| := by rwa [hdist] at hx
  have hs := (hoff p a ψ hc hψ hcoeff r (|z| - r) z hr hrhalf
    (by linarith) hsupp (by linarith) hzL).1
  have hbound := htail z hz1 hzL
  rw [deriv_circle_lift_eq_of_coe_eq L ψ hzx,
    deriv_deriv_circle_lift_eq_of_coe_eq ψ hzx] at hbound
  rw [← hdist] at hbound
  exact ⟨contDiffAt_circle_lift_of_coe_eq ψ hzx hs, hbound⟩

end Internal

/-- Both compact smoothed transport tails of Lemma 5.1, outside
radius two. One constant precedes the sequence, the length and the radius.
The same parameters cover the strict case and the endpoint convention. -/
theorem regUniform_transportTails_compact (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) →
      ∀ a : Scale,
        PrimitiveRegularity (observationLength a) η P.val.2 B
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
        TransportRegularity P (observationLength a)
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
        ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
          ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
            (∀ k : ℤ, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)),
                complexL2Integrable _ _ hψ⟩ k = transportCoeffs P (observationLength a)
                  ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
            ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              2 ≤ |x| → |x| ≤ (observationLength a).val / 2 →
                |deriv (circleMollify ρ (observationLength a).val h
                  (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
                    C * |x| ^ (P.val.2 - 2) ∧
                |deriv (deriv (circleMollify ρ (observationLength a).val h
                  (fun t : ℝ => ψ (t : Circle (observationLength a))))) x| ≤
                    C * |x| ^ (P.val.2 - 3) := by
  obtain ⟨K, hK, htransport⟩ := compact_regTransportBounds P p hp η B n marks α α' C₀
    hη hB hC₀ hα0 hα1 hα' hα'0 hα'1
  let C := K * (2 ^ (2 - P.val.2) + 2 ^ (3 - P.val.2))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun ell hell hfamily a hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hi, hAC, _, _, htail⟩ := htransport ell hell hfamily a hprim hreg
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let F := fun t : ℝ => ψ (t : Circle L)
  let δ := fun t : ℝ => dist (t : Circle L) 0
  have hpF : Function.Periodic F L.val := by intro t; simp only [F, AddCircle.coe_add_period]
  have hFc : Continuous F := hc.comp (AddCircle.continuous_mk' L.val)
  have hδ : ∀ y z : ℝ, δ y ≤ δ z + |y - z| := by
    intro y z
    simp only [δ, dist_coe_zero_eq_circDist]
    exact circDist_le_add_abs L.property y z
  have hall := Internal.compact_transport_tails_all_lifts P p hp a ψ hc hψ hcoeff K htail
  have heq (h : ℝ) (hh : 0 < h) :
      deriv (circleMollify ρ L.val h F) = mollifyLine ρ h (deriv F) := by
    funext x
    rw [Internal.deriv_circleMollify_of_absolutelyContinuous hρ L.property hh hFc hpF hAC,
      circleMollify_eq_mollifyLine hρ L.property hh hi (Riesz1.periodic_deriv hpF)]
  refine ⟨ψ, hc, hψ, hcoeff, fun h hh hh1 x hx hxL => ?_⟩
  have hdx : δ x = |x| := by
    dsimp [δ]
    simpa only [AddCircle.coe_zero, sub_zero] using
      CircleSingularity.dist_coe_eq_abs_sub L.property (x := x) (y := 0) (by simpa using hxL)
  have hfirst := mollifyLine_power_tail hρ hh hh1 hK.le
    (show P.val.2 - 2 ≤ 0 by linarith [P.property.2.2]) hi.aestronglyMeasurable hδ
    (fun y hy => (hall y hy).2.1) (by rwa [hdx])
  have hsecond := deriv_mollifyLine_power_tail hρ hh hh1 hK.le
    (show P.val.2 - 3 ≤ 0 by linarith [P.property.2.2]) hi hδ
    (fun y hy => ((hall y hy).1.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (fun y hy => (hall y hy).2.2) (by rwa [hdx])
  change |deriv (circleMollify ρ L.val h F) x| ≤ _ ∧
    |deriv (deriv (circleMollify ρ L.val h F)) x| ≤ _
  rw [heq h hh]
  rw [hdx] at hfirst hsecond
  constructor
  · refine hfirst.trans ?_
    have hKC : K * 2 ^ (-(P.val.2 - 2)) ≤ C := by
      rw [show -(P.val.2 - 2) = 2 - P.val.2 by ring]
      dsimp [C]
      nlinarith [show 0 ≤ K * (2 : ℝ) ^ (3 - P.val.2) by positivity]
    exact mul_le_mul_of_nonneg_right hKC (by positivity)
  · refine hsecond.trans ?_
    have hKC : K * 2 ^ (-(P.val.2 - 3)) ≤ C := by
      rw [show -(P.val.2 - 3) = 3 - P.val.2 by ring]
      dsimp [C]
      nlinarith [show 0 ≤ K * (2 : ℝ) ^ (2 - P.val.2) by positivity]
    exact mul_le_mul_of_nonneg_right hKC (by positivity)

end Riesz1
