/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformOffSupport
public import Riesz1.Variance.RegUniformCompactCompatibility

/-! # Uniform compact admissibility of the two fixed smoothing families

Part of Lemma 5.1. All constants precede the shrinking sequence,
the smoothing radius and every observation circle.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1

/-- Full compact admissibility data for the actual regularization
and error. The only exponent loss is the permitted endpoint increase. -/
theorem regUniform_admissibility_compact (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (α α' C₀ : ℝ) (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C h₀ r : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              n marks α C₀) →
        ∀ h : ℝ, 0 < h → h ≤ h₀ → ∃ g e : Profile,
          ContDiff ℝ ∞ (fun t : ℝ => g.val (t : Circle unitLength)) ∧
          (∀ x : ℝ, g.val (x : Circle unitLength) =
            circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          CompactProfile g ∧ CompactProfile e ∧
          ∀ a : Scale,
            PrimitiveRegularity (observationLength a) η P.val.2 B
              ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
            TransportRegularity P (observationLength a)
              ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
            PrimitiveRegularity (observationLength a) η P.val.2 B
              ⟨periodizedProfile g (observationLength a), periodizedProfileL2 g a⟩ ∧
            PrimitiveRegularity (observationLength a) η P.val.2 (2 * B)
              ⟨periodizedProfile e (observationLength a), periodizedProfileL2 e a⟩ ∧
            TransportRegularity P (observationLength a)
              ⟨periodizedProfile g (observationLength a), periodizedProfileL2 g a⟩ n marks α' C ∧
            TransportRegularity P (observationLength a)
              ⟨periodizedProfile e (observationLength a), periodizedProfileL2 e a⟩ n marks α' C := by
  obtain ⟨K, hK, htransport⟩ := compact_regTransportBounds P p hp η B n marks α α' C₀
    hη hB hC₀ hα0 hα1 hα' hα'0 hα'1
  obtain ⟨D, hD, hb⟩ := Internal.smoothed_transport_second_of_capped_bound hρ
    (b := 1 - P.val.2 + α') (by linarith) (by linarith [P.property.2.1])
  obtain ⟨T, hT, htail⟩ := Internal.compact_smoothed_second_tail P p hp ρ hρ
  obtain ⟨H, r, hH, hr, hrhalf, hcompat⟩ := regUniform_compactCompatibility p hp ρ hρ
  let A := (2 + |marks ⟨0, n.pos⟩|) ^ (2 - P.val.2 + α')
  let Q := D * K * ((n : ℕ) + 1)
  let C := 2 * ((K + Q) * (A + 1) + K + T)
  have hA : 0 < A := by dsimp [A]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have he : -2 + P.val.2 - α' ≤ 0 := by linarith
  refine ⟨C, min H (1 / 4), r, hC, lt_min hH (by norm_num),
    (min_le_right _ _).trans (by norm_num), hr, hrhalf, fun ell hell hfamily h hh hh₀ => ?_⟩
  have hhH : h ≤ H := hh₀.trans (min_le_left _ _)
  have hhquarter : h ≤ 1 / 4 := hh₀.trans (min_le_right _ _)
  have hh1 : h ≤ 1 := hhquarter.trans (by norm_num)
  obtain ⟨g, e, hgs, hgv, hev, hgzero, hezero, hgc, hec, hcomp⟩ := hcompat h hh hhH
  refine ⟨g, e, hgs, hgv, hev, hgzero, hezero, hgc, hec, fun a hprim hreg => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let f := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  obtain ⟨ψ, hc, hψ, hcoeff, hi, hAC, _, hpoint, hunsmoothedtail⟩ :=
    htransport ell hell hfamily a hprim hreg
  obtain ⟨q, _, hqs, hqv, hqp, hfp⟩ := regUniform_primitive ρ hρ L η P.val.2 B f hprim h hh
  have hqeq : q.val = periodizedProfile g L := by
    funext y
    induction y using Quotient.inductionOn with
    | h x => exact (hqv x).trans (hcomp a x).1.symm
  have heeq : (fun x => f.val x - q.val x) = periodizedProfile e L := by
    funext y
    induction y using Quotient.inductionOn with
    | h x => exact (congrArg (fun z => f.val (x : Circle L) - z) (hqv x)).trans (hcomp a x).2.symm
  have hqsub : q = ⟨periodizedProfile g L, periodizedProfileL2 g a⟩ := Subtype.ext hqeq
  cases hqsub
  have hgp : PrimitiveRegularity L η P.val.2 B
      ⟨periodizedProfile g L, periodizedProfileL2 g a⟩ := hqp
  have hep : PrimitiveRegularity L η P.val.2 (2 * B)
      ⟨periodizedProfile e L, periodizedProfileL2 e a⟩ := by
    have hh := hfp
    rw [show (⟨(fun x => f.val x - (periodizedProfile g L) x), _⟩ :
      {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) =
      ⟨periodizedProfile e L, periodizedProfileL2 e a⟩ from Subtype.ext heeq] at hh
    exact hh
  obtain ⟨φ, _, hφs, hφv, hφcoeff⟩ :=
    Internal.exists_circleMollify_L2 hρ L hh ⟨ψ, hψ⟩
  have hfi : LocallyIntegrable (fun t : ℝ => f.val (t : Circle L)) volume :=
    Internal.locallyIntegrable_circle_lift (T := L.val)
      (f := f.val) (complexL2Integrable L _ f.property).re
  have hfp' : Function.Periodic (fun t : ℝ => f.val (t : Circle L)) L.val := by
    intro t
    simp only [AddCircle.coe_add_period]
  have hgf (k : ℤ) : coeff L ⟨(fun x => ((periodizedProfile g L) x : ℂ)),
      complexL2Integrable L _ (periodizedProfileL2 g a)⟩ k =
      coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k *
        (mollifierFT ρ (h * k / L.val) : ℂ) :=
    Internal.fourierCoeff_circleMollify hρ hh hfi hfp' f.val (periodizedProfile g L) (fun _ => rfl) hqv k
  have hφtransport (k : ℤ) : coeff L ⟨(fun x => (φ.val x : ℂ)),
      complexL2Integrable L _ φ.property⟩ k = transportCoeffs P L
        ⟨periodizedProfile g L, periodizedProfileL2 g a⟩ k := by
    rw [hφcoeff, hcoeff]
    have hgf' := hgf k
    by_cases hk : k = 0
    · simp only [transportCoeffs, hk, ite_true, zero_mul]
    · simp only [transportCoeffs, hk, ite_false]
      rw [hgf']
      ring
  have hφbound (x : ℝ) : |deriv (deriv (fun t : ℝ => φ.val (t : Circle L))) x| ≤
      Q * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^
        (-2 + P.val.2 - α')) := by
    rw [show (fun t : ℝ => φ.val (t : Circle L)) =
      circleMollify ρ L.val h (fun t : ℝ => ψ (t : Circle L)) from funext hφv]
    have ht := hb L ((one_le_inv₀ a.property.1).mpr a.property.2) n marks K hK.le ψ hc hi hAC
      (by simpa only [show -(1 - P.val.2 + α') = -1 + P.val.2 - α' by ring,
        show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hpoint) h hh hh1 x
    simpa only [Q, show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using ht
  have hinner (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L))
      (hx1 : dist (x : Circle L) 0 ≤ 1) :
      |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤
        K * (A + 1) * (∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α')) ∧
      |deriv (deriv (fun t : ℝ => φ.val (t : Circle L))) x| ≤
        Q * (A + 1) * (∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α')) := by
    have hone := Internal.inner_mark_power_sum L n marks he hx1 hx
    change 1 ≤ (2 + |marks ⟨0, n.pos⟩|) ^ (-(-2 + P.val.2 - α')) * _ at hone
    rw [show -(-2 + P.val.2 - α') = 2 - P.val.2 + α' by ring] at hone
    change 1 ≤ A * _ at hone
    have hp := ((hpoint x hx).2.2).trans (mul_le_mul_of_nonneg_left
      (cappedMarkDistance_rpow_le_one_add_sum _ _ _) hK.le)
    have hm : (∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-2 + P.val.2 - α')) ≤
        ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α') := by
      apply Finset.sum_le_sum
      intro j _
      exact Real.rpow_le_rpow_of_nonpos (dist_pos.mpr (hx j)) (le_max_left _ _) he
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hone hK.le]
    · nlinarith [hφbound x, mul_le_mul_of_nonneg_left hm hQ.le,
        mul_le_mul_of_nonneg_left hone hQ.le]
  have houter (x : ℝ) (hx1 : 1 ≤ dist (x : Circle L) 0) :
      |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤ K * dist (x : Circle L) 0 ^ (P.val.2 - 3) ∧
      |deriv (deriv (fun t : ℝ => φ.val (t : Circle L))) x| ≤ T * dist (x : Circle L) 0 ^ (P.val.2 - 3) := by
    constructor
    · exact (Internal.compact_transport_tails_all_lifts P p hp a ψ hc hψ hcoeff K hunsmoothedtail x hx1).2.2
    · rw [show (fun t : ℝ => φ.val (t : Circle L)) =
        circleMollify ρ L.val h (fun t : ℝ => ψ (t : Circle L)) from funext hφv]
      exact htail a ψ hc hψ hcoeff hi hAC h hh hhquarter x hx1
  let χ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)} :=
    ⟨(fun x => ψ x - φ.val x), by
      exact (hψ.sub φ.property).ae_eq
        (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩
  have hχtransport (k : ℤ) : coeff L ⟨(fun x => (χ.val x : ℂ)),
      complexL2Integrable L _ χ.property⟩ k = transportCoeffs P L
        ⟨periodizedProfile e L, periodizedProfileL2 e a⟩ k := by
    rw [Internal.coeff_sub_real_L2 L ⟨ψ, hψ⟩ φ, hcoeff, hφtransport]
    have heq : (⟨periodizedProfile e L, periodizedProfileL2 e a⟩ :
      {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) =
      ⟨(fun x => f.val x - (periodizedProfile g L) x), by
        exact (f.property.sub (periodizedProfileL2 g a)).ae_eq
          (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub]; rfl)⟩ := by
      apply Subtype.ext
      exact heeq.symm
    rw [heq]
    by_cases hk : k = 0
    · simp only [transportCoeffs, hk, ite_true, sub_self]
    · simp only [transportCoeffs, hk, ite_false]
      rw [Internal.coeff_sub_real_L2 L f ⟨periodizedProfile g L, periodizedProfileL2 g a⟩]
      ring
  have henv (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
      |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| +
      |deriv (deriv (fun t : ℝ => φ.val (t : Circle L))) x| ≤ C *
        ((if dist (x : Circle L) 0 ≤ 1 then ∑ j, dist (x : Circle L) (marks j : Circle L) ^
          (-2 + P.val.2 - α') else 0) +
         (if 1 ≤ dist (x : Circle L) 0 then dist (x : Circle L) 0 ^ (P.val.2 - 3) else 0)) := by
    have hs : 0 ≤ ∑ j, dist (x : Circle L) (marks j : Circle L) ^ (-2 + P.val.2 - α') := by positivity
    have ht : 0 ≤ dist (x : Circle L) 0 ^ (P.val.2 - 3) := by positivity
    by_cases hx1 : dist (x : Circle L) 0 ≤ 1
    · have hb' := hinner x hx hx1
      rw [ite_eq_left hx1]
      split_ifs
      all_goals dsimp [C]; nlinarith
    · have hb' := houter x (le_of_not_ge hx1)
      rw [ite_eq_right hx1, ite_eq_left (le_of_not_ge hx1), zero_add]
      dsimp [C]
      nlinarith [mul_nonneg (le_of_lt hA) (le_of_lt hQ),
        mul_nonneg (le_of_lt hA) (le_of_lt hK)]
  refine ⟨hgp, hep, ⟨hreg.1, φ, hφtransport, fun x hx => ?_⟩,
    ⟨hreg.1, χ, hχtransport, fun x hx => ?_⟩⟩
  · refine ⟨(hφs.of_le (by simp)).contDiffAt, ?_⟩
    simpa only [show -3 + P.val.2 = P.val.2 - 3 by ring] using
      (le_trans (le_add_of_nonneg_left (abs_nonneg _)) (henv x hx))
  · have hψs := (hpoint x hx).1
    have hφs' : ContDiff ℝ 2 (fun t : ℝ => φ.val (t : Circle L)) := hφs.of_le (by simp)
    refine ⟨hψs.sub hφs'.contDiffAt, ?_⟩
    have heq : deriv (deriv (fun t : ℝ => χ.val (t : Circle L))) x =
        deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x -
          deriv (deriv (fun t : ℝ => φ.val (t : Circle L))) x := by
      have hnear := hψs.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ ∞)
      have hd : deriv (fun t : ℝ => χ.val (t : Circle L)) =ᶠ[nhds x]
          fun t => deriv (fun t : ℝ => ψ (t : Circle L)) t -
            deriv (fun t : ℝ => φ.val (t : Circle L)) t := by
        filter_upwards [hnear] with y hy
        exact deriv_fun_sub (hy.differentiableAt (by norm_num))
          (hφs'.differentiable (by norm_num) y)
      rw [hd.deriv_eq]
      exact deriv_fun_sub
        ((hψs.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
        ((hφs'.contDiffAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    rw [heq]
    simpa only [show -3 + P.val.2 = P.val.2 - 3 by ring] using
      (abs_sub _ _).trans (henv x hx)

/-- The same compact families with one complete `TestData` each,
independent of the smoothing parameter and of the scale sequence. -/
theorem regUniform_admissible_compact (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (α α' C₀ : ℝ) (hη : 0 < η) (hηs : η < P.val.2)
    (hB : 0 < B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C h₀ r : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              n marks α C₀) →
        ∀ h : ℝ, 0 < h → h ≤ h₀ → ∃ g e : Profile,
          (∀ x : ℝ, g.val (x : Circle unitLength) =
            circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          Admissible P g ell α' (η, B, C, ⟨n, marks⟩) ∧
          Admissible P e ell α' (η, 2 * B, C, ⟨n, marks⟩) := by
  obtain ⟨C, h₀, r, hC, hh₀, hh₁, hr, hrhalf, hb⟩ :=
    regUniform_admissibility_compact P p hp η B n marks α α' C₀ hη hB.le hC₀
      hα0 hα1 hα' hα'0 hα'1 ρ hρ
  refine ⟨C, h₀, r, hC, hh₀, hh₁, hr, hrhalf, fun ell hell hfamily h hh hhh => ?_⟩
  obtain ⟨g, e, _, hgv, hev, hgzero, hezero, hgc, hec, hdata⟩ := hb ell hell hfamily h hh hhh
  refine ⟨g, e, hgv, hev, hgzero, hezero, ?_, ?_⟩
  · refine ⟨hα'0.le, hα'1, hη, hηs, hB, hC, Or.inr ⟨hgc, hell, fun N => ?_⟩⟩
    have hd := hdata (ell N) (hfamily N).1 (hfamily N).2
    exact ⟨hd.1, hd.2.2.1⟩
  · refine ⟨hα'0.le, hα'1, hη, hηs, by positivity, hC, Or.inr ⟨hec, hell, fun N => ?_⟩⟩
    have hd := hdata (ell N) (hfamily N).1 (hfamily N).2
    exact ⟨hd.2.1, hd.2.2.2⟩

end Riesz1
