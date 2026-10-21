/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegTransportBoundsComparison
public import Riesz1.Variance.RegTransportBoundsLargeCircle
public import Riesz1.Variance.RegTransportBoundsOffSupport
public import Riesz1.Frozen.Scales
public import Riesz1.ToMathlib.FiniteMarkDistanceComparison

/-!
# Quantitative compact transport bounds on every observation circle

This completes the compact-profile case of Lemma 5.1.
The constant precedes the shrinking sequence and every observation scale, including
lengths below the threshold of the large-circle theorem.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz1

/-- All bounds of Lemma 5.1 for a compact admissible profile, with
one constant chosen before every shrinking sequence. In fact every observation circle
satisfying the same fixed admissibility bounds is covered, including those outside the
sequence. Taking `α' = α` gives the strict case. Taking `α' = α + δ` gives the endpoint. -/
theorem compact_regTransportBounds (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) → ∀ a : Scale,
      PrimitiveRegularity (observationLength a) η P.val.2 B
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
      TransportRegularity P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
      ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
          (∀ k : ℤ, coeff (observationLength a)
            ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
            transportCoeffs P (observationLength a)
              ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
          LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) volume ∧
          (∀ u v : ℝ, AbsolutelyContinuousOnInterval
            (fun t : ℝ => ψ (t : Circle (observationLength a))) u v) ∧
          (∀ y : Circle (observationLength a), |ψ y| +
            (∫ t in (-(observationLength a).val / 2)..((observationLength a).val / 2),
              |deriv (fun u : ℝ => ψ (u : Circle (observationLength a))) t|) ≤ C) ∧
          (∀ x : ℝ, (∀ j, (x : Circle (observationLength a)) ≠
              (marks j : Circle (observationLength a))) →
            ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle (observationLength a))) x ∧
            |deriv (fun t : ℝ => ψ (t : Circle (observationLength a))) x| ≤ C *
              cappedMarkDistance (fun j => (marks j : Circle (observationLength a)))
                (x : Circle (observationLength a)) ^ (-1 + P.val.2 - α') ∧
            |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤ C *
              cappedMarkDistance (fun j => (marks j : Circle (observationLength a)))
                (x : Circle (observationLength a)) ^ (-2 + P.val.2 - α')) ∧
          ∀ x : ℝ, 1 ≤ |x| → |x| ≤ (observationLength a).val / 2 →
            |deriv (fun t : ℝ => ψ (t : Circle (observationLength a))) x| ≤
              C * |x| ^ (P.val.2 - 2) ∧
            |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
              C * |x| ^ (P.val.2 - 3) := by
  classical
  obtain ⟨D, hD, hbase⟩ := exists_uniform_compact_transport_sup_secondDeriv_tails
    P p hp η B n marks α α' C₀ hη hB hC₀ hα0 hα1 hα'
  obtain ⟨K, L₀, hK, hL₀, hlarge⟩ := Internal.exists_uniform_large_circle_regTransportBounds
    P p hp η B n marks α α' C₀ hη hB hC₀ hα0 hα1 hα' hα'0 hα'1
  obtain ⟨ρ, hρ, hρ1, hsupp⟩ := hp
  let σ := (ρ + 1 / 2) / 2
  have hρσ : ρ < σ := by dsimp [σ]; linarith
  have hσ : σ < 1 / 2 := by dsimp [σ]; linarith
  obtain ⟨Q, hQ, hcompare⟩ := Internal.uniform_transport_difference_lipschitz
    P p hρ hσ hρσ hsupp
  obtain ⟨T, hT, hoff⟩ := Internal.uniform_transport_deriv_off_support P 1 le_rfl
  let Z := ∫ y : ℝ, |zeroExtension p y|
  let E := T * Z * (σ - ρ) ^ (P.val.2 - 2)
  have hZ : 0 ≤ Z := integral_nonneg fun _ => abs_nonneg _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hL₀pos : 0 < L₀ := by linarith
  let V := K + (Q + E) * L₀
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let C := D + K + K * ((n : ℕ) + 1) + Q + E + V + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKN : 0 ≤ K * ((n : ℕ) + 1) := by positivity
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hKC : K ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  have hinnerC : K * ((n : ℕ) + 1) + Q ≤ C := by dsimp [C]; linarith
  let R := 2 + ∑ j, |marks j|
  have hR : 2 ≤ R := by
    dsimp [R]
    linarith [Finset.sum_nonneg (s := Finset.univ) (fun j _ => abs_nonneg (marks j))]
  have hmarks : ∀ j, |marks j| ≤ R := by
    intro j
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun i => |marks i|) (fun i _ => abs_nonneg (marks i)) (Finset.mem_univ j)
    dsimp [R]
    linarith
  refine ⟨C, hC, fun ell hell hfamily a hprim hreg => ?_⟩
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  by_cases ha : L₀ ≤ L.val
  · obtain ⟨ψ, hc, hψ, hcoeff, hi, hAC, hnorm, hpoint, htail⟩ := hlarge a ha hprim hreg
    refine ⟨ψ, hc, hψ, hcoeff, hi, hAC, fun y => (hnorm y).trans hKC, ?_, ?_⟩
    · intro x hx
      exact ⟨(hpoint x hx).1,
        (hpoint x hx).2.1.trans (mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _)),
        (hpoint x hx).2.2.trans (mul_le_mul_of_nonneg_right hKC
          (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _))⟩
    · intro x hx hxL
      exact ⟨(htail x hx hxL).1.trans (mul_le_mul_of_nonneg_right hKC (by positivity)),
        (htail x hx hxL).2.trans (mul_le_mul_of_nonneg_right hKC (by positivity))⟩
  have hsmall : L.val ≤ L₀ := (lt_of_not_ge ha).le
  let U := max L₀ (4 * R)
  have hU : 0 < U := lt_of_lt_of_le (by linarith : 0 < L₀) (le_max_left _ _)
  obtain ⟨j, hj⟩ := (hell.eventually (eventually_lt_nhds (inv_pos.mpr hU))).exists
  let a₀ := ell ⟨j + 1, Nat.succ_pos j⟩
  let L' := observationLength a₀
  have hUL' : U ≤ L'.val :=
    (le_inv_comm₀ hU a₀.property.1).mpr hj.le
  have hL' : L₀ ≤ L'.val := (le_max_left _ _).trans hUL'
  have hR' : 4 * R ≤ L'.val := (le_max_right _ _).trans hUL'
  have : Fact (0 < L'.val) := ⟨L'.property⟩
  obtain ⟨ψ₀, hc₀, hψ₀, hcoeff₀, hi₀, _, hnorm₀, hpoint₀, _⟩ :=
    hlarge a₀ hL' (hfamily ⟨j + 1, Nat.succ_pos j⟩).1
      (hfamily ⟨j + 1, Nat.succ_pos j⟩).2
  obtain ⟨ψ, hc, hψ, hcoeff, hsup, hi, hAC, hpoint, htail⟩ := hbase a hprim hreg
  let f : ℝ → ℝ := fun x => ψ (x : Circle L)
  let f₀ : ℝ → ℝ := fun x => ψ₀ (x : Circle L')
  have hLip := hcompare a a₀ ψ ψ₀ hc hc₀ hψ hψ₀ hcoeff hcoeff₀
  have hdist (x : ℝ) (hx : |x| < σ) (i : Fin (n : ℕ)) :
      dist (x : Circle L') (marks i : Circle L') = |x - marks i| := by
    apply CircleSingularity.dist_coe_eq_abs_sub L'.property
    exact (abs_sub _ _).trans ((add_le_add hx.le (hmarks i)).trans (by linarith))
  have hne (x : ℝ) (hx : |x| < σ)
      (hxm : ∀ i, (x : Circle L) ≠ (marks i : Circle L)) :
      ∀ i, (x : Circle L') ≠ (marks i : Circle L') := by
    intro i he
    have hh : |x - marks i| = 0 := by rw [← hdist x hx i, he, dist_self]
    exact hxm i (by rw [sub_eq_zero.mp (abs_eq_zero.mp hh)])
  have hdiff (x : ℝ) (hx : |x| < σ)
      (hxm : ∀ i, (x : Circle L) ≠ (marks i : Circle L)) :
      |deriv f x| ≤ |deriv f₀ x| + Q := by
    have hh := norm_deriv_le_of_lipschitzOn (isOpen_Ioo.mem_nhds (abs_lt.mp hx)) hLip
    rw [deriv_fun_sub ((hpoint x hxm).1.differentiableAt (by norm_num))
      ((hpoint₀ x (hne x hx hxm)).1.differentiableAt (by norm_num)),
      Real.norm_eq_abs, Real.coe_toNNReal Q hQ.le] at hh
    have ht := abs_sub_abs_le_abs_sub (deriv f x) (deriv f₀ x)
    linarith
  have hout (x : ℝ) (hx : σ ≤ |x|) (hxL : |x| ≤ L.val / 2) : |deriv f x| ≤ E := by
    have hh := (hoff p a ψ hc hψ hcoeff ρ (σ - ρ) x hρ hρ1
      (by linarith) hsupp (by linarith) hxL).2
    simpa only [iteratedDeriv_one, Real.norm_eq_abs, Nat.cast_one,
      show P.val.2 - 1 - 1 = P.val.2 - 2 by ring] using hh
  have hwhole₀ : IntervalIntegrable (deriv f₀) volume (-L'.val / 2) (L'.val / 2) :=
    IntegrableOn.intervalIntegrable (hi₀.integrableOn_isCompact isCompact_uIcc)
  have hwhole : IntervalIntegrable (deriv f) volume (-L.val / 2) (L.val / 2) :=
    IntegrableOn.intervalIntegrable (hi.integrableOn_isCompact isCompact_uIcc)
  have hsub₀ : IntervalIntegrable (deriv f₀) volume (-L.val / 2) (L.val / 2) :=
    IntegrableOn.intervalIntegrable (hi₀.integrableOn_isCompact isCompact_uIcc)
  have hint₀ : (∫ x in (-L.val / 2)..(L.val / 2), |deriv f₀ x|) ≤ K := by
    have hh := intervalIntegral.integral_mono_interval
      (by linarith : -L'.val / 2 ≤ -L.val / 2) (by linarith [L.property])
      (by linarith : L.val / 2 ≤ L'.val / 2)
      (ae_of_all _ fun _ => abs_nonneg _) hwhole₀.abs
    exact hh.trans (by linarith [hnorm₀ (0 : Circle L'), abs_nonneg (ψ₀ 0)])
  have hint : (∫ x in (-L.val / 2)..(L.val / 2), |deriv f x|) ≤ V := by
    have hmajor : (fun x => |deriv f x|) ≤ᵐ[volume.restrict (Icc (-L.val / 2) (L.val / 2))]
        fun x => |deriv f₀ x| + (Q + E) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae
        ((CircleSingularity.countable_marked_lifts (T := L.val) marks).ae_notMem volume)]
        with x hx hxm
      have hxm' : ∀ i, (x : Circle L) ≠ (marks i : Circle L) := by
        simpa only [mem_ofPred_eq, not_exists] using hxm
      by_cases hxσ : |x| < σ
      · linarith [hdiff x hxσ hxm']
      · have hxL : |x| ≤ L.val / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
        linarith [hout x (le_of_not_gt hxσ) hxL, abs_nonneg (deriv f₀ x)]
    have hm := intervalIntegral.integral_mono_ae_restrict
      (by linarith [L.property] : -L.val / 2 ≤ L.val / 2)
      hwhole.abs (hsub₀.abs.add intervalIntegrable_const) hmajor
    rw [intervalIntegral.integral_add hsub₀.abs intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul] at hm
    dsimp [V]
    nlinarith [mul_le_mul_of_nonneg_left hsmall (by linarith : 0 ≤ Q + E)]
  refine ⟨ψ, hc, hψ, hcoeff, hi, hAC, ?_, ?_, ?_⟩
  · intro y
    change |ψ y| + (∫ x in (-L.val / 2)..(L.val / 2), |deriv f x|) ≤ C
    dsimp [C]
    linarith [hsup y]
  · intro x hx
    refine ⟨(hpoint x hx).1, ?_, (hpoint x hx).2.trans
      (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _))⟩
    let y := centralRep L (x : Circle L)
    have hyx : (y : Circle L) = (x : Circle L) := AddCircle.coe_equivIco
    have hym : ∀ i, (y : Circle L) ≠ (marks i : Circle L) := by simpa only [hyx] using hx
    have hyL : |y| ≤ L.val / 2 := by
      have hh := centralRep_mem_Ico L (x : Circle L)
      exact abs_le.mpr ⟨hh.1, hh.2.le⟩
    let r := cappedMarkDistance (fun i => (marks i : Circle L)) (y : Circle L)
    let e := -1 + P.val.2 - α'
    have hr : 0 < r := cappedMarkDistance_pos _ _ hym
    have hr1 : r ≤ 1 := cappedMarkDistance_le_one _ _
    have he : e ≤ 0 := by dsimp [e]; linarith
    have hone : 1 ≤ r ^ e := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 he
    have hybound : |deriv f y| ≤ C * r ^ e := by
      by_cases hyσ : |y| < σ
      · have hdistle (i : Fin (n : ℕ)) :
            dist (y : Circle L) (marks i : Circle L) ≤
              dist (y : Circle L') (marks i : Circle L') := by
          rw [hdist y hyσ i, dist_eq_norm, ← QuotientAddGroup.mk_sub]
          exact QuotientAddGroup.norm_mk_le_norm
        have hp := cappedMarkDistance_rpow_le_of_dist_le
          (fun i => (marks i : Circle L)) (fun i => (marks i : Circle L'))
          (y : Circle L) (y : Circle L') hym he hdistle
        have hq₀' : |deriv f₀ y| ≤ K * ((n : ℕ) + 1) * r ^ e := by
          have hh := (hpoint₀ y (hne y hyσ hym)).2.1.trans
            (mul_le_mul_of_nonneg_left hp hK.le)
          simpa only [Fintype.card_fin, mul_assoc] using hh
        have hqy := hdiff y hyσ hym
        exact hqy.trans (by
          nlinarith [mul_le_mul_of_nonneg_left hone hQ.le,
            mul_le_mul_of_nonneg_right hinnerC (Real.rpow_nonneg hr.le e)])
      · exact (hout y (le_of_not_gt hyσ) hyL).trans
          (hEC.trans (le_mul_of_one_le_right hC.le hone))
    dsimp only [r, e] at hybound
    rw [Internal.deriv_circle_lift_eq_of_coe_eq L ψ hyx, hyx] at hybound
    exact hybound
  · intro x hx hxL
    exact ⟨(htail x hx hxL).1.trans (mul_le_mul_of_nonneg_right hDC (by positivity)),
      (htail x hx hxL).2.trans (mul_le_mul_of_nonneg_right hDC (by positivity))⟩

end Riesz1
