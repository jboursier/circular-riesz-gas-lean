/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformPrimitive
public import Riesz1.Variance.RegUniformFirstTransport
public import Riesz1.Variance.RegUniformSecondTransport

/-! # Transport envelopes uniform over both smoothing families

Internal convolution estimates for Lemma 5.1.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1.Internal

/-- Classical second derivatives subtract wherever the first input is twice
continuously differentiable. Smoothness elsewhere is unnecessary. -/
theorem secondDeriv_sub_of_contDiffAt {F G : ℝ → ℝ} {x : ℝ}
    (hF : ContDiffAt ℝ 2 F x) (hG : ContDiff ℝ 2 G) :
    deriv (deriv (fun t => F t - G t)) x = deriv (deriv F) x - deriv (deriv G) x := by
  have hnear := hF.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ ∞)
  have hd : deriv (fun t => F t - G t) =ᶠ[nhds x] fun t => deriv F t - deriv G t := by
    filter_upwards [hnear] with y hy
    exact deriv_fun_sub (hy.differentiableAt (by norm_num)) (hG.differentiable (by norm_num) y)
  rw [hd.deriv_eq]
  exact deriv_fun_sub
    ((hF.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))
    ((hG.contDiffAt.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

/-- Near-mark transport estimates uniform in both smoothing parameters.
The two inputs at the second step are the actual smoothed transport and its
difference from the original transport, with their exact Fourier identities. -/
theorem transport_family_envelopes {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) {b K : ℝ}
    (hb : 0 ≤ b) (hb1 : b < 1) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Length), 1 ≤ L.val →
      ∀ ψ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
        Continuous ψ.val → (∀ x, |ψ.val x| ≤ K) →
        LocallyIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume →
        (∀ u v, AbsolutelyContinuousOnInterval (fun t : ℝ => ψ.val (t : Circle L)) u v) →
        (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          ContDiffAt ℝ 2 (fun t : ℝ => ψ.val (t : Circle L)) x ∧
          |deriv (fun t : ℝ => ψ.val (t : Circle L)) x| ≤
            K * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-b) ∧
          |deriv (deriv (fun t : ℝ => ψ.val (t : Circle L))) x| ≤
            K * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - b)) →
        ∀ t : ℝ, 0 < t → t ≤ 1 →
          ∃ φ χ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
            (∀ x : ℝ, φ.val (x : Circle L) = circleMollify ρ L.val t
              (fun y : ℝ => ψ.val (y : Circle L)) x) ∧
            (∀ x, χ.val x = ψ.val x - φ.val x) ∧
            (∀ k, coeff L ⟨(fun x => (φ.val x : ℂ)), complexL2Integrable L _ φ.property⟩ k =
              coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k *
                (mollifierFT ρ (t * k / L.val) : ℂ)) ∧
            (∀ k, coeff L ⟨(fun x => (χ.val x : ℂ)), complexL2Integrable L _ χ.property⟩ k =
              coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k -
              coeff L ⟨(fun x => (φ.val x : ℂ)), complexL2Integrable L _ φ.property⟩ k) ∧
            ∀ v, (v = φ ∨ v = χ) →
              Continuous v.val ∧ (∀ x, |v.val x| ≤ C) ∧
              ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
                |circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L)) x| ≤ C ∧
                |deriv (circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L))) x| ≤
                  C * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-b)) ∧
                |deriv (deriv (circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L)))) x| ≤
                  C * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-1 - b)) := by
  obtain ⟨D, hD, hfirst⟩ := smoothed_transport_first_of_capped_bound hρ hb hb1
  obtain ⟨E, hE, hsecond⟩ := smoothed_transport_second_of_capped_bound hρ hb hb1
  let N := (n : ℕ) + (1 : ℝ)
  have hN : 1 ≤ N := by dsimp [N]; linarith [show (0 : ℝ) ≤ (n : ℕ) by positivity]
  let M := 2 * (K + (D + E) * K * N ^ 2 + 1)
  have hM : 0 < M := by dsimp [M]; positivity
  let C := 2 * K + D * M + E * M * N + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hKC : 2 * K ≤ C := by dsimp [C]; nlinarith [show 0 ≤ D * M by positivity, show 0 ≤ E * M * N by positivity]
  have hDC : D * M ≤ C := by dsimp [C]; nlinarith [show 0 ≤ E * M * N by positivity]
  have hEC : E * M * ((n : ℕ) + 1) ≤ C := by
    change E * M * N ≤ C
    dsimp [C]
    nlinarith [show 0 ≤ D * M by positivity]
  refine ⟨C, hC, fun L hL ψ hc hsup hi hAC hpoint t ht ht1 => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨φ, hφc, hφs, hφv, hφcoeff⟩ := exists_circleMollify_L2 hρ L ht ψ
  let χ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)} :=
    ⟨(fun x => ψ.val x - φ.val x), by
      exact (ψ.property.sub φ.property).ae_eq
        (ae_of_all _ fun x => by simp only [Pi.sub_apply, Complex.ofReal_sub])⟩
  have hφs2 : ContDiff ℝ 2 (fun y : ℝ => φ.val (y : Circle L)) := hφs.of_le (by simp)
  have hφhi : LocallyIntegrable (deriv (fun y : ℝ => φ.val (y : Circle L))) volume :=
    (hφs2.continuous_deriv (by norm_num)).locallyIntegrable
  have hφAC (u v : ℝ) : AbsolutelyContinuousOnInterval (fun y : ℝ => φ.val (y : Circle L)) u v :=
    (hφs2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffOn.absolutelyContinuousOnInterval
  have hψper : Function.Periodic (fun y : ℝ => ψ.val (y : Circle L)) L.val := by
    intro y; simp only [AddCircle.coe_add_period]
  have hφsup (x : Circle L) : |φ.val x| ≤ K := by
    induction x using Quotient.inductionOn with
    | h x =>
      rw [hφv]
      exact circleMollify_abs_le hρ L.property ht
        (hc.comp (AddCircle.continuous_mk' L.val)).locallyIntegrable
        hψper (fun y => hsup _) x
  have hφcap (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
      |deriv (fun y : ℝ => φ.val (y : Circle L)) x| ≤
        D * K * N * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-b) ∧
      |deriv (deriv (fun y : ℝ => φ.val (y : Circle L))) x| ≤
        E * K * N ^ 2 * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - b) := by
    have heq : (fun y : ℝ => φ.val (y : Circle L)) =
        circleMollify ρ L.val t (fun y : ℝ => ψ.val (y : Circle L)) := funext hφv
    rw [heq]
    have h1 := hfirst L hL n marks K hK ψ.val hc hi hAC (fun y hy => (hpoint y hy).2.1) t ht ht1 x
    have h2 := hsecond L hL n marks K hK ψ.val hc hi hAC hpoint t ht ht1 x
    have henv (e : ℝ) (he : e ≤ 0) :
        (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) t ^ e) ≤
          N * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ e := by
      have hm : (∑ j, max (dist (x : Circle L) (marks j : Circle L)) t ^ e) ≤
          ∑ j, dist (x : Circle L) (marks j : Circle L) ^ e := by
        apply Finset.sum_le_sum
        intro j _
        exact Real.rpow_le_rpow_of_nonpos (dist_pos.mpr (hx j)) (le_max_left _ _) he
      have hs := sum_dist_rpow_le_cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) hx he
      have ho := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        (cappedMarkDistance_pos _ _ hx) (cappedMarkDistance_le_one _ _) he
      simp only [Fintype.card_fin] at hs
      dsimp [N]
      nlinarith
    constructor
    · exact h1.trans (by nlinarith [mul_le_mul_of_nonneg_left (henv (-b) (by linarith)) (by positivity : 0 ≤ D * K)])
    · exact h2.trans (by nlinarith [mul_le_mul_of_nonneg_left (henv (-1 - b) (by linarith)) (by positivity : 0 ≤ E * K * ((n : ℕ) + 1))])
  have hχcap (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
      ContDiffAt ℝ 2 (fun y : ℝ => χ.val (y : Circle L)) x ∧
      |deriv (fun y : ℝ => χ.val (y : Circle L)) x| ≤
        M * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-b) ∧
      |deriv (deriv (fun y : ℝ => χ.val (y : Circle L))) x| ≤
        M * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - b) := by
    have hr : 0 ≤ cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) :=
      (cappedMarkDistance_pos _ _ hx).le
    have hψs := (hpoint x hx).1
    refine ⟨hψs.sub hφs2.contDiffAt, ?_, ?_⟩
    · change |deriv (fun y : ℝ => ψ.val (y : Circle L) - φ.val (y : Circle L)) x| ≤ _
      rw [deriv_fun_sub (hψs.differentiableAt (by norm_num)) (hφs2.differentiable (by norm_num) x)]
      have hcoef : K + D * K * N ≤ M := by
        dsimp [M]
        nlinarith [sq_nonneg (N - 1), mul_nonneg (hD.le) hK,
          mul_nonneg (hE.le) hK, mul_nonneg (mul_nonneg hD.le hK) (show 0 ≤ N ^ 2 - N by nlinarith)]
      exact (abs_sub _ _).trans (by
        nlinarith [(hpoint x hx).2.1, (hφcap x hx).1,
          mul_le_mul_of_nonneg_right hcoef (show 0 ≤ cappedMarkDistance (fun j => (marks j : Circle L))
            (x : Circle L) ^ (-b) by positivity)])
    · change |deriv (deriv (fun y : ℝ => ψ.val (y : Circle L) - φ.val (y : Circle L))) x| ≤ _
      rw [secondDeriv_sub_of_contDiffAt hψs hφs2]
      have hcoef : K + E * K * N ^ 2 ≤ M := by dsimp [M]; nlinarith [mul_nonneg hD.le hK]
      exact (abs_sub _ _).trans (by
        nlinarith [(hpoint x hx).2.2, (hφcap x hx).2,
          mul_le_mul_of_nonneg_right hcoef (show 0 ≤ cappedMarkDistance (fun j => (marks j : Circle L))
            (x : Circle L) ^ (-1 - b) by positivity)])
  have hχhi : LocallyIntegrable (deriv (fun y : ℝ => χ.val (y : Circle L))) volume := by
    apply (hi.sub hφhi).congr
    filter_upwards [(CircleSingularity.countable_marked_lifts (T := L.val) marks).ae_notMem volume]
      with x hx
    have hne : ∀ j, (x : Circle L) ≠ (marks j : Circle L) := by simpa only [Set.mem_ofPred_eq, not_exists] using hx
    exact (deriv_fun_sub ((hpoint x hne).1.differentiableAt (by norm_num))
      (hφs2.differentiable (by norm_num) x)).symm
  have hχAC (u v : ℝ) : AbsolutelyContinuousOnInterval (fun y : ℝ => χ.val (y : Circle L)) u v :=
    (hAC u v).sub (hφAC u v)
  refine ⟨φ, χ, hφv, fun _ => rfl, hφcoeff, coeff_sub_real_L2 L ψ φ, fun v hv => ?_⟩
  have hvc : Continuous v.val := by rcases hv with rfl | rfl; exact hφc; exact hc.sub hφc
  have hvi : LocallyIntegrable (deriv (fun y : ℝ => v.val (y : Circle L))) volume := by
    rcases hv with rfl | rfl; exact hφhi; exact hχhi
  have hvAC (u w : ℝ) : AbsolutelyContinuousOnInterval (fun y : ℝ => v.val (y : Circle L)) u w := by
    rcases hv with rfl | rfl; exact hφAC u w; exact hχAC u w
  have hvpoint (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) :
      ContDiffAt ℝ 2 (fun y : ℝ => v.val (y : Circle L)) x ∧
      |deriv (fun y : ℝ => v.val (y : Circle L)) x| ≤
        M * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-b) ∧
      |deriv (deriv (fun y : ℝ => v.val (y : Circle L))) x| ≤
        M * cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - b) := by
    have hr : 0 ≤ cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) :=
      (cappedMarkDistance_pos _ _ hx).le
    rcases hv with rfl | rfl
    · refine ⟨hφs2.contDiffAt, (hφcap x hx).1.trans ?_, (hφcap x hx).2.trans ?_⟩
      all_goals apply mul_le_mul_of_nonneg_right _ (by positivity)
      · dsimp [M]; nlinarith [mul_nonneg hE.le hK, mul_nonneg (mul_nonneg hD.le hK)
          (show 0 ≤ N ^ 2 - N by nlinarith)]
      · dsimp [M]; nlinarith [mul_nonneg hD.le hK]
    · exact hχcap x hx
  have hvsup (x : Circle L) : |v.val x| ≤ 2 * K := by
    rcases hv with rfl | rfl
    · linarith [hφsup x]
    · exact (abs_sub _ _).trans (by linarith [hsup x, hφsup x])
  have hvC (x : Circle L) : |v.val x| ≤ C := (hvsup x).trans hKC
  have hvper : Function.Periodic (fun y : ℝ => v.val (y : Circle L)) L.val := by
    intro y; simp only [AddCircle.coe_add_period]
  refine ⟨hvc, hvC, fun h hh hh1 x => ⟨?_, ?_, ?_⟩⟩
  · exact circleMollify_abs_le hρ L.property hh
      (hvc.comp (AddCircle.continuous_mk' L.val)).locallyIntegrable
      hvper (fun y => hvC _) x
  · exact (hfirst L hL n marks M hM.le v.val hvc hvi hvAC (fun y hy => (hvpoint y hy).2.1) h hh hh1 x).trans
      (mul_le_mul_of_nonneg_right hDC (by positivity))
  · exact (hsecond L hL n marks M hM.le v.val hvc hvi hvAC hvpoint h hh hh1 x).trans
      (mul_le_mul_of_nonneg_right hEC (by positivity))

end Riesz1.Internal
