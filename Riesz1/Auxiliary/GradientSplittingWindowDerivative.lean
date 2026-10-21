/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowPVExist

/-!
# The derivative of the background integral is the principal-value difference

For a lift `x`, the background integral `J(x)` of the localized loop satisfies
`J(x) = BT(x) - Φ(x)` (partial window) or `J(x) = -Φ(x)` (full window), with
`Φ(x) = ∫_{-1/2}^{1/2} ψ'((x+v)/ℓ) g(v) dv`. The principal values of `V` in the `v`-frame have the
difference `J'(x)`: this file proves that identity (`gradV_identity_partial`, `gradV_identity_full`).
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- `E(v) = ψ'((x+v)/ℓ)` is the derivative of `D`, and its derivative is `ψ''((x+v)/ℓ)/ℓ`. -/
lemma deriv_deriv_psi_comp_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (_hℓ : ℓ ≠ 0) (x v : ℝ) :
    deriv (fun v : ℝ => deriv ψ ((x + v) / ℓ)) v = deriv (deriv ψ) ((x + v) / ℓ) * (1 / ℓ) := by
  have hlin : HasDerivAt (fun v : ℝ => (x + v) / ℓ) (1 / ℓ) v := by
    simpa using ((hasDerivAt_id v).const_add x).div_const ℓ
  have hdd : HasDerivAt (deriv ψ) (deriv (deriv ψ) ((x + v) / ℓ)) ((x + v) / ℓ) :=
    ((contDiff_infty_iff_deriv.1 hψ).2.differentiable (by simp)) _ |>.hasDerivAt
  exact (hdd.comp v hlin).deriv

/-- The endpoint hypotheses of the partial window, from the lift being at distance `≥ t` from `ℤ`. -/
lemma partial_endpoint_hyps {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ t : ℝ} (hℓ : ℓ ≠ 0)
    (ht : 0 < t) (ht2 : t ≤ 1 / 2) (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (x : ℝ) :
    ((∃ m : ℤ, -t - x = m) → ∀ᶠ v in 𝓝 (-t - x), gradD ψ ℓ x v = 0) ∧
    ((∃ m : ℤ, t - x = m) → ∀ᶠ v in 𝓝 (t - x), gradD ψ ℓ x v = 0) ∧
    ((∃ m : ℤ, -t - x = m) → deriv ψ (x / ℓ) = 0) ∧
    ((∃ m : ℤ, t - x = m) → deriv ψ (x / ℓ) = 0) := by
  have hfa : (∃ m : ℤ, -t - x = m) → ∀ m : ℤ, t ≤ |x - m| := by
    rintro ⟨n, hn⟩
    exact far_of_endpoint ht ht2 (Or.inl ⟨n, by linarith⟩)
  have hfb : (∃ m : ℤ, t - x = m) → ∀ m : ℤ, t ≤ |x - m| := by
    rintro ⟨n, hn⟩
    exact far_of_endpoint ht ht2 (Or.inr ⟨n, by linarith⟩)
  have hq : (∃ m : ℤ, -t - x = m) ∨ (∃ m : ℤ, t - x = m) → deriv ψ (x / ℓ) = 0 := by
    intro h
    have hfar : ∀ m : ℤ, t ≤ |x - m| := by
      rcases h with h | h
      · exact hfa h
      · exact hfb h
    exact deriv_psi_zero_of_eventually hℓ (eventually_psi_zero_near ht hsupp hfar)
      ((hψ.differentiable (by simp)) _)
  refine ⟨?_, ?_, fun h => hq (Or.inl h), fun h => hq (Or.inr h)⟩
  · intro h
    refine gradD_eventually_zero hℓ ht hsupp (hfa h) ?_
    intro m
    rw [show x + (-t - x) - m = -(t + m) by ring, abs_neg]
    exact le_abs_add_int ht ht2 m
  · intro h
    refine gradD_eventually_zero hℓ ht hsupp (hfb h) ?_
    intro m
    rw [show x + (t - x) - m = t + ((-m : ℤ) : ℝ) by push_cast; ring]
    exact le_abs_add_int ht ht2 (-m)

/-- The derivative of `Φ`, with the period trick: `Φ'(x) = (1/ℓ) ∫_{-1/2}^{1/2} ψ''((x+v)/ℓ) g(v) dv`. -/
lemma deriv_gradPhi_eq {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    deriv (fun y => gradPhi s ψ ℓ y) x
      = (1 / ℓ) * ∫ v in (-1 / 2 : ℝ)..(1 / 2), deriv (deriv ψ) ((x + v) / ℓ) * hurwitzKernel s v := by
  have hψ1 : ContDiff ℝ 1 (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2.of_le (by simp)
  have h := deriv_gradPhiFam hψ1 hℓ hs0 hs1 x
  simp only [gradPhi, gradPhiFam] at h ⊢
  rw [h]

/-- The partial-window identity: the principal values of `V` have difference `J'(x)`
(`J = BT - Φ`, with `BT'` the product-form derivative `gradBTpartDeriv`). -/
theorem gradV_identity_partial {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {t : ℝ}
    (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) (x : ℝ) :
    ∃ LA LB : ℝ,
      Tendsto (fun δ : ℝ => ∫ v in (-t - x)..(t - x),
        (gradAllowed δ).indicator (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v) (𝓝[>] 0)
        (𝓝 LA) ∧
      Tendsto (fun δ : ℝ => ∫ v in (-t - x)..(t - x),
        (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v)
        (𝓝[>] 0) (𝓝 LB) ∧
      LA - LB = gradBTpartDeriv s ψ ℓ t x - deriv (fun y => gradPhi s ψ ℓ y) x := by
  have hab : -t - x < t - x := by linarith
  obtain ⟨ha, hb, hqa, hqb⟩ := partial_endpoint_hyps hψ hℓ.ne' ht ht2 hsupp x
  obtain ⟨LA, LB, hA, hB, hid⟩ :=
    gradV_pv_limits hψ hℓ hp hs0 hs1 x hab ha hb hqa hqb
  refine ⟨LA, LB, hA, hB, ?_⟩
  rw [hid]
  -- the boundary values of `D` and `D'`
  have hpt := psi_zero_at_pm_t ht ht2 hsupp
  have hDb : gradD ψ ℓ x (t - x) = -ℓ * ψ (x / ℓ) := by
    unfold gradD
    rw [show x + (t - x) = t by ring, hpt.1]
    ring
  have hDa : gradD ψ ℓ x (-t - x) = -ℓ * ψ (x / ℓ) := by
    unfold gradD
    rw [show x + (-t - x) = -t by ring, hpt.2]
    ring
  have hEb : deriv (gradD ψ ℓ x) (t - x) = 0 := by
    rw [deriv_gradD_eq hψ hℓ.ne' x (t - x), show x + (t - x) = t by ring]
    exact deriv_psi_zero_of_mem_Icc hψ hℓ.ne' ht hsupp (z := t) ⟨le_rfl, by linarith⟩
  have hEa : deriv (gradD ψ ℓ x) (-t - x) = 0 := by
    rw [deriv_gradD_eq hψ hℓ.ne' x (-t - x), show x + (-t - x) = -t by ring]
    have hfar : ∀ m : ℤ, t ≤ |-t - m| := by
      intro m
      rw [show -t - (m : ℝ) = -(t + m) by ring, abs_neg]
      exact le_abs_add_int ht ht2 m
    exact deriv_psi_zero_of_eventually hℓ.ne'
      ((eventually_psi_zero_near ht hsupp hfar)) ((hψ.differentiable (by simp)) _)
  -- the integral of `E'` against `g` is `Φ'`
  have hψdd : ContDiff ℝ ∞ (deriv (deriv ψ)) :=
    (contDiff_infty_iff_deriv.1 ((contDiff_infty_iff_deriv.1 hψ).2)).2
  have hint : ∫ v in (-t - x)..(t - x), deriv (deriv (gradD ψ ℓ x)) v * hurwitzKernel s v
      = deriv (fun y => gradPhi s ψ ℓ y) x := by
    have hE : deriv (gradD ψ ℓ x) = fun v => deriv ψ ((x + v) / ℓ) := funext fun v =>
      deriv_gradD_eq hψ hℓ.ne' x v
    have hsim : ∀ v : ℝ, deriv (deriv (gradD ψ ℓ x)) v * hurwitzKernel s v
        = (1 / ℓ) * (deriv (deriv ψ) ((x + v) / ℓ) * hurwitzKernel s v) := by
      intro v
      rw [hE, deriv_deriv_psi_comp_eq hψ hℓ.ne' x v]
      ring
    rw [intervalIntegral.integral_congr (fun v _ => hsim v), intervalIntegral.integral_const_mul]
    rw [integral_coeff_mul_eq_period hℓ (deriv_periodic_of (deriv_periodic_of hp))
      hψdd.continuous hs0 hs1 ht ht2
      (fun z hz => deriv_deriv_psi_zero_of_mem_Icc hℓ.ne' ht hsupp hz) x]
    rw [deriv_gradPhi_eq hψ hℓ.ne' hs0 hs1 x]
  rw [hDb, hDa, hEb, hEa, hint]
  unfold gradBTpartDeriv
  ring

/-- The full-window identity: the principal values of `V` have difference `-Φ'(x) = J'(x)`. -/
theorem gradV_identity_full {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    ∃ LA LB : ℝ,
      Tendsto (fun δ : ℝ => ∫ v in (-1 / 2 : ℝ)..(1 / 2),
        (gradAllowed δ).indicator (fun v => gradZx ψ ℓ x (x + v) * gradKernelH s v) v) (𝓝[>] 0)
        (𝓝 LA) ∧
      Tendsto (fun δ : ℝ => ∫ v in (-1 / 2 : ℝ)..(1 / 2),
        (gradAllowed δ).indicator (fun v => gradZ ψ ℓ x (x + v) * deriv (gradKernelH s) v) v)
        (𝓝[>] 0) (𝓝 LB) ∧
      LA - LB = - deriv (fun y => gradPhi s ψ ℓ y) x := by
  have hab : (-1 / 2 : ℝ) < 1 / 2 := by norm_num
  have hnint : ∀ c : ℝ, (c = -1 / 2 ∨ c = 1 / 2) → ¬ ∃ m : ℤ, c = m := by
    rintro c hc ⟨m, hm⟩
    rcases hc with hc | hc <;> rw [hc] at hm
    · have h2 : ((2 * m : ℤ) : ℝ) = -1 := by push_cast; linarith
      have h3 : (2 * m : ℤ) = -1 := by exact_mod_cast h2
      omega
    · have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
      have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
      omega
  have ha : (∃ m : ℤ, (-1 / 2 : ℝ) = m) → ∀ᶠ v in 𝓝 (-1 / 2 : ℝ), gradD ψ ℓ x v = 0 :=
    fun h => absurd h (hnint _ (Or.inl rfl))
  have hb : (∃ m : ℤ, (1 / 2 : ℝ) = m) → ∀ᶠ v in 𝓝 (1 / 2 : ℝ), gradD ψ ℓ x v = 0 :=
    fun h => absurd h (hnint _ (Or.inr rfl))
  have hqa : (∃ m : ℤ, (-1 / 2 : ℝ) = m) → deriv ψ (x / ℓ) = 0 :=
    fun h => absurd h (hnint _ (Or.inl rfl))
  have hqb : (∃ m : ℤ, (1 / 2 : ℝ) = m) → deriv ψ (x / ℓ) = 0 :=
    fun h => absurd h (hnint _ (Or.inr rfl))
  obtain ⟨LA, LB, hA, hB, hid⟩ := gradV_pv_limits hψ hℓ hp hs0 hs1 x hab ha hb hqa hqb
  refine ⟨LA, LB, hA, hB, ?_⟩
  rw [hid]
  -- evenness and periodicity at `±1/2`
  have hGhalf : deriv (hurwitzKernel s) (1 / 2) = 0 := by
    have h1 : deriv (hurwitzKernel s) ((-1 / 2 : ℝ) + 1) = deriv (hurwitzKernel s) (-1 / 2) :=
      deriv_hurwitzKernel_add_one' s (-1 / 2)
    rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, show (-1 / 2 : ℝ) = -(1 / 2) by ring,
      deriv_hurwitzKernel_neg'] at h1
    linarith
  have hGm : deriv (hurwitzKernel s) (-1 / 2) = 0 := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, deriv_hurwitzKernel_neg', hGhalf, neg_zero]
  have hg : hurwitzKernel s (-1 / 2) = hurwitzKernel s (1 / 2) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, hurwitzKernel_neg']
  have hD : gradD ψ ℓ x (1 / 2) = gradD ψ ℓ x (-1 / 2) := by
    have h := gradD_periodic hp x (-1 / 2)
    rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
    exact h
  have hE : deriv (gradD ψ ℓ x) (1 / 2) = deriv (gradD ψ ℓ x) (-1 / 2) := by
    rw [deriv_gradD_eq hψ hℓ.ne' x, deriv_gradD_eq hψ hℓ.ne' x]
    have h := deriv_periodic_of hp ((x + (-1 / 2)) / ℓ)
    rw [show (x + (-1 / 2)) / ℓ + 1 / ℓ = (x + 1 / 2) / ℓ by ring] at h
    exact h
  -- the integral of `E'` against `g` is `Φ'`
  have hψdd : ContDiff ℝ ∞ (deriv (deriv ψ)) :=
    (contDiff_infty_iff_deriv.1 ((contDiff_infty_iff_deriv.1 hψ).2)).2
  have hint : ∫ v in (-1 / 2 : ℝ)..(1 / 2), deriv (deriv (gradD ψ ℓ x)) v * hurwitzKernel s v
      = deriv (fun y => gradPhi s ψ ℓ y) x := by
    have hsim : ∀ v : ℝ, deriv (deriv (gradD ψ ℓ x)) v * hurwitzKernel s v
        = (1 / ℓ) * (deriv (deriv ψ) ((x + v) / ℓ) * hurwitzKernel s v) := by
      intro v
      have hE' : deriv (gradD ψ ℓ x) = fun v => deriv ψ ((x + v) / ℓ) := funext fun v =>
        deriv_gradD_eq hψ hℓ.ne' x v
      rw [hE', deriv_deriv_psi_comp_eq hψ hℓ.ne' x v]
      ring
    rw [intervalIntegral.integral_congr (fun v _ => hsim v), intervalIntegral.integral_const_mul]
    rw [deriv_gradPhi_eq hψ hℓ.ne' hs0 hs1 x]
  rw [hg, hGhalf, hGm, hD, hE, hint]
  ring

end

end Riesz1
