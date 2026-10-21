/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.NearestForcing
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Order.Basic

/-!
# Exponential bounds for the nearest-neighbour convexification

Lemma 5.2, first two claims, in the form that follows from a single-gap
tail bound. Write `P` for the Gibbs law of `N` particles, `Q` for `nearestLaw`, and `F` for
`nearestForcing`.

* `rpow_mul_exp_neg_le` removes the polynomial prefactor `K^γ` from the exponential: for `b > 0`,
  `K^γ exp (-b K^ε) ≤ exp ((γ/ε)^2 / b)`. The proof bounds `log t ≤ 2 √t` for `t = K^ε`.
* `nearestForcing_pos_le_exp` gives `P(F > 0) ≤ C exp (-c K^ε)` with explicit `C` and `c`.
* `totalVariation_nearestLaw_le_exp` gives `TV(P, Q) ≤ C exp (-c K^ε)`, and
  `ae_rnDeriv_nearestLaw_le_two` gives `dQ/dP ≤ 2` almost everywhere once `C exp (-c K^ε) ≤ 1/2`.
* `a_priori_convexity_of_gapTail` assembles these, with `K₀` independent of `N`.

The single-gap tail bound is an explicit hypothesis `hTail` of the internal results. It is obtained
from the block-length moments of Lemma 4.2 (see `NearestForcingMoments`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The quadratic `2 g r - b r^2` is at most `g^2 / b`, with equality at `r = g / b`. -/
theorem two_mul_sub_mul_sq_le (g r b : ℝ) (hb : 0 < b) :
    2 * g * r - b * r ^ 2 ≤ g ^ 2 / b := by
  rw [le_div_iff₀ hb]
  nlinarith [sq_nonneg (g - b * r)]

/-- The polynomial prefactor is absorbed by the exponential: for `K > 0`, `b > 0`,
`K^γ exp (-b K^ε) ≤ exp ((γ/ε)^2 / b)`. With `t = K^ε` and `r = √t`, one has
`γ log K = (γ/ε) log t ≤ (2γ/ε) r`, and then `-b r^2 + (2γ/ε) r ≤ (γ/ε)^2 / b`. -/
theorem rpow_mul_exp_neg_le {K γ ε b : ℝ} (hK : 0 < K) (hγ : 0 ≤ γ) (hε : 0 < ε) (hb : 0 < b) :
    K ^ γ * Real.exp (-b * K ^ ε) ≤ Real.exp ((γ / ε) ^ 2 / b) := by
  set t := K ^ ε with ht_def
  set r := Real.sqrt t with hr_def
  have ht : 0 < t := Real.rpow_pos_of_pos hK ε
  have hr : 0 < r := Real.sqrt_pos.2 ht
  have hrt : t = r ^ 2 := (Real.sq_sqrt ht.le).symm
  have hlogt : Real.log t = ε * Real.log K := Real.log_rpow hK ε
  have hlogt2 : Real.log t = 2 * Real.log r := by
    rw [hrt, Real.log_pow]
    push_cast
    ring
  have hlogr : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr
  have hg0 : 0 ≤ γ / ε := div_nonneg hγ hε.le
  have hγlog : γ * Real.log K = (γ / ε) * Real.log t := by
    rw [hlogt]
    field_simp
  have hlin : γ * Real.log K ≤ 2 * (γ / ε) * r := by
    rw [hγlog, hlogt2]
    have h1 := mul_le_mul_of_nonneg_left hlogr hg0
    nlinarith
  have hexp : γ * Real.log K - b * t ≤ (γ / ε) ^ 2 / b := by
    have h := two_mul_sub_mul_sq_le (γ / ε) r b hb
    rw [hrt]
    linarith
  have hsplit : K ^ γ * Real.exp (-b * t) = Real.exp (γ * Real.log K - b * t) := by
    rw [Real.rpow_def_of_pos hK, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  exact Real.exp_le_exp.2 hexp

/-- The constants of the nearest-neighbour bound: `C = 8 A exp ((γ/ε)^2 / (a/2))` and `c = a/2`.
They depend only on the tail constants `A` and `a`, and on `γ` and `ε`. -/
noncomputable def nearestBoundC (A a γ ε : ℝ) : ℝ :=
  8 * A * Real.exp ((γ / ε) ^ 2 / (a / 2))

/-- The rate of the nearest-neighbour bound: `c = a/2`. -/
noncomputable def nearestBoundc (a : ℝ) : ℝ := a / 2

section Bounds

variable {P : Parameters} {N : ℕ+} {θ : ℝ → ℝ} {K γ ε : ℝ}

/-- The probability of the forcing event decays exponentially in `K^ε`, under the single-gap tail
bound `hTail`. -/
theorem nearestForcing_pos_le_exp (hθ : IsForcingCutoff θ) {A a : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ)
    (hε : 0 < ε) (ha : 0 < a) (hA : 0 ≤ A)
    (hTail : ∀ (j : ℤ) (u : ℝ), (gibbsMeasure P N).real {X | u < gap X j} ≤
      A * Real.exp (-a * u)) :
    (gibbsMeasure P N).real {X | 0 < nearestForcing θ N K γ ε X} ≤
      nearestBoundC A a γ ε * Real.exp (-nearestBoundc a * K ^ ε) := by
  have hK0 : 0 < K := by linarith
  have h2 := measureReal_nearestForcing_pos_le (P := P) (N := N) (γ := γ) (ε := ε) hθ hK0 hTail
  have h3 := card_nearestPairs_window_le (N := N) (γ := γ) hK hγ
  have hb : 0 < a / 2 := half_pos ha
  have e1 := rpow_mul_exp_neg_le (γ := γ) (ε := ε) hK0 hγ hε hb
  have e2 : Real.exp (-a * K ^ ε) =
      Real.exp (-(a / 2) * K ^ ε) * Real.exp (-(a / 2) * K ^ ε) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexp : K ^ γ * Real.exp (-a * K ^ ε) ≤
      Real.exp ((γ / ε) ^ 2 / (a / 2)) * Real.exp (-(a / 2) * K ^ ε) := by
    calc K ^ γ * Real.exp (-a * K ^ ε)
        = (K ^ γ * Real.exp (-(a / 2) * K ^ ε)) * Real.exp (-(a / 2) * K ^ ε) := by
          rw [e2]
          ring
      _ ≤ Real.exp ((γ / ε) ^ 2 / (a / 2)) * Real.exp (-(a / 2) * K ^ ε) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
  have hnn : 0 ≤ A * Real.exp (-a * K ^ ε) := mul_nonneg hA (Real.exp_pos _).le
  unfold nearestBoundC nearestBoundc
  calc (gibbsMeasure P N).real {X | 0 < nearestForcing θ N K γ ε X}
      ≤ ((nearestPairs N (window N K γ)).card : ℝ) * (A * Real.exp (-a * K ^ ε)) :=
        measureReal_nearestForcing_pos_le hθ hK0 hTail
    _ ≤ 8 * K ^ γ * (A * Real.exp (-a * K ^ ε)) :=
        mul_le_mul_of_nonneg_right h3 hnn
    _ = 8 * A * (K ^ γ * Real.exp (-a * K ^ ε)) := by ring
    _ ≤ 8 * A * (Real.exp ((γ / ε) ^ 2 / (a / 2)) * Real.exp (-(a / 2) * K ^ ε)) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ = 8 * A * Real.exp ((γ / ε) ^ 2 / (a / 2)) * Real.exp (-(a / 2) * K ^ ε) := by ring

/-- The total variation between the Gibbs law and the nearest-neighbour law decays
exponentially in `K^ε`, under the single-gap tail bound `hTail`. -/
theorem totalVariation_nearestLaw_le_exp (hθ : IsForcingCutoff θ) {A a : ℝ} (hK : 1 ≤ K)
    (hγ : 0 ≤ γ) (hε : 0 < ε) (ha : 0 < a) (hA : 0 ≤ A)
    (hTail : ∀ (j : ℤ) (u : ℝ), (gibbsMeasure P N).real {X | u < gap X j} ≤
      A * Real.exp (-a * u)) :
    totalVariation (gibbsMeasure P N) (nearestLaw P θ N K γ ε) ≤
      nearestBoundC A a γ ε * Real.exp (-nearestBoundc a * K ^ ε) := by
  have hK0 : 0 < K := by linarith
  unfold nearestLaw
  exact (totalVariation_forcedLaw_le (P := P)
      (measurable_nearestForcing (N := N) (K := K) (γ := γ) (ε := ε) hθ)
      (nearestForcing_nonneg (N := N) (γ := γ) (ε := ε) hθ hK0)).trans
    (nearestForcing_pos_le_exp hθ hK hγ hε ha hA hTail)

/-- The density of the nearest-neighbour law is at most two almost everywhere, once the forcing
event has probability at most one half. -/
theorem ae_rnDeriv_nearestLaw_le_two (hθ : IsForcingCutoff θ) {A a : ℝ} (hK : 1 ≤ K)
    (hγ : 0 ≤ γ) (hε : 0 < ε) (ha : 0 < a) (hA : 0 ≤ A)
    (hTail : ∀ (j : ℤ) (u : ℝ), (gibbsMeasure P N).real {X | u < gap X j} ≤
      A * Real.exp (-a * u))
    (hsmall : nearestBoundC A a γ ε * Real.exp (-nearestBoundc a * K ^ ε) ≤ 1 / 2) :
    ∀ᵐ X ∂(gibbsMeasure P N), (nearestLaw P θ N K γ ε).rnDeriv (gibbsMeasure P N) X ≤ 2 := by
  have hK0 : 0 < K := by linarith
  have hpos := (nearestForcing_pos_le_exp (P := P) (N := N) (γ := γ) hθ hK hγ hε ha hA hTail).trans
    hsmall
  unfold nearestLaw
  exact ae_rnDeriv_forcedLaw_le_two (P := P) (measurable_nearestForcing (N := N) (K := K)
      (γ := γ) (ε := ε) hθ) (nearestForcing_nonneg (N := N) (γ := γ) (ε := ε) hθ hK0)
    (half_le_forcedNormalizer (P := P) (measurable_nearestForcing (N := N) (K := K) (γ := γ)
      (ε := ε) hθ) (nearestForcing_nonneg (N := N) (γ := γ) (ε := ε) hθ hK0) hpos)

end Bounds

/-- A constant times `exp (-c K^ε)` is eventually below one half, as `K → ∞`, for `c, ε > 0`. -/
theorem eventually_mul_exp_lt_half (C c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → C * Real.exp (-c * K ^ ε) < 1 / 2 := by
  have hT : Tendsto (fun K : ℝ => c * K ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).const_mul_atTop hc
  have hE : Tendsto (fun K : ℝ => Real.exp (-(c * K ^ ε))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hT
  have hE' : Tendsto (fun K : ℝ => Real.exp (-c * K ^ ε)) atTop (𝓝 0) :=
    hE.congr fun K => by rw [neg_mul]
  have hC : Tendsto (fun K : ℝ => C * Real.exp (-c * K ^ ε)) atTop (𝓝 (C * 0)) :=
    hE'.const_mul C
  rw [mul_zero] at hC
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 ((tendsto_order.1 hC).2 (1 / 2) (by norm_num))
  exact ⟨K₀, fun K hK => hK₀ K hK⟩

/-- Lemma 5.2, first two claims, from a single-gap tail bound valid for
every `N ≥ 2`. The total variation bound `TV(P, Q) ≤ C exp (-c K^ε)` holds for every `K ≥ 1` with
constants `c, C > 0` independent of `N` and `K`. There is `K₀`, independent of `N`, such that
`dQ/dP ≤ 2` almost everywhere for every `K ≥ K₀`. -/
theorem a_priori_convexity_of_gapTail {P : Parameters} {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    {γ ε A a : ℝ} (hγ : 0 ≤ γ) (hε : 0 < ε) (ha : 0 < a) (hA : 0 < A)
    (hTail : ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (j : ℤ) (u : ℝ),
      (gibbsMeasure P N).real {X | u < gap X j} ≤ A * Real.exp (-a * u)) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ K : ℝ, 1 ≤ K →
      totalVariation (gibbsMeasure P N) (nearestLaw P θ N K γ ε) ≤
        C * Real.exp (-c * K ^ ε)) ∧
    (∃ K₀ : ℝ, ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ K : ℝ, K₀ ≤ K → 1 ≤ K →
      ∀ᵐ X ∂(gibbsMeasure P N),
        (nearestLaw P θ N K γ ε).rnDeriv (gibbsMeasure P N) X ≤ 2) := by
  have hc : 0 < nearestBoundc a := half_pos ha
  have hC : 0 < nearestBoundC A a γ ε := by
    unfold nearestBoundC
    exact mul_pos (mul_pos (by norm_num) hA) (Real.exp_pos _)
  obtain ⟨K₀, hK₀⟩ := eventually_mul_exp_lt_half (nearestBoundC A a γ ε) (nearestBoundc a) ε hc hε
  refine ⟨⟨nearestBoundc a, nearestBoundC A a γ ε, hc, hC, fun N hN K hK => ?_⟩,
    ⟨K₀, fun N hN K hK₀K hK => ?_⟩⟩
  · exact totalVariation_nearestLaw_le_exp (P := P) (N := N) hθ hK hγ hε ha hA.le
      (hTail N hN)
  · exact ae_rnDeriv_nearestLaw_le_two (P := P) (N := N) hθ hK hγ hε ha hA.le (hTail N hN)
      (hK₀ K hK₀K).le

end Riesz1

end
