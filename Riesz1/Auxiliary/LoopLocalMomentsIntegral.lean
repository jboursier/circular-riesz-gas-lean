/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsRegularity
public import Riesz1.Auxiliary.LoopSizeBiasMoments
public import Riesz1.Auxiliary.LoopLocalMomentsTransport
public import Riesz1.ToMathlib.Moments.RpowLpBound
import all Mathlib.Data.PNat.Defs
import all Init.Data.Nat.Basic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Basic.NNReal.Defs

/-!
# Uniform particle-background estimates

The arbitrary-position background estimate in the proof of the local moments part of
Lemma 5.8. The position need not belong to the background arc.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace Riesz1

/-- The first derivative bound, with its constant uniform in the period `N`. -/
theorem loopLocal_deriv_kernel_bound_three_quarters {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (r : ℝ), 0 < r → r ≤ 3 * (N : ℝ) / 4 →
      |deriv (loopArcG s N) r| ≤ C * r ^ (-s - 1) := by
  obtain ⟨C, hC, hb⟩ := gradSplit_kernel_deriv_bound s hs hs1
  refine ⟨C, hC, fun N r hr hrR => ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hx0 : 0 < r / N := div_pos hr hN
  have hx1 : r / N ≤ 3 / 4 := by
    rw [div_le_iff₀ hN]
    linarith
  have hbd := hb (r / N) (by rw [abs_of_pos hx0]; exact hx0)
    (by rw [abs_of_pos hx0]; exact hx1) 1 le_rfl (by norm_num)
  rw [iteratedDeriv_one, abs_of_pos hx0, Nat.cast_one] at hbd
  rw [deriv_loopArcG_eq s hs hs1 N hr (by linarith), abs_mul, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hN _), abs_of_pos (inv_pos.mpr hN)]
  have hpow : (r / N) ^ (-s - 1) = r ^ (-s - 1) * (N : ℝ) ^ (s + 1) := by
    rw [show (-s - 1 : ℝ) = -(s + 1) by ring, Real.div_rpow hr.le hN.le,
      Real.rpow_neg hN.le, div_inv_eq_mul]
  have hmul : (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1)) = 1 := by
    have he : (N : ℝ) ^ (-s) * (N : ℝ) ^ (s + 1) = N := by
      rw [← Real.rpow_add hN]
      norm_num
    calc (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1))
        = ((N : ℝ) ^ (-s) * (N : ℝ) ^ (s + 1)) * (N : ℝ)⁻¹ := by ring
      _ = 1 := by rw [he, mul_inv_cancel₀ hN.ne']
  calc (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * |deriv (hurwitzKernel s) (r / N)|)
      ≤ (N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (C * (r / N) ^ (-s - 1))) := by gcongr
    _ = C * ((N : ℝ) ^ (-s) * ((N : ℝ)⁻¹ * (N : ℝ) ^ (s + 1))) * r ^ (-s - 1) := by
      rw [hpow]
      ring
    _ = C * r ^ (-s - 1) := by rw [hmul, mul_one]

/-- On three quarters of a period the microscopic pair kernel is bounded by `C Lip(b) |z-u|⁻ˢ`.
The diagonal is included: the pair kernel vanishes there. -/
theorem loopLocal_pair_kernel_bound_three_quarters {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) {b : ℝ → ℝ} {L : NNReal}, LipschitzWith L b →
      ∀ z u : ℝ, |z - u| ≤ 3 * (N : ℝ) / 4 →
        |loopArcKernel s N b z u| ≤ C * L * |z - u| ^ (-s) := by
  obtain ⟨C, hC, hb⟩ := loopLocal_deriv_kernel_bound_three_quarters hs hs1
  refine ⟨C, hC, fun N b L hL z u hzu => ?_⟩
  by_cases he : z = u
  · subst u
    rw [loopArcKernel_self, abs_zero]
    positivity
  have hr : 0 < |z - u| := abs_pos.mpr (sub_ne_zero.mpr he)
  have hd : |deriv (loopArcG s N) (z - u)| ≤ C * |z - u| ^ (-s - 1) := by
    rcases le_or_gt 0 (z - u) with hpos | hneg
    · simpa only [abs_of_nonneg hpos] using hb N |z - u| hr hzu
    · have ho := deriv_loopArcG_neg s N (-(z - u))
      rw [neg_neg] at ho
      rw [ho, abs_neg]
      simpa only [abs_of_neg hneg] using hb N |z - u| hr hzu
  have hdiff := hL.norm_sub_le z u
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hdiff
  have hpow : |z - u| * |z - u| ^ (-s - 1) = |z - u| ^ (-s) := by
    rw [Real.rpow_sub_one hr.ne', mul_div_cancel₀ _ hr.ne']
  unfold loopArcKernel
  rw [abs_mul]
  calc |b z - b u| * |deriv (loopArcG s N) (z - u)|
      ≤ ((L : ℝ) * |z - u|) * (C * |z - u| ^ (-s - 1)) :=
        mul_le_mul hdiff hd (abs_nonneg _) (by positivity)
    _ = C * L * |z - u| ^ (-s) := by rw [mul_mul_mul_comm, hpow, mul_comm (L : ℝ) C]

namespace Internal

/-- Absolute powers are integrable on every finite interval, even when the center
lies outside that interval. -/
private theorem power_integrable {s : ℝ} (hs1 : s < 1) (z a c : ℝ) (hac : a ≤ c) :
    IntervalIntegrable (fun u : ℝ => |u - z| ^ (-s)) volume a c := by
  apply intervalIntegrable_abs_sub_rpow_radius hs1
    (R := |z| + |a| + |c| + 1) (by positivity) hac
  · linarith [le_abs_self z, neg_abs_le a, abs_nonneg c]
  · linarith [neg_abs_le z, le_abs_self c, abs_nonneg a]

/-- Moving the center to its closest point of the interval can only increase the
integral of a negative power. -/
private theorem power_integral_le_length {s a c : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hac : a ≤ c) (z : ℝ) :
    (∫ u in a..c, |u - z| ^ (-s)) ≤ 2 * (c - a) ^ (1 - s) / (1 - s) := by
  let q := max a (min c z)
  have hq : q ∈ Icc a c := ⟨le_max_left _ _, max_le hac (min_le_left _ _)⟩
  have hd : ∀ u ∈ Icc a c, |u - q| ≤ |u - z| := by
    intro u hu
    dsimp [q]
    rcases le_or_gt z a with hza | haz
    · rw [min_eq_right (hza.trans hac), max_eq_left hza,
        abs_of_nonneg (sub_nonneg.mpr hu.1), abs_of_nonneg (by linarith [hu.1])]
      linarith
    · rcases le_or_gt c z with hcz | hzc
      · rw [min_eq_left hcz, max_eq_right hac,
          abs_of_nonpos (sub_nonpos.mpr hu.2), abs_of_nonpos (by linarith [hu.2])]
        linarith
      · rw [min_eq_right hzc.le, max_eq_right haz.le]
  have hmono : (∫ u in a..c, |u - z| ^ (-s)) ≤ ∫ u in a..c, |u - q| ^ (-s) := by
    apply intervalIntegral.integral_mono_ae_restrict hac
      (power_integrable hs1 z a c hac) (power_integrable hs1 q a c hac)
    have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ q := by
      rw [ae_iff]
      simp
    filter_upwards [hne.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Icc] with u hu huI
    exact Real.rpow_le_rpow_of_nonpos (abs_pos.mpr (sub_ne_zero.mpr hu)) (hd u huI) (by linarith)
  exact hmono.trans (integral_abs_sub_rpow_le_radius hs1 (sub_nonneg.mpr hac) hac
    (by linarith [hq.2]) (by linarith [hq.1]))

end Internal

/-- Periodicity in the particle position, complementary to the periodicity in
the integrated variable. -/
theorem loopLocalKernel_periodic_left {b : ℝ → ℝ} {N : ℕ+}
    (hp : Function.Periodic b (N : ℝ)) (s u : ℝ) :
    Function.Periodic (fun z => loopArcKernel s N b z u) (N : ℝ) := by
  intro z
  unfold loopArcKernel
  dsimp only
  rw [hp z, show z + N - u = (z - u) + N by ring, deriv_loopArcG_periodic]

/-- The particle/background integral has the required uniform bound for every real
particle position, including positions outside the chosen background interval. -/
theorem loopLocalKernel_integral_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) {b : ℝ → ℝ} {L : NNReal},
      2 ≤ (N : ℕ) → 0 ≤ ℓ → 1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → ContDiff ℝ 1 b →
      Function.Periodic b (N : ℝ) → LipschitzWith L b → ∀ z : ℝ,
      |∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ, loopArcKernel s N b z u| ≤
        C * L * gradM N ℓ γ := by
  obtain ⟨A, hA, hk⟩ := loopLocal_pair_kernel_bound_three_quarters hs hs1
  refine ⟨16 * A / (1 - s), by positivity, ?_⟩
  intro N ℓ γ b L hN _hℓ hK hγ _hb hp hL z
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hden : 0 < 1 - s := by linarith
  by_cases hP : GradPartial N ℓ γ
  · simp only [loopLocalLo, loopLocalHi, hP, ↓reduceIte]
    let q := toIcoMod hNpos (-(N : ℝ) / 2) z
    have hq : -(N : ℝ) / 2 ≤ q ∧ q ≤ (N : ℝ) / 2 := by
      have h := toIcoMod_mem_Ico hNpos (-(N : ℝ) / 2) z
      exact ⟨h.1, by linarith [h.2]⟩
    have he : ∀ u, loopArcKernel s N b q u = loopArcKernel s N b z u := by
      intro u
      exact (loopLocalKernel_periodic_left hp s u).sub_zsmul_eq
        (toIcoDiv hNpos (-(N : ℝ) / 2) z)
    simp_rw [← he]
    have hsmall : ∀ u ∈ Icc (-gradM N ℓ γ) (gradM N ℓ γ),
        |q - u| ≤ 3 * (N : ℝ) / 4 := by
      intro u hu
      have hPr : gradM N ℓ γ < (N : ℝ) / 8 := hP
      rw [abs_le]
      constructor <;> linarith [hq.1, hq.2, hu.1, hu.2]
    have hi := (Internal.power_integrable hs1 q (-gradM N ℓ γ) (gradM N ℓ γ)
      (by linarith)).const_mul (A * L)
    have hbd : |∫ u in -gradM N ℓ γ..gradM N ℓ γ, loopArcKernel s N b q u| ≤
        A * L * (2 * (2 * gradM N ℓ γ) ^ (1 - s) / (1 - s)) := by
      calc
        _ ≤ ∫ u in -gradM N ℓ γ..gradM N ℓ γ, A * L * |u - q| ^ (-s) := by
          rw [← Real.norm_eq_abs]
          apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ hi
          exact Filter.Eventually.of_forall fun u hu => by
            rw [Real.norm_eq_abs, abs_sub_comm u q]
            exact hk N hL q u (hsmall u ⟨hu.1.le, hu.2⟩)
        _ = A * L * ∫ u in -gradM N ℓ γ..gradM N ℓ γ, |u - q| ^ (-s) :=
          intervalIntegral.integral_const_mul _ _
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [sub_neg_eq_add, ← two_mul] using
            Internal.power_integral_le_length hs hs1 (by linarith : -gradM N ℓ γ ≤ gradM N ℓ γ) q
    apply hbd.trans
    have hpw : (2 * gradM N ℓ γ) ^ (1 - s) ≤ 2 * gradM N ℓ γ :=
      Real.rpow_le_self_of_one_le (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_left
      (show 2 * (2 * gradM N ℓ γ) ^ (1 - s) ≤ 16 * gradM N ℓ γ by linarith)
      (mul_nonneg hA.le L.property)
    calc
      _ = (A * L * (2 * (2 * gradM N ℓ γ) ^ (1 - s))) / (1 - s) := by ring
      _ ≤ (A * L * (16 * gradM N ℓ γ)) / (1 - s) := div_le_div_of_nonneg_right hm hden.le
      _ = _ := by ring
  · simp only [loopLocalLo, loopLocalHi, hP, ↓reduceIte]
    have he := (loopLocalKernel_periodic_right hp s z).intervalIntegral_add_eq
      (z - (N : ℝ) / 2) 0
    have he' : (∫ u in (0 : ℝ)..(N : ℝ), loopArcKernel s N b z u) =
        ∫ u in (z - (N : ℝ) / 2)..(z + (N : ℝ) / 2), loopArcKernel s N b z u := by
      simpa only [zero_add, show z - (N : ℝ) / 2 + N = z + (N : ℝ) / 2 by ring] using he.symm
    rw [he']
    have hi := Internal.loopLocal_integral_radius hs1 hA.le N
      (fun z u hu => hk N hL z u (by linarith))
      (z := z) (a := z - (N : ℝ) / 2) (c := z + (N : ℝ) / 2) (R := (N : ℝ) / 2)
      (by positivity) (by linarith) le_rfl le_rfl
      (fun u hu => by rw [abs_le]; constructor <;> linarith [hu.1, hu.2])
    apply hi.trans
    have hpw : ((N : ℝ) / 2) ^ (1 - s) ≤ (N : ℝ) / 2 :=
      Real.rpow_le_self_of_one_le (by linarith) (by linarith)
    have hNM : (N : ℝ) ≤ 8 * gradM N ℓ γ := by
      have := not_lt.mp hP
      linarith
    have hm := mul_le_mul_of_nonneg_left
      (show 2 * ((N : ℝ) / 2) ^ (1 - s) ≤ 16 * gradM N ℓ γ by linarith)
      (mul_nonneg hA.le L.property)
    calc
      _ = (A * L * (2 * ((N : ℝ) / 2) ^ (1 - s))) / (1 - s) := by ring
      _ ≤ (A * L * (16 * gradM N ℓ γ)) / (1 - s) := div_le_div_of_nonneg_right hm hden.le
      _ = _ := by ring

/-- The anchored cyclic lift agrees with the preceding offsets at every integer label,
including labels outside the chosen period. -/
theorem loopPreceding_anchoredCyclicOffset (n : ℕ)
    (X : LoopPrecedingConfiguration (n + 1).succPNat) (j : ℤ) :
    anchoredCyclicOffset (n + 1) (loopPrecedingOffsets X) j =
      cyclicLift X.val (loopPrecedingLabel X + j) - cyclicLift X.val (loopPrecedingLabel X) := by
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := (n + 1).succPNat) j
  erw [anchoredCyclicOffset_add_mul,
    anchoredCyclicOffset_natCast (n + 1) (loopPrecedingOffsets X) ⟨i, hi⟩,
    ← loopPrecedingY_eq_anchorVector]
  change (cyclicLift X.val (loopPrecedingLabel X + (i : ℤ)) -
    cyclicLift X.val (loopPrecedingLabel X)) + q = _
  rw [show loopPrecedingLabel X + ((i : ℤ) + ((n + 1).succPNat : ℕ) * q) =
    (loopPrecedingLabel X + i) + ((n + 1).succPNat : ℕ) * q by ring,
    boundary_cyclicLift_add_mul]
  ring

/-- Directed microscopic blocks in the preceding coordinates. -/
theorem loopPrecedingLift_sub_eq_block (n : ℕ)
    (X : LoopPrecedingConfiguration (n + 1).succPNat) (i : ℤ) (k : ℕ) :
    loopPrecedingLift X (i + k) - loopPrecedingLift X i =
      loopAnchoredBlock n i k (loopPrecedingOffsets X) := by
  unfold loopAnchoredBlock
  rw [loopPreceding_anchoredCyclicOffset, loopPreceding_anchoredCyclicOffset]
  simp only [loopPrecedingLift, Nat.succPNat_coe, Nat.cast_succ]
  ring

/-- Uniform inverse-block norms on the actual preceding-particle carrier.
Only the Prékopa–Leindler inequality `External.PrekopaLeindler` is needed. There is no rigidity hypothesis. -/
theorem loopPreceding_inverse_block_eLpNorm (P : Parameters) {s p : ℝ}
    (hs : 0 < s) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (n : ℕ) (i : ℤ)
      (k : ℕ), 0 < k →
      eLpNorm (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
        (loopPrecedingLift X (i + k) - loopPrecedingLift X i) ^ (-s))
        (ENNReal.ofReal p) (loopPrecedingMeasure P _) ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB, hb⟩ := loopSizeBiased_inverse_blocks P (p := s * p) (mul_pos hs hp)
  refine ⟨B ^ (1 / p), Real.rpow_pos_of_pos hB _, ?_⟩
  intro hPL n i k hk
  let μ := loopPrecedingMeasure P (n + 1).succPNat
  let S := fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
    loopPrecedingLift X (i + k) - loopPrecedingLift X i
  have hm : Measurable S := (measurable_loopPrecedingLift _ _).sub
    (measurable_loopPrecedingLift _ _)
  have hpos : ∀ X, 0 < S X := by
    intro X
    exact sub_pos.mpr ((loopPrecedingLift_strictMono X) (by exact_mod_cast Int.lt_add_of_pos_right i (by exact_mod_cast hk)))
  apply eLpNorm_le_of_lintegral_rpow_le μ (hm.pow_const (-s))
    (fun X => Real.rpow_nonneg (hpos X).le _) hp (by positivity)
  have he : (∫⁻ X, ENNReal.ofReal ((S X ^ (-s)) ^ p) ∂μ) =
      ∫⁻ y, ENNReal.ofReal (loopAnchoredBlock n i k y ^ (-(s * p)))
        ∂loopSizeBiasedLaw P n := by
    erw [← map_loopPrecedingOffsets P n,
      lintegral_map ((measurable_loopAnchoredBlock n i k).pow_const _).ennreal_ofReal
        (measurable_loopPrecedingOffsets _)]
    apply lintegral_congr
    intro X
    rw [← loopPrecedingLift_sub_eq_block, ← Real.rpow_mul (hpos X).le]
    congr 2
    ring
  rw [he, one_div, Real.rpow_inv_rpow hB.le hp.ne']
  apply (hb hPL n i k hk).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_of_le_one_right hB.le
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by nlinarith)

/-- The pair kernel can be controlled by the two complementary directed lengths.
This includes pairs near the periodic seam. -/
theorem loopLocalKernel_directed_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) {b : ℝ → ℝ} {L : NNReal},
      Function.Periodic b (N : ℝ) → LipschitzWith L b → ∀ z u : ℝ,
      0 < u - z → u - z < N →
      |loopArcKernel s N b z u| ≤ C * L * ((u - z) ^ (-s) + ((N : ℝ) - (u - z)) ^ (-s)) := by
  obtain ⟨A, hA, hk⟩ := loopLocal_pair_kernel_bound hs hs1
  refine ⟨A, hA, fun N b L hp hL z u hzu hzuN => ?_⟩
  have hAL : 0 ≤ A * L := by positivity
  by_cases hhalf : u - z ≤ (N : ℝ) / 2
  · have h := hk N hL z u (by rw [abs_of_neg (by linarith)]; linarith)
    rw [abs_of_neg (show z - u < 0 by linarith)] at h
    have he : -(z - u) = u - z := by ring
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hAL)
  · have he := (loopLocalKernel_periodic_right hp s z).sub_eq u
    rw [← he]
    have h := hk N hL z (u - N) (by
      rw [abs_of_pos (by linarith)]
      linarith)
    have he' : |z - (u - N)| = (N : ℝ) - (u - z) := by rw [abs_of_pos (by linarith)]; ring
    rw [he'] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hAL)

/-- Symmetry of the microscopic pair integrand. -/
theorem loopLocalKernel_swap (s : ℝ) (N : ℕ+) (b : ℝ → ℝ) (z u : ℝ) :
    loopArcKernel s N b u z = loopArcKernel s N b z u := by
  unfold loopArcKernel
  rw [show u - z = -(z - u) by ring, deriv_loopArcG_neg]
  ring

/-- Distinct labels in a local window have index separation strictly smaller than
one period, also in the full-window regime. -/
theorem loopLocalLabels_span {N : ℕ+} {ℓ γ : ℝ} {i j : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) :
    |j - i| < (N : ℤ) := by
  by_cases hP : GradPartial N ℓ γ
  · have hi' := (mem_gradLabels_partial hP i).mp hi
    have hj' := (mem_gradLabels_partial hP j).mp hj
    have hfl := Int.floor_le (gradM N ℓ γ)
    have hPr : gradM N ℓ γ < (N : ℝ) / 8 := hP
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hlim : 2 * ⌊gradM N ℓ γ⌋ < (N : ℤ) := by
      have : (2 : ℝ) * (⌊gradM N ℓ γ⌋ : ℤ) < N := by linarith
      exact_mod_cast this
    rw [abs_lt]
    constructor <;> omega
  · simp only [gradLabels, hP, ↓reduceIte, Finset.mem_Ico] at hi hj
    rw [abs_lt]
    constructor <;> omega

namespace Internal

private theorem increasing_pair_norm {P : Parameters} {s p A B : ℝ}
    (hA : 0 ≤ A) (hp : 1 ≤ p)
    (hk : ∀ (N : ℕ+) {b : ℝ → ℝ} {L : NNReal},
      Function.Periodic b (N : ℝ) → LipschitzWith L b → ∀ z u : ℝ,
      0 < u - z → u - z < N →
      |loopArcKernel s N b z u| ≤ A * L * ((u - z) ^ (-s) + ((N : ℝ) - (u - z)) ^ (-s)))
    (hB : 0 ≤ B)
    (hb : ∀ (n : ℕ) (i : ℤ) (k : ℕ), 0 < k →
      eLpNorm (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
        (loopPrecedingLift X (i + k) - loopPrecedingLift X i) ^ (-s))
        (ENNReal.ofReal p) (loopPrecedingMeasure P _) ≤ ENNReal.ofReal B)
    (n : ℕ) {b : ℝ → ℝ} {L : NNReal} (hbc : Continuous b)
    (hbp : Function.Periodic b ((n + 1).succPNat : ℝ)) (hL : LipschitzWith L b)
    {i j : ℤ} (hij : i < j) (hspan : j - i < ((n + 1).succPNat : ℤ)) :
    eLpNorm (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
      loopArcKernel s (n + 1).succPNat b (loopPrecedingLift X i) (loopPrecedingLift X j))
      (ENNReal.ofReal p) (loopPrecedingMeasure P _) ≤ ENNReal.ofReal (2 * A * L * B) := by
  let N := (n + 1).succPNat
  let μ := loopPrecedingMeasure P N
  let S := fun X : LoopPrecedingConfiguration N => loopPrecedingLift X j - loopPrecedingLift X i
  let T := fun X : LoopPrecedingConfiguration N =>
    loopPrecedingLift X (i + N) - loopPrecedingLift X j
  have heT : ∀ X, T X = (N : ℝ) - S X := by
    intro X
    dsimp [T, S]
    rw [loopPrecedingLift_add_N]
    ring
  have hS : ∀ X, 0 < S X := fun X => sub_pos.mpr ((loopPrecedingLift_strictMono X) hij)
  have hT : ∀ X, 0 < T X := fun X => sub_pos.mpr
    ((loopPrecedingLift_strictMono X) (by change j < i + ((n + 1).succPNat : ℤ); omega))
  have hSnorm : eLpNorm (fun X => S X ^ (-s)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B := by
    have h := hb n i (j - i).toNat (by omega)
    have he : i + ((j - i).toNat : ℤ) = j := by omega
    simpa only [he] using h
  have hTnorm : eLpNorm (fun X => T X ^ (-s)) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B := by
    have h := hb n j (i + ((n + 1).succPNat : ℤ) - j).toNat (by omega)
    have he : j + ((i + (N : ℤ) - j).toNat : ℤ) = i + N := by
      change j + ((i + ((n + 1).succPNat : ℤ) - j).toNat : ℤ) = i + ((n + 1).succPNat : ℤ)
      omega
    simpa only [N, T, μ, he] using h
  have hm : Measurable (fun X : LoopPrecedingConfiguration N =>
      loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j)) :=
    (measurable_loopLocalKernel hbc s N).comp
      ((measurable_loopPrecedingLift N i).prodMk (measurable_loopPrecedingLift N j))
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  calc
    _ ≤ eLpNorm (fun X => (A * (L : ℝ)) * (S X ^ (-s) + T X ^ (-s)))
        (ENNReal.ofReal p) μ := by
      apply eLpNorm_mono_real hm.aestronglyMeasurable
      intro X
      rw [Real.norm_eq_abs, heT]
      exact hk N hbp hL _ _ (hS X) (by linarith [hT X, heT X])
    _ = ENNReal.ofReal (A * L) * eLpNorm (fun X => S X ^ (-s) + T X ^ (-s))
        (ENNReal.ofReal p) μ := by
      rw [show (fun X => A * (L : ℝ) * (S X ^ (-s) + T X ^ (-s))) =
        (A * (L : ℝ)) • (fun X => S X ^ (-s) + T X ^ (-s)) by rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
    _ ≤ ENNReal.ofReal (A * L) * (ENNReal.ofReal B + ENNReal.ofReal B) := by
      gcongr
      exact (eLpNorm_add_le hpE).trans (add_le_add hSnorm hTnorm)
    _ = _ := by rw [← ENNReal.ofReal_add hB hB, ← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end Internal

/-- Each atomic pair has a uniform moment bound on the preceding carrier, using
both directed blocks when the two positions straddle a periodic seam. -/
theorem loopLocal_pair_eLpNorm (P : Parameters) {s p : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (n : ℕ)
      (ℓ γ : ℝ) {b : ℝ → ℝ} {L : NNReal}, Continuous b →
      Function.Periodic b ((n + 1).succPNat : ℝ) → LipschitzWith L b →
      ∀ i ∈ gradLabels (n + 1).succPNat ℓ γ, ∀ j ∈ gradLabels (n + 1).succPNat ℓ γ, i ≠ j →
      eLpNorm (fun X : LoopPrecedingConfiguration (n + 1).succPNat =>
        loopArcKernel s (n + 1).succPNat b (loopPrecedingLift X i) (loopPrecedingLift X j))
        (ENNReal.ofReal p) (loopPrecedingMeasure P _) ≤ ENNReal.ofReal (C * L) := by
  obtain ⟨A, hA, hk⟩ := loopLocalKernel_directed_bound hs hs1
  obtain ⟨B, hB, hb⟩ := loopPreceding_inverse_block_eLpNorm P hs (by linarith : 0 < p)
  refine ⟨2 * A * B, by positivity, ?_⟩
  intro hPL n ℓ γ b L hbc hbp hL i hi j hj hij
  have hspan := loopLocalLabels_span hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := Internal.increasing_pair_norm hA.le hp hk hB.le (hb hPL) n hbc hbp hL hlt
      (lt_of_le_of_lt (le_abs_self (j - i)) hspan)
    convert h using 1; congr 1; ring
  · have h := Internal.increasing_pair_norm hA.le hp hk hB.le (hb hPL) n hbc hbp hL hgt
      (lt_of_le_of_lt (le_abs_self (i - j)) (loopLocalLabels_span hj hi))
    simp_rw [loopLocalKernel_swap s (n + 1).succPNat b] at h
    convert h using 1; congr 1; ring

/-- The full random localized loop, for an arbitrary smooth periodic microscopic
transport, with its Lipschitz constant explicit. Both window regimes are included. -/
theorem loopLocalLoop_eLpNorm (P : Parameters) {s p : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (n : ℕ)
      (ℓ γ : ℝ) {b : ℝ → ℝ} {L : NNReal}, 0 ≤ ℓ →
      1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ γ → ContDiff ℝ 1 b →
      Function.Periodic b ((n + 1).succPNat : ℝ) → LipschitzWith L b →
      eLpNorm (loopLocalLoop s (n + 1).succPNat ℓ γ b) (ENNReal.ofReal p)
        (loopPrecedingMeasure P _) ≤ ENNReal.ofReal (C * L * gradM (n + 1).succPNat ℓ γ ^ 2) := by
  obtain ⟨A, hA, ha⟩ := loopLocal_pair_eLpNorm P hs hs1 hp
  obtain ⟨D, hD, hd⟩ := loopLocalKernel_integral_bound hs hs1
  refine ⟨64 * A + 16 * D, by positivity, ?_⟩
  intro hPL n ℓ γ b L hℓ hK hγ hb hbp hL
  let N := (n + 1).succPNat
  let μ := loopPrecedingMeasure P N
  let I := gradLabels N ℓ γ
  let M := gradM N ℓ γ
  have hM : 1 ≤ M := Real.one_le_rpow hK hγ
  have hc : (I.card : ℝ) ≤ 8 * M := card_gradLabels_le hK hγ
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  let F := fun X : LoopPrecedingConfiguration N => ∑ i ∈ I, ∑ j ∈ I.erase i,
    loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j)
  have hin : ∀ i ∈ I,
      eLpNorm (fun X : LoopPrecedingConfiguration N => ∑ j ∈ I.erase i,
        loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j))
        (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((I.card : ℝ) * A * L) := by
    intro i hi
    calc
      _ ≤ ∑ j ∈ I.erase i, eLpNorm (fun X : LoopPrecedingConfiguration N =>
          loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j))
          (ENNReal.ofReal p) μ := by
        simpa only [Finset.sum_fn] using (eLpNorm_sum_le (μ := μ) (s := I.erase i)
          (f := fun j X => loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j)) hpE)
      _ ≤ ∑ j ∈ I.erase i, ENNReal.ofReal (A * L) := by
        apply Finset.sum_le_sum
        intro j hj
        exact ha hPL n ℓ γ hb.continuous hbp hL i hi j (Finset.mem_erase.mp hj).2
          (Finset.mem_erase.mp hj).1.symm
      _ ≤ ∑ j ∈ I, ENNReal.ofReal (A * L) := Finset.sum_le_sum_of_subset (Finset.erase_subset i I)
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hF : eLpNorm F (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (64 * A * L * M ^ 2) := by
    calc
      _ ≤ ∑ i ∈ I, eLpNorm (fun X : LoopPrecedingConfiguration N => ∑ j ∈ I.erase i,
          loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j))
          (ENNReal.ofReal p) μ := by
        simpa only [Finset.sum_fn, F] using (eLpNorm_sum_le (μ := μ) (s := I)
          (f := fun i X => ∑ j ∈ I.erase i,
            loopArcKernel s N b (loopPrecedingLift X i) (loopPrecedingLift X j)) hpE)
      _ ≤ ∑ i ∈ I, ENNReal.ofReal ((I.card : ℝ) * A * L) := Finset.sum_le_sum hin
      _ = ENNReal.ofReal ((I.card : ℝ) ^ 2 * A * L) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hsq : (I.card : ℝ) ^ 2 ≤ (8 * M) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hc 2
        have hmul := mul_le_mul_of_nonneg_right hsq (show 0 ≤ A * (L : ℝ) by positivity)
        nlinarith [hmul]
  let G := fun X : LoopPrecedingConfiguration N => 2 * ∑ i ∈ I,
    ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ, loopArcKernel s N b (loopPrecedingLift X i) u
  have hGm : Measurable G := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact (measurable_loopLocalKernel_integral hb.continuous s N
      (loopLocalLo_le_hi N hℓ)).comp (measurable_loopPrecedingLift N i)
  have hGpoint : ∀ X, ‖G X‖ ≤ 16 * D * L * M ^ 2 := by
    intro X
    rw [Real.norm_eq_abs]
    dsimp only [G]
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc
      _ ≤ 2 * ∑ i ∈ I, |∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
          loopArcKernel s N b (loopPrecedingLift X i) u| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ 2 * ∑ _i ∈ I, D * L * M := by
        gcongr with i hi
        exact hd N ℓ γ (by simp [N]) hℓ hK hγ hb hbp hL _
      _ = 2 * (I.card : ℝ) * (D * L * M) := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 16 * D * L * M ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2 * D * L * M by positivity)
        nlinarith [hmul]
  have hG : eLpNorm G (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (16 * D * L * M ^ 2) := by
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
      (eLpNorm_le_of_ae_bound (μ := μ) hGm.aestronglyMeasurable (Filter.Eventually.of_forall hGpoint))
  calc
    _ ≤ eLpNorm F (ENNReal.ofReal p) μ + eLpNorm G (ENNReal.ofReal p) μ :=
      eLpNorm_sub_le hpE
    _ ≤ ENNReal.ofReal (64 * A * L * M ^ 2) + ENNReal.ofReal (16 * D * L * M ^ 2) := add_le_add hF hG
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- The local moments part of Lemma 5.8, every assertion. The finite
extended norm and the deterministic background appear in the same bound. The
constant is uniform even in `γ > 1`, and the unnecessary upper bound `ℓ ≤ 1` is dropped. -/
theorem auxiliary_Loop_local_moments (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    {α p : ℝ} (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hp : 1 ≤ p)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+)
      (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → 1 ≤ (N : ℝ) * ℓ → 1 < γ → 0 ≤ C0 → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
      let b := loopLocalTransport χ N ℓ γ ψ
      MemLp (loopLocalLoop s N ℓ γ b) (ENNReal.ofReal p) (loopPrecedingMeasure P N) ∧
      IntervalIntegrable (fun z => ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
        loopArcKernel s N b z u) volume (loopLocalLo N ℓ γ) (loopLocalHi N ℓ γ) ∧
      eLpNorm (loopLocalLoop s N ℓ γ b) (ENNReal.ofReal p) (loopPrecedingMeasure P N) +
        ENNReal.ofReal |loopLocalBackground s N ℓ γ b| ≤
          ENNReal.ofReal (C * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ)) := by
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  obtain ⟨A, hA, ha⟩ := loopLocalLoop_eLpNorm P hs hs1 hp
  obtain ⟨D, hD, hd⟩ := loopLocalBackground_bound hs hs1
  obtain ⟨B, hB, hb⟩ := loopLocalTransport_deriv_bound hs hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  refine ⟨(A + D) * (B + 1), by positivity, ?_⟩
  intro hPL N ℓ γ ψ C0 hN hℓ hK hγ hC0 hψ hpψ hdψ hddψ
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n + 1).succPNat := by
    refine ⟨(N : ℕ) - 2, ?_⟩
    apply Subtype.ext
    change (N : ℕ) = ((N : ℕ) - 2 + 1) + 1
    omega
  let N := (n + 1).succPNat
  let b := loopLocalTransport χ N ℓ γ ψ
  let L := Real.toNNReal (B * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α))
  have hLreal : (L : ℝ) = B * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) :=
    Real.coe_toNNReal _ (by positivity)
  have hLip : LipschitzWith L b := (hb N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hpψ hdψ hddψ).2
  have hb0 : ContDiff ℝ 1 b := (contDiff_loopLocalTransport hχ hψ hχs N hℓ γ).of_le (by simp)
  have hp0 : Function.Periodic b (N : ℝ) := loopLocalTransport_periodic hℓ χ hpψ
  have hn := ha hPL n ℓ γ hℓ.le hK (by linarith) hb0 hp0 hLip
  obtain ⟨hi, hbg⟩ := hd N ℓ γ hN hℓ.le hK (by linarith) hb0 hp0 hLip
  have hKpos : 0 < (N : ℝ) * ℓ := by linarith
  have hpow : ((N : ℝ) * ℓ) ^ (1 - s + α) * gradM N ℓ γ ^ 2 =
      ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ) := by
    unfold gradM
    rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le, ← Real.rpow_add hKpos]
    congr 1
    ring
  have hsum : eLpNorm (loopLocalLoop s N ℓ γ b) (ENNReal.ofReal p) (loopPrecedingMeasure P N) +
      ENNReal.ofReal |loopLocalBackground s N ℓ γ b| ≤
        ENNReal.ofReal ((A + D) * (B + 1) * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ)) := by
    calc
      _ ≤ ENNReal.ofReal (A * L * gradM N ℓ γ ^ 2) +
          ENNReal.ofReal (D * L * gradM N ℓ γ ^ 2) := add_le_add hn (ENNReal.ofReal_le_ofReal hbg)
      _ = ENNReal.ofReal ((A + D) * B * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [hLreal]
        calc
          _ = (A + D) * B * C0 * (((N : ℝ) * ℓ) ^ (1 - s + α) * gradM N ℓ γ ^ 2) := by ring
          _ = _ := by rw [hpow]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr; linarith)
  exact ⟨(le_trans le_self_add hsum).trans_lt ENNReal.ofReal_lt_top, hi, hsum⟩

end Riesz1

end
