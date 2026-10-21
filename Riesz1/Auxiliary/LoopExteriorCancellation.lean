/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorRegularity
public import Riesz1.Kernel.TransportScaledLattice
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Deterministic exterior-force cancellation

Kernel estimates used in the exterior part of Lemma 5.8. The estimates
include periodic seams and the antipodal label, using the lattice distance.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- Inside one period, distance to the lattice is bounded below by the distance
to either endpoint of the period. Both signs of the argument are included. -/
theorem loopExterior_latticeDist_lower {L r d : ℝ} (hL : 0 < L)
    (hd : d ≤ |r|) (hLd : d ≤ L - |r|) : d ≤ latticeDist L r := by
  have hk (k : ℤ) : d ≤ |r - L * k| := by
    by_cases hk0 : k = 0
    · simpa only [hk0, Int.cast_zero, mul_zero, sub_zero] using hd
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      exact_mod_cast (show (1 : ℤ) ≤ |k| from Int.one_le_abs hk0)
    have hN : L ≤ |L * (k : ℝ)| := by
      rw [abs_mul, abs_of_pos hL]
      nlinarith
    have htri : |L * (k : ℝ)| ≤ |r - L * k| + |r| := by
      calc |L * (k : ℝ)| = |r - (r - L * k)| := by congr 1; ring
        _ ≤ |r| + |r - L * k| := abs_sub _ _
        _ = _ := add_comm _ _
    linarith
  exact hk (round (r / L))

/-- All derivative orders of the microscopic kernel obey the scale-invariant
lattice-distance bound, with a constant chosen before the period. -/
theorem loopExterior_iteratedDeriv_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (r : ℝ),
      ((r / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0 →
      |iteratedDeriv m (loopArcG s N) r| ≤
        C * latticeDist (N : ℝ) r ^ (-s - (m : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_hurwitzKernel_bound s hs hs1 m
  refine ⟨C, hC, fun N r hr => ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hmem : (N : ℝ)⁻¹ * r ∈ {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
    change (((N : ℝ)⁻¹ * r : ℝ) : UnitAddCircle) ≠ 0
    simpa only [div_eq_mul_inv, mul_comm] using hr
  have hscale := iteratedDeriv_comp_mul_of_contDiffOn gradSplit_isOpen_nonInt
    (N : ℝ)⁻¹ m (hurwitzKernel s) (gradSplit_contDiffOn_kernel s hs hs1) r hmem
  have he : iteratedDeriv m (loopArcG s N) r =
      (N : ℝ) ^ (-s) * (N : ℝ)⁻¹ ^ m *
        iteratedDeriv m (hurwitzKernel s) (r / N) := by
    unfold loopArcG
    rw [iteratedDeriv_const_mul_field]
    have hfun : (fun x : ℝ => hurwitzKernel s (x / N)) =
        (fun x : ℝ => hurwitzKernel s ((N : ℝ)⁻¹ * x)) := by
      funext x
      congr 1
      ring
    rw [hfun, hscale]
    simp only [← div_eq_mul_inv, mul_comm ((N : ℝ)⁻¹) r]
    ring
  have hdist : dist ((r / (N : ℝ) : ℝ) : UnitAddCircle) 0 = latticeDist (N : ℝ) r / N := by
    rw [dist_zero_right, UnitAddCircle.norm_eq]
    unfold latticeDist
    rw [show r - (N : ℝ) * round (r / N) =
      (N : ℝ) * (r / N - round (r / N)) by field_simp, abs_mul, abs_of_pos hN]
    field_simp
  have hbd := hb (r / N) hr
  rw [hdist] at hbd
  have hld : 0 ≤ latticeDist (N : ℝ) r := abs_nonneg _
  have hpow : (N : ℝ) ^ (-s - (m : ℝ)) =
      (N : ℝ) ^ (-s) * (N : ℝ)⁻¹ ^ m := by
    rw [sub_eq_add_neg, Real.rpow_add hN,
      Real.rpow_neg hN.le (m : ℝ), Real.rpow_natCast, inv_pow]
  rw [he, abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hN _),
    abs_of_pos (by positivity : 0 < (N : ℝ)⁻¹ ^ m)]
  calc
    _ ≤ (N : ℝ) ^ (-s) * (N : ℝ)⁻¹ ^ m *
        (C * (latticeDist (N : ℝ) r / N) ^ (-s - (m : ℝ))) := by gcongr
    _ = C * latticeDist (N : ℝ) r ^ (-s - (m : ℝ)) := by
      rw [Real.div_rpow hld hN.le, hpow]
      field_simp

/-- A positive lower bound for lattice distance makes all the scaled derivative
bounds applicable, without a separate nonsingularity assumption. -/
theorem loopExterior_iteratedDeriv_le_of_separated {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (r d : ℝ), 0 < d →
      d ≤ latticeDist (N : ℝ) r →
      |iteratedDeriv m (loopArcG s N) r| ≤ C * d ^ (-s - (m : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := loopExterior_iteratedDeriv_bound hs hs1 m
  refine ⟨C, hC, fun N r d hd hsep => ?_⟩
  have hr : ((r / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := by
    intro hr
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hr
    rw [zsmul_eq_mul, mul_one] at hk
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
    have he : r = (k : ℝ) * (N : ℝ) := by rw [hk, div_mul_cancel₀ _ hN]
    have hz := latticeDist_le_abs_sub (N : ℝ) r (by exact_mod_cast N.pos) k
    rw [he, sub_self, abs_zero] at hz
    rw [he] at hsep
    linarith
  apply (hb N r hr).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_nonpos hd hsep (by have := Nat.cast_nonneg (α := ℝ) m; linarith)

/-- Good-event separation bounds every exterior force summand uniformly over space.
This is the estimate used on the exceptional displacement event. -/
theorem loopExteriorSummand_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ+} {ℓ γ : ℝ},
      1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → GradPartial N ℓ γ →
      ∀ {X : LoopPrecedingConfiguration N}, X ∈ loopExteriorGood N ℓ γ →
      ∀ {j : ℤ}, j ∈ loopExteriorLabels N ℓ γ →
      ∀ {z : ℝ}, z ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4) →
      |deriv (loopArcG s N) (z - loopPrecedingLift X j)| ≤
        C * gradM N ℓ γ ^ (-s - 1) := by
  obtain ⟨C, hC, hb⟩ := loopExterior_iteratedDeriv_le_of_separated hs hs1 1
  refine ⟨C * (1 / 4 : ℝ) ^ (-s - 1), by positivity, ?_⟩
  intro N ℓ γ hK hγ hP X hX j hj z hz
  have hM : 0 < gradM N ℓ γ := lt_of_lt_of_le zero_lt_one (Real.one_le_rpow hK hγ)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hsep : gradM N ℓ γ / 4 ≤ latticeDist (N : ℝ) (z - loopPrecedingLift X j) := by
    apply loopExterior_latticeDist_lower hN
    · rcases loopExteriorLift_barriers hK hγ hP hX hj with hp | hn
      · rw [abs_of_neg (by linarith [hz.2, hp.1])]
        linarith [hz.2, hp.1]
      · rw [abs_of_pos (by linarith [hz.1, hn.2])]
        linarith [hz.1, hn.2]
    · rcases loopExteriorLift_barriers hK hγ hP hX hj with hp | hn
      · rw [abs_of_neg (by linarith [hz.2, hp.1])]
        linarith [hz.1, hp.2]
      · rw [abs_of_pos (by linarith [hz.1, hn.2])]
        linarith [hz.2, hn.1]
  have h := hb N (z - loopPrecedingLift X j) (gradM N ℓ γ / 4) (by positivity) hsep
  simp only [iteratedDeriv_one, Nat.cast_one] at h
  calc
    _ ≤ C * (gradM N ℓ γ / 4) ^ (-s - 1) := h
    _ = _ := by
      rw [show gradM N ℓ γ / 4 = (1 / 4 : ℝ) * gradM N ℓ γ by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hM.le]
      ring

/-- For a reference point at distance at most half a period, the entire segment
to a point displaced by at most half its magnitude remains far from the central
interval and from every periodic singularity. -/
theorem loopExterior_segment_separation {N : ℕ+} {j z t : ℝ}
    (hj : 0 < |j|) (hjN : |j| ≤ (N : ℝ) / 2) (hz : |z| ≤ |j| / 4)
    (ht : |t - j| ≤ |j| / 2) :
    |j| / 4 ≤ latticeDist (N : ℝ) (z - t) ∧
      (((z - t) / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hlo : |j| / 4 ≤ |z - t| := by
    have htri : |j| ≤ |t - j| + |z - t| + |z| := by
      calc |j| = |(j - t) + (t - z) + z| := by congr 1; ring
        _ ≤ |(j - t) + (t - z)| + |z| := abs_add_le _ _
        _ ≤ (|j - t| + |t - z|) + |z| :=
          add_le_add (abs_add_le _ _) le_rfl
        _ = _ := by rw [abs_sub_comm j t, abs_sub_comm t z]
    linarith
  have hhi : |z - t| ≤ 7 * |j| / 4 := by
    have htri : |z - t| ≤ |z| + |t - j| + |j| := by
      calc |z - t| = |z - (t - j) - j| := by congr 1; ring
        _ ≤ |z - (t - j)| + |j| := abs_sub _ _
        _ ≤ (|z| + |t - j|) + |j| := add_le_add (abs_sub _ _) le_rfl
    linarith
  refine ⟨loopExterior_latticeDist_lower hN hlo (by linarith), ?_⟩
  apply gradSplit_coe_ne_zero
  · rw [abs_div, abs_of_pos hN]
    exact div_pos (by linarith) hN
  · rw [abs_div, abs_of_pos hN, div_lt_one hN]
    linarith

/-- The per-label mean-value estimate in the exterior part of Lemma 5.8.
It is uniform over the central interval, and includes the antipodal reference point.
Here `u-j` is the actual displacement. No probabilistic assumption is used. -/
theorem loopExterior_reference_difference_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (j u z : ℝ),
      0 < |j| → |j| ≤ (N : ℝ) / 2 → |z| ≤ |j| / 4 → |u - j| ≤ |j| / 2 →
      |deriv (loopArcG s N) (z - u) - deriv (loopArcG s N) (z - j)| ≤
        C * |j| ^ (-s - 2) * |u - j| := by
  obtain ⟨C, hC, hb⟩ := loopExterior_iteratedDeriv_le_of_separated hs hs1 2
  refine ⟨C * (1 / 4 : ℝ) ^ (-s - 2), by positivity,
    fun N j u z hj hjN hz hu => ?_⟩
  let S := Icc (j - |j| / 2) (j + |j| / 2)
  have ht (t : ℝ) (ht : t ∈ S) : |t - j| ≤ |j| / 2 :=
    abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hderiv (t : ℝ) (htS : t ∈ S) :
      HasDerivWithinAt (fun t => deriv (loopArcG s N) (z - t))
        (-deriv (deriv (loopArcG s N)) (z - t)) S t := by
    have hc := contDiffAt_deriv_loopArcG hs hs1 N
      (loopExterior_segment_separation hj hjN hz (ht t htS)).2
    have hd := hc.differentiableAt (by simp)
    convert! (hd.hasDerivAt.comp t ((hasDerivAt_id t).const_sub z)).hasDerivWithinAt
      using 1
    simp only [mul_neg_one]
  have hbound (t : ℝ) (htS : t ∈ S) :
      ‖-deriv (deriv (loopArcG s N)) (z - t)‖ ≤ C * (|j| / 4) ^ (-s - 2) := by
    have h := hb N (z - t) (|j| / 4) (by positivity)
      (loopExterior_segment_separation hj hjN hz (ht t htS)).1
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat,
      norm_neg, Real.norm_eq_abs] using h
  have hjS : j ∈ S := ⟨by linarith [hj], by linarith [hj]⟩
  have huS : u ∈ S := ⟨by linarith [(abs_le.mp hu).1], by linarith [(abs_le.mp hu).2]⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc _ _) hjS huS
  simp only [Real.norm_eq_abs] at h
  calc
    _ ≤ C * (|j| / 4) ^ (-s - 2) * |u - j| := h
    _ = _ := by
      rw [show |j| / 4 = (1 / 4 : ℝ) * |j| by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) (abs_nonneg j)]
      ring

/-- The reference force and its unit-cell integral differ by the summable cell
error. Integrability is returned explicitly, including for the antipodal cell. -/
theorem loopExterior_reference_cell_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (j z : ℝ),
      1 ≤ |j| → |j| ≤ (N : ℝ) / 2 → |z| ≤ |j| / 4 →
      IntervalIntegrable (fun u => deriv (loopArcG s N) (z - u)) volume
        (j - 1 / 2) (j + 1 / 2) ∧
      |deriv (loopArcG s N) (z - j) -
        ∫ u in (j - 1 / 2)..(j + 1 / 2), deriv (loopArcG s N) (z - u)| ≤
          C * |j| ^ (-s - 2) := by
  obtain ⟨C, hC, hb⟩ := loopExterior_reference_difference_bound hs hs1
  refine ⟨C / 2, by positivity, fun N j z hj hjN hz => ?_⟩
  have hab (u : ℝ) (hu : u ∈ Icc (j - 1 / 2) (j + 1 / 2)) : |u - j| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hc : ContinuousOn (fun u => deriv (loopArcG s N) (z - u))
      (Icc (j - 1 / 2) (j + 1 / 2)) := by
    intro u hu
    have hsep := loopExterior_segment_separation (by linarith : 0 < |j|) hjN hz
      ((hab u hu).trans (by linarith))
    exact ((contDiffAt_deriv_loopArcG hs hs1 N hsep.2).continuousAt.comp
      (f := fun u : ℝ => z - u) (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have hi : IntervalIntegrable (fun u => deriv (loopArcG s N) (z - u)) volume
      (j - 1 / 2) (j + 1 / 2) :=
    hc.intervalIntegrable_of_Icc (by linarith : j - (1 / 2 : ℝ) ≤ j + 1 / 2)
  refine ⟨hi, ?_⟩
  have hbound : ∀ u ∈ uIoc (j - 1 / 2) (j + 1 / 2),
      ‖deriv (loopArcG s N) (z - u) - deriv (loopArcG s N) (z - j)‖ ≤
        C * |j| ^ (-s - 2) / 2 := by
    intro u hu
    have hu' : u ∈ Icc (j - 1 / 2) (j + 1 / 2) := by
      rw [uIoc_of_le (by linarith)] at hu
      exact ⟨hu.1.le, hu.2⟩
    rw [Real.norm_eq_abs]
    apply (hb N j u z (by linarith) hjN hz ((hab u hu').trans (by linarith))).trans
    have := mul_le_mul_of_nonneg_left (hab u hu')
      (show 0 ≤ C * |j| ^ (-s - 2) by positivity)
    linarith
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_const] at hn
  have hlen : j + 1 / 2 - (j - 1 / 2) = (1 : ℝ) := by ring
  simp only [hlen, one_smul, Real.norm_eq_abs, abs_one, mul_one] at hn
  rw [abs_sub_comm]
  convert hn using 1
  ring

end Riesz1

end
