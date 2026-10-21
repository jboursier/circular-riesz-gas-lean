/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingGapMain

/-!
# Packing sums for the translation bound

The two particle sums used when summing (A2) in the estimates part of Lemma 5.7. The cell count
and lattice weight sum
are results of the convolution part of Lemma 5.7.
-/

@[expose] public section

namespace Riesz1

noncomputable section

/-- Transfer a nonnegative lattice bound to particles by microscopic packing. -/
lemma gradEst_particle_sum_le {s γ ε ℓ B D : ℝ} {N : ℕ+}
    {X : Fin (N : ℕ) → ℝ} (F : ℝ → ℝ)
    (hs : 0 < s) (hγ : 1 < γ) (hε : 0 < ε)
    (hεs : ε < (1 - s / 2) / 8) (hK : 1 ≤ (N : ℝ) * ℓ)
    (hN : 2 ≤ (N : ℕ)) (hX : gradEvent s γ ε N ℓ X)
    (hB : 0 ≤ B) (hF : ∀ z, 0 ≤ F z)
    (hper : ∀ z (m : ℤ), F (z + (m : ℝ) * (N : ℝ)) = F z)
    (hcell : ∀ z v, |z - v| ≤ 1 → F z ≤ B * F v)
    (hlattice : ∑ r ∈ Finset.range (N : ℕ), F r ≤ D) :
    ∑ j ∈ gradLabels N ℓ γ, F ((N : ℝ) * gradLift N X j)
      ≤ B * (2 + ((N : ℝ) * ℓ) ^ ε) * D := by
  classical
  have hpoint (r : ℕ) (j : ℤ)
      (hj : j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N 0 (gradLift N X j) = r)) :
      F ((N : ℝ) * gradLift N X j) ≤ B * F r := by
    obtain ⟨m, hm⟩ := gradCell_floor_eq N 0 (gradLift N X j)
    rw [(Finset.mem_filter.mp hj).2] at hm
    have hmr : (⌊(N : ℝ) * gradLift N X j⌋ : ℝ) = (r : ℝ) + (m : ℝ) * (N : ℝ) := by
      exact_mod_cast (by simpa [mul_comm] using hm)
    have hd : |(N : ℝ) * gradLift N X j - (⌊(N : ℝ) * gradLift N X j⌋ : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [Int.floor_le ((N : ℝ) * gradLift N X j),
        Int.lt_floor_add_one ((N : ℝ) * gradLift N X j)]
    have h := hcell _ _ hd
    rw [hmr, hper] at h
    exact h
  calc ∑ j ∈ gradLabels N ℓ γ, F ((N : ℝ) * gradLift N X j)
      = ∑ r ∈ Finset.range (N : ℕ),
          ∑ j ∈ (gradLabels N ℓ γ).filter (fun j => gradCell N 0 (gradLift N X j) = r),
            F ((N : ℝ) * gradLift N X j) := sum_cell_fiber X 0 _
    _ ≤ ∑ r ∈ Finset.range (N : ℕ), B * (2 + ((N : ℝ) * ℓ) ^ ε) * F r := by
      apply Finset.sum_le_sum
      intro r _
      have hc := card_filter_cell_le hs hγ hε hεs hK hN hX 0 r
      calc _ ≤ ∑ j ∈ (gradLabels N ℓ γ).filter
              (fun j => gradCell N 0 (gradLift N X j) = r), B * F r :=
            Finset.sum_le_sum (fun j hj => hpoint r j hj)
        _ = (((gradLabels N ℓ γ).filter
              (fun j => gradCell N 0 (gradLift N X j) = r)).card : ℝ) * (B * F r) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 + ((N : ℝ) * ℓ) ^ ε) * (B * F r) :=
            mul_le_mul_of_nonneg_right hc (mul_nonneg hB (hF _))
        _ = _ := by ring
    _ = B * (2 + ((N : ℝ) * ℓ) ^ ε) * ∑ r ∈ Finset.range (N : ℕ), F r := by
        rw [Finset.mul_sum]
    _ ≤ B * (2 + ((N : ℝ) * ℓ) ^ ε) * D :=
        mul_le_mul_of_nonneg_left hlattice (by positivity)

/-- The spatial decay kernel has a lattice sum independent of the circumference. -/
lemma gradEst_decay_lattice {s : ℝ} (hs : 0 < s) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ+, ∑ r ∈ Finset.range (N : ℕ),
      (1 + circDist (N : ℝ) r) ^ (-(1 + s / 2)) ≤ D := by
  let f : ℕ → ℝ := fun m => (1 + (m : ℝ)) ^ (-(1 + s / 2))
  have hf : Summable f := summable_one_add_rpow_neg (by linarith)
  have hf0 (m : ℕ) : 0 ≤ f m := by dsimp [f]; positivity
  have hT : 0 ≤ ∑' m, f m := tsum_nonneg hf0
  refine ⟨2 * (∑' m, f m) + 1, by linarith, fun N => ?_⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hb := sum_shell_le (N : ℕ) N.pos 0
    (fun z => (1 + circDist (N : ℝ) z) ^ (-(1 + s / 2)))
    (fun z => (1 + z) ^ (-(1 + s / 2))) (fun _ => rfl)
    (fun _ hz _ => Real.rpow_nonneg (by linarith) _)
    (fun x y hx hxy _ => Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
      (by linarith))
  simp only [zero_add] at hb
  have ht := hf.sum_le_tsum (Finset.range (⌊(N : ℝ) / 2⌋₊ + 1)) (fun m _ => hf0 m)
  dsimp [f] at ht
  dsimp [f] at hT ⊢
  linarith

/-- Packing controls the sum of the two weights appearing in (A2). Constants
are chosen before the particle count, scale and configuration. -/
theorem gradEst_sum_envelope {s a γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ha0 : 0 ≤ a) (_ha : a < 1 - s / 2) (hγ : 1 < γ) :
    ∀ ε : ℝ, 0 < ε → ε < (1 - s / 2) / 8 →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      gradEvent s γ ε N ℓ X →
      ∑ i ∈ gradLabels N ℓ γ,
        (ℓ⁻¹ * gradWeightTwo s a ((N : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
          (N : ℝ) * ((N : ℝ) * ℓ) ^ a /
            (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2))
      ≤ C * (N : ℝ) * ((N : ℝ) * ℓ) ^ (a + 2 * ε) := by
  intro ε hε hεs
  obtain ⟨D, hD, hdec⟩ := gradEst_decay_lattice hs0
  let B : ℝ := 2 ^ (4 + a)
  let E : ℝ := 2 ^ (1 + s / 2)
  let C : ℝ := 24 * B * (1 + 1 / ε) + 3 * E * D
  have hB : 0 < B := by dsimp [B]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hlogC : 0 < 1 + 1 / ε := by positivity
  refine ⟨C, by dsimp [C]; positivity, fun N ℓ X hN hℓ hℓ1 hK hX => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hcount : 2 + ((N : ℝ) * ℓ) ^ ε ≤ 3 * ((N : ℝ) * ℓ) ^ ε := by
    linarith [Real.one_le_rpow hK hε.le]
  have hweights := gradEst_particle_sum_le (gradW2 s a N ℓ) hs0 hγ hε hεs hK hN hX hB.le
    (gradW2_nonneg s a N ℓ) (gradW2_add_mul s a N hℓ)
    (fun z v hz => gradW2_cell_le s a hs0 hs1 ha0 N hK
      (circDist_le_add_one_of_abs_sub_le hN0 (by rwa [abs_sub_comm])))
    (by simpa only [gradW2, zero_add] using sum_gradWeightTwo_le hs1 ha0 (N : ℕ) hN hK 0)
  have hspatial := gradEst_particle_sum_le
    (fun z => (1 + circDist (N : ℝ) z) ^ (-(1 + s / 2))) hs0 hγ hε hεs hK hN hX hE.le
    (fun z => Real.rpow_nonneg (by linarith [circDist_nonneg (N : ℝ) z]) _)
    (fun z m => by rw [circDist_add_int_mul hN0])
    (fun z v hz => rpow_one_add_neg_le_two_pow (by linarith)
      (circDist_nonneg _ _) (circDist_nonneg _ _)
      ((abs_circDist_sub_circDist_le hN0).trans ((circDist_le_abs_self hN0 _).trans hz)))
    (hdec N)
  have hw : ∑ i ∈ gradLabels N ℓ γ, gradW2 s a N ℓ ((N : ℝ) * gradLift N X i)
      ≤ 24 * B * (1 + 1 / ε) * ((N : ℝ) * ℓ) ^ (1 + a + 2 * ε) := by
    calc _ ≤ B * (2 + ((N : ℝ) * ℓ) ^ ε) *
          (8 * ((N : ℝ) * ℓ) ^ (1 + a) * (1 + Real.log ((N : ℝ) * ℓ))) := by
            simpa only [zero_add] using hweights
      _ ≤ B * (3 * ((N : ℝ) * ℓ) ^ ε) *
          (8 * ((N : ℝ) * ℓ) ^ (1 + a) * ((1 + 1 / ε) * ((N : ℝ) * ℓ) ^ ε)) := by
            have hl := Real.log_nonneg hK
            gcongr
            exact gapLog_le_rpow hK hε
      _ = _ := by
        have hp : ((N : ℝ) * ℓ) ^ (1 + a + 2 * ε) =
            ((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * ℓ) ^ (1 + a) * ((N : ℝ) * ℓ) ^ ε := by
          rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
          congr 1
          ring
        rw [hp]
        ring
  have hd : ∑ i ∈ gradLabels N ℓ γ,
      (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2))
      ≤ 3 * E * D * ((N : ℝ) * ℓ) ^ (2 * ε) := by
    simp only [circDist_mul_self_scale hN0] at hspatial
    calc _ ≤ E * (2 + ((N : ℝ) * ℓ) ^ ε) * D := hspatial
      _ ≤ E * (3 * ((N : ℝ) * ℓ) ^ ε) * D := by gcongr
      _ ≤ E * (3 * ((N : ℝ) * ℓ) ^ (2 * ε)) * D := by
          gcongr
          linarith
      _ = _ := by ring
  have hw' := mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hℓ.le)
  have hd' := mul_le_mul_of_nonneg_left hd
    (mul_nonneg hN0.le (Real.rpow_nonneg hK0.le a))
  have hp : ℓ⁻¹ * ((N : ℝ) * ℓ) ^ (1 + a + 2 * ε)
      = (N : ℝ) * ((N : ℝ) * ℓ) ^ (a + 2 * ε) := by
    rw [show 1 + a + 2 * ε = 1 + (a + 2 * ε) by ring, Real.rpow_add hK0,
      Real.rpow_one]
    field_simp
  have hdiv (i : ℤ) : (N : ℝ) * ((N : ℝ) * ℓ) ^ a /
      (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2) =
      ((N : ℝ) * ((N : ℝ) * ℓ) ^ a) *
        (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)) :=
    div_rpow_eq_mul_rpow_neg (by have := circDist_nonneg 1 (gradLift N X i); positivity)
  have hw'' : ℓ⁻¹ * ∑ i ∈ gradLabels N ℓ γ, gradW2 s a N ℓ ((N : ℝ) * gradLift N X i)
      ≤ (24 * B * (1 + 1 / ε)) * (N : ℝ) * ((N : ℝ) * ℓ) ^ (a + 2 * ε) := by
    calc _ ≤ (24 * B * (1 + 1 / ε)) * (ℓ⁻¹ * ((N : ℝ) * ℓ) ^ (1 + a + 2 * ε)) := by
          convert hw' using 1; ring
      _ = _ := by rw [hp]; ring
  have hd'' : (N : ℝ) * ((N : ℝ) * ℓ) ^ a *
      ∑ i ∈ gradLabels N ℓ γ, (1 + (N : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2))
      ≤ (3 * E * D) * (N : ℝ) * ((N : ℝ) * ℓ) ^ (a + 2 * ε) := by
    rw [Real.rpow_add hK0]
    convert hd' using 1; ring
  simp only [hdiv, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [← gradW2_eq_micro s a N hℓ] at hw''
  dsimp [C]
  nlinarith [hw'', hd'']

end

end Riesz1
