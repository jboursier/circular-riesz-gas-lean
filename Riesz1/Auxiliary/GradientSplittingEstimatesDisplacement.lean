/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDisplacement

/-!
# Displacement assembly without a support premise

The background cancels from `V^(1)`. Assemble `pair_decay_le`,
`sum_erase_weight_le` and particle convolution bounds without a support
premise. This is needed for the circular support convention in the estimates part of Lemma 5.7:
the final displacement theorem
has an unused real-absolute-value support premise, which is stronger than
circular support. No kernel or convolution estimate is reproved here.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1

noncomputable section

/-- The displacement estimate assembled from its pair and sum lemmas.
No support or background estimate is needed. -/
theorem gradEst_displacement {s α γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα0 : s - 1 ≤ α) (hα1 : α < s / 2) (_hγ : 4 ≤ γ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε < εstar →
      ∃ C : ℝ, 0 < C ∧ ∀ C0 : ℝ, 0 ≤ C0 → ∀ (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ) (ψ : ℝ → ℝ) (i : ℤ),
        2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
        (∀ t : ℝ, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t) →
        (∀ t : ℝ, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ t) →
        gradEvent s γ ε N ℓ X →
        |((N : ℕ) : ℝ) * gradLift N X 0| ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε →
        i ∈ gradLabels N ℓ γ →
        |gradV1lab s ψ N ℓ γ X i| ≤
          C * C0 * (((N : ℕ) : ℝ) * ℓ) ^ (κ * ε) *
            (ℓ⁻¹ * gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) +
              ((N : ℕ) : ℝ) * (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α) /
                (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := (gradient_splitting_kernel s hs0 hs1).2.2.1
  have hC_val : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 → |gradKernelH s u| ≤ C₁ * |u| ^ (-s) := by
    intro u hu hu34
    have h := (hC₁ u hu hu34).2 0 (Nat.zero_le _)
    simpa using h
  have hC_der : ∀ u : ℝ, 0 < |u| → |u| ≤ 3 / 4 →
      |iteratedDeriv 1 (gradKernelH s) u| ≤ C₁ * |u| ^ (-s - 1) := by
    intro u hu hu34
    have h := (hC₁ u hu hu34).2 1 (by norm_num)
    simpa using h
  obtain ⟨_, _, hpartG⟩ := gradient_splitting_particle_sum_two (a := 1 - s + α) hs0 hs1
    (by linarith) (by linarith)
  obtain ⟨CL, hCL, hdecayG⟩ := sum_labels_decay_le (s := s) hs0
  refine ⟨(1 - s / 2) / 8, by linarith, (s + 2) + (2 + s / 2) + 1, by positivity,
    fun ε hε hεs => ?_⟩
  obtain ⟨Ca, hCa, hpartε⟩ := hpartG ε hε hεs
  have hA1 : 0 < gradZConst (1 - s + α) s + 1 := by
    have := gradZConst_nonneg (a := 1 - s + α) (s := s) (by linarith) hs1
    linarith
  have hN₀pos : (0 : ℝ) < ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) :=
    Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _
  have hp1 : (0 : ℝ) < 2 ^ s + 1 := by
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) s
    linarith
  have hCp : (0 : ℝ) < C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2) :=
    mul_pos (mul_pos hC₁pos hp1) hN₀pos
  have hCEf : (0 : ℝ) < (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) := by
    have h1 : 0 < 2 * (gradZConst (1 - s + α) s + 1)
        * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2)) :=
      mul_pos (mul_pos (by norm_num) hA1) hCp
    have h2 : 0 < 6 * (gradZConst (1 - s + α) s + 1) * C₁ :=
      mul_pos (mul_pos (by norm_num) hA1) hC₁pos
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)
  have hone : (0 : ℝ) < 1 + 1 / ε := by
    have := one_div_pos.mpr hε
    linarith
  have hCL' : (0 : ℝ) < CL + Ca * (1 + 1 / ε) := by
    have := mul_pos hCa hone
    linarith
  refine ⟨(2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) * (CL + Ca * (1 + 1 / ε)),
    mul_pos hCEf hCL', fun C0 hC0 N ℓ X ψ i hN hℓ hℓ1 hK hψ hper hbd hbd2 hX _hanch hi => ?_⟩
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hγ1 : 1 < γ := by linarith
  have hα_a0 : 0 ≤ 1 - s + α := by linarith
  have hα_a1 : 1 - s + α < 1 := by linarith
  have hlam1 : 1 ≤ (((N : ℕ) : ℝ) * ℓ) ^ ε := Real.one_le_rpow hK hε.le
  have hlampos : 0 < (((N : ℕ) : ℝ) * ℓ) ^ ε := Real.rpow_pos_of_pos hK0 _
  have hL : 1 + Real.log (((N : ℕ) : ℝ) * ℓ) ≤ (1 + 1 / ε) * (((N : ℕ) : ℝ) * ℓ) ^ ε := by
    have h := Real.log_le_rpow_div hK0.le hε
    have e : (1 + 1 / ε) * (((N : ℕ) : ℝ) * ℓ) ^ ε
        = (((N : ℕ) : ℝ) * ℓ) ^ ε + (((N : ℕ) : ℝ) * ℓ) ^ ε / ε := by ring
    linarith
  have hL0 : 0 ≤ 1 + Real.log (((N : ℕ) : ℝ) * ℓ) := by
    have := Real.log_nonneg hK
    linarith
  -- the pair terms
  rw [gradV1lab_eq_sum]
  have hterm : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      |2 * ((N : ℕ) : ℝ) ^ (-s) * (gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          * gradKernelH s (gradSep N ℓ γ X i j)
        - gradZx ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ))
          * gradKernelH s ((gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)))
      - 2 * ((N : ℕ) : ℝ) ^ (-s) * (gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j)
          - gradZ ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)))
          * deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ))|
      ≤ ((2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) * (C0 * ℓ⁻¹)
        * (((((N : ℕ) : ℝ) * ℓ) ^ ε)) ^ (s + 2))
        * ((gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + gradSep N ℓ γ X i j) / ℓ)
          + gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹
              ((gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / ((N : ℕ) : ℝ)) / ℓ))
          * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))) := by
    intro j hj
    have hjI := Finset.mem_of_mem_erase hj
    have hne := Finset.ne_of_mem_erase hj
    have h := pair_decay_le hs0 hs1 hα0 hα1 hC0 hℓ hℓ1 hK hN hψ hper hbd hbd2 hC₁pos.le hC_val
      hC_der hε hεs hγ1 hX hi hjI hne
    exact le_of_le_of_eq h (by ring)
  -- the particle sum, in multiplicative form
  have hyX : 0 ≤ 1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i) := by
    have h1 : 0 ≤ circDist 1 (gradLift N X i) := circDist_nonneg _ _
    have h2 : 0 ≤ ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i) := mul_nonneg hN0.le h1
    linarith
  have hdn : ∀ j ∈ gradLabels N ℓ γ, 0 ≤ 1 + (gradLabelDist N i j : ℝ) := by
    intro j hj
    have h : (0 : ℝ) ≤ (gradLabelDist N i j : ℝ) := by
      exact_mod_cast gradLabelDist_nonneg (gradLabels_abs_sub_lt hi hj)
    linarith
  have hpart' : ∑ j ∈ gradLabels N ℓ γ,
        (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
          + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ)))
          * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
      ≤ Ca * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) * (1 + Real.log (((N : ℕ) : ℝ) * ℓ))
        * (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
          + (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
            * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2))) := by
    have hpartε' := hpartε γ N ℓ X i hγ1 hN hℓ hℓ1 hK hX hi
    have e1 : ∑ j ∈ gradLabels N ℓ γ,
          (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
            + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ)))
            * (1 + (gradLabelDist N i j : ℝ)) ^ (-(1 + s / 2))
        = ∑ j ∈ gradLabels N ℓ γ,
          (gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X j)
            + gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ)))
            / (1 + (gradLabelDist N i j : ℝ)) ^ (1 + s / 2) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [div_rpow_eq_mul_rpow_neg (hdn j hj)]
    have e2 : (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
        / (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)
        = (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
          * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)) :=
      div_rpow_eq_mul_rpow_neg hyX
    rw [e1]
    refine le_trans hpartε' ?_
    rw [e2]
  have hWx_eq : gradW2 s (1 - s + α) N ℓ (((N : ℕ) : ℝ) * gradLift N X i)
      = gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) :=
    (gradW2_eq_micro s (1 - s + α) N hℓ (gradLift N X i)).symm
  have hW := sum_erase_weight_le (s := s) (α := α) (γ := γ) (ε := ε) (Ca := Ca) (C_L := CL)
    (N := N) (ℓ := ℓ) (X := X) hs0 hℓ hCL.le (fun i' hi' => hdecayG N ℓ γ i' hN hi') hi hCa.le hpart'
  rw [hWx_eq] at hW
  have hKκ : (((N : ℕ) : ℝ) * ℓ) ^ (((s + 2) + (2 + s / 2) + 1) * ε)
      = (((N : ℕ) : ℝ) * ℓ) ^ (ε * (s + 2)) * (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε)
        * (((N : ℕ) : ℝ) * ℓ) ^ ε := by
    rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
    congr 1
    ring
  have hMeq : (((N : ℕ) : ℝ) * ℓ) ^ (ε * (s + 2)) = ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2) :=
    Real.rpow_mul hK0.le ε (s + 2)
  have hQ1 : 1 ≤ (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) :=
    Real.one_le_rpow hK (mul_nonneg (by linarith) hε.le)
  have hWxnn : 0 ≤ gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) :=
    gradWeightTwo_nonneg_unconditional _ _ _ _ _
  have hYnn : 0 ≤ (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
      * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)) :=
    mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg hyX _)
  have hY : ℓ⁻¹ * ((((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
      * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)))
      = ((N : ℕ) : ℝ) * (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α)
        / (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2) := by
    rw [div_rpow_eq_mul_rpow_neg hyX, Real.rpow_add hK0, Real.rpow_one]
    field_simp
  have hK1 : 0 ≤ ((2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2)) * (C0 * ℓ⁻¹)
        * ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2) :=
    mul_nonneg (mul_nonneg hCEf.le (mul_nonneg hC0 (inv_nonneg.mpr hℓ.le)))
      (Real.rpow_nonneg hlampos.le _)
  have hsum1 := le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  rw [← Finset.mul_sum] at hsum1
  have hfin1 := le_trans hsum1 (mul_le_mul_of_nonneg_left hW hK1)
  set Wx := gradWeightTwo s (1 - s + α) (((N : ℕ) : ℝ) * ℓ) ℓ⁻¹ (gradLift N X i / ℓ) with hWx_def
  set Y := (((N : ℕ) : ℝ) * ℓ) ^ (1 + (1 - s + α))
      * (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (-(1 + s / 2)) with hY_def
  set M := ((((N : ℕ) : ℝ) * ℓ) ^ ε) ^ (s + 2) with hM_def
  set Q := (((N : ℕ) : ℝ) * ℓ) ^ ((2 + s / 2) * ε) with hQ_def
  set Pp := (((N : ℕ) : ℝ) * ℓ) ^ ε with hPp_def
  set L := 1 + Real.log (((N : ℕ) : ℝ) * ℓ) with hL_def
  set CEf := (2 * (gradZConst (1 - s + α) s + 1)
            * (C₁ * (2 ^ s + 1) * ((4 : ℝ) ^ (2 / (1 - s / 2))) ^ (1 - s / 2))
          + 6 * (gradZConst (1 - s + α) s + 1) * C₁) * 2 ^ (1 + s / 2) with hCEf_def
  calc _ ≤ CEf * (C0 * ℓ⁻¹) * M * (Wx * CL + Ca * Q * L * (Wx + Y)) := hfin1
    _ = CEf * C0 * ℓ⁻¹ * M * (Wx * CL + Ca * Q * L * (Wx + Y)) := by ring
    _ ≤ CEf * (CL + Ca * (1 + 1 / ε)) * C0 * (M * Q * Pp) * (ℓ⁻¹ * (Wx + Y)) :=
        disp_numeric hCEf.le hC0 (inv_nonneg.mpr hℓ.le) (Real.rpow_nonneg hlampos.le _) hQ1 hlam1
          hL0 hL hCL.le hCa.le hε hWxnn hYnn
    _ = (CEf * (CL + Ca * (1 + 1 / ε))) * C0 * ((((N : ℕ) : ℝ) * ℓ) ^ (((s + 2) + (2 + s / 2) + 1) * ε))
          * (ℓ⁻¹ * Wx + ((N : ℕ) : ℝ) * (((N : ℕ) : ℝ) * ℓ) ^ (1 - s + α)
            / (1 + ((N : ℕ) : ℝ) * circDist 1 (gradLift N X i)) ^ (1 + s / 2)) := by
        rw [hKκ, hMeq, mul_add ℓ⁻¹ Wx Y, hY]


end

end Riesz1
