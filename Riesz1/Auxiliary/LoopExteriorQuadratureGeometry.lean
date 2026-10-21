/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorComparison
public import Riesz1.ToMathlib.UnitCellIntegral

/-!
# Exterior reference cells

Exact label and background partitions for the exterior part of Lemma 5.8.
The even-period antipodal label occurs once, in the positive interval of labels.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The two consecutive ranges of exterior labels, including exactly one antipode. -/
theorem loopExteriorLabels_eq_Ico_union {N : ℕ+} {ℓ γ : ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) (hP : GradPartial N ℓ γ) :
    loopExteriorLabels N ℓ γ =
      Finset.Ico (-(((N : ℤ) - 1) / 2)) (-⌊gradM N ℓ γ⌋) ∪
        Finset.Ico (⌊gradM N ℓ γ⌋ + 1) ((N : ℤ) / 2 + 1) := by
  have hn : 0 ≤ ⌊gradM N ℓ γ⌋ :=
    Int.floor_nonneg.mpr (zero_le_one.trans (Real.one_le_rpow hK hγ))
  have hN : (0 : ℤ) < N := by exact_mod_cast N.pos
  ext j
  simp only [loopExteriorLabels, gradLabels, hP, ↓reduceIte, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]
  omega

/-- The exterior arclength integral is the sum of the two oriented side integrals. -/
theorem loopExteriorBackground_integral_eq {N : ℕ+} {ℓ γ : ℝ} {f : ℝ → ℝ}
    (hM : 0 < gradM N ℓ γ) (hP : GradPartial N ℓ γ)
    (hl : IntervalIntegrable f volume (-(N : ℝ) / 2) (-gradM N ℓ γ))
    (hr : IntervalIntegrable f volume (gradM N ℓ γ) ((N : ℝ) / 2)) :
    (∫ u in loopExteriorBackground N ℓ γ, f u) =
      (∫ u in (-(N : ℝ) / 2)..(-gradM N ℓ γ), f u) +
        ∫ u in (gradM N ℓ γ)..((N : ℝ) / 2), f u := by
  have hP' : gradM N ℓ γ < (N : ℝ) / 8 := hP
  have hset : loopExteriorBackground N ℓ γ =
      Ico (-(N : ℝ) / 2) (-gradM N ℓ γ) ∪
        Ioc (gradM N ℓ γ) ((N : ℝ) / 2) := by
    ext u
    simp only [loopExteriorBackground, mem_sdiff, mem_Icc, mem_union, mem_Ico, mem_Ioc]
    constructor
    · rintro ⟨⟨hu1, hu2⟩, hu⟩
      by_cases h : u < -gradM N ℓ γ
      · exact Or.inl ⟨hu1, h⟩
      · exact Or.inr ⟨by by_contra! hc; exact hu ⟨by linarith, hc⟩, hu2⟩
    · rintro (hu | hu)
      · exact ⟨⟨hu.1, by linarith [hu.2]⟩, by intro hc; linarith [hc.1, hu.2]⟩
      · exact ⟨⟨by linarith [hu.1], hu.2⟩, by intro hc; linarith [hc.2, hu.1]⟩
  have hdis : Disjoint (Ico (-(N : ℝ) / 2) (-gradM N ℓ γ))
      (Ioc (gradM N ℓ γ) ((N : ℝ) / 2)) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    linarith [hu.2, hv.1]
  have hl' : IntegrableOn f (Ico (-(N : ℝ) / 2) (-gradM N ℓ γ)) := by
    exact (intervalIntegrable_iff_integrableOn_Ico_of_le (by linarith)).mp hl
  rw [hset, setIntegral_union hdis measurableSet_Ioc hl' hr.1,
    integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_of_le (by linarith)]

/-- The reference cells and their boundary strips remain separated, including the
half cell extending past the positive antipode. -/
theorem loopExterior_reference_band_separation {N : ℕ+} {M z u : ℝ}
    (hM : 1 ≤ M) (hP : M < (N : ℝ) / 8) (hz : |z| ≤ M / 4)
    (hu : M / 2 ≤ |u|) (huN : |u| ≤ (N : ℝ) / 2 + 1 / 2) :
    M / 4 ≤ latticeDist (N : ℝ) (z - u) ∧
      (((z - u) / (N : ℝ) : ℝ) : UnitAddCircle) ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hlo : M / 4 ≤ |z - u| := by
    have ht : |u| ≤ |z - u| + |z| := by
      calc |u| = |z - (z - u)| := by congr 1; ring
        _ ≤ |z| + |z - u| := abs_sub _ _
        _ = _ := add_comm _ _
    linarith
  have hhi : |z - u| ≤ M / 4 + (N : ℝ) / 2 + 1 / 2 :=
    (abs_sub _ _).trans (by linarith)
  refine ⟨loopExterior_latticeDist_lower hN hlo (by linarith), ?_⟩
  apply gradSplit_coe_ne_zero
  · rw [abs_div, abs_of_pos hN]
    exact div_pos (by linarith) hN
  · rw [abs_div, abs_of_pos hN, div_lt_one hN]
    linarith

/-- A uniform force bound throughout all reference cells and endpoint strips. -/
theorem loopExterior_reference_band_bound {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (M z u : ℝ),
      1 ≤ M → M < (N : ℝ) / 8 → |z| ≤ M / 4 →
      M / 2 ≤ |u| → |u| ≤ (N : ℝ) / 2 + 1 / 2 →
      |deriv (loopArcG s N) (z - u)| ≤ C * M ^ (-s - 1) := by
  obtain ⟨C, hC, hb⟩ := loopExterior_iteratedDeriv_le_of_separated hs hs1 1
  refine ⟨C * (1 / 4 : ℝ) ^ (-s - 1), by positivity, ?_⟩
  intro N M z u hM hP hz hu huN
  have h := hb N (z - u) (M / 4) (by linarith)
    (loopExterior_reference_band_separation hM hP hz hu huN).1
  simp only [iteratedDeriv_one, Nat.cast_one] at h
  calc
    _ ≤ C * (M / 4) ^ (-s - 1) := h
    _ = _ := by
      rw [show M / 4 = (1 / 4 : ℝ) * M by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) (by linarith : 0 ≤ M)]
      ring

end Riesz1

end
