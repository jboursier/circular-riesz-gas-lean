/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorQuadratureGeometry
public import Riesz1.ToMathlib.UnitCellQuadratureBoundary
public import Riesz1.ToMathlib.Calculus.IntegerPowerTail

/-!
# Reference quadrature for the exterior force

The deterministic lattice/background estimate in the exterior part of
Lemma 5.8, with the exact objects.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The exterior reference sum approximates the arclength background uniformly.
Its constant depends only on the Riesz exponent. -/
theorem loopExterior_reference_quadrature (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ),
      1 ≤ (N : ℝ) * ℓ → 0 ≤ γ → GradPartial N ℓ γ →
      ∀ z ∈ Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4),
        |(∑ j ∈ loopExteriorLabels N ℓ γ,
            deriv (loopArcG s N) (z - (j : ℝ))) -
          ∫ u in loopExteriorBackground N ℓ γ, deriv (loopArcG s N) (z - u)| ≤
            C * gradM N ℓ γ ^ (-s - 1) := by
  obtain ⟨A, hA, hcell⟩ := loopExterior_reference_cell_bound hs hs1
  obtain ⟨B, hB, hband⟩ := loopExterior_reference_band_bound hs hs1
  refine ⟨A * (2 * (1 + 1 / (s + 1))) + 2 * B, by positivity, ?_⟩
  intro N ℓ γ hK hγ hP z hz
  let M := gradM N ℓ γ
  let H := (N : ℝ) / 2
  let n : ℤ := ⌊M⌋
  let a : ℤ := -(((N : ℤ) - 1) / 2)
  let b : ℤ := (N : ℤ) / 2 + 1
  let f : ℝ → ℝ := fun u => deriv (loopArcG s N) (z - u)
  let I := loopExteriorLabels N ℓ γ
  have hM : 1 ≤ M := Real.one_le_rpow hK hγ
  have hPM : M < (N : ℝ) / 8 := hP
  have hz' : |z| ≤ M / 4 := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
  have hnlo : (n : ℝ) ≤ M := Int.floor_le M
  have hnhi : M < (n : ℝ) + 1 := Int.lt_floor_add_one M
  have hn1 : (1 : ℤ) ≤ n := by
    apply Int.le_floor.mpr
    simpa only [Int.cast_one] using hM
  have hqa : (N : ℤ) - 1 - 1 ≤ 2 * (((N : ℤ) - 1) / 2) ∧
      2 * (((N : ℤ) - 1) / 2) ≤ (N : ℤ) - 1 := by omega
  have hqb : (N : ℤ) - 1 ≤ 2 * ((N : ℤ) / 2) ∧
      2 * ((N : ℤ) / 2) ≤ (N : ℤ) := by omega
  have haR : -H ≤ (a : ℝ) - 1 / 2 ∧ (a : ℝ) - 1 / 2 ≤ -H + 1 / 2 := by
    have h1 : (N : ℝ) - 2 ≤ 2 * ((((N : ℤ) - 1) / 2 : ℤ) : ℝ) := by
      exact_mod_cast (show (N : ℤ) - 2 ≤ 2 * (((N : ℤ) - 1) / 2) by omega)
    have h2 : 2 * ((((N : ℤ) - 1) / 2 : ℤ) : ℝ) ≤ (N : ℝ) - 1 := by
      exact_mod_cast hqa.2
    dsimp [a, H]
    push_cast
    constructor <;> linarith
  have hbR : H ≤ (b : ℝ) - 1 / 2 ∧ (b : ℝ) - 1 / 2 ≤ H + 1 / 2 := by
    have h1 : (N : ℝ) - 1 ≤ 2 * (((N : ℤ) / 2 : ℤ) : ℝ) := by
      exact_mod_cast hqb.1
    have h2 : 2 * (((N : ℤ) / 2 : ℤ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hqb.2
    dsimp [b, H]
    push_cast
    constructor <;> linarith
  have hnR : M / 2 ≤ (n : ℝ) + 1 / 2 := by linarith
  have hnH : (n : ℝ) + 1 / 2 ≤ H := by dsimp [H]; linarith
  have han : a ≤ -n := by
    have : (a : ℝ) ≤ (-n : ℤ) := by push_cast; dsimp [H] at haR; linarith [haR.2]
    exact_mod_cast this
  have hnb : n + 1 ≤ b := by
    have : ((n + 1 : ℤ) : ℝ) ≤ (b : ℝ) := by push_cast; linarith [hbR.1]
    exact_mod_cast this
  have hleft (u : ℝ) (hu : u ∈ Icc (-H - 1 / 2) (-M / 2)) :
      M / 2 ≤ |u| ∧ |u| ≤ H + 1 / 2 := by
    rw [abs_of_neg (by linarith [hu.2])]
    constructor <;> linarith [hu.1, hu.2]
  have hright (u : ℝ) (hu : u ∈ Icc (M / 2) (H + 1 / 2)) :
      M / 2 ≤ |u| ∧ |u| ≤ H + 1 / 2 := by
    rw [abs_of_pos (by linarith [hu.1])]
    exact hu
  have hcont (S : Set ℝ) (hS : ∀ u ∈ S, M / 2 ≤ |u| ∧ |u| ≤ H + 1 / 2) :
      ContinuousOn f S := by
    intro u hu
    have hsep := (loopExterior_reference_band_separation hM hPM hz' (hS u hu).1 (hS u hu).2).2
    exact ((contDiffAt_deriv_loopArcG hs hs1 N hsep).continuousAt.comp
      (f := fun u : ℝ => z - u) (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have hil (c d : ℝ) (hc : c ∈ Icc (-H - 1 / 2) (-M / 2))
      (hd : d ∈ Icc (-H - 1 / 2) (-M / 2)) : IntervalIntegrable f volume c d :=
    ((hcont _ hleft).mono (uIcc_subset_Icc hc hd)).intervalIntegrable
  have hir (c d : ℝ) (hc : c ∈ Icc (M / 2) (H + 1 / 2))
      (hd : d ∈ Icc (M / 2) (H + 1 / 2)) : IntervalIntegrable f volume c d :=
    ((hcont _ hright).mono (uIcc_subset_Icc hc hd)).intervalIntegrable
  have hpL : (a : ℝ) - 1 / 2 ∈ Icc (-H - 1 / 2) (-M / 2) :=
    ⟨by linarith [haR.1], by dsimp [H] at haR; linarith [haR.2]⟩
  have hpC : ((-n : ℤ) : ℝ) - 1 / 2 ∈ Icc (-H - 1 / 2) (-M / 2) := by
    push_cast
    exact ⟨by linarith, by linarith⟩
  have hpH : -H ∈ Icc (-H - 1 / 2) (-M / 2) :=
    ⟨by linarith, by dsimp [H]; linarith⟩
  have hpM : -M ∈ Icc (-H - 1 / 2) (-M / 2) :=
    ⟨by dsimp [H]; linarith, by linarith⟩
  have hqC : ((n + 1 : ℤ) : ℝ) - 1 / 2 ∈ Icc (M / 2) (H + 1 / 2) := by
    push_cast
    exact ⟨by linarith, by linarith⟩
  have hqR : (b : ℝ) - 1 / 2 ∈ Icc (M / 2) (H + 1 / 2) :=
    ⟨by dsimp [H] at hbR; linarith [hbR.1], hbR.2⟩
  have hqM : M ∈ Icc (M / 2) (H + 1 / 2) :=
    ⟨by linarith, by dsimp [H]; linarith⟩
  have hqH : H ∈ Icc (M / 2) (H + 1 / 2) :=
    ⟨by dsimp [H]; linarith, by linarith⟩
  have hlint := hil _ _ hpL hpC
  have hrint := hir _ _ hqC hqR
  have hlbg := hil _ _ hpH hpM
  have hrbg := hir _ _ hqM hqH
  have htileL := sum_Ico_unitCell_integral han hlint
  have htileR := sum_Ico_unitCell_integral hnb hrint
  have hdis : Disjoint (Finset.Ico a (-n)) (Finset.Ico (n + 1) b) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    simp only [Finset.mem_Ico] at hj hk
    omega
  have htile : (∑ j ∈ I, ∫ u in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2), f u) =
      (∫ u in ((a : ℝ) - 1 / 2)..(((-n : ℤ) : ℝ) - 1 / 2), f u) +
        ∫ u in (((n + 1 : ℤ) : ℝ) - 1 / 2)..((b : ℝ) - 1 / 2), f u := by
    rw [show I = Finset.Ico a (-n) ∪ Finset.Ico (n + 1) b from
      loopExteriorLabels_eq_Ico_union hK hγ hP, Finset.sum_union hdis, htileL, htileR]
  have hbndL (u : ℝ) (hu : u ∈ Icc (-H - 1 / 2) (-M / 2)) : |f u| ≤ B * M ^ (-s - 1) :=
    hband N M z u hM hPM hz' (hleft u hu).1 (hleft u hu).2
  have hbndR (u : ℝ) (hu : u ∈ Icc (M / 2) (H + 1 / 2)) : |f u| ≤ B * M ^ (-s - 1) :=
    hband N M z u hM hPM hz' (hright u hu).1 (hright u hu).2
  have heL := abs_integral_sub_integral_le_endpoints hlint hlbg (hil _ _ hpL hpH)
    (fun u hu => hbndL u (uIcc_subset_Icc hpL hpH hu))
    (fun u hu => hbndL u (uIcc_subset_Icc hpC hpM hu))
  have heR := abs_integral_sub_integral_le_endpoints hrint hrbg (hir _ _ hqC hqM)
    (fun u hu => hbndR u (uIcc_subset_Icc hqC hqM hu))
    (fun u hu => hbndR u (uIcc_subset_Icc hqR hqH hu))
  have hlenL : |-H - ((a : ℝ) - 1 / 2)| + |-M - (((-n : ℤ) : ℝ) - 1 / 2)| ≤ 1 := by
    have h1 : |-H - ((a : ℝ) - 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [haR.2], by linarith [haR.1]⟩
    have h2 : |-M - (((-n : ℤ) : ℝ) - 1 / 2)| ≤ 1 / 2 := by
      push_cast
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hlenR : |M - (((n + 1 : ℤ) : ℝ) - 1 / 2)| + |H - ((b : ℝ) - 1 / 2)| ≤ 1 := by
    have h1 : |M - (((n + 1 : ℤ) : ℝ) - 1 / 2)| ≤ 1 / 2 := by
      push_cast
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |H - ((b : ℝ) - 1 / 2)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hbR.2], by linarith [hbR.1]⟩
    linarith
  have hb0 : 0 ≤ B * M ^ (-s - 1) := by positivity
  have hboundary : |(∑ j ∈ I, ∫ u in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2), f u) -
      ∫ u in loopExteriorBackground N ℓ γ, f u| ≤ 2 * B * M ^ (-s - 1) := by
    rw [htile, loopExteriorBackground_integral_eq (by linarith : 0 < gradM N ℓ γ) hP
      (by simpa only [H, neg_div] using hlbg) hrbg]
    calc
      _ = |((∫ u in ((a : ℝ) - 1 / 2)..(((-n : ℤ) : ℝ) - 1 / 2), f u) -
          ∫ u in (-H)..(-M), f u) +
        ((∫ u in (((n + 1 : ℤ) : ℝ) - 1 / 2)..((b : ℝ) - 1 / 2), f u) -
          ∫ u in M..H, f u)| := by
            dsimp [H, M]
            simp only [neg_div]
            congr 1
            ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ (B * M ^ (-s - 1)) * 1 + (B * M ^ (-s - 1)) * 1 := by
        apply add_le_add (heL.trans _) (heR.trans _)
        · exact mul_le_mul_of_nonneg_left hlenL hb0
        · exact mul_le_mul_of_nonneg_left hlenR hb0
      _ = _ := by ring
  have hlabel (j : ℤ) (hj : j ∈ I) :
      1 ≤ |(j : ℝ)| ∧ |(j : ℝ)| ≤ (N : ℝ) / 2 ∧ |z| ≤ |(j : ℝ)| / 4 := by
    obtain ⟨hjM, _, hjN⟩ := loopExteriorLabels_abs hK hγ hP hj
    have hnN : 2 * j.natAbs ≤ (N : ℕ) := by omega
    have hrN : (2 : ℝ) * j.natAbs ≤ N := by exact_mod_cast hnN
    rw [natAbs_cast_eq_abs] at hrN
    exact ⟨hM.trans hjM.le, by linarith, hz'.trans (by linarith)⟩
  have hsum : |(∑ j ∈ I, f j) -
      ∑ j ∈ I, ∫ u in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2), f u| ≤
        A * (2 * (1 + 1 / (s + 1))) * M ^ (-s - 1) := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j ∈ I, A * |(j : ℝ)| ^ (-s - 2) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hcell N j z (hlabel j hj).1 (hlabel j hj).2.1 (hlabel j hj).2.2).2
      _ = A * ∑ j ∈ I, |(j : ℝ)| ^ (-s - 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ A * ((2 * (1 + 1 / (s + 1))) * M ^ (-s - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        simpa only [show -(s + 2) = -s - 2 by ring,
          show s + 2 - 1 = s + 1 by ring, show 1 - (s + 2) = -s - 1 by ring] using
          sum_int_abs_rpow_tail (a := s + 2) (by linarith) hM I
            (fun j hj => (loopExteriorLabels_abs hK hγ hP hj).1.le)
      _ = _ := by ring
  change |(∑ j ∈ I, f j) - ∫ u in loopExteriorBackground N ℓ γ, f u| ≤ _
  calc
    _ ≤ |(∑ j ∈ I, f j) -
        ∑ j ∈ I, ∫ u in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2), f u| +
      |(∑ j ∈ I, ∫ u in ((j : ℝ) - 1 / 2)..((j : ℝ) + 1 / 2), f u) -
        ∫ u in loopExteriorBackground N ℓ γ, f u| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hsum hboundary
    _ = _ := by dsimp [M]; ring

end Riesz1

end
