/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopExteriorDefs
public import Riesz1.Auxiliary.LoopLocalMomentsIntegral
public import Riesz1.Auxiliary.LoopSizeBiasTails
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Probability of the exterior good event

The probability assertion of the exterior part of Lemma 5.8, on the
preceding-particle carrier. The endpoint estimates use actual
integer-floor blocks. The displacement is bounded by the boundary-selected gap.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz1

/-- Integer changes of the starting label by whole periods preserve an anchored block. -/
theorem loopAnchoredBlock_add_period (n : ℕ) (y : Fin (n + 1) → ℝ)
    (j q : ℤ) (k : ℕ) :
    loopAnchoredBlock n (j + ((n + 1).succPNat : ℕ) * q) k y =
      loopAnchoredBlock n j k y := by
  unfold loopAnchoredBlock
  rw [show j + ((n + 1).succPNat : ℕ) * q + k =
    (j + k) + ((n + 1).succPNat : ℕ) * q by ring,
    anchoredCyclicOffset_add_mul, anchoredCyclicOffset_add_mul]
  ring

/-- The displacement from zero has a uniform exponential upper tail. -/
theorem loopPrecedingD_upper_tail :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler)
      (P : Parameters) (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (u : ℝ), 0 ≤ u →
      loopPrecedingMeasure P N {X | u < loopPrecedingD X} ≤
        ENNReal.ofReal (C * Real.exp (-c * u)) := by
  obtain ⟨c, C, hc, hC, ht⟩ := boundary_selection_gap_tail
  refine ⟨c, C, hc, hC, fun hPL P N hN u hu => ?_⟩
  let E : Set (Configuration N) := {X | u < gap X (precedingLabel 0 0 X)}
  have hm : Measurable (fun X : Configuration N => gap X (precedingLabel 0 0 X)) := by
    have h : Measurable (fun p : Configuration N × ℤ => gap p.1 p.2) :=
      measurable_from_prod_countable_left fun j => measurable_gap j
    exact h.comp (measurable_id.prodMk (measurable_precedingLabel 0 0))
  have hE : MeasurableSet E := measurableSet_lt measurable_const hm
  have hsub : {X : LoopPrecedingConfiguration N | u < loopPrecedingD X} ⊆
      Subtype.val ⁻¹' E := by
    intro X hX
    exact hX.trans (loopPrecedingD_mem X).2
  apply (measure_mono hsub).trans
  rw [← Measure.map_apply measurable_subtype_coe hE, map_loopPrecedingMeasure]
  have := (modelWellDefined P N).2.2
  rw [← ofReal_measureReal (μ := gibbsMeasure P N) (s := E)]
  exact ENNReal.ofReal_le_ofReal (ht hPL P N hN 0 0 u hu)

/-- If the displacement and the two actual endpoint blocks are controlled, the
configuration belongs to the good event. The floor error is included. -/
theorem loopExteriorGood_of_blocks {n : ℕ} {ℓ γ : ℝ}
    (hM : 8 ≤ gradM (n + 1).succPNat ℓ γ)
    (X : LoopPrecedingConfiguration (n + 1).succPNat)
    (hD : loopPrecedingD X ≤ gradM (n + 1).succPNat ℓ γ / 8)
    (hp : |loopAnchoredBlock n 0 ⌊gradM (n + 1).succPNat ℓ γ⌋₊
      (loopPrecedingOffsets X) - (⌊gradM (n + 1).succPNat ℓ γ⌋₊ : ℝ)| <
        (⌊gradM (n + 1).succPNat ℓ γ⌋₊ : ℝ) / 4)
    (hm : |loopAnchoredBlock n (-⌊gradM (n + 1).succPNat ℓ γ⌋)
      ⌊gradM (n + 1).succPNat ℓ γ⌋₊ (loopPrecedingOffsets X) -
        (⌊gradM (n + 1).succPNat ℓ γ⌋₊ : ℝ)| <
          (⌊gradM (n + 1).succPNat ℓ γ⌋₊ : ℝ) / 4) :
    X ∈ loopExteriorGood (n + 1).succPNat ℓ γ := by
  have hM0 : 0 ≤ gradM (n + 1).succPNat ℓ γ := by linarith
  have hf : (⌊gradM (n + 1).succPNat ℓ γ⌋₊ : ℤ) =
      ⌊gradM (n + 1).succPNat ℓ γ⌋ := Int.natCast_floor_eq_floor hM0
  have hfloor := Nat.lt_floor_add_one (gradM (n + 1).succPNat ℓ γ)
  have hp' := (abs_lt.mp hp).1
  have hm' := (abs_lt.mp hm).1
  rw [← loopPrecedingLift_sub_eq_block, zero_add, hf, loopPrecedingLift_zero] at hp'
  rw [← loopPrecedingLift_sub_eq_block, hf, neg_add_cancel,
    loopPrecedingLift_zero] at hm'
  have hD0 := (loopPrecedingD_mem X).1
  exact ⟨hD, by linarith, by linarith⟩

/-- The displacement of an integer-labelled particle is controlled by its directed
block fluctuation and the displacement of the preceding particle. Negative labels
use the backward block, expressed in the same block coordinates. -/
theorem loopPrecedingLift_displacement_le (n : ℕ)
    (X : LoopPrecedingConfiguration (n + 1).succPNat) (j : ℤ) :
    |loopPrecedingLift X j - (j : ℝ)| ≤
      |loopAnchoredBlock n (pairBase 0 j) j.natAbs (loopPrecedingOffsets X) -
        (j.natAbs : ℝ)| + loopPrecedingD X := by
  have he : |loopPrecedingLift X j - loopPrecedingLift X 0 - (j : ℝ)| =
      |loopAnchoredBlock n (pairBase 0 j) j.natAbs (loopPrecedingOffsets X) -
        (j.natAbs : ℝ)| := by
    by_cases hj : 0 ≤ j
    · have hjZ : (j.natAbs : ℤ) = j := by rw [Int.natCast_natAbs, abs_of_nonneg hj]
      have hjR : (j.natAbs : ℝ) = (j : ℝ) := by
        rw [natAbs_cast_eq_abs, abs_of_nonneg (by exact_mod_cast hj)]
      simp only [pairBase, hj, ↓reduceIte, ← loopPrecedingLift_sub_eq_block,
        zero_add, hjZ, hjR]
    · have hjZ : (j.natAbs : ℤ) = -j := by rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hj)]
      have hjR : (j.natAbs : ℝ) = -(j : ℝ) := by
        rw [natAbs_cast_eq_abs, abs_of_neg (by exact_mod_cast lt_of_not_ge hj)]
      simp only [pairBase, hj, ↓reduceIte, zero_add,
        ← loopPrecedingLift_sub_eq_block, hjZ, add_neg_cancel, hjR]
      rw [← abs_neg (loopPrecedingLift X 0 - loopPrecedingLift X j - -(j : ℝ))]
      congr 1
      ring
  calc
    |loopPrecedingLift X j - (j : ℝ)| =
        |(loopPrecedingLift X j - loopPrecedingLift X 0 - (j : ℝ)) + loopPrecedingLift X 0| := by
      congr 1
      ring
    _ ≤ |loopPrecedingLift X j - loopPrecedingLift X 0 - (j : ℝ)| + |loopPrecedingLift X 0| :=
      abs_add_le _ _
    _ = _ := by rw [he, loopPrecedingLift_zero, abs_neg, abs_of_pos (loopPrecedingD_mem X).1]

namespace Internal

private theorem quarter_power_threshold {a : ℝ} (ha : a < 1) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ x : ℝ, T ≤ x → x ^ a ≤ x / 4 := by
  have ht := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  obtain ⟨T, hT⟩ := eventually_atTop.mp ht
  refine ⟨max 1 T, le_max_left _ _, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hx)
  have h := hT x ((le_max_right _ _).trans hx)
  rw [show -(1 - a) = a - 1 by ring, Real.rpow_sub hx0, Real.rpow_one] at h
  have h' := (div_lt_iff₀ hx0).mp h
  linarith

/-- The size-biased rigidity tail, transported to the actual preceding lifts
and to every integer starting label. -/
theorem loopPreceding_block_tail_of_rigidity (β s : ℝ) (hβ : 0 < β)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion β s hβ hs hs1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < eps0 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler)
        (n : ℕ) (j : ℤ) (k : ℕ), 1 ≤ k → k ≤ (n + 2) / 2 →
        loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat
          {X | |loopPrecedingLift X (j + k) - loopPrecedingLift X j - k| ≥
            (k : ℝ) ^ (s / 2 + δ)} ≤
              ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2))))) := by
  obtain ⟨eps0, heps0, ht⟩ := loopSizeBiased_gap_tail_of_rigidity β s hβ hs hs1 hRig
  refine ⟨eps0, heps0, fun δ hδ hδ0 => ?_⟩
  obtain ⟨c, C, hc, hC, hb⟩ := ht δ hδ hδ0
  refine ⟨c, C, hc, hC, fun hPL n j k hk hkN => ?_⟩
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := (n + 1).succPNat) j
  have hE : MeasurableSet {y : Fin (n + 1) → ℝ |
      |loopAnchoredBlock n i k y - k| ≥ (k : ℝ) ^ (s / 2 + δ)} :=
    measurableSet_le measurable_const ((measurable_loopAnchoredBlock n i k).sub_const _).abs
  have he : {X : LoopPrecedingConfiguration (n + 1).succPNat |
      |loopPrecedingLift X ((i : ℤ) + ((n + 1).succPNat : ℕ) * q + k) -
        loopPrecedingLift X ((i : ℤ) + ((n + 1).succPNat : ℕ) * q) - k| ≥
          (k : ℝ) ^ (s / 2 + δ)} =
      (loopPrecedingOffsets (N := (n + 1).succPNat)) ⁻¹' {y | |loopAnchoredBlock n i k y - k| ≥
        (k : ℝ) ^ (s / 2 + δ)} := by
    ext X
    change |loopPrecedingLift X _ - loopPrecedingLift X _ - k| ≥ _ ↔ _
    rw [loopPrecedingLift_sub_eq_block]
    erw [loopAnchoredBlock_add_period]
    rfl
  rw [he, ← Measure.map_apply (measurable_loopPrecedingOffsets _) hE,
    map_loopPrecedingOffsets]
  exact hb hPL n ⟨i, hi⟩ k hk hkN

/-- The large-displacement event for each exterior label has a uniform stretched
exponential bound, with the preceding displacement included. This is the exceptional
event used in the per-label force comparison in the exterior part of Lemma 5.8. -/
theorem loopPrecedingLift_displacement_tail_of_rigidity (β s : ℝ) (hβ : 0 < β)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion β s hβ hs hs1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 →
      ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ T ∧
        ∀ (_hPL : External.PrekopaLeindler) (n : ℕ) (j : ℤ),
          T ≤ (j.natAbs : ℝ) → j.natAbs ≤ (n + 2) / 2 →
          loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat
            {X | |loopPrecedingLift X j - (j : ℝ)| ≥ |(j : ℝ)| / 2} ≤
              ENNReal.ofReal (C * Real.exp (-c * |(j : ℝ)| ^
                (δ / (4 * (s + 2))))) := by
  obtain ⟨eps0, heps0, ht⟩ := loopPreceding_block_tail_of_rigidity β s hβ hs hs1 hRig
  obtain ⟨d, A, hd, hA, hD⟩ := loopPrecedingD_upper_tail
  refine ⟨eps0, heps0, fun δ hδ hδ0 => ?_⟩
  obtain ⟨b, B, hb, hB, hblock⟩ := ht δ hδ (lt_of_lt_of_le hδ0 (min_le_right _ _))
  have ha : s / 2 + δ < 1 := by
    have := lt_of_lt_of_le hδ0 (min_le_left _ _)
    linarith
  obtain ⟨T, hT, hpower⟩ := quarter_power_threshold ha
  let τ := δ / (4 * (s + 2))
  have hτ1 : τ ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 4 * (s + 2))).mpr
    have := lt_of_lt_of_le hδ0 (min_le_left _ _)
    linarith
  let c := min (d / 8) b
  have hc : 0 < c := lt_min (by positivity) hb
  refine ⟨c, A + B, T, hc, by positivity, hT, fun hPL n j hjT hjN => ?_⟩
  let k := j.natAbs
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := loopPrecedingMeasure P (n + 1).succPNat
  have hk1 : 1 ≤ k := by exact_mod_cast hT.trans hjT
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkpow := hpower k hjT
  let E0 : Set (LoopPrecedingConfiguration (n + 1).succPNat) :=
    {X | (k : ℝ) / 8 < loopPrecedingD X}
  let E1 : Set (LoopPrecedingConfiguration (n + 1).succPNat) :=
    {X | (k : ℝ) / 4 ≤ |loopAnchoredBlock n (pairBase 0 j) k
      (loopPrecedingOffsets X) - k|}
  have hsub : {X | |loopPrecedingLift X j - (j : ℝ)| ≥ |(j : ℝ)| / 2} ⊆ E0 ∪ E1 := by
    intro X hX
    by_contra h
    have hh : X ∉ E0 ∧ X ∉ E1 := not_or.mp h
    have h0 : loopPrecedingD X ≤ (k : ℝ) / 8 := le_of_not_gt hh.1
    have h1 : |loopAnchoredBlock n (pairBase 0 j) k (loopPrecedingOffsets X) - k| <
        (k : ℝ) / 4 := lt_of_not_ge hh.2
    have hle := loopPrecedingLift_displacement_le n X j
    rw [← natAbs_cast_eq_abs] at hX
    change (k : ℝ) / 2 ≤ |loopPrecedingLift X j - (j : ℝ)| at hX
    change |loopPrecedingLift X j - (j : ℝ)| ≤
      |loopAnchoredBlock n (pairBase 0 j) k (loopPrecedingOffsets X) - k| + loopPrecedingD X at hle
    linarith
  have h0 : μ E0 ≤ ENNReal.ofReal (A * Real.exp (-d * ((k : ℝ) / 8))) :=
    hD hPL P _ (by simp) _ (by positivity)
  have h1 : μ E1 ≤ ENNReal.ofReal (B * Real.exp (-b * (k : ℝ) ^ τ)) := by
    have hsub' : E1 ⊆ {X | (k : ℝ) ^ (s / 2 + δ) ≤
        |loopPrecedingLift X (pairBase 0 j + k) - loopPrecedingLift X (pairBase 0 j) - k|} := by
      intro X hX
      change (k : ℝ) ^ (s / 2 + δ) ≤
        |loopPrecedingLift X (pairBase 0 j + k) - loopPrecedingLift X (pairBase 0 j) - k|
      rw [loopPrecedingLift_sub_eq_block]
      exact hkpow.trans hX
    exact (measure_mono hsub').trans (hblock hPL n (pairBase 0 j) k hk1 hjN)
  have hkpow1 : (k : ℝ) ^ τ ≤ (k : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ k by exact_mod_cast hk1) hτ1
  have hexp0 : Real.exp (-d * ((k : ℝ) / 8)) ≤ Real.exp (-c * (k : ℝ) ^ τ) := by
    apply Real.exp_le_exp.mpr
    have hc1 : c ≤ d / 8 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_left hkpow1 (show 0 ≤ d / 8 by positivity),
      mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hkr.le τ)]
  have hexp1 : Real.exp (-b * (k : ℝ) ^ τ) ≤ Real.exp (-c * (k : ℝ) ^ τ) := by
    apply Real.exp_le_exp.mpr
    have hc2 : c ≤ b := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hkr.le τ)]
  calc
    μ {X | |loopPrecedingLift X j - (j : ℝ)| ≥ |(j : ℝ)| / 2} ≤ μ (E0 ∪ E1) := measure_mono hsub
    _ ≤ μ E0 + μ E1 := measure_union_le _ _
    _ ≤ ENNReal.ofReal (A * Real.exp (-d * ((k : ℝ) / 8))) +
        ENNReal.ofReal (B * Real.exp (-b * (k : ℝ) ^ τ)) := add_le_add h0 h1
    _ ≤ ENNReal.ofReal (A * Real.exp (-c * (k : ℝ) ^ τ)) +
        ENNReal.ofReal (B * Real.exp (-c * (k : ℝ) ^ τ)) := by gcongr
    _ = ENNReal.ofReal ((A + B) * Real.exp (-c * |(j : ℝ)| ^ τ)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← natAbs_cast_eq_abs]
      congr 1
      ring

/-- The exterior part of Lemma 5.8, its entire good-event probability
assertion. Constants and the scale threshold are uniform in the window exponent.
The Prékopa–Leindler inequality `External.PrekopaLeindler` supplies the selected-gap estimate. -/
theorem loopExteriorGood_probability_of_rigidity (β s : ℝ) (hβ : 0 < β)
    (hs : 0 < s) (hs1 : s < 1) (hRig : RigidityConclusion β s hβ hs hs1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 →
      ∃ c C K0 : ℝ, 0 < c ∧ 0 < C ∧ 1 ≤ K0 ∧
        ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (ℓ γ : ℝ),
          2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → K0 ≤ (N : ℝ) * ℓ → 1 < γ →
          GradPartial N ℓ γ →
          loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ N
            (loopExteriorGood N ℓ γ)ᶜ ≤
              ENNReal.ofReal (C * Real.exp (-c * gradM N ℓ γ ^
                (δ / (4 * (s + 2))))) := by
  obtain ⟨eps0, heps0, ht⟩ := loopPreceding_block_tail_of_rigidity β s hβ hs hs1 hRig
  obtain ⟨d, A, hd, hA, hD⟩ := loopPrecedingD_upper_tail
  refine ⟨eps0, heps0, fun δ hδ hδ0 => ?_⟩
  obtain ⟨b, B, hb, hB, hblock⟩ := ht δ hδ (lt_of_lt_of_le hδ0 (min_le_right _ _))
  have ha : s / 2 + δ < 1 := by
    have := lt_of_lt_of_le hδ0 (min_le_left _ _)
    linarith
  obtain ⟨T, hT, hpower⟩ := quarter_power_threshold ha
  let τ := δ / (4 * (s + 2))
  have hτ : 0 < τ := div_pos hδ (by positivity)
  have hτ1 : τ ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 4 * (s + 2))).mpr
    have := lt_of_lt_of_le hδ0 (min_le_left _ _)
    linarith
  let c := min (d / 8) (b * (1 / 2 : ℝ) ^ τ)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, A + 2 * B, max 8 (2 * T + 2), hc, by positivity,
    by exact (by norm_num : (1 : ℝ) ≤ 8).trans (le_max_left _ _), ?_⟩
  intro hPL N ℓ γ hN _hℓ _hℓ1 hK hγ hP
  obtain ⟨n, hn⟩ : ∃ n : ℕ, N = (n + 1).succPNat := by
    refine ⟨(N : ℕ) - 2, ?_⟩
    apply Subtype.ext
    change (N : ℕ) = (N : ℕ) - 2 + 1 + 1
    omega
  subst N
  let N := (n + 1).succPNat
  let M := gradM N ℓ γ
  let k := ⌊M⌋₊
  let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
  let μ := loopPrecedingMeasure P N
  have hK1 : 1 ≤ (N : ℝ) * ℓ := by
    have := (le_max_left 8 (2 * T + 2)).trans hK
    linarith
  have hKM : (N : ℝ) * ℓ ≤ M := Real.self_le_rpow_of_one_le hK1 hγ.le
  have hM8 : 8 ≤ M := (le_max_left _ _).trans (hK.trans hKM)
  have hMT : 2 * T + 2 ≤ M := (le_max_right _ _).trans (hK.trans hKM)
  have hkM : (k : ℝ) ≤ M := Nat.floor_le (by linarith)
  have hMk : M < (k : ℝ) + 1 := Nat.lt_floor_add_one M
  have hkT : T ≤ (k : ℝ) := by linarith
  have hk1 : 1 ≤ k := by exact_mod_cast hT.trans hkT
  have hkN : k ≤ (n + 2) / 2 := by
    have hPr : M < (n + 2 : ℕ) / (8 : ℝ) := hP
    have : (2 : ℝ) * k ≤ (n + 2 : ℕ) := by linarith
    have : 2 * k ≤ n + 2 := by exact_mod_cast this
    omega
  have hpk : (k : ℝ) ^ (s / 2 + δ) ≤ (k : ℝ) / 4 := hpower k hkT
  let E0 : Set (LoopPrecedingConfiguration N) := {X | M / 8 < loopPrecedingD X}
  let E1 : Set (LoopPrecedingConfiguration N) :=
    {X | (k : ℝ) / 4 ≤ |loopPrecedingLift X (0 + k) - loopPrecedingLift X 0 - k|}
  let E2 : Set (LoopPrecedingConfiguration N) :=
    {X | (k : ℝ) / 4 ≤ |loopPrecedingLift X (-⌊M⌋ + k) - loopPrecedingLift X (-⌊M⌋) - k|}
  have hsub : (loopExteriorGood N ℓ γ)ᶜ ⊆ (E0 ∪ E1) ∪ E2 := by
    intro X hX
    by_contra hh
    have hh' : X ∉ E0 ∧ X ∉ E1 ∧ X ∉ E2 := by
      simpa only [mem_union, not_or, and_assoc] using hh
    apply hX
    apply loopExteriorGood_of_blocks hM8 X
    · exact le_of_not_gt hh'.1
    · have hp' : |loopPrecedingLift X (0 + k) - loopPrecedingLift X 0 - k| <
          (k : ℝ) / 4 := lt_of_not_ge hh'.2.1
      rwa [loopPrecedingLift_sub_eq_block] at hp'
    · have hm' : |loopPrecedingLift X (-⌊M⌋ + k) - loopPrecedingLift X (-⌊M⌋) - k| <
          (k : ℝ) / 4 := lt_of_not_ge hh'.2.2
      rwa [loopPrecedingLift_sub_eq_block] at hm'
  have h0 : μ E0 ≤ ENNReal.ofReal (A * Real.exp (-d * (M / 8))) :=
    hD hPL P N hN (M / 8) (by linarith)
  have h1 : μ E1 ≤ ENNReal.ofReal (B * Real.exp (-b * (k : ℝ) ^ τ)) := by
    apply (measure_mono (show E1 ⊆ {X | (k : ℝ) ^ (s / 2 + δ) ≤
      |loopPrecedingLift X (0 + k) - loopPrecedingLift X 0 - k|} from
        fun X hX => hpk.trans hX)).trans
    exact hblock hPL n 0 k hk1 hkN
  have h2 : μ E2 ≤ ENNReal.ofReal (B * Real.exp (-b * (k : ℝ) ^ τ)) := by
    apply (measure_mono (show E2 ⊆ {X | (k : ℝ) ^ (s / 2 + δ) ≤
      |loopPrecedingLift X (-⌊M⌋ + k) - loopPrecedingLift X (-⌊M⌋) - k|} from
        fun X hX => hpk.trans hX)).trans
    exact hblock hPL n (-⌊M⌋) k hk1 hkN
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hpowM : M ^ τ ≤ M := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM1 hτ1
  have hkhalf : M / 2 ≤ (k : ℝ) := by linarith
  have hpowk : (1 / 2 : ℝ) ^ τ * M ^ τ ≤ (k : ℝ) ^ τ := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hM0.le]
    apply Real.rpow_le_rpow (by positivity) _ hτ.le
    linarith
  have hdexp : Real.exp (-d * (M / 8)) ≤ Real.exp (-c * M ^ τ) := by
    apply Real.exp_le_exp.mpr
    have hc1 : c ≤ d / 8 := min_le_left _ _
    nlinarith [mul_le_mul_of_nonneg_left hpowM (show 0 ≤ d / 8 by positivity),
      mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hM0.le τ)]
  have hbexp : Real.exp (-b * (k : ℝ) ^ τ) ≤ Real.exp (-c * M ^ τ) := by
    apply Real.exp_le_exp.mpr
    have hc2 : c ≤ b * (1 / 2 : ℝ) ^ τ := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hpowk hb.le,
      mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hM0.le τ)]
  calc
    μ (loopExteriorGood N ℓ γ)ᶜ ≤ μ ((E0 ∪ E1) ∪ E2) := measure_mono hsub
    _ ≤ (μ E0 + μ E1) + μ E2 := (measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (A * Real.exp (-d * (M / 8))) +
        ENNReal.ofReal (B * Real.exp (-b * (k : ℝ) ^ τ)) +
        ENNReal.ofReal (B * Real.exp (-b * (k : ℝ) ^ τ)) :=
      add_le_add (add_le_add h0 h1) h2
    _ ≤ ENNReal.ofReal (A * Real.exp (-c * M ^ τ)) +
        ENNReal.ofReal (B * Real.exp (-c * M ^ τ)) +
        ENNReal.ofReal (B * Real.exp (-c * M ^ τ)) := by
      gcongr
    _ = ENNReal.ofReal ((A + 2 * B) * Real.exp (-c * M ^ τ)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end Internal

end Riesz1

end
