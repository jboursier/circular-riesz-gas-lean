/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffEvent
public import Riesz1.Auxiliary.LoopCutoffTail
public import Riesz1.Auxiliary.RigidityConclusion
public import Riesz1.Rigidity.BlockMoments
public import Riesz1.Rigidity.NoExplosionUniform

/-!
# The probability of a nontrivial anchored cutoff

The cutoff part of Lemma 5.8, the probability clause: for every `B₀ > 0` there is `C`
such that `ℙ(η ≠ 1) ≤ C K^{-B₀}` for every `N ≥ 2` and every `ℓ` with `K = Nℓ ≥ 1`.

The proof is a union bound over the pairs `(i, k)` of labels in `I_{2γ}` and over the edges
`(i, i+1)`. Each term is bounded in one of two ways:

* a pair with `|k| < K^ρ`, `ρ = ε / (4 (1 - s/2))`, is a forward block of length `|k|` whose
  length exceeds its mean by a multiple of `K^ε |k|^{s/2-1}`, and the exponential block tail of
  `blockLength_upper_tail` bounds it.
* a pair with `|k| ≥ K^ρ` deviates from `|k|` by more than `|k|^{s/2+τ}`, and the rigidity
  conclusion bounds it.
* an edge deviates from one by more than `K^ε/2`, which the exponential block tail bounds. An edge
  with a gap below `2K^{-ε}` is bounded by the inverse moments of `no_explosion_uniform`.

The rigidity conclusion enters as the explicit hypothesis `Riesz1.Internal.RigidityConclusion`,
so the main result is `Riesz1.Internal.loopCutoff_probability_of_rigidity`.
-/

@[expose] public section

open MeasureTheory Filter

namespace Riesz1

noncomputable section

/-! ## Elementary measure facts -/

/-- A real bound on the Gibbs probability of a set gives an `ENNReal` bound. -/
lemma gibbs_le_ofReal_of_real_le {P : Parameters} {N : ℕ+} {S : Set (Configuration N)} {b : ℝ}
    (h : (gibbsMeasure P N).real S ≤ b) : gibbsMeasure P N S ≤ ENNReal.ofReal b := by
  have := (modelWellDefined P N).2.2
  rw [← ENNReal.ofReal_toReal (measure_ne_top (gibbsMeasure P N) S)]
  exact ENNReal.ofReal_le_ofReal h

/-- A finite sum of equal nonnegative terms. -/
lemma sum_const_ofReal {α : Type*} (I : Finset α) (x : ℝ) :
    ∑ _i ∈ I, ENNReal.ofReal x = ENNReal.ofReal (I.card * x) := by
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

/-- The absolute value of a natural cast of an integer. -/
lemma natAbs_cast_eq_abs (k : ℤ) : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
  have h : ((k.natAbs : ℕ) : ℤ) = |k| := Int.natCast_natAbs k
  have h2 : ((k.natAbs : ℕ) : ℝ) = (((k.natAbs : ℕ) : ℤ) : ℝ) := (Int.cast_natCast _).symm
  rw [h2, h, Int.cast_abs]

/-- The gap of a configuration is the length of the block of one gap. -/
lemma gradLift_gap_eq_blockLength {N : ℕ+} (X : Configuration N) (i : ℤ) :
    (N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i) = blockLength X i 1 := by
  rw [gradLift_val, gradLift_val]
  unfold blockLength
  simp

/-- The exponent of the exponential block tail. -/
lemma blockTail_exponent_pos : 0 < blockMomentExponent := blockMomentExponent_pos

/-! ## Edges -/

/-- The edge event `{2 N (x_{i+1} - x_i) > 2 K^ε}`... more precisely the upper edge failure
`{1 < 2 N (x_{i+1} - x_i) / K^ε}`, bounded by the exponential block tail. -/
lemma edge_up_bound {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hPL : External.PrekopaLeindler) {ε b : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ ℓ : ℝ, 0 < ℓ → 1 ≤ (N : ℝ) * ℓ → ∀ i : ℤ,
      gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N
          {X : Configuration N | 1 < 2 * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)) /
            ((N : ℝ) * ℓ) ^ ε}
        ≤ ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (-b)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exp_neg_rpow_le (c := blockMomentExponent / 2) (θ := ε) (b := b)
    (by linarith [blockTail_exponent_pos]) hε
  refine ⟨3 * C₁, by positivity, fun N hN ℓ hℓ hK i => ?_⟩
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have := (modelWellDefined (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N).2.2
  set K := (N : ℝ) * ℓ with hKdef
  apply gibbs_le_ofReal_of_real_le
  have hsub : {X : Configuration N | 1 < 2 * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)) /
            K ^ ε} ⊆ {X : Configuration N | ((1 : ℕ) : ℝ) * (K ^ ε / 2) < blockLength X i 1} := by
    intro X hX
    simp only [Set.mem_ofPred_eq] at hX ⊢
    rw [gradLift_gap_eq_blockLength] at hX
    have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK0 ε
    rw [lt_div_iff₀ hKε] at hX
    rw [Nat.cast_one, one_mul]
    linarith
  have htail := blockLength_upper_tail hPL ⟨(β, s), hβ, hs, hs1⟩ N hN i 1 one_pos (K ^ ε / 2)
  calc (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N).real
        {X : Configuration N | 1 < 2 * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)) /
            K ^ ε}
      ≤ (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N).real
          {X : Configuration N | ((1 : ℕ) : ℝ) * (K ^ ε / 2) < blockLength X i 1} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ 3 * Real.exp (-blockMomentExponent * (K ^ ε / 2)) := htail
    _ = 3 * Real.exp (-(blockMomentExponent / 2 * K ^ ε)) := by ring_nf
    _ ≤ 3 * (C₁ * K ^ (-b)) := by
        gcongr
        exact h₁ K (by linarith)
    _ = 3 * C₁ * K ^ (-b) := by ring

/-- The lower edge failure `{1 < 2 / (K^ε N (x_{i+1} - x_i))}`, that is a gap below `2 K^{-ε}`,
bounded by the inverse moments of `no_explosion_uniform`. -/
lemma edge_low_bound {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hPL : External.PrekopaLeindler) {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ ℓ : ℝ, 0 < ℓ → 1 ≤ (N : ℝ) * ℓ → ∀ i : ℤ,
      gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N
          {X : Configuration N | 1 < 2 / (((N : ℝ) * ℓ) ^ ε *
              ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)))}
        ≤ ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (-b)) := by
  set q : ℝ := b / ε with hqdef
  have hq : 0 < q := div_pos hb hε
  obtain ⟨Cn, hCn, hno⟩ := no_explosion_uniform (⟨(β, s), hβ, hs, hs1⟩ : Parameters) hq
  refine ⟨Cn * 2 ^ q, by positivity, fun N hN ℓ hℓ hK i => ?_⟩
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have := (modelWellDefined (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N).2.2
  set K := (N : ℝ) * ℓ with hKdef
  set a : ℝ := 2 * K ^ (-ε) with hadef
  have ha : 0 < a := by positivity
  set t : ℝ := a ^ (-q) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos ha _
  set f : Configuration N → ℝ := fun X => gap X i ^ (-q) with hfdef
  obtain ⟨hfi, hfint⟩ := hno hPL N i
  have hfnn : 0 ≤ᵐ[gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N] f :=
    ae_of_all _ fun X => Real.rpow_nonneg (gap_pos X i).le _
  have hintle : ∫ X, f X ∂gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N ≤ Cn := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hfi hfnn
    have h2 : ENNReal.ofReal (∫ X, f X ∂gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N) ≤
        ENNReal.ofReal Cn := by
      rw [h1]
      exact hfint
    exact (ENNReal.ofReal_le_ofReal_iff hCn.le).mp h2
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hfnn hfi t
  have hreal_le : (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N).real {X | t ≤ f X} ≤ Cn / t := by
    rw [le_div_iff₀ ht]
    linarith
  have hinv : 1 / t = a ^ q := by
    rw [htdef, Real.rpow_neg ha.le, one_div, inv_inv]
  have ha_eq : a ^ q = 2 ^ q * K ^ (-b) := by
    rw [hadef, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hK0.le _), ← Real.rpow_mul hK0.le,
      hqdef]
    congr 2
    field_simp
  have hsub : {X : Configuration N | 1 < 2 / (K ^ ε *
      ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)))} ⊆ {X | t ≤ f X} := by
    intro X hX
    simp only [Set.mem_ofPred_eq] at hX ⊢
    have hG : (N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i) = gap X i := by
      unfold gap
      rw [gradLift_val, gradLift_val]
    rw [hG] at hX
    have hG0 := gap_pos X i
    have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK0 ε
    have hpos : 0 < K ^ ε * gap X i := mul_pos hKε hG0
    rw [lt_div_iff₀ hpos] at hX
    have hGa : gap X i ≤ a := by
      rw [hadef, Real.rpow_neg hK0.le]
      have : K ^ ε * gap X i < 2 := by linarith
      have h3 : gap X i < 2 * (K ^ ε)⁻¹ := by
        rw [← div_eq_mul_inv, lt_div_iff₀ hKε]
        linarith
      linarith [le_of_lt h3]
    exact Real.rpow_le_rpow_of_nonpos hG0 hGa (by linarith)
  have hmono := measureReal_mono hsub (measure_ne_top (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N) _)
  apply gibbs_le_ofReal_of_real_le
  calc (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N).real
        {X : Configuration N | 1 < 2 / (K ^ ε *
          ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)))}
      ≤ (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N).real {X | t ≤ f X} := hmono
    _ ≤ Cn / t := hreal_le
    _ = Cn * a ^ q := by rw [div_eq_mul_one_div, hinv, mul_comm]
    _ = Cn * 2 ^ q * K ^ (-b) := by rw [ha_eq]; ring


namespace Internal

/-! ## Pairs -/

/-- The threshold `16^{2/ε}` above which `K^{ε/2} ≥ 16`. -/
def pairThreshold (ε : ℝ) : ℝ := (16 : ℝ) ^ (2 / ε)

/-- The threshold is positive. -/
lemma pairThreshold_pos (ε : ℝ) : 0 < pairThreshold ε :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- Above the threshold, `K^{ε/2} ≥ 16`. -/
lemma pairThreshold_le {ε K : ℝ} (hε : 0 < ε) (hK : pairThreshold ε ≤ K) :
    16 ≤ K ^ (ε / 2) := by
  have h1 : (pairThreshold ε) ^ (ε / 2) ≤ K ^ (ε / 2) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hK (by linarith)
  have h2 : (pairThreshold ε) ^ (ε / 2) = 16 := by
    unfold pairThreshold
    rw [← Real.rpow_mul (by norm_num), show 2 / ε * (ε / 2) = 1 by field_simp]
    simp
  linarith

/-- A block from the label `j` is a block from the label `j` reduced modulo `N`, and the label of
`Fin N` attached to `j` is that residue. -/
lemma blockLength_eq_gradIndex {N : ℕ+} (X : Configuration N) (j : ℤ) (m : ℕ) :
    blockLength X j m = (N : ℝ) * (cyclicLift X ((gradIndex N j).val + m) -
      cyclicLift X ((gradIndex N j).val)) := by
  rw [blockLength_eq_mod, gradIndex_val_cast]

/-- **Pair bound.** The cutoff part of Lemma 5.8, the pair factors. For `K ≥ 16^{2/ε}`
the probability that the pair `(i, i+k)` violates its threshold, with `k ≠ 0` and `2|k| ≤ N`, is
at most `C K^{-b}`. The rigidity input is the explicit hypothesis `hR`. -/
lemma pair_bound_of_rigidity {β s : ℝ} (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hPL : External.PrekopaLeindler) {γ ε τ c_r C_r b : ℝ} (hγ : 0 < γ) (hε : 0 < ε)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hτγ : τ ≤ ε / (4 * γ)) (hc_r : 0 < c_r)
    (hC_r : 0 < C_r)
    (hR : ∀ (N : ℕ+) (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
      gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N {X : Configuration N |
        |(N : ℝ) * (cyclicLift X ((i.val : ℤ) + k) - cyclicLift X i.val) - k| ≥
          (k : ℝ) ^ (s / 2 + τ)} ≤
        ENNReal.ofReal (C_r * Real.exp (-c_r * (k : ℝ) ^ (τ / (4 * (s + 2)))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ ℓ : ℝ, 0 < ℓ → 1 ≤ (N : ℝ) * ℓ →
      pairThreshold ε ≤ (N : ℝ) * ℓ → ∀ i k : ℤ, |k| ≤ loopBound N ℓ γ →
        gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N {X : Configuration N |
            (k ≠ 0 ∧ 2 * |k| ≤ (N : ℤ)) ∧
              1 < 2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
                (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))}
          ≤ ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (-b)) := by
  have h1s2 : 0 < 1 - s / 2 := by linarith
  have h2s : (2 : ℝ) - s ≠ 0 := by intro h; linarith
  set ρ : ℝ := ε / (4 * (1 - s / 2)) with hρdef
  have hρpos : 0 < ρ := div_pos hε (by linarith)
  have hρ : ρ * (1 - s / 2) = ε / 4 := by
    rw [hρdef]
    field_simp
  have hθτ : 0 < τ / (4 * (s + 2)) := div_pos hτ (by linarith)
  obtain ⟨C₁, hC₁, h₁⟩ := exp_neg_rpow_le (c := blockMomentExponent / 2) (θ := 3 * ε / 4)
    (b := b) (by linarith [blockTail_exponent_pos]) (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := exp_neg_rpow_le (c := c_r) (θ := ρ * (τ / (4 * (s + 2)))) (b := b)
    hc_r (mul_pos hρpos hθτ)
  refine ⟨3 * C₁ + C_r * C₂, add_pos (mul_pos (by norm_num) hC₁) (mul_pos hC_r hC₂),
    fun N hN ℓ hℓ hK hK0 i k hkA => ?_⟩
  have hprob := (modelWellDefined (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N).2.2
  set K : ℝ := (N : ℝ) * ℓ with hKdef
  have hK0' : 0 < K := by linarith
  have hKε : 0 < K ^ ε := Real.rpow_pos_of_pos hK0' ε
  have h16 : 16 ≤ K ^ (ε / 2) := pairThreshold_le hε hK0
  have hK3 : 16 ≤ K ^ (3 * ε / 4) :=
    le_trans h16 (Real.rpow_le_rpow_of_exponent_le hK (by linarith))
  have hbnn : 0 ≤ K ^ (-b) := Real.rpow_nonneg hK0'.le _
  by_cases hcond : k ≠ 0 ∧ 2 * |k| ≤ (N : ℤ)
  swap
  · calc gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N _
        ≤ gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N ∅ :=
          measure_mono (fun X hX => absurd hX.1 hcond)
      _ = 0 := measure_empty
      _ ≤ _ := zero_le
  obtain ⟨hk0, hkN⟩ := hcond
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k.natAbs = m := ⟨_, rfl⟩
  have hm1 : 1 ≤ m := by
    rw [← hm]
    exact Int.natAbs_pos.mpr hk0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmR : (m : ℝ) = |(k : ℝ)| := by
    rw [← hm]
    exact natAbs_cast_eq_abs k
  have hmN : 2 * m ≤ (N : ℕ) := by
    rw [Int.abs_eq_natAbs, hm] at hkN
    omega
  have hmhalf : m ≤ (N : ℕ) / 2 := by omega
  -- The defining inequality of the event, after the block reduction.
  have hEsub : ∀ X : Configuration N,
      1 < 2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
        (K ^ ε * |(k : ℝ)| ^ (s / 2)) →
      K ^ ε * (m : ℝ) ^ (s / 2) / 2 < |blockLength X (pairBase i k) m - (m : ℝ)| := by
    intro X hX
    rw [← hmR] at hX
    have hQ : 0 < K ^ ε * (m : ℝ) ^ (s / 2) := mul_pos hKε (Real.rpow_pos_of_pos hmpos _)
    rw [one_lt_div hQ, gradLift_val, gradLift_val] at hX
    have hid := abs_pair_eq_block X i k
    rw [hm] at hid
    rw [← hid]
    linarith
  by_cases hsmall : (m : ℝ) < K ^ ρ
  · -- Small pairs: the forward block exceeds its mean by a multiple of `K^ε m^{s/2-1}`.
    have hW : K ^ (3 * ε / 4) ≤ K ^ ε * (m : ℝ) ^ (s / 2 - 1) := by
      have h1 : (K ^ ρ) ^ (s / 2 - 1) ≤ (m : ℝ) ^ (s / 2 - 1) :=
        Real.rpow_le_rpow_of_nonpos hmpos hsmall.le (by linarith)
      rw [← Real.rpow_mul hK0'.le] at h1
      have h2 : K ^ ε * K ^ (ρ * (s / 2 - 1)) = K ^ (3 * ε / 4) := by
        rw [← Real.rpow_add hK0']
        congr 1
        have e : ρ * (s / 2 - 1) = -(ρ * (1 - s / 2)) := by ring
        rw [e, hρ]
        ring
      calc K ^ (3 * ε / 4) = K ^ ε * K ^ (ρ * (s / 2 - 1)) := h2.symm
        _ ≤ K ^ ε * (m : ℝ) ^ (s / 2 - 1) := mul_le_mul_of_nonneg_left h1 hKε.le
    set W : ℝ := K ^ ε * (m : ℝ) ^ (s / 2 - 1) with hWdef
    have hWge : 2 ≤ W := le_trans (by norm_num) (le_trans hK3 hW)
    have hms : (m : ℝ) ^ (s / 2) = (m : ℝ) ^ (s / 2 - 1) * m := by
      rw [← Real.rpow_add_one (ne_of_gt hmpos)]
      congr 1
      ring
    have hQW : K ^ ε * (m : ℝ) ^ (s / 2) = W * m := by
      rw [hms, hWdef]
      ring
    have hWm : 2 * (m : ℝ) ≤ W * m := by nlinarith
    have hBsub : {X : Configuration N |
        (k ≠ 0 ∧ 2 * |k| ≤ (N : ℤ)) ∧
          1 < 2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
            (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))} ⊆
        {X : Configuration N | ((m : ℕ) : ℝ) * (1 + W / 2) < blockLength X (pairBase i k) m} := by
      intro X hX
      have hX' := hEsub X hX.2
      rw [hQW] at hX'
      have hpos := blockLength_pos X (pairBase i k) (L := m) (by omega)
      simp only [Set.mem_ofPred_eq]
      rcases lt_abs.mp hX' with h | h
      · linarith
      · nlinarith
    have htail := blockLength_upper_tail hPL ⟨(β, s), hβ, hs, hs1⟩ N hN (pairBase i k) m
      (by omega) (1 + W / 2)
    have hu : K ^ (3 * ε / 4) / 2 ≤ 1 + W / 2 := by linarith
    have hexp : Real.exp (-blockMomentExponent * (1 + W / 2)) ≤
        Real.exp (-(blockMomentExponent / 2 * K ^ (3 * ε / 4))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hu blockTail_exponent_pos.le
      linarith
    have hC := h₁ K hK
    apply gibbs_le_ofReal_of_real_le
    calc (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N).real {X : Configuration N |
          (k ≠ 0 ∧ 2 * |k| ≤ (N : ℤ)) ∧
            1 < 2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
              (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))}
        ≤ (gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N).real {X : Configuration N |
            ((m : ℕ) : ℝ) * (1 + W / 2) < blockLength X (pairBase i k) m} :=
          measureReal_mono hBsub (measure_ne_top _ _)
      _ ≤ 3 * Real.exp (-blockMomentExponent * (1 + W / 2)) := htail
      _ ≤ 3 * Real.exp (-(blockMomentExponent / 2 * K ^ (3 * ε / 4))) := by gcongr
      _ ≤ 3 * (C₁ * K ^ (-b)) := by gcongr
      _ ≤ (3 * C₁ + C_r * C₂) * K ^ (-b) := by
          have e : (3 * C₁ + C_r * C₂) * K ^ (-b) = 3 * (C₁ * K ^ (-b)) + C_r * (C₂ * K ^ (-b)) := by
            ring
          rw [e]
          exact le_add_of_nonneg_right (mul_nonneg hC_r.le (mul_nonneg hC₂.le hbnn))
  · -- Large pairs: the rigidity conclusion at the reduced label.
    have hsmall' : K ^ ρ ≤ (m : ℝ) := not_lt.mp hsmall
    have hmK : (m : ℝ) ≤ 8 * K ^ (2 * γ) := by
      rw [Int.abs_eq_natAbs, hm] at hkA
      have h2 : ((loopBound N ℓ γ : ℤ) : ℝ) ≤ 8 * gradM N ℓ (2 * γ) := by
        unfold loopBound
        exact Int.floor_le _
      have h3 : (m : ℝ) ≤ ((loopBound N ℓ γ : ℤ) : ℝ) := by exact_mod_cast hkA
      have h4 : gradM N ℓ (2 * γ) = K ^ (2 * γ) := by
        unfold gradM
        rfl
      linarith
    have hτK : (m : ℝ) ^ τ ≤ K ^ ε / 2 := by
      have e1 : (m : ℝ) ^ τ ≤ (8 * K ^ (2 * γ)) ^ τ := Real.rpow_le_rpow hmpos.le hmK hτ.le
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hK0'.le _),
        ← Real.rpow_mul hK0'.le] at e1
      have e2 : (8 : ℝ) ^ τ ≤ 8 := by
        calc (8 : ℝ) ^ τ ≤ 8 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hτ1
          _ = 8 := Real.rpow_one 8
      have hγτ : 2 * γ * τ ≤ ε / 2 := by
        have h := mul_le_mul_of_nonneg_left hτγ (by linarith : (0 : ℝ) ≤ 2 * γ)
        have e : 2 * γ * (ε / (4 * γ)) = ε / 2 := by
          field_simp
          ring
        linarith
      have e3 : K ^ (2 * γ * τ) ≤ K ^ (ε / 2) :=
        Real.rpow_le_rpow_of_exponent_le hK hγτ
      have e4 : K ^ ε = K ^ (ε / 2) * K ^ (ε / 2) := by
        rw [← Real.rpow_add hK0']
        congr 1
        ring
      have hP : 0 ≤ K ^ (2 * γ * τ) := Real.rpow_nonneg hK0'.le _
      have s1 : (8 : ℝ) ^ τ * K ^ (2 * γ * τ) ≤ 8 * K ^ (ε / 2) :=
        mul_le_mul e2 e3 hP (by norm_num)
      have s2 : 8 * K ^ (ε / 2) ≤ K ^ ε / 2 := by
        rw [e4]
        nlinarith [h16]
      linarith
    have hrig := hR N (gradIndex N (pairBase i k)) m hm1 hmhalf
    have hsub : {X : Configuration N |
        (k ≠ 0 ∧ 2 * |k| ≤ (N : ℤ)) ∧
          1 < 2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
            (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))} ⊆
        {X : Configuration N |
          |(N : ℝ) * (cyclicLift X ((gradIndex N (pairBase i k)).val + m) -
              cyclicLift X ((gradIndex N (pairBase i k)).val)) - m| ≥
            (m : ℝ) ^ (s / 2 + τ)} := by
      intro X hX
      have hX' := hEsub X hX.2
      have hpow : (m : ℝ) ^ (s / 2 + τ) ≤ K ^ ε * (m : ℝ) ^ (s / 2) / 2 := by
        rw [Real.rpow_add hmpos]
        have hms0 : 0 ≤ (m : ℝ) ^ (s / 2) := Real.rpow_nonneg hmpos.le _
        linarith [mul_le_mul_of_nonneg_left hτK hms0]
      have hid := blockLength_eq_gradIndex X (pairBase i k) m
      simp only [Set.mem_ofPred_eq, ge_iff_le]
      rw [← hid]
      linarith
    have hθ : K ^ (ρ * (τ / (4 * (s + 2)))) ≤ (m : ℝ) ^ (τ / (4 * (s + 2))) := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg hK0'.le ρ) hsmall' hθτ.le
      rwa [← Real.rpow_mul hK0'.le] at h
    have hexp2 : Real.exp (-c_r * (m : ℝ) ^ (τ / (4 * (s + 2)))) ≤
        Real.exp (-(c_r * K ^ (ρ * (τ / (4 * (s + 2)))))) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hθ hc_r.le
      linarith
    have hC := h₂ K hK
    calc gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N {X : Configuration N |
            (k ≠ 0 ∧ 2 * |k| ≤ (N : ℤ)) ∧
              1 < 2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
                (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))}
        ≤ gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N {X : Configuration N |
            |(N : ℝ) * (cyclicLift X ((gradIndex N (pairBase i k)).val + m) -
                cyclicLift X ((gradIndex N (pairBase i k)).val)) - m| ≥
              (m : ℝ) ^ (s / 2 + τ)} := measure_mono hsub
      _ ≤ ENNReal.ofReal (C_r * Real.exp (-c_r * (m : ℝ) ^ (τ / (4 * (s + 2))))) := hrig
      _ ≤ ENNReal.ofReal (C_r * (C₂ * K ^ (-b))) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hexp2.trans hC) hC_r.le)
      _ ≤ ENNReal.ofReal ((3 * C₁ + C_r * C₂) * K ^ (-b)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e : (3 * C₁ + C_r * C₂) * K ^ (-b) = 3 * (C₁ * K ^ (-b)) + C_r * (C₂ * K ^ (-b)) := by
            ring
          rw [e]
          exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (mul_nonneg hC₁.le hbnn))

end Internal

/-! ## The probability bound -/

namespace Internal

/-- **Probability of a nontrivial anchored cutoff**, the cutoff part of Lemma 5.8, the
probability clause. For every `B₀ > 0` there is `C` with `ℙ(η ≠ 1) ≤ C K^{-B₀}` for all `N ≥ 2`
and all `ℓ` with `K = Nℓ ≥ 1`. The rigidity conclusion is the explicit hypothesis `hRig`. The
statement is the paper's, with `α` omitted, since `η` does not depend on
it. -/
theorem loopCutoff_probability_of_rigidity (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hPL : External.PrekopaLeindler) (hRig : RigidityConclusion β s hβ hs hs1)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) (hε1 : ε < min (1 / 8) ((1 - s / 2) / 8))
    (B₀ : ℝ) (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N {X : Configuration N | loopCutoff s γ ε N ℓ X.val ≠ 1} ≤
        ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (-B₀)) := by
  have hε8 : ε < 1 / 8 := lt_of_lt_of_le hε1 (min_le_left _ _)
  have hγ0 : 0 < γ := by linarith
  -- The rigidity constants at a small exponent `τ`.
  unfold RigidityConclusion at hRig
  dsimp only at hRig
  obtain ⟨eps0, heps0, hR⟩ := hRig
  have hτpos : 0 < min (eps0 / 2) (ε / (4 * γ)) := lt_min (half_pos heps0) (div_pos hε (by linarith))
  have hτlt : min (eps0 / 2) (ε / (4 * γ)) < eps0 :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self heps0)
  obtain ⟨c_r, C_r, hc_r, hC_r, hRN⟩ := hR _ hτpos hτlt
  set τ : ℝ := min (eps0 / 2) (ε / (4 * γ)) with hτdef
  have hτγ : τ ≤ ε / (4 * γ) := min_le_right _ _
  have hτ1 : τ ≤ 1 := by
    have h1 : ε / (4 * γ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      nlinarith
    linarith
  -- The pair and edge bounds.
  have hb : 0 < B₀ + 4 * γ + 1 := by linarith
  obtain ⟨Cp, hCp, hpair⟩ := pair_bound_of_rigidity hβ hs hs1 hPL (γ := γ) (ε := ε) (τ := τ) (c_r := c_r)
    (C_r := C_r) (b := B₀ + 4 * γ + 1) hγ0 hε hτpos hτ1 hτγ hc_r hC_r
    (fun N i k h1 h2 => (hRN N).1 i k h1 h2)
  obtain ⟨CU, hCU, hup⟩ := edge_up_bound hβ hs hs1 hPL (ε := ε) (b := B₀ + 4 * γ + 1) hε
  obtain ⟨CL, hCL, hlow⟩ := edge_low_bound hβ hs hs1 hPL (ε := ε) (b := B₀ + 4 * γ + 1) hε hb
  have hK0pos : 0 < pairThreshold ε := pairThreshold_pos ε
  refine ⟨289 * Cp + 17 * (CU + CL) + pairThreshold ε ^ B₀,
    add_pos (add_pos (mul_pos (by norm_num) hCp) (mul_pos (by norm_num) (add_pos hCU hCL)))
      (Real.rpow_pos_of_pos hK0pos _), ?_⟩
  intro N hN ℓ hℓ hℓ1 hK
  set K : ℝ := (N : ℝ) * ℓ with hKdef
  have hK0 : 0 < K := by linarith
  have hprob := (modelWellDefined (⟨(β, s), hβ, hs, hs1⟩ : Parameters) N).2.2
  set μ := gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N with hμdef
  by_cases hthr : pairThreshold ε ≤ K
  · -- The main case: a union bound over the pairs and the edges of the window.
    set A : ℤ := loopBound N ℓ γ with hAdef
    set I : Finset ℤ := Finset.Icc (-A) A with hIdef
    set Ep : ℤ → ℤ → Set (Configuration N) := fun i k => {X : Configuration N |
        (k ≠ 0 ∧ 2 * |k| ≤ (N : ℤ)) ∧
          1 < 2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
            (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))} with hEpdef
    set Eu : ℤ → Set (Configuration N) := fun i => {X : Configuration N |
        1 < 2 * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)) / ((N : ℝ) * ℓ) ^ ε}
      with hEudef
    set El : ℤ → Set (Configuration N) := fun i => {X : Configuration N |
        1 < 2 / (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)))}
      with hEldef
    have hIA : ∀ j : ℤ, j ∈ gradLabels N ℓ (2 * γ) → j ∈ I := by
      intro j hj
      rw [hIdef, Finset.mem_Icc]
      exact abs_le.mp (abs_le_loopBound_of_mem hℓ hj)
    have hIk : ∀ k : ℤ, |k| ≤ A → k ∈ I := by
      intro k hk
      rw [hIdef, Finset.mem_Icc]
      exact abs_le.mp hk
    have hsub : {X : Configuration N | loopCutoff s γ ε N ℓ X.val ≠ 1} ⊆
        ((⋃ i ∈ I, ⋃ k ∈ I, Ep i k) ∪ (⋃ i ∈ I, Eu i)) ∪ (⋃ i ∈ I, El i) := by
      intro X hX
      have hX1 : loopCutoff s γ ε N ℓ X.val ≠ 1 := hX
      rcases exists_gt_one_of_loopCutoff_ne_one s γ ε ℓ X.val hX1 with
        ⟨i, hi, k, hk, hk0, hw, hgt⟩ | ⟨i, hi, hw, hgt⟩
      · have hkN : 2 * |k| ≤ (N : ℤ) := by
          obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
          rcases abs_cases k with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> omega
        have hkA : |k| ≤ A := abs_le_loopBound_of_window hℓ hi hw hkN
        left
        left
        simp only [Set.mem_iUnion]
        exact ⟨i, hIA i hi, k, hIk k hkA, ⟨⟨hk0, hkN⟩, hgt⟩⟩
      · rcases hgt with hgt | hgt
        · left
          right
          simp only [Set.mem_iUnion]
          exact ⟨i, hIA i hi, hgt⟩
        · right
          simp only [Set.mem_iUnion]
          exact ⟨i, hIA i hi, hgt⟩
    -- The three families, bounded term by term.
    have hsumA : μ (⋃ i ∈ I, ⋃ k ∈ I, Ep i k) ≤
        ∑ _i ∈ I, ∑ _k ∈ I, ENNReal.ofReal (Cp * K ^ (-(B₀ + 4 * γ + 1))) := by
      refine (measure_biUnion_finset_le I _).trans (Finset.sum_le_sum fun i hi => ?_)
      refine (measure_biUnion_finset_le I _).trans (Finset.sum_le_sum fun k hk => ?_)
      have hkA : |k| ≤ A := abs_le.mpr (Finset.mem_Icc.mp hk)
      exact hpair N hN ℓ hℓ hK hthr i k hkA
    have hsumB : μ (⋃ i ∈ I, Eu i) ≤
        ∑ _i ∈ I, ENNReal.ofReal (CU * K ^ (-(B₀ + 4 * γ + 1))) := by
      refine (measure_biUnion_finset_le I _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact hup N hN ℓ hℓ hK i
    have hsumC : μ (⋃ i ∈ I, El i) ≤
        ∑ _i ∈ I, ENNReal.ofReal (CL * K ^ (-(B₀ + 4 * γ + 1))) := by
      refine (measure_biUnion_finset_le I _).trans (Finset.sum_le_sum fun i _ => ?_)
      exact hlow N hN ℓ hℓ hK i
    -- The cardinality of the window: `|I| = 2A + 1 ≤ 17 K^{2γ}`.
    have hA0 : (0 : ℤ) ≤ A := by
      rw [hAdef, loopBound]
      apply Int.floor_nonneg.mpr
      have := gradM_nonneg (N := N) (γ := 2 * γ) hℓ
      linarith
    have hcardZ : ((I.card : ℕ) : ℤ) = 2 * A + 1 := by
      rw [hIdef, Int.card_Icc]
      omega
    have hcardR : (I.card : ℝ) = 2 * (A : ℝ) + 1 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hcardZ
      push_cast at this
      linarith
    have hA8 : (A : ℝ) ≤ 8 * K ^ (2 * γ) := by
      have h := Int.floor_le (8 * gradM N ℓ (2 * γ))
      have e : gradM N ℓ (2 * γ) = K ^ (2 * γ) := by
        unfold gradM
        rfl
      rw [e] at h
      rw [hAdef, loopBound]
      exact h
    have hM1 : 1 ≤ K ^ (2 * γ) := Real.one_le_rpow hK (by linarith)
    have hcI0 : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg _
    have hcI17 : (I.card : ℝ) ≤ 17 * K ^ (2 * γ) := by
      rw [hcardR]
      linarith
    have hq0 : 0 ≤ K ^ (-(B₀ + 4 * γ + 1)) := Real.rpow_nonneg hK0.le _
    have hMM : K ^ (2 * γ) * K ^ (2 * γ) * K ^ (-(B₀ + 4 * γ + 1)) = K ^ (-B₀ - 1) := by
      rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
      congr 1
      ring
    have hMq : K ^ (2 * γ) * K ^ (-(B₀ + 4 * γ + 1)) = K ^ (-B₀ - 2 * γ - 1) := by
      rw [← Real.rpow_add hK0]
      congr 1
      ring
    have hle1 : K ^ (-B₀ - 1) ≤ K ^ (-B₀) :=
      Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    have hle2 : K ^ (-B₀ - 2 * γ - 1) ≤ K ^ (-B₀) :=
      Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    have hcc : (I.card : ℝ) * (I.card : ℝ) ≤ 289 * (K ^ (2 * γ) * K ^ (2 * γ)) := by
      calc (I.card : ℝ) * (I.card : ℝ) ≤ (17 * K ^ (2 * γ)) * (17 * K ^ (2 * γ)) :=
            mul_le_mul hcI17 hcI17 hcI0 (by linarith)
        _ = 289 * (K ^ (2 * γ) * K ^ (2 * γ)) := by ring
    have key1 : (I.card : ℝ) * ((I.card : ℝ) * (Cp * K ^ (-(B₀ + 4 * γ + 1)))) ≤
        289 * Cp * K ^ (-B₀) := by
      calc (I.card : ℝ) * ((I.card : ℝ) * (Cp * K ^ (-(B₀ + 4 * γ + 1))))
          = ((I.card : ℝ) * (I.card : ℝ)) * (Cp * K ^ (-(B₀ + 4 * γ + 1))) := by ring
        _ ≤ (289 * (K ^ (2 * γ) * K ^ (2 * γ))) * (Cp * K ^ (-(B₀ + 4 * γ + 1))) :=
            mul_le_mul_of_nonneg_right hcc (mul_nonneg hCp.le hq0)
        _ = 289 * Cp * (K ^ (2 * γ) * K ^ (2 * γ) * K ^ (-(B₀ + 4 * γ + 1))) := by ring
        _ = 289 * Cp * K ^ (-B₀ - 1) := by rw [hMM]
        _ ≤ 289 * Cp * K ^ (-B₀) := mul_le_mul_of_nonneg_left hle1 (by linarith)
    have key2 : (I.card : ℝ) * (CU * K ^ (-(B₀ + 4 * γ + 1))) +
        (I.card : ℝ) * (CL * K ^ (-(B₀ + 4 * γ + 1))) ≤ 17 * (CU + CL) * K ^ (-B₀) := by
      calc (I.card : ℝ) * (CU * K ^ (-(B₀ + 4 * γ + 1))) +
            (I.card : ℝ) * (CL * K ^ (-(B₀ + 4 * γ + 1)))
          = (I.card : ℝ) * ((CU + CL) * K ^ (-(B₀ + 4 * γ + 1))) := by ring
        _ ≤ (17 * K ^ (2 * γ)) * ((CU + CL) * K ^ (-(B₀ + 4 * γ + 1))) :=
            mul_le_mul_of_nonneg_right hcI17 (mul_nonneg (by linarith) hq0)
        _ = 17 * (CU + CL) * (K ^ (2 * γ) * K ^ (-(B₀ + 4 * γ + 1))) := by ring
        _ = 17 * (CU + CL) * K ^ (-B₀ - 2 * γ - 1) := by rw [hMq]
        _ ≤ 17 * (CU + CL) * K ^ (-B₀) := mul_le_mul_of_nonneg_left hle2 (by linarith)
    -- Assemble the union bound.
    have nA : 0 ≤ (I.card : ℝ) * ((I.card : ℝ) * (Cp * K ^ (-(B₀ + 4 * γ + 1)))) :=
      mul_nonneg hcI0 (mul_nonneg hcI0 (mul_nonneg hCp.le hq0))
    have nB : 0 ≤ (I.card : ℝ) * (CU * K ^ (-(B₀ + 4 * γ + 1))) :=
      mul_nonneg hcI0 (mul_nonneg hCU.le hq0)
    have nC : 0 ≤ (I.card : ℝ) * (CL * K ^ (-(B₀ + 4 * γ + 1))) :=
      mul_nonneg hcI0 (mul_nonneg hCL.le hq0)
    have hfinal : μ {X : Configuration N | loopCutoff s γ ε N ℓ X.val ≠ 1} ≤
        ENNReal.ofReal ((I.card : ℝ) * ((I.card : ℝ) * (Cp * K ^ (-(B₀ + 4 * γ + 1)))) +
          (I.card : ℝ) * (CU * K ^ (-(B₀ + 4 * γ + 1))) +
          (I.card : ℝ) * (CL * K ^ (-(B₀ + 4 * γ + 1)))) := by
      have hsum2 : ∀ (c : ℝ), 0 ≤ c → ∑ _i ∈ I, ∑ _k ∈ I, ENNReal.ofReal c =
          ENNReal.ofReal ((I.card : ℝ) * ((I.card : ℝ) * c)) := fun c hc => by
        simp only [sum_const_ofReal]
      calc μ {X : Configuration N | loopCutoff s γ ε N ℓ X.val ≠ 1}
          ≤ μ ((((⋃ i ∈ I, ⋃ k ∈ I, Ep i k) ∪ (⋃ i ∈ I, Eu i)) ∪ (⋃ i ∈ I, El i))) :=
            measure_mono hsub
        _ ≤ μ ((⋃ i ∈ I, ⋃ k ∈ I, Ep i k) ∪ (⋃ i ∈ I, Eu i)) + μ (⋃ i ∈ I, El i) :=
            measure_union_le _ _
        _ ≤ (μ (⋃ i ∈ I, ⋃ k ∈ I, Ep i k) + μ (⋃ i ∈ I, Eu i)) + μ (⋃ i ∈ I, El i) :=
            add_le_add_left (measure_union_le _ _) _
        _ ≤ (∑ _i ∈ I, ∑ _k ∈ I, ENNReal.ofReal (Cp * K ^ (-(B₀ + 4 * γ + 1)))) +
              (∑ _i ∈ I, ENNReal.ofReal (CU * K ^ (-(B₀ + 4 * γ + 1)))) +
              (∑ _i ∈ I, ENNReal.ofReal (CL * K ^ (-(B₀ + 4 * γ + 1)))) :=
            add_le_add (add_le_add hsumA hsumB) hsumC
        _ = ENNReal.ofReal ((I.card : ℝ) * ((I.card : ℝ) * (Cp * K ^ (-(B₀ + 4 * γ + 1))))) +
              ENNReal.ofReal ((I.card : ℝ) * (CU * K ^ (-(B₀ + 4 * γ + 1)))) +
              ENNReal.ofReal ((I.card : ℝ) * (CL * K ^ (-(B₀ + 4 * γ + 1)))) := by
            rw [hsum2 _ (mul_nonneg hCp.le hq0), sum_const_ofReal, sum_const_ofReal]
        _ = ENNReal.ofReal ((I.card : ℝ) * ((I.card : ℝ) * (Cp * K ^ (-(B₀ + 4 * γ + 1)))) +
              (I.card : ℝ) * (CU * K ^ (-(B₀ + 4 * γ + 1))) +
              (I.card : ℝ) * (CL * K ^ (-(B₀ + 4 * γ + 1)))) := by
            rw [ENNReal.ofReal_add (add_nonneg nA nB) nC, ENNReal.ofReal_add nA nB]
    refine hfinal.trans (ENNReal.ofReal_le_ofReal ?_)
    have hC : (289 * Cp + 17 * (CU + CL) + pairThreshold ε ^ B₀) * K ^ (-B₀) =
        289 * Cp * K ^ (-B₀) + 17 * (CU + CL) * K ^ (-B₀) +
          pairThreshold ε ^ B₀ * K ^ (-B₀) := by ring
    rw [hC]
    have hK3 : 0 ≤ pairThreshold ε ^ B₀ * K ^ (-B₀) :=
      mul_nonneg (Real.rpow_nonneg hK0pos.le _) (Real.rpow_nonneg hK0.le _)
    linarith [key1, key2]
  · -- The trivial case `K < 16^{2/ε}`: the probability is at most one, and `C K^{-B₀} ≥ 1`.
    have hKle : K ≤ pairThreshold ε := le_of_lt (not_le.mp hthr)
    have h1 : pairThreshold ε ^ (-B₀) ≤ K ^ (-B₀) :=
      Real.rpow_le_rpow_of_nonpos hK0 hKle (by linarith)
    have hC1 : 0 ≤ 289 * Cp + 17 * (CU + CL) := by linarith
    have h2 : (1 : ℝ) ≤ (289 * Cp + 17 * (CU + CL) + pairThreshold ε ^ B₀) * K ^ (-B₀) := by
      calc (1 : ℝ) = pairThreshold ε ^ B₀ * pairThreshold ε ^ (-B₀) := by
            rw [← Real.rpow_add hK0pos]
            simp
        _ ≤ pairThreshold ε ^ B₀ * K ^ (-B₀) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hK0pos.le _)
        _ ≤ (289 * Cp + 17 * (CU + CL) + pairThreshold ε ^ B₀) * K ^ (-B₀) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hK0.le _)
    exact prob_le_one.trans (ENNReal.one_le_ofReal.mpr h2)

end Internal

end

end Riesz1

