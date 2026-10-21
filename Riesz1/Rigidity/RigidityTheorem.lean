/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.RigidityTheoremCount
public import Riesz1.Auxiliary.RigidityConclusion

/-!
# Near-optimal rigidity with the external inequalities as hypotheses

Assembly of the proof of Theorem 1. All particle numbers and positive
arc scales are included. The constants are chosen before the particle
number, gap index, and arc data.
-/

public section

noncomputable section

open MeasureTheory Filter

namespace Riesz1

/-- The full rigidity conclusion, with the Bakry–Émery criterion `External.BakryEmery` and
the Prékopa–Leindler inequality `External.PrekopaLeindler` as explicit hypotheses. -/
theorem Internal.rigidityConclusion_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    Internal.RigidityConclusion beta s hbeta hs hs1 := by
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  have hm : 0 < min (1 : ℝ) (1 - s / 2) := lt_min zero_lt_one (by linarith)
  refine ⟨min 1 (1 - s / 2) / 2, half_pos hm, ?_⟩
  intro eps heps heps0
  have hepsm : eps / 2 < min 1 (1 - s / 2) := by linarith
  have ha : s / 2 + eps < 1 := by
    have := min_le_right (1 : ℝ) (1 - s / 2)
    linarith
  have hb : 0 ≤ s / 2 + eps / 2 := by linarith
  let delta := eps / (4 * (s + 2))
  have hd : 0 < delta := div_pos heps (by linarith)
  have hda : delta ≤ s / 2 + eps := by
    have he : eps / (4 * (s + 2)) ≤ eps / 2 :=
      div_le_div_of_nonneg_left heps.le (by norm_num) (by linarith)
    dsimp only [delta]
    linarith
  obtain ⟨cg, Cg, hcg, hCg, hgap⟩ :=
    almost_optimal_rigidity_gaps hBE hPL P (half_pos heps) hepsm
  have hrate : eps / 2 / (2 * (s + 2)) = delta := by
    dsimp only [delta]
    rw [div_div]
    congr 1
    ring
  rw [show (parametersExponent P).val = s from rfl, hrate] at hgap
  obtain ⟨B, hB, hselect⟩ := Internal.rigidity_boundary_block_bound
  obtain ⟨cb, Cb, hcb, hCb, hboundary⟩ := boundary_selection_gap_tail
  obtain ⟨K0, hK02, hlarge⟩ := Internal.rigidity_large_scale hs heps ha
  let c := min (cg / 2) (cb / 2)
  have hc : 0 < c := lt_min (half_pos hcg) (half_pos hcb)
  have hccg : c ≤ cg / 2 := min_le_left _ _
  have hccb : c ≤ cb / 2 := min_le_right _ _
  let C := Cg + Cb + 2 * B * Cg ^ (1 / (2 : ℝ)) + Real.exp (c * K0 ^ delta)
  have hsqrt : 0 ≤ B * Cg ^ (1 / (2 : ℝ)) := mul_nonneg hB.le (by positivity)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCgC : Cg ≤ C := by
    dsimp only [C]
    linarith [Real.exp_pos (c * K0 ^ delta)]
  have hsumC : Cb + 2 * B * Cg ^ (1 / (2 : ℝ)) ≤ C := by
    dsimp only [C]
    linarith [Real.exp_pos (c * K0 ^ delta)]
  refine ⟨c, C, hc, hC, ?_⟩
  intro N
  let := (modelWellDefined P N).2.2
  constructor
  · intro i k hk hkN
    have hN : 2 ≤ (N : ℕ) := by omega
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hp : (k : ℝ) ^ (s / 2 + eps / 2) ≤ (k : ℝ) ^ (s / 2 + eps) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
    have he := (hgap N hN i.val).1 k hk (by omega)
    have ht : (gibbsMeasure P N).real {X | (k : ℝ) ^ (s / 2 + eps) ≤
        |blockLength X i.val k - k|} ≤ Cg * Real.exp (-cg * (k : ℝ) ^ delta) :=
      (measureReal_mono fun _ hX => hp.trans hX).trans he
    have htail : (gibbsMeasure P N).real {X | (k : ℝ) ^ (s / 2 + eps) ≤
        |blockLength X i.val k - k|} ≤ C * Real.exp (-c * (k : ℝ) ^ delta) := by
      calc
        _ ≤ Cg * Real.exp (-cg * (k : ℝ) ^ delta) := ht
        _ ≤ Cg * Real.exp (-c * (k : ℝ) ^ delta) :=
          mul_le_mul_of_nonneg_left
            (Internal.rigidity_exp_rate_mono (by linarith : c ≤ cg)
              (Real.rpow_nonneg (by positivity) _)) hCg.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hCgC (Real.exp_pos _).le
    have he := ENNReal.ofReal_le_ofReal htail
    rw [ofReal_measureReal] at he
    exact he
  · intro a ell hell hell4
    let K : ℝ := (N : ℝ) * ell
    have hKpos : 0 < K := mul_pos (by exact_mod_cast N.pos) hell
    have hK4 : K ≤ (N : ℝ) / 4 := by
      have := mul_le_mul_of_nonneg_left hell4 (le_of_lt (show (0 : ℝ) < N by exact_mod_cast N.pos))
      dsimp only [K]
      linarith
    have hcenter : 2 * (N : ℝ) * ell = 2 * K := by dsimp only [K]; ring
    rw [hcenter]
    have ht : (gibbsMeasure P N).real {X | K ^ (s / 2 + eps) ≤ |arcCount a ell X - 2 * K|} ≤
        C * Real.exp (-c * K ^ delta) := by
      by_cases hbig : K0 ≤ K
      · have hK2 : 2 ≤ K := hK02.trans hbig
        have hK1 : 1 ≤ K := by linarith
        have hN : 2 ≤ (N : ℕ) := by
          have : (2 : ℝ) ≤ (N : ℝ) := by linarith
          exact_mod_cast this
        obtain ⟨hlam, hKlam, hT⟩ := hlarge K hbig
        have hblock (k : ℕ) (hk : 1 ≤ k) (hkN : k < (N : ℕ))
            (hKr : K ≤ min (k : ℝ) ((N : ℝ) - k))
            (hr3 : min (k : ℝ) ((N : ℝ) - k) ≤ 3 * K) :
            (gibbsMeasure P N).real {X | K ^ (s / 2 + eps) / 2 ≤
              |blockLength X (precedingLabel a ell X) k - k|} ≤
              B * Cg ^ (1 / (2 : ℝ)) * Real.exp (-c * K ^ delta) := by
          have hcast : ((min k ((N : ℕ) - k) : ℕ) : ℝ) =
              min (k : ℝ) ((N : ℝ) - k) := by
            rw [Nat.cast_min, Nat.cast_sub hkN.le]
          have hg := (hgap N hN 0).2 k hk hkN
          rw [hcast] at hg
          have hh := Internal.rigidity_selected_block_tail P N a ell hKpos.le hKr hr3
            hb hd.le hB.le hCg.le hcg.le hT hg
            (hselect hPL P N hN a ell k (K ^ (s / 2 + eps) / 2))
          exact hh.trans (mul_le_mul_of_nonneg_left
            (Internal.rigidity_exp_rate_mono hccg (Real.rpow_nonneg hKpos.le _)) hsqrt)
        obtain ⟨hp, hpN, hpK, hp3⟩ := plus_index_bounds N hlam hK4 hKlam
        obtain ⟨hm, hmN, hmK, hm3⟩ := minus_index_bounds N hlam hK4 hKlam
        have hgapJ := hboundary hPL P N hN a ell (K ^ (s / 2 + eps) / 2) (by positivity)
        have hpower : K ^ delta ≤ K ^ (s / 2 + eps) :=
          Real.rpow_le_rpow_of_exponent_le hK1 hda
        have hexp : Real.exp (-cb * (K ^ (s / 2 + eps) / 2)) ≤
            Real.exp (-c * K ^ delta) := by
          apply Real.exp_le_exp.mpr
          nlinarith [Real.rpow_nonneg hKpos.le delta]
        have hgapJ' : (gibbsMeasure P N).real
            {X | K ^ (s / 2 + eps) / 2 < gap X (precedingLabel a ell X)} ≤
            Cb * Real.exp (-c * K ^ delta) :=
          hgapJ.trans (mul_le_mul_of_nonneg_left hexp hCb.le)
        have hunion := Internal.rigidity_count_union_bound P N a hell hell4 hlam rfl hKlam
        calc
          _ ≤ Cb * Real.exp (-c * K ^ delta) +
              (B * Cg ^ (1 / (2 : ℝ)) * Real.exp (-c * K ^ delta) +
              B * Cg ^ (1 / (2 : ℝ)) * Real.exp (-c * K ^ delta)) :=
            hunion.trans (add_le_add hgapJ' (add_le_add (hblock _ hp hpN hpK hp3)
              (hblock _ hm hmN hmK hm3)))
          _ = (Cb + 2 * B * Cg ^ (1 / (2 : ℝ))) * Real.exp (-c * K ^ delta) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hsumC (Real.exp_pos _).le
      · have hKK0 : K ≤ K0 := (lt_of_not_ge hbig).le
        have hpow : K ^ delta ≤ K0 ^ delta := Real.rpow_le_rpow hKpos.le hKK0 hd.le
        have hone : 1 ≤ Real.exp (c * K0 ^ delta) * Real.exp (-c * K ^ delta) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp_iff.mpr
          nlinarith
        have hEC : Real.exp (c * K0 ^ delta) ≤ C := by dsimp only [C]; linarith
        calc
          _ ≤ 1 := measureReal_le_one
          _ ≤ Real.exp (c * K0 ^ delta) * Real.exp (-c * K ^ delta) := hone
          _ ≤ _ := mul_le_mul_of_nonneg_right hEC (Real.exp_pos _).le
    have he := ENNReal.ofReal_le_ofReal ht
    rw [ofReal_measureReal] at he
    exact he

/-- Near-optimal rigidity, Theorem 1, with only the Bakry–Émery criterion
`External.BakryEmery` and the Prékopa–Leindler inequality `External.PrekopaLeindler`
as hypotheses. -/
theorem almost_optimal_rigidity_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ModelWellDefined P ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ N : ℕ+,
          (∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
            gibbsMeasure P N {X |
              |(N : ℝ) * (cyclicLift X ((i.val : ℤ) + k) - cyclicLift X i.val) - k| ≥
                (k : ℝ) ^ (s / 2 + eps)} ≤
              ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (eps / (4 * (s + 2)))))) ∧
          (∀ (x : UnitAddCircle) (ell : ℝ), 0 < ell → ell ≤ 1 / 4 →
            gibbsMeasure P N {X |
              |arcCount x ell X - 2 * (N : ℝ) * ell| ≥
                ((N : ℝ) * ell) ^ (s / 2 + eps)} ≤
              ENNReal.ofReal (C * Real.exp (-c * ((N : ℝ) * ell) ^ (eps / (4 * (s + 2)))))) := by
  intro beta s hbeta hs hs1
  exact ⟨modelWellDefined _,
    Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1⟩

end Riesz1

end
