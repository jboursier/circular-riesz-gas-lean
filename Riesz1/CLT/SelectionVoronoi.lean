/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SelectionNearest
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Voronoi cells of the nearest particle

The geometric part of the proof of Corollary 1 of the paper. Let `g`
be an increasing sequence of positions with `g (j + N) = g j + 1`. Shifting all positions by a real
`t` gives the lifts `t + g j`, and the nearest label of these lifts is `nearestLabelOf` of them.

* `mem_cell_iff`: the label is `j` exactly when `t` lies in the half-open cell
  `[-(g j + g (j+1))/2, -(g (j-1) + g j)/2)`.
* `lintegral_nearestLabel_Ioc`: for an `N`-periodic function `c` of the label, integrating
  `c (nearestLabel)` over one period of `t` gives `∑_i c_i · (g (i+1) - g (i-1))/2`. The cell of
  label `i` has length `(g (i+1) - g (i-1))/2`, which is `w_i / N` for the anchored offsets.

The proof unfolds the one-period integral over the labels `j = i + N q`, which is a bijection
`Fin N × ℤ ≃ ℤ`, and then tiles `ℝ` by the unit intervals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace Riesz1

/-! ### Cells -/

/-- The cell of label `j`: the set of shifts `t` for which the lift `t + g j` is nearest to `0`. -/
def cellOf (g : ℤ → ℝ) (j : ℤ) : Set ℝ :=
  Ico (-(g j + g (j + 1)) / 2) (-(g (j - 1) + g j) / 2)

/-- The label of the shifted lifts is `j` exactly on the cell of `j`. -/
lemma mem_cell_iff {N : ℕ} (hN : 0 < N) (g : ℤ → ℝ) (hmono : ∀ j, g j < g (j + 1))
    (hper : ∀ j, g (j + N) = g j + 1) (j : ℤ) (t : ℝ) :
    t ∈ cellOf g j ↔ nearestLabelOf (fun k => t + g k) = j := by
  have hLper : ∀ k, (t + g (k + N)) = (t + g k) + 1 := fun k => by rw [hper k]; ring
  have hLmono : ∀ k, t + g k < t + g (k + 1) := fun k => by linarith [hmono k]
  rw [nearestLabelOf_eq_iff hN (fun k => t + g k) hLper hLmono j]
  simp only [cellOf, mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- Shifting the label by `N q` shifts the cell by `q`. -/
lemma cellOf_add_mul {N : ℕ} (g : ℤ → ℝ) (hper : ∀ j, g (j + N) = g j + 1) (j : ℤ) (q : ℤ) :
    cellOf g (j + (N : ℤ) * q) = (fun t : ℝ => t + (q : ℝ)) ⁻¹' cellOf g j := by
  have e1 : g (j + (N : ℤ) * q) = g j + q := lift_add_mul_eq g hper j q
  have e2 : g (j + (N : ℤ) * q + 1) = g (j + 1) + q := by
    rw [show j + (N : ℤ) * q + 1 = (j + 1) + (N : ℤ) * q by ring]
    exact lift_add_mul_eq g hper (j + 1) q
  have e3 : g (j + (N : ℤ) * q - 1) = g (j - 1) + q := by
    rw [show j + (N : ℤ) * q - 1 = (j - 1) + (N : ℤ) * q by ring]
    exact lift_add_mul_eq g hper (j - 1) q
  ext t
  simp only [cellOf, mem_Ico, mem_preimage, e1, e2, e3]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- The cell of label `j` has length `(g (j+1) - g (j-1)) / 2`. -/
lemma volume_cellOf (g : ℤ → ℝ) (j : ℤ) :
    volume (cellOf g j) = ENNReal.ofReal ((g (j + 1) - g (j - 1)) / 2) := by
  rw [cellOf, Real.volume_Ico]
  congr 1
  ring

/-! ### Tiling the line by unit intervals -/

/-- Summing the one-period parts of a set over its integer translates gives its full length. -/
lemma tsum_volume_inter_preimage_add (E : Set ℝ) (hE : MeasurableSet E) :
    ∑' q : ℤ, volume (Ioc (0 : ℝ) 1 ∩ (fun t : ℝ => t + (q : ℝ)) ⁻¹' E) = volume E := by
  have h1 : ∀ q : ℤ, volume (Ioc (0 : ℝ) 1 ∩ (fun t : ℝ => t + (q : ℝ)) ⁻¹' E) =
      volume (Ioc (q : ℝ) (q + 1) ∩ E) := by
    intro q
    have hset : Ioc (0 : ℝ) 1 ∩ (fun t : ℝ => t + (q : ℝ)) ⁻¹' E =
        (fun t : ℝ => t + (q : ℝ)) ⁻¹' (Ioc (q : ℝ) (q + 1) ∩ E) := by
      ext t
      simp only [mem_inter_iff, mem_preimage, mem_Ioc]
      constructor
      · rintro ⟨⟨ha, hb⟩, hE'⟩
        exact ⟨⟨by linarith, by linarith⟩, hE'⟩
      · rintro ⟨⟨ha, hb⟩, hE'⟩
        exact ⟨⟨by linarith, by linarith⟩, hE'⟩
    rw [hset, measure_preimage_add_right]
  have hdisj : Pairwise (Disjoint on fun q : ℤ => Ioc (q : ℝ) (q + 1) ∩ E) := by
    intro q q' hqq'
    refine Set.disjoint_left.2 fun t ht ht' => ?_
    rcases lt_or_gt_of_ne hqq' with h | h
    · have : (q : ℝ) + 1 ≤ (q' : ℝ) := by exact_mod_cast (show q + 1 ≤ q' by omega)
      linarith [ht.1.2, ht'.1.1]
    · have : (q' : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast (show q' + 1 ≤ q by omega)
      linarith [ht'.1.2, ht.1.1]
  have hU : E = ⋃ q : ℤ, Ioc (q : ℝ) (q + 1) ∩ E := by
    rw [← iUnion_inter, iUnion_Ioc_intCast, univ_inter]
  have h2 : volume E = ∑' q : ℤ, volume (Ioc (q : ℝ) (q + 1) ∩ E) := by
    conv_lhs => rw [hU]
    exact measure_iUnion hdisj fun q => measurableSet_Ioc.inter hE
  simp_rw [h1]
  exact h2.symm

/-! ### Residues modulo the period -/

/-- The bijection `Fin N × ℤ ≃ ℤ` sending `(i, q)` to `i + N q`. -/
def residueEquiv (N : ℕ) (hN : 0 < N) : Fin N × ℤ ≃ ℤ where
  toFun p := (p.1 : ℤ) + (N : ℤ) * p.2
  invFun j := (⟨(j % (N : ℤ)).toNat,
      (Int.toNat_lt (Int.emod_nonneg j (by exact_mod_cast hN.ne'))).mpr
        (Int.emod_lt_of_pos j (by exact_mod_cast hN))⟩, j / (N : ℤ))
  left_inv p := by
    have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    obtain ⟨i, q⟩ := p
    have hi : ((i : ℤ) + (N : ℤ) * q) % (N : ℤ) = (i : ℤ) := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt)]
    have hq : ((i : ℤ) + (N : ℤ) * q) / (N : ℤ) = q := by
      rw [Int.add_mul_ediv_left _ _ hNz, Int.ediv_eq_zero_of_lt (by positivity)
        (by exact_mod_cast i.isLt), zero_add]
    simp only [hi, hq, Int.toNat_natCast, Fin.eta]
  right_inv j := by
    have hNz : (0 : ℤ) < N := by exact_mod_cast hN
    have hdef := Int.emod_def j (N : ℤ)
    simp only
    rw [Int.toNat_of_nonneg (Int.emod_nonneg j hNz.ne')]
    linarith

/-- An `N`-periodic function of the label, summed over all labels, is the sum over one period of
the sums over each residue class. -/
lemma tsum_int_eq_sum_residues {N : ℕ} (hN : 0 < N) (f : ℤ → ℝ≥0∞) :
    ∑' j : ℤ, f j = ∑ i : Fin N, ∑' q : ℤ, f ((i : ℕ) + (N : ℤ) * q) := by
  rw [← (residueEquiv N hN).tsum_eq f, ENNReal.tsum_prod', tsum_fintype]
  rfl

/-! ### The one-period integral of a periodic function of the nearest label -/

/-- A function on the integers that is `N`-periodic is `N q`-periodic for every integer `q`. -/
lemma periodic_add_mul {N : ℕ} {β : Type*} (f : ℤ → β) (hf : ∀ j, f (j + N) = f j)
    (j q : ℤ) : f (j + (N : ℤ) * q) = f j := by
  refine Int.induction_on q ?_ ?_ ?_
  · simp
  · intro i ih
    rw [show j + (N : ℤ) * ((i : ℤ) + 1) = j + (N : ℤ) * i + N by ring, hf, ih]
  · intro i ih
    rw [← ih, ← hf (j + (N : ℤ) * (-(i : ℤ) - 1))]
    congr 1
    ring

/-- **Nearest-particle selection over one period.** Let `g` be an increasing sequence with
`g (j + N) = g j + 1`, and let `c` be a `N`-periodic function of the label. Then integrating
`c (nearestLabel)` over one period of the shift `t` gives `∑_i c_i (g (i+1) - g (i-1)) / 2`. -/
theorem lintegral_nearestLabel_Ioc {N : ℕ} (hN : 0 < N) (g : ℤ → ℝ)
    (hmono : ∀ j, g j < g (j + 1)) (hper : ∀ j, g (j + N) = g j + 1)
    (c : ℤ → ℝ≥0∞) (hc : ∀ j, c (j + N) = c j) :
    ∫⁻ t in Ioc (0 : ℝ) 1, c (nearestLabelOf (fun k => t + g k)) =
      ∑ i : Fin N, c (i : ℕ) * ENNReal.ofReal ((g ((i : ℕ) + 1) - g ((i : ℕ) - 1)) / 2) := by
  have hcell : ∀ t : ℝ, t ∈ cellOf g (nearestLabelOf (fun k => t + g k)) := fun t =>
    (mem_cell_iff hN g hmono hper _ t).mpr rfl
  -- Step 1: split the period into the cells of the labels.
  have hU : Ioc (0 : ℝ) 1 = ⋃ j : ℤ, Ioc (0 : ℝ) 1 ∩ cellOf g j := by
    ext t
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro ht
      exact ⟨nearestLabelOf (fun k => t + g k), ht, hcell t⟩
    · rintro ⟨j, ht, -⟩
      exact ht
  have hcellMeas : ∀ j : ℤ, MeasurableSet (cellOf g j) := fun j => by
    unfold cellOf
    exact measurableSet_Ico
  have hdisj : Pairwise (Disjoint on fun j : ℤ => Ioc (0 : ℝ) 1 ∩ cellOf g j) := by
    intro j k hjk
    refine Set.disjoint_left.2 fun t ht ht' => hjk ?_
    rw [← (mem_cell_iff hN g hmono hper j t).mp ht.2,
      ← (mem_cell_iff hN g hmono hper k t).mp ht'.2]
  have hpart : ∫⁻ t in Ioc (0 : ℝ) 1, c (nearestLabelOf (fun k => t + g k)) =
      ∑' j : ℤ, c j * volume (Ioc (0 : ℝ) 1 ∩ cellOf g j) := by
    conv_lhs => rw [hU]
    rw [lintegral_iUnion (fun j => measurableSet_Ioc.inter (hcellMeas j)) hdisj]
    congr 1
    funext j
    rw [← setLIntegral_const]
    refine setLIntegral_congr_fun (measurableSet_Ioc.inter (hcellMeas j)) fun t ht => ?_
    rw [(mem_cell_iff hN g hmono hper j t).mp ht.2]
  -- Step 2: fold the labels into residue classes, then tile each class by the unit intervals.
  rw [hpart, tsum_int_eq_sum_residues hN]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc ∑' q : ℤ, c ((i : ℕ) + (N : ℤ) * q) * volume (Ioc (0 : ℝ) 1 ∩
          cellOf g ((i : ℕ) + (N : ℤ) * q))
      = ∑' q : ℤ, c (i : ℕ) * volume (Ioc (0 : ℝ) 1 ∩
          (fun t : ℝ => t + (q : ℝ)) ⁻¹' cellOf g (i : ℕ)) := by
        congr 1
        funext q
        rw [periodic_add_mul c hc, cellOf_add_mul g hper (i : ℕ) q]
    _ = c (i : ℕ) * ∑' q : ℤ, volume (Ioc (0 : ℝ) 1 ∩
          (fun t : ℝ => t + (q : ℝ)) ⁻¹' cellOf g (i : ℕ)) := by
        rw [ENNReal.tsum_mul_left]
    _ = c (i : ℕ) * volume (cellOf g (i : ℕ)) := by
        rw [tsum_volume_inter_preimage_add _ (hcellMeas _)]
    _ = c (i : ℕ) * ENNReal.ofReal ((g ((i : ℕ) + 1) - g ((i : ℕ) - 1)) / 2) := by
        rw [volume_cellOf]

end Riesz1

end

end
