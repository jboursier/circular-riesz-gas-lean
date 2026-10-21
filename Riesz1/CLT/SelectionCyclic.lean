/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SelectionNearest
public import Riesz1.CLT.SelectionVoronoi
public import Riesz1.Rigidity.GapLawSymmetry

/-!
# Cyclic relabelling of the gap vector

Part of the proof of Corollary 1, the cyclic step of the selection argument. A gap vector
is a function `Fin N → ℝ`. Its periodic extension `gapOf h j` reads the entry `j mod N`, and the
cyclic relabelling `shiftFin N i h` starts the period at the integer label `i`.

The gap law is invariant under every cyclic relabelling (`map_shiftFin_gibbsMeasure`), so the
selection weight `w_i` times `F_i` has the same expectation for every label `i`
(`lintegral_shift_gapVector`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace Riesz1

variable {N : ℕ+}

/-! ### The periodic extension of a gap vector -/

/-- The index of the period containing the integer label `j`. -/
def modFin (N : ℕ+) (j : ℤ) : Fin (N : ℕ) :=
  ⟨(j % (N : ℕ)).toNat, (Int.toNat_lt (Int.emod_nonneg j
      (by exact_mod_cast N.ne_zero))).mpr (Int.emod_lt_of_pos j (by exact_mod_cast N.pos))⟩

/-- The periodic extension of a gap vector: `gapOf h j = h (j mod N)`. -/
def gapOf (h : Fin (N : ℕ) → ℝ) (j : ℤ) : ℝ :=
  h (modFin N j)

lemma modFin_coe (j : ℤ) : ((modFin N j : ℕ) : ℤ) = j % (N : ℕ) := by
  unfold modFin
  exact Int.toNat_of_nonneg (Int.emod_nonneg j (by exact_mod_cast N.ne_zero))

lemma modFin_add_N (j : ℤ) : modFin N (j + (N : ℕ)) = modFin N j := by
  apply Fin.ext
  have h3 : ((modFin N (j + (N : ℕ)) : ℕ) : ℤ) = ((modFin N j : ℕ) : ℤ) := by
    rw [modFin_coe, modFin_coe, show (j : ℤ) + (N : ℕ) = j + (N : ℤ) * 1 by ring,
      Int.add_mul_emod_self_left]
  exact_mod_cast h3

lemma gapOf_add_N (h : Fin (N : ℕ) → ℝ) (j : ℤ) : gapOf h (j + (N : ℕ)) = gapOf h j := by
  unfold gapOf
  rw [modFin_add_N]

lemma gapOf_coe (h : Fin (N : ℕ) → ℝ) (k : Fin (N : ℕ)) : gapOf h (k : ℕ) = h k := by
  have hk : ((modFin N (k : ℕ) : ℕ) : ℤ) = (k : ℕ) := by
    rw [modFin_coe]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast k.isLt)
  have hfin : modFin N (k : ℕ) = k := Fin.ext (by exact_mod_cast hk)
  unfold gapOf
  rw [hfin]

/-- The gap of a configuration is the periodic extension of its gap vector. -/
lemma gap_eq_gapOf_gapVector (X : Configuration N) (j : ℤ) :
    gap X j = gapOf (gapVector X) j := by
  have hper : ∀ j : ℤ, gap X (j + (N : ℕ)) = gap X j := fun j => gap_add_N X j
  have hdecomp : j % (N : ℕ) + (N : ℤ) * (j / (N : ℕ)) = j := by
    have := Int.emod_def j (N : ℕ)
    linarith
  have h1 : gap X (j % (N : ℕ)) = gap X j := by
    have := periodic_add_mul (fun m => gap X m) hper (j % (N : ℕ)) (j / (N : ℕ))
    rw [hdecomp] at this
    exact this.symm
  rw [← h1]
  show gap X (j % (N : ℕ)) = gap X ((modFin N j : ℕ) : ℤ)
  rw [modFin_coe]

/-! ### Cyclic relabelling -/

/-- The gap vector relabelled to start at the integer label `i`: `(shiftFin N i h) k = h (i + k)`. -/
def shiftFin (N : ℕ+) (i : ℤ) (h : Fin (N : ℕ) → ℝ) : Fin (N : ℕ) → ℝ :=
  fun k => gapOf h (i + (k : ℕ))

lemma measurable_shiftFin (i : ℤ) : Measurable (shiftFin N i) := by
  refine Measurable.of_eval fun k => ?_
  show Measurable fun h : Fin (N : ℕ) → ℝ => h (modFin N (i + (k : ℕ)))
  exact measurable_pi_apply _

lemma gapOf_shiftFin (i j : ℤ) (h : Fin (N : ℕ) → ℝ) :
    gapOf (shiftFin N i h) j = gapOf h (i + j) := by
  have hdecomp : gapOf h (i + j) = gapOf h (i + j % (N : ℕ)) := by
    have := periodic_add_mul (fun m => gapOf h m) (fun m => gapOf_add_N h m)
      (i + j % (N : ℕ)) (j / (N : ℕ))
    have hdecomp' : i + j % (N : ℕ) + (N : ℤ) * (j / (N : ℕ)) = i + j := by
      have := Int.emod_def j (N : ℕ)
      linarith
    rw [hdecomp'] at this
    exact this
  rw [hdecomp]
  show gapOf h (i + ((modFin N j : ℕ) : ℤ)) = gapOf h (i + j % (N : ℕ))
  rw [modFin_coe]

/-! ### Relabelled gap vectors and the selection weights -/

/-- Relabelling by zero is the identity. -/
lemma shiftFin_zero (h : Fin (N : ℕ) → ℝ) : shiftFin N 0 h = h := by
  funext k
  show gapOf h (0 + (k : ℕ)) = h k
  rw [zero_add]
  exact gapOf_coe h k

/-- The relabelled gap vector of a configuration is the gap vector starting at label `i`. -/
lemma gapFrom_eq_shiftFin (X : Configuration N) (i : ℤ) :
    gapFrom X i = shiftFin N i (gapVector X) := by
  funext k
  unfold gapFrom shiftFin
  rw [gap_eq_gapOf_gapVector]

/-- The selection weight of a configuration in terms of its gap vector. -/
lemma selectionWeight_eq_gapOf (X : Configuration N) (i : ℤ) :
    selectionWeight X i = (gapOf (gapVector X) (i - 1) + gapOf (gapVector X) i) / 2 := by
  unfold selectionWeight
  rw [gap_eq_gapOf_gapVector, gap_eq_gapOf_gapVector]

/-- The selection weight of the relabelled gap vector `shiftFin N i` at the label zero equals the
selection weight of the configuration at label `i`. -/
lemma gapOf_shiftFin_selectionWeight (X : Configuration N) (i : ℤ) :
    (gapOf (shiftFin N i (gapVector X)) (-1) + gapOf (shiftFin N i (gapVector X)) 0) / 2 =
      selectionWeight X i := by
  rw [selectionWeight_eq_gapOf, gapOf_shiftFin, gapOf_shiftFin]
  congr 3
  ring

/-! ### Invariance of the gap law under cyclic relabelling -/

/-- One cyclic step of the gap vector leaves the Gibbs gap law invariant. -/
lemma map_shiftFin_one_gibbsMeasure (P : Parameters) (hN : 2 ≤ (N : ℕ)) :
    (gibbsMeasure P N).map (fun X => shiftFin N 1 (gapVector X)) =
      (gibbsMeasure P N).map gapVector := by
  have h := map_gapFamily_add_one_gibbsMeasure P N hN (fun i : Fin (N : ℕ) => ((i : ℕ) : ℤ))
  have heq : (fun X : Configuration N => shiftFin N 1 (gapVector X)) =
      (fun X : Configuration N => fun i : Fin (N : ℕ) => gap X (((i : ℕ) : ℤ) + 1)) := by
    funext X i
    show gapOf (gapVector X) (1 + ((i : ℕ) : ℤ)) = gap X (((i : ℕ) : ℤ) + 1)
    rw [← gap_eq_gapOf_gapVector, add_comm]
  rw [heq]
  exact h

/-- Every cyclic relabelling by a natural number of steps leaves the Gibbs gap law invariant. -/
lemma map_shiftFin_gibbsMeasure (P : Parameters) (hN : 2 ≤ (N : ℕ)) (i : ℕ) :
    (gibbsMeasure P N).map (fun X => shiftFin N (i : ℤ) (gapVector X)) =
      (gibbsMeasure P N).map gapVector := by
  induction i with
  | zero =>
    have hid : (fun X : Configuration N => shiftFin N ((0 : ℕ) : ℤ) (gapVector X)) = gapVector := by
      funext X
      exact shiftFin_zero _
    rw [hid]
  | succ i ih =>
    have hF : Measurable (fun X : Configuration N => shiftFin N (i : ℤ) (gapVector X)) :=
      (measurable_shiftFin _).comp (measurable_gapVector N)
    have hcomp : (fun X : Configuration N => shiftFin N ((i + 1 : ℕ) : ℤ) (gapVector X)) =
        shiftFin N 1 ∘ (fun X : Configuration N => shiftFin N (i : ℤ) (gapVector X)) := by
      funext X
      show shiftFin N ((i + 1 : ℕ) : ℤ) (gapVector X) =
        shiftFin N 1 (shiftFin N (i : ℤ) (gapVector X))
      funext k
      show gapOf (gapVector X) (((i + 1 : ℕ) : ℤ) + (k : ℕ)) =
        gapOf (shiftFin N (i : ℤ) (gapVector X)) (1 + (k : ℕ))
      rw [gapOf_shiftFin]
      congr 1
      push_cast
      ring
    rw [hcomp, ← Measure.map_map (measurable_shiftFin 1) hF, ih,
      Measure.map_map (measurable_shiftFin 1) (measurable_gapVector N)]
    exact map_shiftFin_one_gibbsMeasure P hN

/-- The integral of a function of the relabelled gap vector does not depend on the label. -/
lemma lintegral_shiftFin_gapVector (P : Parameters) (hN : 2 ≤ (N : ℕ))
    (Kf : (Fin (N : ℕ) → ℝ) → ℝ≥0∞) (hK : Measurable Kf) (i : ℕ) :
    ∫⁻ X, Kf (shiftFin N (i : ℤ) (gapVector X)) ∂(gibbsMeasure P N) =
      ∫⁻ X, Kf (gapVector X) ∂(gibbsMeasure P N) := by
  have hg : Measurable (gapVector : Configuration N → (Fin (N : ℕ) → ℝ)) :=
    measurable_gapVector N
  have hs : Measurable (shiftFin N (i : ℤ)) := measurable_shiftFin _
  calc ∫⁻ X, Kf (shiftFin N (i : ℤ) (gapVector X)) ∂(gibbsMeasure P N)
      = ∫⁻ h, Kf (shiftFin N (i : ℤ) h) ∂((gibbsMeasure P N).map gapVector) :=
        (lintegral_map (hK.comp hs) hg).symm
    _ = ∫⁻ h, Kf h ∂(((gibbsMeasure P N).map gapVector).map (shiftFin N (i : ℤ))) :=
        (lintegral_map hK hs).symm
    _ = ∫⁻ h, Kf h ∂((gibbsMeasure P N).map gapVector) := by
        rw [Measure.map_map hs hg]
        exact congrArg (fun μ => ∫⁻ h, Kf h ∂μ) (map_shiftFin_gibbsMeasure P hN i)
    _ = ∫⁻ X, Kf (gapVector X) ∂(gibbsMeasure P N) := lintegral_map hK hg

end Riesz1

end

end
