/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.Cutoff
public import Riesz1.Rigidity.Gaps
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.OrderedDomain
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Lifted blocks, the forcing potential and the constrained law

Definitions for a block `I = [i0, i0 + L] ∩ ℤ` of `L + 1`
consecutive labels in a configuration of `N` particles, with `1 ≤ L < N`.

* `liftedBlock` is the map `π_I`. Its coordinates are the lifts `x_{i0}, …, x_{i0+L}`
  shifted by the common integer `⌊x_{i0}⌋`, so the first coordinate lies in `[0, 1)`. Its values lie in
  the ordered chamber `orderedDomain (L + 1)`.
* `forcingPotential` is the forcing potential `F_{I,R}`, for a cutoff `θ`.
* `constrainedNormalizer` and `constrainedLaw` are the normalizer `z_{I,R}` and the constrained law
  `Q_{I,R}`. The Gibbs law is `gibbsMeasure P N`, where `P : Parameters` encodes
  the pair `(β, s)` with `β = P.val.1 > 0` and `s = P.val.2 ∈ (0, 1)`.

The smooth forcing cutoff enters through the predicate `IsForcingCutoff`. The
comparison of the forcing is proved in `Riesz1.Rigidity.ForcingComparison`, and the range of
`liftedBlock` is proved in `Riesz1.Rigidity.ForcingBlockRange`.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### The smooth forcing cutoff -/

open scoped ContDiff

/-- A smooth forcing cutoff. It is a smooth function `θ : ℝ → ℝ` (its values on `(-∞, 0)` are
irrelevant, since only `θ` on `[0, ∞)` is used. A cutoff defined on `[0, ∞)` extends by zero,
since it vanishes on `[0, 1]`) with the following properties. It is
nonnegative on `[0, ∞)`, it vanishes on `[0, 1]`, its second derivative lies in `[0, 2]` on
`[0, ∞)`, and its second derivative equals `2` on `[2, ∞)`. -/
def IsForcingCutoff (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ θ ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, θ t = 0) ∧ (∀ t, 0 ≤ t → 0 ≤ θ t) ∧
    (∀ t, 0 ≤ t → 0 ≤ deriv (deriv θ) t ∧ deriv (deriv θ) t ≤ 2) ∧
    (∀ t, 2 ≤ t → deriv (deriv θ) t = 2)

/-- The explicit cutoff `forcingCutoff` of `Riesz1.Rigidity.Cutoff` is a forcing cutoff, so the
class of forcing cutoffs is nonempty. -/
theorem isForcingCutoff_forcingCutoff : IsForcingCutoff forcingCutoff := by
  have hzero : ∀ t ∈ Set.Icc (0 : ℝ) 1, forcingCutoff t = 0 := fun t ht => forcingCutoff_eq_zero ht.2
  exact ⟨forcingCutoff_contDiff, hzero,
    cutoff_nonneg forcingCutoff_contDiff_two hzero forcingCutoff_deriv_deriv_bounds,
    forcingCutoff_deriv_deriv_bounds, fun t ht => forcingCutoff_deriv_deriv_of_two_le ht⟩

/-! ### The lifted block -/

/-- The coordinates of the lifted block of `X` on the labels `i0, …, i0 + L`: the lifts
`x_{i0 + r}` shifted by the common integer `⌊x_{i0}⌋`. -/
noncomputable def liftedBlockCoords (i0 : ℤ) (L : ℕ) (X : Configuration N) : Fin (L + 1) → ℝ :=
  fun r => cyclicLift X (i0 + ((r : ℕ) : ℤ)) - ((⌊cyclicLift X i0⌋ : ℤ) : ℝ)

/-- The coordinates of a lifted block lie in the ordered chamber `D_{L + 1}`. -/
theorem liftedBlockCoords_mem (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ)) (X : Configuration N) :
    liftedBlockCoords i0 L X ∈ orderedDomain (Nat.succPNat L) := by
  have hsm : StrictMono (liftedBlockCoords i0 L X) := by
    intro r s hrs
    have hrs' : (r : ℕ) < (s : ℕ) := hrs
    have h1 : i0 + ((r : ℕ) : ℤ) < i0 + ((s : ℕ) : ℤ) := by omega
    have h2 := cyclicLift_strictMono X h1
    unfold liftedBlockCoords
    linarith
  have hlast : ∀ r : Fin (L + 1), cyclicLift X (i0 + ((r : ℕ) : ℤ)) < cyclicLift X i0 + 1 := by
    intro r
    have hr : (r : ℕ) < (N : ℕ) := by omega
    have h1 : i0 + ((r : ℕ) : ℤ) < i0 + ((N : ℕ) : ℤ) := by omega
    have h2 := cyclicLift_strictMono X h1
    rw [cyclicLift_add_N] at h2
    exact h2
  refine ⟨hsm, ?_, ?_, fun r => ?_⟩
  · unfold liftedBlockCoords
    simp only [Nat.cast_zero, add_zero]
    linarith [Int.floor_le (cyclicLift X i0)]
  · unfold liftedBlockCoords
    simp only [Nat.cast_zero, add_zero]
    linarith [Int.lt_floor_add_one (cyclicLift X i0)]
  · unfold liftedBlockCoords
    have h := hlast r
    simp only [Nat.cast_zero, add_zero]
    linarith

/-- The lifted block `π_I`: the map `X ↦ (x_{i0 + r} - ⌊x_{i0}⌋)_{0 ≤ r ≤ L}`
from the configurations of `N` particles to the ordered chamber of `L + 1` particles. The shift
`⌊x_{i0}⌋` is the unique integer making the first coordinate lie in `[0, 1)`. -/
noncomputable def liftedBlock (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ)) (X : Configuration N) :
    Configuration (Nat.succPNat L) :=
  ⟨liftedBlockCoords i0 L X, liftedBlockCoords_mem i0 hL X⟩

/-- The lifted block map is measurable. -/
theorem measurable_liftedBlock (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ)) :
    Measurable (liftedBlock (N := N) i0 hL) := by
  unfold liftedBlock
  refine Measurable.subtype_mk (Measurable.of_eval fun r => ?_)
  have hfl : Measurable fun X : Configuration N => ⌊cyclicLift X i0⌋ :=
    Int.measurable_floor.comp (measurable_cyclicLift i0)
  exact (measurable_cyclicLift _).sub
    ((Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp hfl)

/-! ### The forcing potential -/

/-- The forcing potential `F_{I,R}`, for the block `I = [i0, i0 + L] ∩ ℤ`,
the scale `R`, and the cutoff `θ`:
`F_{I,R}(X) = 2 ∑ θ (N (x_q - x_p) / R)` over the pairs `i0 ≤ p < q ≤ i0 + L`. -/
noncomputable def forcingPotential (θ : ℝ → ℝ) (i0 : ℤ) (L : ℕ) (R : ℝ) (X : Configuration N) :
    ℝ :=
  2 * ∑ p ∈ Finset.Icc i0 (i0 + L), ∑ q ∈ Finset.Ioc p (i0 + L),
    θ (((N : ℕ) : ℝ) * (cyclicLift X q - cyclicLift X p) / R)

/-- The forcing potential is nonnegative when the cutoff is nonnegative on `[0, ∞)` and `R > 0`. -/
theorem forcingPotential_nonneg {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R)
    (i0 : ℤ) (L : ℕ) (X : Configuration N) : 0 ≤ forcingPotential θ i0 L R X := by
  unfold forcingPotential
  refine mul_nonneg zero_le_two (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q hq => ?_)
  have hpq : p < q := (Finset.mem_Ioc.1 hq).1
  have hlt : cyclicLift X p < cyclicLift X q := cyclicLift_strictMono X hpq
  have hNpos : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
  exact hθ.2.2.1 _ (div_nonneg (mul_nonneg hNpos (sub_nonneg.2 hlt.le)) hR.le)

/-- The forcing potential vanishes when the block length `S_{i0,L}` is at most `R`. -/
theorem forcingPotential_eq_zero {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 0 < R)
    (i0 : ℤ) (L : ℕ) (X : Configuration N) (hS : blockLength X i0 L ≤ R) :
    forcingPotential θ i0 L R X = 0 := by
  unfold forcingPotential
  have hNpos : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hterm : ∀ p ∈ Finset.Icc i0 (i0 + L), ∀ q ∈ Finset.Ioc p (i0 + L),
      θ (((N : ℕ) : ℝ) * (cyclicLift X q - cyclicLift X p) / R) = 0 := by
    intro p hp q hq
    have hpq : p < q := (Finset.mem_Ioc.1 hq).1
    have hqL : q ≤ i0 + L := (Finset.mem_Ioc.1 hq).2
    have hip : i0 ≤ p := (Finset.mem_Icc.1 hp).1
    have hlt : cyclicLift X p < cyclicLift X q := cyclicLift_strictMono X hpq
    have hq1 : cyclicLift X q ≤ cyclicLift X (i0 + L) := (cyclicLift_strictMono X).monotone hqL
    have hp1 : cyclicLift X i0 ≤ cyclicLift X p := (cyclicLift_strictMono X).monotone hip
    have hdiff : cyclicLift X q - cyclicLift X p ≤ cyclicLift X (i0 + L) - cyclicLift X i0 := by
      linarith
    have hblock : ((N : ℕ) : ℝ) * (cyclicLift X q - cyclicLift X p) ≤ R := by
      have h := mul_le_mul_of_nonneg_left hdiff hNpos
      unfold blockLength at hS
      linarith
    exact hθ.2.1 _ ⟨div_nonneg (mul_nonneg hNpos (sub_nonneg.2 hlt.le)) hR.le,
      (div_le_one hR).2 hblock⟩
  rw [Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => hterm p hp q hq, mul_zero]

/-- A positive forcing potential forces the block length above the scale: `0 < F_{I,R}(X)`
implies `R < S_{i0,L}(X)`. -/
theorem blockLength_gt_of_forcingPotential_pos {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ}
    (hR : 0 < R) (i0 : ℤ) (L : ℕ) (X : Configuration N) (hF : 0 < forcingPotential θ i0 L R X) :
    R < blockLength X i0 L := by
  by_contra h
  exact hF.ne' (forcingPotential_eq_zero hθ hR i0 L X (not_lt.1 h))

/-- The forcing potential is measurable on the configuration space. -/
theorem measurable_forcingPotential {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i0 : ℤ) (L : ℕ)
    (R : ℝ) : Measurable (fun X : Configuration N => forcingPotential θ i0 L R X) := by
  unfold forcingPotential
  refine measurable_const.mul (Finset.measurable_sum _ fun p _ =>
    Finset.measurable_sum _ fun q _ => ?_)
  refine (hθ.1.continuous.measurable).comp ?_
  exact (measurable_const.mul ((measurable_cyclicLift _).sub (measurable_cyclicLift _))).div_const R

/-! ### The constrained law -/

/-- The normalizer `z_{I,R} = E_P[exp (-β F_{I,R})]`, for the Gibbs law
`gibbsMeasure P N` and the inverse temperature `β = P.val.1`. -/
noncomputable def constrainedNormalizer (P : Parameters) (N : ℕ+) (θ : ℝ → ℝ) (i0 : ℤ) (L : ℕ)
    (R : ℝ) : ℝ :=
  ∫ X, Real.exp (-P.val.1 * forcingPotential θ i0 L R X) ∂(gibbsMeasure P N)

/-- The constrained law `Q_{I,R}`: `dQ = z^{-1} exp (-β F_{I,R}) dP`,
with `z = constrainedNormalizer`. -/
noncomputable def constrainedLaw (P : Parameters) (N : ℕ+) (θ : ℝ → ℝ) (i0 : ℤ) (L : ℕ) (R : ℝ) :
    Measure (Configuration N) :=
  (gibbsMeasure P N).withDensity fun X =>
    ENNReal.ofReal ((constrainedNormalizer P N θ i0 L R)⁻¹ *
      Real.exp (-P.val.1 * forcingPotential θ i0 L R X))

end Riesz1

end
