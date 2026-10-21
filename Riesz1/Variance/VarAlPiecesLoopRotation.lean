/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesLoopShift
public import Riesz1.Variance.VarAlPiecesLoopMemLp
public import Riesz1.Rigidity.GapLaw
public import Riesz1.Frozen.Variance

/-!
# Translation invariance of the Gibbs variance of the loop functional

Proposition 5.9, the last clause of the variance statement: translating a profile
does not change the variance of its loop under the Gibbs law. The proof is the "rotate the
configuration" argument.

Write `X₀ = cyclicLift X 0` for the first lift and `y = (anchorCoords n X).2` for the anchored
offsets, so that `X_i = X₀ + anchorVector y i` (`apply_eq_anchor_add`). The loop of `g` at `X`
is `Φ(X₀, y)`, where `Φ(z, y)` is the loop of the lifts `t + anchorVector y` at a real lift
`t` of `z`. This value is independent of the lift because the loop is invariant under integer
shifts. The loop of the translate `g(· + c)` at `X` is `Φ(X₀ + c, y)` by the shift identity of
`VarAlPiecesLoopShift`. The joint law of `(X₀, y)` is uniform on the circle times the anchored
law (`map_cyclicLift_anchorCoords_gibbsMeasure`), and translation of the circle variable
preserves that product measure. Hence the two loop laws agree, and so do their variances.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Riesz1

/-! ### A measurable real lift of the circle -/

/-- A real representative of a point of the unit circle, in the window `[0, 1)`. -/
noncomputable def circleRepIco (z : UnitAddCircle) : ℝ := (AddCircle.equivIco 1 0 z).val

lemma circleRepIco_coe (z : UnitAddCircle) : ((circleRepIco z : ℝ) : UnitAddCircle) = z := by
  unfold circleRepIco
  exact AddCircle.coe_equivIco

lemma measurable_circleRepIco : Measurable circleRepIco :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

/-- A real representative of a circle point differs from any real lift of the same point by an
integer. -/
lemma circleRepIco_eq_add_int (r : ℝ) : ∃ m : ℤ, circleRepIco (r : UnitAddCircle) = r + m := by
  have h : ((circleRepIco (r : UnitAddCircle) - r : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, circleRepIco_coe, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
  refine ⟨m, ?_⟩
  rw [zsmul_eq_mul, mul_one] at hm
  linarith

/-! ### The loop as a function of the first lift and the anchored offsets -/

/-- The loop functional of the lifts `t + anchorVector y` of `n + 1` particles. -/
noncomputable def offsetLoop (s : ℝ) (n : ℕ) (g : ℝ → ℝ) (t : ℝ) (y : Fin n → ℝ) : ℝ :=
  loopFunctional s (n.succPNat : ℕ) g (fun i => t + anchorVector y i)

/-- The offset loop is invariant under an integer shift of the first lift. -/
lemma offsetLoop_add_int (s : ℝ) {g : ℝ → ℝ} (hp : Function.Periodic g 1) (n : ℕ) (t : ℝ)
    (y : Fin n → ℝ) (m : ℤ) : offsetLoop s n g (t + m) y = offsetLoop s n g t y := by
  unfold offsetLoop
  have hx : (fun i : Fin (n.succPNat : ℕ) => t + (m : ℝ) + anchorVector y i) =
      fun i => (t + anchorVector y i) + m := by
    funext i
    ring
  rw [hx, loopFunctional_add_int s hp]

/-- The offset loop at a circle point is the offset loop at any real lift of it. -/
lemma offsetLoop_circleRepIco (s : ℝ) {g : ℝ → ℝ} (hp : Function.Periodic g 1) (n : ℕ)
    (r : ℝ) (y : Fin n → ℝ) :
    offsetLoop s n g (circleRepIco (r : UnitAddCircle)) y = offsetLoop s n g r y := by
  obtain ⟨m, hm⟩ := circleRepIco_eq_add_int r
  rw [hm, offsetLoop_add_int s hp]

/-- The offset loop is jointly measurable in the first lift and the offsets, for a continuous
profile. -/
lemma measurable_offsetLoop (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) {g : ℝ → ℝ}
    (hg : Continuous g) :
    Measurable (fun q : ℝ × (Fin n → ℝ) => offsetLoop s n g q.1 q.2) := by
  have hmap : Measurable (fun q : ℝ × (Fin n → ℝ) =>
      fun i : Fin (n.succPNat : ℕ) => q.1 + anchorVector q.2 i) := by
    refine Measurable.of_eval fun i => ?_
    exact measurable_fst.add ((measurable_pi_apply i).comp
      ((measurable_anchorVector n).comp measurable_snd))
  exact (measurable_loopFunctional ⟨s, hs0, hs1⟩ (n.succPNat : ℕ) hg).comp hmap

/-- The loop functional of a configuration in terms of the first lift and the anchored offsets.
Here `X₀ = cyclicLift X 0` is the first lift. -/
lemma offsetLoop_config (s : ℝ) (g : ℝ → ℝ) (n : ℕ)
    (X : Configuration n.succPNat) :
    offsetLoop s n g (cyclicLift X 0 : ℝ) (anchorCoords n X.val).2 =
      loopFunctional s (n.succPNat : ℕ) g X.val := by
  unfold offsetLoop
  rw [cyclicLift_zero]
  congr 1
  funext i
  exact (apply_eq_anchor_add n X.val i).symm

/-- A rotation of the first lift by `c` changes the loop to the loop of the configuration shifted
by `c`. -/
lemma offsetLoop_rotate_config (s : ℝ) (g : ℝ → ℝ) (n : ℕ)
    (X : Configuration n.succPNat) (c : ℝ) :
    offsetLoop s n g (cyclicLift X 0 + c) (anchorCoords n X.val).2 =
      loopFunctional s (n.succPNat : ℕ) g (fun i => X.val i + c) := by
  unfold offsetLoop
  have h0 : cyclicLift X 0 = X.val 0 := cyclicLift_zero X
  rw [h0]
  congr 1
  funext i
  rw [apply_eq_anchor_add n X.val i]
  ring

/-! ### Invariance of the product measure under rotation of the first lift -/

/-- Translating the circle coordinate of the product of the uniform law with the anchored law
leaves the product measure unchanged. -/
lemma map_rotation_volume_prod (P : Parameters) (n : ℕ) (c : ℝ) :
    ((volume : Measure UnitAddCircle).prod (anchoredLaw P n)).map
      (fun p : UnitAddCircle × (Fin n → ℝ) => (p.1 + (c : UnitAddCircle), p.2)) =
      (volume : Measure UnitAddCircle).prod (anchoredLaw P n) := by
  have := isProbabilityMeasure_anchoredLaw P n
  have hc : Measurable (fun z : UnitAddCircle => z + (c : UnitAddCircle)) :=
    measurable_id.add_const _
  have hpf : (fun p : UnitAddCircle × (Fin n → ℝ) => (p.1 + (c : UnitAddCircle), p.2)) =
      Prod.map (fun z : UnitAddCircle => z + (c : UnitAddCircle)) id := rfl
  rw [hpf, ← Measure.map_prod_map _ _ hc measurable_id,
    map_add_right_eq_self (volume : Measure UnitAddCircle) (c : UnitAddCircle), Measure.map_id]

/-! ### The variance depends only on the law -/

/-- Two integrable real random variables with the same law have the same variance. The proof
transports the mean and the centred lower integral through the common law. -/
theorem variance_congr_of_map_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G) (h : μ.map F = μ.map G)
    (h1 : Integrable F μ) (h2 : Integrable G μ) : variance μ F h1 = variance μ G h2 := by
  have hmean : ∫ ω, F ω ∂μ = ∫ ω, G ω ∂μ := by
    calc ∫ ω, F ω ∂μ = ∫ y, y ∂(μ.map F) :=
          (integral_map hF.aemeasurable aestronglyMeasurable_id).symm
      _ = ∫ y, y ∂(μ.map G) := by rw [h]
      _ = ∫ ω, G ω ∂μ := integral_map hG.aemeasurable aestronglyMeasurable_id
  unfold variance
  rw [hmean]
  calc ∫⁻ ω, ENNReal.ofReal ((F ω - ∫ ω', G ω' ∂μ) ^ 2) ∂μ
      = ∫⁻ y, ENNReal.ofReal ((y - ∫ ω', G ω' ∂μ) ^ 2) ∂(μ.map F) :=
        (lintegral_map ((measurable_id.sub_const _).pow_const 2).ennreal_ofReal hF).symm
    _ = ∫⁻ y, ENNReal.ofReal ((y - ∫ ω', G ω' ∂μ) ^ 2) ∂(μ.map G) := by rw [h]
    _ = ∫⁻ ω, ENNReal.ofReal ((G ω - ∫ ω', G ω' ∂μ) ^ 2) ∂μ :=
        lintegral_map ((measurable_id.sub_const _).pow_const 2).ennreal_ofReal hG

/-! ### The rotation identity for the Gibbs law -/

/-- **Rotation invariance of the loop law.** Under the Gibbs law, the loop of the translated
profile `g(· + c)` and the loop of `g` have the same distribution. -/
theorem map_loopFunctional_shift_gibbs (P : Parameters) (N : ℕ+) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) {g : ℝ → ℝ} {M : NNReal} (hg : LipschitzWith M g)
    (hp : Function.Periodic g 1) (c : ℝ) :
    (gibbsMeasure P N).map
        (fun X : Configuration N => loopFunctional s (N : ℕ) (fun u => g (u + c)) X.val) =
      (gibbsMeasure P N).map (fun X : Configuration N => loopFunctional s (N : ℕ) g X.val) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have := isProbabilityMeasure_anchoredLaw P n
  -- The joint law of the first lift on the circle and of the anchored offsets.
  have hΛlaw : (gibbsMeasure P n.succPNat).map
      (fun X : Configuration n.succPNat =>
        (((cyclicLift X 0 : ℝ) : UnitAddCircle), (anchorCoords n X.val).2)) =
      (volume : Measure UnitAddCircle).prod (anchoredLaw P n) :=
    map_cyclicLift_anchorCoords_gibbsMeasure P n 0
  have hΛm : Measurable (fun X : Configuration n.succPNat =>
      (((cyclicLift X 0 : ℝ) : UnitAddCircle), (anchorCoords n X.val).2)) :=
    (measurable_coe_circle.comp (measurable_cyclicLift 0)).prodMk
      (measurable_snd.comp (measurable_anchorCoords_config n))
  have hRotM : Measurable (fun p : UnitAddCircle × (Fin n → ℝ) =>
      (p.1 + (c : UnitAddCircle), p.2)) :=
    (measurable_fst.add_const _).prodMk measurable_snd
  -- The loop as a function of the circle point and the anchored offsets.
  have hΦ : Measurable (fun p : UnitAddCircle × (Fin n → ℝ) =>
      offsetLoop s n g (circleRepIco p.1) p.2) :=
    (measurable_offsetLoop s hs0 hs1 n hg.continuous).comp
      ((measurable_circleRepIco.comp measurable_fst).prodMk measurable_snd)
  have hF : ∀ X : Configuration n.succPNat,
      offsetLoop s n g (circleRepIco ((cyclicLift X 0 : ℝ) : UnitAddCircle))
        (anchorCoords n X.val).2 = loopFunctional s (n.succPNat : ℕ) g X.val := by
    intro X
    rw [offsetLoop_circleRepIco s hp n, offsetLoop_config s g n X]
  have hFc : ∀ X : Configuration n.succPNat,
      loopFunctional s (n.succPNat : ℕ) (fun u => g (u + c)) X.val =
        offsetLoop s n g
          (circleRepIco (((cyclicLift X 0 : ℝ) : UnitAddCircle) + (c : UnitAddCircle)))
          (anchorCoords n X.val).2 := by
    intro X
    rw [← AddCircle.coe_add, offsetLoop_circleRepIco s hp n, offsetLoop_rotate_config s g n X c,
      loopFunctional_shift_profile s hp (n.succPNat : ℕ) c X.val]
  calc (gibbsMeasure P n.succPNat).map (fun X : Configuration n.succPNat =>
          loopFunctional s (n.succPNat : ℕ) (fun u => g (u + c)) X.val)
      = (gibbsMeasure P n.succPNat).map (fun X : Configuration n.succPNat =>
          offsetLoop s n g
            (circleRepIco (((cyclicLift X 0 : ℝ) : UnitAddCircle) + (c : UnitAddCircle)))
            (anchorCoords n X.val).2) := by
        congr 1
        funext X
        exact hFc X
    _ = (((gibbsMeasure P n.succPNat).map
          (fun X : Configuration n.succPNat =>
            (((cyclicLift X 0 : ℝ) : UnitAddCircle), (anchorCoords n X.val).2))).map
          (fun p : UnitAddCircle × (Fin n → ℝ) => (p.1 + (c : UnitAddCircle), p.2))).map
          (fun p : UnitAddCircle × (Fin n → ℝ) => offsetLoop s n g (circleRepIco p.1) p.2) := by
        rw [Measure.map_map hRotM hΛm, Measure.map_map hΦ (hRotM.comp hΛm)]
        rfl
    _ = (((volume : Measure UnitAddCircle).prod (anchoredLaw P n)).map
          (fun p : UnitAddCircle × (Fin n → ℝ) => (p.1 + (c : UnitAddCircle), p.2))).map
          (fun p : UnitAddCircle × (Fin n → ℝ) => offsetLoop s n g (circleRepIco p.1) p.2) := by
        rw [hΛlaw]
    _ = ((volume : Measure UnitAddCircle).prod (anchoredLaw P n)).map
          (fun p : UnitAddCircle × (Fin n → ℝ) => offsetLoop s n g (circleRepIco p.1) p.2) := by
        rw [map_rotation_volume_prod P n c]
    _ = ((gibbsMeasure P n.succPNat).map
          (fun X : Configuration n.succPNat =>
            (((cyclicLift X 0 : ℝ) : UnitAddCircle), (anchorCoords n X.val).2))).map
          (fun p : UnitAddCircle × (Fin n → ℝ) => offsetLoop s n g (circleRepIco p.1) p.2) := by
        rw [hΛlaw]
    _ = (gibbsMeasure P n.succPNat).map (fun X : Configuration n.succPNat =>
          offsetLoop s n g (circleRepIco ((cyclicLift X 0 : ℝ) : UnitAddCircle))
            (anchorCoords n X.val).2) := by
        rw [Measure.map_map hΦ hΛm]
        rfl
    _ = (gibbsMeasure P n.succPNat).map
          (fun X : Configuration n.succPNat => loopFunctional s (n.succPNat : ℕ) g X.val) := by
        congr 1
        funext X
        exact hF X

/-! ### The variance clause for a translated profile -/

/-- **Translation invariance of the Gibbs variance** (Proposition 5.9, the last
assertion). For a Lipschitz one-periodic profile `g` and a real shift `c`, the loop of
`g(· + c)` under the Gibbs law is integrable, and its variance equals the variance of the loop
of `g`. -/
theorem variance_loopFunctional_shift (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {g : ℝ → ℝ} {M : NNReal}
    (hg : LipschitzWith M g) (hp : Function.Periodic g 1) (c : ℝ) :
    ∃ h1 : Integrable (fun X : Configuration N =>
        loopFunctional s (N : ℕ) (fun u => g (u + c)) X.val) (gibbsMeasure P N),
      ∃ h2 : Integrable (fun X : Configuration N => loopFunctional s (N : ℕ) g X.val)
          (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ h1 = variance (gibbsMeasure P N) _ h2 := by
  have hF : Measurable (fun X : Configuration N => loopFunctional s (N : ℕ) g X.val) :=
    (measurable_loopFunctional ⟨s, hs0, hs1⟩ (N : ℕ) hg.continuous).comp measurable_subtype_coe
  have hFc : Measurable (fun X : Configuration N =>
      loopFunctional s (N : ℕ) (fun u => g (u + c)) X.val) :=
    (measurable_loopFunctional ⟨s, hs0, hs1⟩ (N : ℕ)
      (hg.continuous.comp (continuous_id.add continuous_const))).comp measurable_subtype_coe
  have h2 := integrable_loopFunctional_gibbs P hPL N hs0 hs1 hg hp
  have hlaw := map_loopFunctional_shift_gibbs P N hs0 hs1 hg hp c
  have h1 : Integrable (fun X : Configuration N =>
      loopFunctional s (N : ℕ) (fun u => g (u + c)) X.val) (gibbsMeasure P N) := by
    have hI : Integrable (id : ℝ → ℝ) ((gibbsMeasure P N).map
        (fun X : Configuration N => loopFunctional s (N : ℕ) g X.val)) :=
      (integrable_map_measure measurable_id.aestronglyMeasurable hF.aemeasurable).mpr h2
    rw [← hlaw] at hI
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hFc.aemeasurable).mp hI
  exact ⟨h1, h2, variance_congr_of_map_eq _ hFc hF hlaw h1 h2⟩

end Riesz1

end
