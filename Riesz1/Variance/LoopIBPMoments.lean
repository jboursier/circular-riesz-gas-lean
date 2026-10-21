/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPKernel
public import Riesz1.Variance.LoopIBPHessian
public import Riesz1.Rigidity.ForcingComparison
import all Riesz1.Variance.LoopScale

/-!
# Finite moments of the loop functional and of the Hessian quadratic term

Proposition 5.5, clause 4: for each fixed `N`, `ℓ` and profile `ψ`, the
loop functional `Loop_ℓ[ψ]` and the Hessian quadratic term `β Ψ_ψ · ∇²H_N Ψ_ψ` have every finite
moment under the Gibbs law `gibbsMeasure P N`. The only external input is the Prékopa–Leindler
inequality `External.PrekopaLeindler`, passed as an explicit hypothesis. It is used through the
uniform inverse moment bound.
-/

@[expose] public section

open MeasureTheory Set Filter Topology UnitAddCircle

namespace Riesz1

variable {N : ℕ+}

/-- The loop functional `Loop_ℓ[ψ]` on a configuration. -/
noncomputable def loopOnConfiguration (s : RieszExponent) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) : ℝ :=
  loopScale s N ℓ ψ X.val (fun _ _ hij => coe_sub_ne_zero X hij)

/-- The Hessian quadratic term `β Ψ_ψ · ∇²H_N Ψ_ψ` of Proposition 5.5,
with `Ψ_ψ(X) = (ℓ ψ(xᵢ/ℓ))ᵢ`. The Hessian is the second partial derivative of the lifted energy. -/
noncomputable def hessianQuadratic (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) : ℝ :=
  P.val.1 * ∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ),
    loopScaleField ℓ.val ψ.val (X.val k) * loopScaleField ℓ.val ψ.val (X.val l) *
      partialDeriv (fun y => partialDeriv (energyLift (parametersExponent P) (N : ℕ)) k y) l
        X.val

/-- The Hessian quadratic term in the closed form of the second derivatives. -/
lemma hessianQuadratic_eq (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) :
    hessianQuadratic P N ℓ ψ X = P.val.1 * ∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ),
      loopScaleField ℓ.val ψ.val (X.val k) * loopScaleField ℓ.val ψ.val (X.val l) *
        hessianSum (parametersExponent P).val (N : ℕ) k l X.val := by
  unfold hessianQuadratic
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [partialDeriv_partialDeriv_energyLift_eq' (parametersExponent P) X.val
    (fun i j hij => coe_sub_ne_zero X hij) k l]

/-- The loop functional is the loop of the Lipschitz profile `ℓψ(·/ℓ)`. -/
lemma loopOnConfiguration_eq (s : RieszExponent) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) (X : Configuration N) :
    loopOnConfiguration s N ℓ ψ X = loopFunctional s.val (N : ℕ) (loopScaleField ℓ.val ψ.val)
      X.val := rfl

/-- The loop functional of a continuous profile is measurable in the configuration. -/
lemma measurable_loopFunctional (s : RieszExponent) (N : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable (fun x : Fin N → ℝ => loopFunctional s.val N f x) := by
  unfold loopFunctional
  have hA : Measurable (fun x : Fin N → ℝ => ∑ i : Fin N, ∑ j : Fin N,
      (if j = i then (0 : ℝ) else loopKernel s.val f (x i) (x j))) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    split_ifs
    · exact measurable_const
    · exact (measurable_loopKernel_pair s.val hf).comp
        (Measurable.prodMk (measurable_pi_apply i) (measurable_pi_apply j))
  have hSI : Measurable (fun x : Fin N → ℝ => ∑ i : Fin N,
      ∫ y in (0 : ℝ)..1, loopKernel s.val f (x i) y) :=
    Finset.measurable_sum _ fun i _ => (measurable_background s.val hf).comp (measurable_pi_apply i)
  have hSJ : Measurable (fun x : Fin N → ℝ => ∑ j : Fin N,
      ∫ u in (0 : ℝ)..1, loopKernel s.val f u (x j)) := by
    refine Finset.measurable_sum _ fun j _ => ?_
    have e : (fun x : Fin N → ℝ => ∫ u in (0 : ℝ)..1, loopKernel s.val f u (x j)) =
        fun x : Fin N → ℝ => ∫ y in (0 : ℝ)..1, loopKernel s.val f (x j) y :=
      funext fun x => integral_kernel_left_eq s.val f (x j)
    rw [e]
    exact (measurable_background s.val hf).comp (measurable_pi_apply j)
  exact measurable_const.mul
    ((((hA.sub (measurable_const.mul hSI)).sub (measurable_const.mul hSJ)).add
      (measurable_const.mul measurable_const)))

/-- The inequality `(1 + G)^p ≤ 2^p (1 + G^p)` for `G ≥ 0` and `p > 0`. -/
lemma one_add_rpow_le {G p : ℝ} (hG : 0 ≤ G) (hp : 0 < p) :
    (1 + G) ^ p ≤ 2 ^ p * (1 + G ^ p) := by
  have h2 : (0 : ℝ) ≤ 2 ^ p := Real.rpow_nonneg (by norm_num) _
  have hGp : 0 ≤ G ^ p := Real.rpow_nonneg hG _
  rcases le_total G 1 with h | h
  · have h1 : (1 + G) ^ p ≤ 2 ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp.le
    nlinarith
  · have h1 : (1 + G) ^ p ≤ (2 * G) ^ p :=
      Real.rpow_le_rpow (by linarith) (by linarith) hp.le
    rw [Real.mul_rpow (by norm_num) hG] at h1
    nlinarith

/-- A measurable function of the configuration with a bound by a constant times
`1 + ∑ₖ gapₖ^{-r}` has every finite moment under the Gibbs law. -/
theorem integrable_abs_rpow_of_le (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) {F : Configuration N → ℝ} (hF : Measurable F) {r : ℝ} (hr : 0 < r) {C : ℝ}
    (hC : ∀ X, |F X| ≤ C * (1 + gapPowerSum r X)) {p : ℝ} (hp : 0 < p) :
    Integrable (fun X => |F X| ^ p) (gibbsMeasure P N) := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hC' : ∀ X, |F X| ≤ |C| * (1 + gapPowerSum r X) := fun X =>
    (hC X).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (by linarith [gapPowerSum_nonneg r X]))
  have hbound : ∀ X, |F X| ^ p ≤ |C| ^ p * (2 ^ p * (1 + (N : ℝ) ^ p * gapPowerSum (r * p) X)) := by
    intro X
    have h1 : |F X| ^ p ≤ (|C| * (1 + gapPowerSum r X)) ^ p :=
      Real.rpow_le_rpow (abs_nonneg _) (hC' X) hp.le
    rw [Real.mul_rpow (abs_nonneg C) (by linarith [gapPowerSum_nonneg r X])] at h1
    have h2 := one_add_rpow_le (gapPowerSum_nonneg r X) hp
    have h3 := gapPowerSum_rpow_le X (r := r) hp.le
    have hC0 : (0 : ℝ) ≤ |C| ^ p := Real.rpow_nonneg (abs_nonneg _) _
    have h4 : (2 : ℝ) ^ p * (1 + gapPowerSum r X ^ p) ≤
        2 ^ p * (1 + (N : ℝ) ^ p * gapPowerSum (r * p) X) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (by norm_num) _)
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h4) hC0)
  have hone : Integrable (fun _ : Configuration N => (1 : ℝ)) (gibbsMeasure P N) :=
    integrable_const (1 : ℝ)
  have hpow : Integrable (fun X : Configuration N => (N : ℝ) ^ p * gapPowerSum (r * p) X)
      (gibbsMeasure P N) :=
    (integrable_gapPowerSum P hPL (mul_pos hr hp) N).const_mul ((N : ℝ) ^ p)
  have hsum : Integrable (fun X : Configuration N => 1 + (N : ℝ) ^ p * gapPowerSum (r * p) X)
      (gibbsMeasure P N) :=
    hone.add hpow
  have hint : Integrable (fun X : Configuration N =>
      |C| ^ p * (2 ^ p * (1 + (N : ℝ) ^ p * gapPowerSum (r * p) X))) (gibbsMeasure P N) :=
    (hsum.const_mul ((2 : ℝ) ^ p)).const_mul (|C| ^ p)
  have hmeas : AEStronglyMeasurable (fun X : Configuration N => |F X| ^ p) (gibbsMeasure P N) :=
    (((continuous_abs.measurable.comp hF)).pow_const p).aestronglyMeasurable
  refine hint.mono' hmeas (Eventually.of_forall fun X => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact hbound X

/-- A Lipschitz profile of period one is bounded. -/
lemma exists_abs_le_of_lipschitz_periodic {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ Ψm : ℝ, 0 ≤ Ψm ∧ ∀ u : ℝ, |f u| ≤ Ψm := by
  refine ⟨|f 0| + (M : ℝ), by positivity, fun u => ?_⟩
  have h := loopScale_lipschitz_increment hf hp 0 u
  rw [zero_add] at h
  have hd : dist (u : UnitAddCircle) 0 ≤ 1 := by
    rw [dist_coe_zero_eq]
    linarith [abs_sub_round u]
  have hM : (M : ℝ) * dist (u : UnitAddCircle) 0 ≤ M :=
    mul_le_of_le_one_right M.property hd
  have hu := abs_le.mp (h.trans hM)
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2, le_abs_self (f 0), neg_abs_le (f 0)]

/-- The Hessian quadratic term is measurable on the configuration space. -/
theorem measurable_hessianQuadratic (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) : Measurable (hessianQuadratic P N ℓ ψ) := by
  obtain ⟨M, hM⟩ := loopScaleField_lipschitz ψ
  have hΨ : ∀ k : Fin (N : ℕ), Measurable (fun X : Configuration N =>
      loopScaleField ℓ.val ψ.val (X.val k)) := fun k =>
    hM.continuous.measurable.comp ((measurable_pi_apply k).comp measurable_subtype_coe)
  have e : hessianQuadratic P N ℓ ψ = fun X : Configuration N => P.val.1 *
      ∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ), loopScaleField ℓ.val ψ.val (X.val k) *
        loopScaleField ℓ.val ψ.val (X.val l) *
          hessianSum (parametersExponent P).val (N : ℕ) k l X.val :=
    funext (hessianQuadratic_eq P N ℓ ψ)
  rw [e]
  refine measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    Finset.measurable_sum _ fun l _ => ?_)
  exact (((hΨ k).mul (hΨ l)).mul
    ((measurable_hessianSum _ _ k l).comp measurable_subtype_coe))

/-- The Hessian quadratic term is bounded by a constant multiple of `1 + ∑ₖ gapₖ^{-(s+2)}`. -/
theorem exists_hessianQuadratic_le (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Configuration N,
      |hessianQuadratic P N ℓ ψ X| ≤ C * (1 + gapPowerSum ((parametersExponent P).val + 2) X) := by
  obtain ⟨M, hM⟩ := loopScaleField_lipschitz ψ
  obtain ⟨Ψm, hΨ0, hΨ⟩ := exists_abs_le_of_lipschitz_periodic hM
    (loopScaleField_periodic ψ.property.1)
  obtain ⟨CH, hCH0, hCH⟩ := exists_hessianSum_le (parametersExponent P) N
  have hNpos : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le _)
  set K : ℝ := |P.val.1| * ((N : ℝ) * ((N : ℝ) * (Ψm * Ψm * CH))) with hK
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _)
    (mul_nonneg hNpos (mul_nonneg hNpos (mul_nonneg (mul_nonneg hΨ0 hΨ0) hCH0)))
  refine ⟨K, hK0, fun X => ?_⟩
  set G := gapPowerSum ((parametersExponent P).val + 2) X with hG
  have hG0 : 0 ≤ G := gapPowerSum_nonneg _ X
  -- Each summand is bounded by `Ψm Ψm CH G`.
  have hterm : ∀ k l : Fin (N : ℕ), |loopScaleField ℓ.val ψ.val (X.val k) *
      loopScaleField ℓ.val ψ.val (X.val l) * hessianSum (parametersExponent P).val (N : ℕ) k l X.val|
        ≤ Ψm * Ψm * (CH * G) := by
    intro k l
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hΨ (X.val k)) (hΨ (X.val l)) (abs_nonneg _) hΨ0)
      (hCH X k l) (abs_nonneg _) (mul_nonneg hΨ0 hΨ0)
  have hsum : |∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ),
      loopScaleField ℓ.val ψ.val (X.val k) * loopScaleField ℓ.val ψ.val (X.val l) *
        hessianSum (parametersExponent P).val (N : ℕ) k l X.val| ≤
      (N : ℝ) * ((N : ℝ) * (Ψm * Ψm * (CH * G))) := by
    calc _ ≤ ∑ k : Fin (N : ℕ), |∑ l : Fin (N : ℕ),
          loopScaleField ℓ.val ψ.val (X.val k) * loopScaleField ℓ.val ψ.val (X.val l) *
            hessianSum (parametersExponent P).val (N : ℕ) k l X.val| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ), Ψm * Ψm * (CH * G) :=
          Finset.sum_le_sum fun k _ => (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun l _ => hterm k l)
      _ = (N : ℝ) * ((N : ℝ) * (Ψm * Ψm * (CH * G))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hessianQuadratic_eq, abs_mul]
  calc |P.val.1| * |∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ),
          loopScaleField ℓ.val ψ.val (X.val k) * loopScaleField ℓ.val ψ.val (X.val l) *
            hessianSum (parametersExponent P).val (N : ℕ) k l X.val|
      ≤ |P.val.1| * ((N : ℝ) * ((N : ℝ) * (Ψm * Ψm * (CH * G)))) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
    _ = K * G := by rw [hK]; ring
    _ ≤ K * (1 + G) := mul_le_mul_of_nonneg_left (by linarith) hK0

/-- **Clause 4 of Proposition 5.5.** For fixed `N`, `ℓ` and a Lipschitz profile
`ψ` of period `ℓ⁻¹`, the loop functional and the Hessian quadratic term have every finite moment
under the Gibbs law. The only hypothesis is the Prékopa–Leindler inequality
`External.PrekopaLeindler`. -/
theorem loop_moments (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ψ : LoopScaleProfile ℓ.val) :
    (∀ p : ℝ, 0 < p → Integrable (fun X : Configuration N =>
        |loopOnConfiguration (parametersExponent P) N ℓ ψ X| ^ p) (gibbsMeasure P N)) ∧
    (∀ p : ℝ, 0 < p → Integrable (fun X : Configuration N =>
        |hessianQuadratic P N ℓ ψ X| ^ p) (gibbsMeasure P N)) := by
  obtain ⟨M, hM⟩ := loopScaleField_lipschitz ψ
  obtain ⟨C₁, -, hC₁⟩ := exists_loopFunctional_le (parametersExponent P) N hM
    (loopScaleField_periodic ψ.property.1)
  obtain ⟨CH, -, hCH⟩ := exists_hessianQuadratic_le P N ℓ ψ
  have hs : 0 < (parametersExponent P).val := (parametersExponent P).property.1
  have hs2 : 0 < (parametersExponent P).val + 2 := by linarith
  have hmeasL : Measurable (loopOnConfiguration (parametersExponent P) N ℓ ψ) :=
    (measurable_loopFunctional (parametersExponent P) (N : ℕ) hM.continuous).comp
      measurable_subtype_coe
  constructor
  · intro p hp
    exact integrable_abs_rpow_of_le P hPL N hmeasL hs (C := C₁) (fun X => hC₁ X) hp
  · intro p hp
    exact integrable_abs_rpow_of_le P hPL N (measurable_hessianQuadratic P N ℓ ψ) hs2
      (C := CH) hCH hp

end Riesz1

end
