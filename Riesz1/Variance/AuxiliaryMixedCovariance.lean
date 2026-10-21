/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPProposition
public import Riesz1.Variance.LoopMasterTransport
public import Riesz1.Variance.LoopMaster
public import Riesz1.ToMathlib.CircleFourierPairing
public import Riesz1.ToMathlib.CirclePullback
public import Riesz1.Variance.AuxiliaryMixedApprox
public import Riesz1.CLT.IdentityDefs
import all Riesz1.Variance.LoopMaster
public import Riesz1.Variance.LoopMasterScaling
public import Riesz1.Variance.LoopForce
public import Riesz1.CLT.IdentityDerivatives
public import Riesz1.CLT.IdentityStatistic
public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.Bridges.FluctuationSquare
public import Riesz1.ToMathlib.CauchySchwarzIntegral
public import Riesz1.Kernel.MeanFieldEnergyKernel
public import Mathlib.Algebra.Order.Chebyshev
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceEnergy
import all Riesz1.Variance.LoopIBPUniform

/-!
# The covariance of the statistic with the loop potential

Part of Proposition 5.6 (the mixed part), the covariance step. For `Φ = 𝓛Φ_ψ` the loop operator
potential of Proposition 5.5 and a statistic `F = Fluct_N[f]`, the covariance `Cov(F, Φ)` is
`∫ F Φ` (the potential is centred). Three computations give it:

* for a torus-smooth statistic `Fluct_N[G]` with `G` smooth and one-periodic, the integration by
  parts part of Proposition 5.5 and the uniform marginals give `Cov = N a ℓ ∫₀¹ G' ψ(·/ℓ)`
  (`Riesz1.gibbsCov_fluctIntegral_eq`).
* integration by parts on the unit circle moves the derivative to the profile
  (`Riesz1.integral_deriv_mul_eq_neg_of_periodic`).
* the `L²` bound `E[Fluct_N[g]²] ≤ 4N² ∫ g²` (`Riesz1.integral_sq_fluctuation_le`) transfers the
  identity to general `L²` profiles by approximation (see `AuxiliaryMixedApprox`).

The main results are `Riesz1.integral_sq_fluctuation_le`, `Riesz1.gibbsCov_eq_integral_of_mean_zero`
and `Riesz1.gibbsCov_fluctIntegral_eq`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Riesz1

/-- The expectation of a function of one coordinate, for an arbitrary strongly measurable
function on the unit circle. -/
lemma integral_comp_coord_aesm (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ))
    {f : UnitAddCircle → ℝ} (hf : AEStronglyMeasurable f volume) :
    ∫ X : Configuration N, f ((X.val i : ℝ) : UnitAddCircle) ∂(gibbsMeasure P N) = ∫ x, f x := by
  have hA : AEStronglyMeasurable f
      ((gibbsMeasure P N).map (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle))) := by
    rw [map_coord_gibbsMeasure]
    exact hf
  rw [← integral_map (measurable_coord N i).aemeasurable hA, map_coord_gibbsMeasure]

/-- The coordinate function of an integrable function on the unit circle is integrable under the
Gibbs law. -/
lemma integrable_comp_coord_aesm (P : Parameters) (N : ℕ+) (i : Fin (N : ℕ))
    {f : UnitAddCircle → ℝ} (hf : Integrable f volume) :
    Integrable (fun X : Configuration N => f ((X.val i : ℝ) : UnitAddCircle))
      (gibbsMeasure P N) := by
  have hA : AEStronglyMeasurable f
      ((gibbsMeasure P N).map (fun X : Configuration N => ((X.val i : ℝ) : UnitAddCircle))) := by
    rw [map_coord_gibbsMeasure]
    exact hf.aestronglyMeasurable
  have h := (integrable_map_measure hA (measurable_coord N i).aemeasurable).mp
    (by rw [map_coord_gibbsMeasure]; exact hf)
  exact h

/-- The square of a sum of `N` terms is at most `N` times the sum of the squares. -/
lemma sq_sum_coord_le (N : ℕ+) (g : UnitAddCircle → ℝ) (x : Fin (N : ℕ) → ℝ) :
    (∑ i : Fin (N : ℕ), g (x i : UnitAddCircle)) ^ 2 ≤
      (N : ℝ) * ∑ i : Fin (N : ℕ), g (x i : UnitAddCircle) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (N : ℕ))))
    (f := fun i : Fin (N : ℕ) => g (x i : UnitAddCircle))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- The second moment of the linear statistic of an `L²` function on the unit circle. -/
lemma integral_sq_linearStatistic_le (P : Parameters) (N : ℕ+) {g : UnitAddCircle → ℝ}
    (hg : MemLp g 2 volume) :
    ∫ X, linearStatistic g X ^ 2 ∂(gibbsMeasure P N) ≤ (N : ℝ) ^ 2 * ∫ x, g x ^ 2 := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hg2 : Integrable (fun x => g x ^ 2) volume := hg.integrable_sq
  have hYsq : Integrable (fun X : Configuration N => linearStatistic g X ^ 2) (gibbsMeasure P N) :=
    (memLp_linearStatistic P N hg).integrable_sq
  have hcoordint : ∀ i : Fin (N : ℕ), Integrable
      (fun X : Configuration N => g ((X.val i : ℝ) : UnitAddCircle) ^ 2) (gibbsMeasure P N) :=
    fun i => integrable_comp_coord_aesm (f := fun x => g x ^ 2) P N i hg2
  have hsumint : Integrable (fun X : Configuration N =>
      (N : ℝ) * ∑ i : Fin (N : ℕ), g ((X.val i : ℝ) : UnitAddCircle) ^ 2) (gibbsMeasure P N) :=
    (integrable_finsetSum _ fun i _ => hcoordint i).const_mul _
  have hpt : ∀ X : Configuration N, linearStatistic g X ^ 2 ≤
      (N : ℝ) * ∑ i : Fin (N : ℕ), g ((X.val i : ℝ) : UnitAddCircle) ^ 2 := by
    intro X
    unfold linearStatistic
    exact sq_sum_coord_le N g X.val
  have hint1 : ∫ X, linearStatistic g X ^ 2 ∂(gibbsMeasure P N) ≤
      ∫ X, (N : ℝ) * ∑ i : Fin (N : ℕ), g ((X.val i : ℝ) : UnitAddCircle) ^ 2
        ∂(gibbsMeasure P N) := integral_mono hYsq hsumint hpt
  have hcoord : ∀ i : Fin (N : ℕ), ∫ X : Configuration N, g ((X.val i : ℝ) : UnitAddCircle) ^ 2
      ∂(gibbsMeasure P N) = ∫ x, g x ^ 2 := fun i =>
    integral_comp_coord_aesm (f := fun x => g x ^ 2) P N i hg2.aestronglyMeasurable
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hcoordint i] at hint1
  simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hint1
  calc ∫ X, linearStatistic g X ^ 2 ∂(gibbsMeasure P N)
      ≤ (N : ℝ) * ((N : ℝ) * ∫ x, g x ^ 2) := hint1
    _ = (N : ℝ) ^ 2 * ∫ x, g x ^ 2 := by ring

/-- The mean of an `L²` function on the unit circle has square at most its second moment. -/
lemma sq_integral_le_integral_sq {g : UnitAddCircle → ℝ} (hg : MemLp g 2 volume) :
    (∫ x, g x) ^ 2 ≤ ∫ x, g x ^ 2 := by
  have hc := abs_integral_mul_le_sqrt_integral_sq (μ := (volume : Measure UnitAddCircle))
    (X := g) (Y := fun _ => (1 : ℝ)) hg (memLp_const 1)
  have hvol : volume.real (Set.univ : Set UnitAddCircle) = 1 := by
    simp [Measure.real]
  have h1 : |∫ x, g x| ≤ Real.sqrt (∫ x, g x ^ 2) := by
    simpa [hvol] using hc
  have h2 : |∫ x, g x| ^ 2 ≤ (Real.sqrt (∫ x, g x ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (g x)), sq_abs] at h2
  exact h2

/-- The elementary inequality `(a - b)² ≤ 2a² + 2b²`. -/
lemma sq_sub_le_two_mul (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h := sq_nonneg (a + b)
  have e : (a - b) ^ 2 = 2 * a ^ 2 + 2 * b ^ 2 - (a + b) ^ 2 := by ring
  rw [e]
  linarith

/-- The `L²` bound for the Gibbs fluctuation of an `L²` function on the unit circle:
`E[Fluct_N[g]²] ≤ 4 N² ∫ g²`. -/
theorem integral_sq_fluctuation_le (P : Parameters) (N : ℕ+) {g : UnitAddCircle → ℝ}
    (hg : MemLp g 2 volume) :
    ∫ X, (fluctuation ⟨g, hg.integrable one_le_two⟩ X) ^ 2 ∂(gibbsMeasure P N) ≤
      4 * (N : ℝ) ^ 2 * ∫ x, g x ^ 2 := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hYsq : Integrable (fun X : Configuration N => linearStatistic g X ^ 2) (gibbsMeasure P N) :=
    (memLp_linearStatistic P N hg).integrable_sq
  have hm := sq_integral_le_integral_sq hg
  have hfl : ∀ X : Configuration N, fluctuation ⟨g, hg.integrable one_le_two⟩ X ^ 2 ≤
      2 * linearStatistic g X ^ 2 + 2 * ((N : ℝ) * ∫ x, g x) ^ 2 := fun X =>
    sq_sub_le_two_mul _ _
  have hflint : Integrable (fun X : Configuration N =>
      fluctuation ⟨g, hg.integrable one_le_two⟩ X ^ 2) (gibbsMeasure P N) :=
    (memLp_fluctuation P N hg).integrable_sq
  have hm' : ((N : ℝ) * ∫ x, g x) ^ 2 ≤ (N : ℝ) ^ 2 * ∫ x, g x ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hm (sq_nonneg _)
  have hY2 := integral_sq_linearStatistic_le P N hg
  have hint2 : ∫ X, (2 * linearStatistic g X ^ 2 + 2 * ((N : ℝ) * ∫ x, g x) ^ 2)
      ∂(gibbsMeasure P N) = 2 * ∫ X, linearStatistic g X ^ 2 ∂(gibbsMeasure P N) +
        2 * ((N : ℝ) * ∫ x, g x) ^ 2 := by
    rw [integral_add (hYsq.const_mul 2) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  have hint_int : Integrable (fun X : Configuration N =>
      2 * linearStatistic g X ^ 2 + 2 * ((N : ℝ) * ∫ x, g x) ^ 2) (gibbsMeasure P N) :=
    (hYsq.const_mul 2).add (integrable_const _)
  have hmono : ∫ X, fluctuation ⟨g, hg.integrable one_le_two⟩ X ^ 2 ∂(gibbsMeasure P N) ≤
      ∫ X, (2 * linearStatistic g X ^ 2 + 2 * ((N : ℝ) * ∫ x, g x) ^ 2) ∂(gibbsMeasure P N) :=
    integral_mono hflint hint_int hfl
  rw [hint2] at hmono
  linarith

/-- For a centred second factor, the covariance is the mixed expectation. -/
lemma gibbsCov_eq_integral_of_mean_zero (P : Parameters) (N : ℕ+) {F Φ : Configuration N → ℝ}
    (hF : MemLp F 2 (gibbsMeasure P N)) (hΦ : MemLp Φ 2 (gibbsMeasure P N))
    (hΦm : ∫ X, Φ X ∂(gibbsMeasure P N) = 0) :
    gibbsCov (gibbsMeasure P N) F Φ = ∫ X, F X * Φ X ∂(gibbsMeasure P N) := by
  unfold gibbsCov
  simp only [hΦm, sub_zero]
  have hFΦ : Integrable (fun X => F X * Φ X) (gibbsMeasure P N) :=
    hF.integrable_mul hΦ
  have hsplit : ∀ X : Configuration N, (F X - ∫ Y, F Y ∂(gibbsMeasure P N)) * Φ X =
      F X * Φ X - (∫ Y, F Y ∂(gibbsMeasure P N)) * Φ X := fun X => by ring
  simp_rw [hsplit]
  rw [integral_sub hFΦ ((hΦ.integrable one_le_two).const_mul _), integral_const_mul, hΦm,
    mul_zero, sub_zero]

/-- The periodic integration by parts on `[0, 1]`: for smooth one-periodic `G` and `φ`,
`∫₀¹ G' φ = -∫₀¹ G φ'`. -/
theorem integral_deriv_mul_eq_neg_of_periodic {G φ : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hφ : ContDiff ℝ ∞ φ) (hGp : Function.Periodic G 1) (hφp : Function.Periodic φ 1) :
    ∫ u in (0 : ℝ)..1, deriv G u * φ u = -∫ u in (0 : ℝ)..1, G u * deriv φ u := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by simp)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hIG : IntervalIntegrable (deriv G) volume 0 1 :=
    (hG1.continuous_deriv (by simp)).intervalIntegrable 0 1
  have hIφ : IntervalIntegrable (deriv φ) volume 0 1 :=
    (hφ1.continuous_deriv (by simp)).intervalIntegrable 0 1
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := φ)
    (v := G) (u' := deriv φ) (v' := deriv G)
    (fun x _ => (hφ1.differentiable (by simp)).differentiableAt.hasDerivAt)
    (fun x _ => (hG1.differentiable (by simp)).differentiableAt.hasDerivAt) hIφ hIG
  have hb : φ 1 * G 1 - φ 0 * G 0 = 0 := by
    rw [show (1 : ℝ) = 0 + 1 by norm_num, hφp 0, hGp 0]
    ring
  rw [hb] at key
  have e1 : ∫ u in (0 : ℝ)..1, deriv G u * φ u = ∫ u in (0 : ℝ)..1, φ u * deriv G u := by
    congr 1
    funext u
    ring
  have e2 : ∫ u in (0 : ℝ)..1, deriv φ u * G u = ∫ u in (0 : ℝ)..1, G u * deriv φ u := by
    congr 1
    funext u
    ring
  rw [e1, key, e2]
  ring

/-- The fluctuation of a smooth one-periodic function is a torus-smooth function of the lift. -/
lemma isTorusSmooth_fluctIntegral {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hGp : Function.Periodic G 1) (N : ℕ) :
    IsTorusSmooth (fun x : Fin N → ℝ => fluctIntegral G N x) := by
  refine ⟨?_, ?_⟩
  · unfold fluctIntegral
    exact ContDiff.sub (ContDiff.sum fun i _ => hG.comp (by fun_prop : ContDiff ℝ ∞
      fun x : Fin N → ℝ => x i)) contDiff_const
  · intro k x
    show fluctIntegral G N (Function.update x k (x k + 1)) = fluctIntegral G N x
    unfold fluctIntegral
    have hsum : ∑ i : Fin N, G (Function.update x k (x k + 1) i) = ∑ i : Fin N, G (x i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hik : i = k
      · subst hik
        simp [hGp (x i)]
      · simp [Function.update_of_ne hik]
    rw [hsum]

/-- The partial derivative of the fluctuation of a smooth function is its derivative at the
coordinate. -/
lemma partialDeriv_fluctIntegral_eq {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) {N : ℕ}
    (k : Fin N) (x : Fin N → ℝ) :
    partialDeriv (fun y => fluctIntegral G N y) k x = deriv G (x k) := by
  have h := partialDeriv_fluctIntegral_scaled (N := N) (R := G)
    (hG.differentiable (by simp)) (ℓ := 1) k x
  have e : (fun u => G (u / 1)) = G := funext fun u => by simp
  rw [e] at h
  simpa using h

/-- The derivative weight of the smooth statistic: the periodic integrand of the covariance. -/
lemma periodic_mul_deriv_profile (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (_hψ : ContDiff ℝ ∞ ψ.val) {G : ℝ → ℝ} (_hG : ContDiff ℝ ∞ G)
    (hGp : Function.Periodic G 1) :
    Function.Periodic (fun u : ℝ => deriv G u * (a * ℓ.val * ψ.val (u / ℓ.val))) 1 := by
  intro u
  have hψp := ψ.property.1
  simp only
  rw [deriv_add_one_of_periodic (F := G) hGp u, add_div, one_div, hψp (u / ℓ.val)]

/-- The covariance of a smooth fluctuation with the loop potential (the integration by parts
part of Proposition 5.5, evaluated with the uniform marginals): for a smooth one-periodic
`G`, `Cov(Fluct_N[G], 𝓛Φ_ψ) = N a ℓ ∫₀¹ G'(u) ψ(u/ℓ) du`. -/
theorem gibbsCov_fluctIntegral_eq (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hGp : Function.Periodic G 1) :
    gibbsCov (gibbsMeasure P N) (fun X : Configuration N => fluctIntegral G N X.val)
        (loopOperatorPotential P N ℓ a ψ) =
      (N : ℝ) * ∫ u in (0 : ℝ)..1, deriv G u * (a * ℓ.val * ψ.val (u / ℓ.val)) := by
  have h2 := (loop_equations_ibp P hPL N ℓ a ψ hψ hmean).2.1.2 (fun x => fluctIntegral G N x)
    (isTorusSmooth_fluctIntegral hG hGp N)
  rw [h2]
  have hper := periodic_mul_deriv_profile ℓ a ψ hψ hG hGp
  have hcont : Continuous (fun u : ℝ => deriv G u * (a * ℓ.val * ψ.val (u / ℓ.val))) :=
    ((hG.continuous_deriv (by simp)).mul
      (continuous_const.mul (hψ.continuous.comp (continuous_id.div_const _))))
  have hmem := memLp_lift_of_continuous hcont hper
  have hgd : ∀ X : Configuration N,
      gradDotPotential (fun x : Fin (N : ℕ) → ℝ => fluctIntegral G N x)
          (loopScalePotential ℓ a ψ (N : ℕ)) X.val =
        linearStatistic (hper.lift : UnitAddCircle → ℝ) X := by
    intro X
    unfold gradDotPotential linearStatistic
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialDeriv_fluctIntegral_eq hG, partialDeriv_loopScalePotential, hper.lift_coe]
  calc ∫ X : Configuration N, gradDotPotential (fun x : Fin (N : ℕ) → ℝ => fluctIntegral G N x)
          (loopScalePotential ℓ a ψ (N : ℕ)) X.val ∂(gibbsMeasure P N)
      = ∫ X : Configuration N, linearStatistic (hper.lift : UnitAddCircle → ℝ) X
          ∂(gibbsMeasure P N) := by
        congr 1
        funext X
        exact hgd X
    _ = (N : ℝ) * ∫ x : UnitAddCircle, (hper.lift : UnitAddCircle → ℝ) x :=
        integral_linearStatistic P N hmem
    _ = (N : ℝ) * ∫ u in (0 : ℝ)..1, deriv G u * (a * ℓ.val * ψ.val (u / ℓ.val)) := by
        congr 1
        rw [← UnitAddCircle.intervalIntegral_preimage 0 (hper.lift : UnitAddCircle → ℝ)]
        simp only [zero_add, Function.Periodic.lift_coe]

/-- A real `L²` function on the unit circle, given by its complex lift. -/
lemma memLp_real_of_complex {f : UnitAddCircle → ℝ}
    (h : MemLp (fun x : UnitAddCircle => (f x : ℂ)) 2 volume) : MemLp f 2 volume := by
  have := h.re
  simpa using this

/-- The fluctuation of a function on the unit circle is the fluctuation of its lift on `[0, 1]`. -/
lemma fluctuation_eq_fluctIntegral_lift {N : ℕ+} (G : UnitAddCircle → ℝ)
    (hG : Integrable G volume) (X : Configuration N) :
    fluctuation ⟨G, hG⟩ X = fluctIntegral (fun u : ℝ => G (u : UnitAddCircle)) N X.val := by
  unfold fluctuation linearStatistic fluctIntegral
  rw [← UnitAddCircle.intervalIntegral_preimage 0 G]
  simp only [zero_add]

/-- The fluctuation of a difference is the difference of the fluctuations. -/
lemma fluctuation_sub_lift {N : ℕ+} (G g : UnitAddCircle → ℝ) (hG : Integrable G volume)
    (hg : Integrable g volume) (X : Configuration N) :
    fluctuation ⟨fun z => G z - g z, hG.sub hg⟩ X =
      fluctuation ⟨G, hG⟩ X - fluctuation ⟨g, hg⟩ X := by
  unfold fluctuation linearStatistic
  rw [integral_sub hG hg, Finset.sum_sub_distrib]
  ring

/-- The loop profile of a smooth transport on the long circle is the pulled-back transport. -/
lemma loopMasterProfile_val_div (ℓ : Ioc (0 : ℝ) 1) (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ)))) (u : ℝ) :
    (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val) = loopMasterPullback (loopMasterLength ℓ) ψh u := by
  rw [loopMasterPullback_coe, div_eq_mul_inv]
  rfl

/-- The covariance of the fluctuation of a smooth unit-circle function with the loop potential:
`Cov(Fluct_N[G], 𝓛Φ) = -N a ℓ ∫_{𝕋} G ψ_c'`, where `ψ_c` is the pulled-back transport. -/
theorem gibbsCov_smooth_circle_eq (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, (loopMasterProfile ℓ ψh hψh).val t = 0)
    {Gc : UnitAddCircle → ℝ} (hGc : IsSmoothCircle Gc) :
    gibbsCov (gibbsMeasure P N) (fun X : Configuration N =>
        fluctuation ⟨Gc, (memLp_real_of_complex (memLp_unitCircle_of_isSmoothCircle hGc)).integrable
          one_le_two⟩ X)
        (loopOperatorPotential P N ℓ a (loopMasterProfile ℓ ψh hψh)) =
      -((N : ℝ) * a * ℓ.val) * ∫ z : UnitAddCircle, Gc z *
        loopMasterCircleDeriv (loopMasterPullback (loopMasterLength ℓ) ψh)
          (loopMasterPullback_smooth _ ψh hψh) z := by
  set ψc := loopMasterPullback (loopMasterLength ℓ) ψh with hψcdef
  have hψcS : IsSmoothCircle ψc := loopMasterPullback_smooth _ ψh hψh
  -- The lift of `Gc` and its smoothness.
  have hGr : ContDiff ℝ ∞ (fun u : ℝ => Gc (u : UnitAddCircle)) := hGc
  have hGp : Function.Periodic (fun u : ℝ => Gc (u : UnitAddCircle)) 1 := by
    intro u
    simp only [AddCircle.coe_add_period]
  -- The statistic is the fluctuation of the lift.
  have hfun : (fun X : Configuration N => fluctuation ⟨Gc, (memLp_real_of_complex (memLp_unitCircle_of_isSmoothCircle hGc)).integrable
      one_le_two⟩ X) = fun X : Configuration N =>
        fluctIntegral (fun u : ℝ => Gc (u : UnitAddCircle)) N X.val :=
    funext fun X => fluctuation_eq_fluctIntegral_lift Gc _ X
  rw [hfun]
  -- The Gibbs covariance computed by `gibbsCov_fluctIntegral_eq`.
  have hψφ : ∀ u : ℝ, (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val) = ψc u :=
    fun u => loopMasterProfile_val_div ℓ ψh hψh u
  have hφ : ContDiff ℝ ∞ (fun u : ℝ => a * ℓ.val * ψc (u : UnitAddCircle)) :=
    contDiff_const.mul hψcS
  have hφp : Function.Periodic (fun u : ℝ => a * ℓ.val * ψc (u : UnitAddCircle)) 1 := by
    intro u
    simp only [AddCircle.coe_add_period]
  have hG1 := gibbsCov_fluctIntegral_eq hPL P N ℓ a (loopMasterProfile ℓ ψh hψh) hψh hmean hGr hGp
  rw [hG1]
  have hφeq : ∀ u : ℝ, a * ℓ.val * (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val) =
      a * ℓ.val * ψc (u : UnitAddCircle) := fun u => by rw [hψφ]
  simp_rw [hφeq]
  -- Integration by parts moves the derivative onto the transport.
  have hIBP := integral_deriv_mul_eq_neg_of_periodic hGr hφ hGp hφp
  have hdφ : ∀ u : ℝ, deriv (fun u : ℝ => a * ℓ.val * ψc (u : UnitAddCircle)) u =
      a * ℓ.val * loopMasterCircleDeriv ψc hψcS (u : UnitAddCircle) := by
    intro u
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => ψc (u : UnitAddCircle)) u :=
      (hψcS.differentiable (by simp)).differentiableAt
    rw [deriv_const_mul _ hdiff, (loopMasterCircleDeriv_coe ψc hψcS u).symm]
  have hcirc : ∫ u in (0 : ℝ)..1, Gc (u : UnitAddCircle) *
      loopMasterCircleDeriv ψc hψcS (u : UnitAddCircle) =
      ∫ z : UnitAddCircle, Gc z * loopMasterCircleDeriv ψc hψcS z := by
    rw [← UnitAddCircle.intervalIntegral_preimage 0
      (fun z : UnitAddCircle => Gc z * loopMasterCircleDeriv ψc hψcS z)]
    simp only [zero_add]
  have hpull : ∫ u in (0 : ℝ)..1, Gc (u : UnitAddCircle) *
      (a * ℓ.val * loopMasterCircleDeriv ψc hψcS (u : UnitAddCircle)) =
      a * ℓ.val * ∫ z : UnitAddCircle, Gc z * loopMasterCircleDeriv ψc hψcS z := by
    rw [← hcirc, ← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    ring
  rw [hIBP]
  simp_rw [hdφ]
  rw [hpull]
  ring

/-- The Gibbs covariance of a fluctuation with a centred `L²` function is bounded by the `L²`
norm of the profile: `|E[Fluct_N[g] Φ]| ≤ 2N ‖g‖₂ ‖Φ‖₂`. -/
lemma abs_integral_fluctuation_mul_le (P : Parameters) (N : ℕ+) {g : UnitAddCircle → ℝ}
    (hg : MemLp g 2 volume) {Φ : Configuration N → ℝ}
    (hΦ : MemLp Φ 2 (gibbsMeasure P N)) :
    |∫ X, fluctuation ⟨g, hg.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N)| ≤
      2 * (N : ℝ) * Real.sqrt (∫ x, g x ^ 2) *
        Real.sqrt (∫ X, Φ X ^ 2 ∂(gibbsMeasure P N)) := by
  have hC := abs_integral_mul_le_sqrt_integral_sq (μ := gibbsMeasure P N)
    (X := fun X => fluctuation ⟨g, hg.integrable one_le_two⟩ X) (Y := Φ)
    (memLp_fluctuation P N hg) hΦ
  have hB := integral_sq_fluctuation_le P N hg
  have h4 : Real.sqrt (4 * (N : ℝ) ^ 2 * ∫ x, g x ^ 2) = 2 * (N : ℝ) * Real.sqrt (∫ x, g x ^ 2) := by
    rw [show 4 * (N : ℝ) ^ 2 * ∫ x, g x ^ 2 = (2 * (N : ℝ)) ^ 2 * ∫ x, g x ^ 2 by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hS : Real.sqrt (∫ X, fluctuation ⟨g, hg.integrable one_le_two⟩ X ^ 2 ∂(gibbsMeasure P N)) ≤
      2 * (N : ℝ) * Real.sqrt (∫ x, g x ^ 2) := by
    rw [← h4]
    exact Real.sqrt_le_sqrt hB
  have hnn : 0 ≤ Real.sqrt (∫ X, Φ X ^ 2 ∂(gibbsMeasure P N)) := Real.sqrt_nonneg _
  calc |∫ X, fluctuation ⟨g, hg.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N)|
      ≤ Real.sqrt (∫ X, fluctuation ⟨g, hg.integrable one_le_two⟩ X ^ 2 ∂(gibbsMeasure P N)) *
          Real.sqrt (∫ X, Φ X ^ 2 ∂(gibbsMeasure P N)) := hC
    _ ≤ 2 * (N : ℝ) * Real.sqrt (∫ x, g x ^ 2) * Real.sqrt (∫ X, Φ X ^ 2 ∂(gibbsMeasure P N)) :=
        mul_le_mul_of_nonneg_right hS hnn

/-- The covariance with a centred `L²` potential, obtained from the smooth identity by
approximation: the smooth identity is linear in the profile, and the Gibbs `L²` bound transfers
the `L²` distance of profiles to the distance of covariances. -/
theorem gibbsCov_eq_of_smooth_approx (P : Parameters) (N : ℕ+) {Φ : Configuration N → ℝ}
    (hΦ : MemLp Φ 2 (gibbsMeasure P N)) (hΦm : ∫ X, Φ X ∂(gibbsMeasure P N) = 0)
    {ξc Ψ : UnitAddCircle → ℝ} (hξc : MemLp ξc 2 volume) (hΨ : MemLp Ψ 2 volume) (c : ℝ)
    (hid : ∀ (Gc : UnitAddCircle → ℝ) (hGc : IsSmoothCircle Gc),
      gibbsCov (gibbsMeasure P N) (fun X : Configuration N =>
        fluctuation ⟨Gc, (memLp_real_of_complex (memLp_unitCircle_of_isSmoothCircle hGc)).integrable
          one_le_two⟩ X) Φ = c * (∫ z, Gc z * Ψ z))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ Gc : UnitAddCircle → ℝ, ∃ _hGc : IsSmoothCircle Gc,
      (∫ x, (Gc x - ξc x) ^ 2) < ε) :
    gibbsCov (gibbsMeasure P N) (fun X : Configuration N =>
        fluctuation ⟨ξc, hξc.integrable one_le_two⟩ X) Φ = c * (∫ z, ξc z * Ψ z) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hF := memLp_fluctuation P N hξc
  rw [gibbsCov_eq_integral_of_mean_zero P N hF hΦ hΦm]
  set M : ℝ := 2 * (N : ℝ) * Real.sqrt (∫ X, Φ X ^ 2 ∂(gibbsMeasure P N)) +
    |c| * Real.sqrt (∫ z, Ψ z ^ 2) with hMdef
  have hM : 0 ≤ M := by
    have h1 := Real.sqrt_nonneg (∫ X, Φ X ^ 2 ∂(gibbsMeasure P N))
    have h2 := Real.sqrt_nonneg (∫ z, Ψ z ^ 2)
    have h3 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    rw [hMdef]
    positivity
  -- The key estimate for every smooth profile.
  have key : ∀ (Gc : UnitAddCircle → ℝ) (hGc : IsSmoothCircle Gc),
      |(∫ X, fluctuation ⟨ξc, hξc.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N)) -
        c * (∫ z, ξc z * Ψ z)| ≤ M * Real.sqrt (∫ x, (Gc x - ξc x) ^ 2) := by
    intro Gc hGc
    have hGL : MemLp Gc 2 volume := memLp_real_of_complex (memLp_unitCircle_of_isSmoothCircle hGc)
    have hg : MemLp (fun z => Gc z - ξc z) 2 volume := hGL.sub hξc
    have hFG := memLp_fluctuation P N hGL
    have hid' := hid Gc hGc
    rw [gibbsCov_eq_integral_of_mean_zero P N hFG hΦ hΦm] at hid'
    have hdiff : ∀ X : Configuration N, fluctuation ⟨ξc, hξc.integrable one_le_two⟩ X * Φ X =
        fluctuation ⟨Gc, hGL.integrable one_le_two⟩ X * Φ X -
          fluctuation ⟨fun z => Gc z - ξc z, hg.integrable one_le_two⟩ X * Φ X := by
      intro X
      rw [fluctuation_sub_lift Gc ξc (hGL.integrable one_le_two) (hξc.integrable one_le_two) X]
      ring
    have hint1 : Integrable (fun X : Configuration N =>
        fluctuation ⟨Gc, hGL.integrable one_le_two⟩ X * Φ X) (gibbsMeasure P N) :=
      hFG.integrable_mul hΦ
    have hint2 : Integrable (fun X : Configuration N =>
        fluctuation ⟨fun z => Gc z - ξc z, hg.integrable one_le_two⟩ X * Φ X) (gibbsMeasure P N) :=
      (memLp_fluctuation P N hg).integrable_mul hΦ
    have hsplit : (∫ X, fluctuation ⟨ξc, hξc.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N)) =
        c * (∫ z, Gc z * Ψ z) -
          (∫ X, fluctuation ⟨fun z => Gc z - ξc z, hg.integrable one_le_two⟩ X * Φ X
            ∂(gibbsMeasure P N)) := by
      have e1 : (∫ X, fluctuation ⟨ξc, hξc.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N)) =
          (∫ X, fluctuation ⟨Gc, hGL.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N)) -
          (∫ X, fluctuation ⟨fun z => Gc z - ξc z, hg.integrable one_le_two⟩ X * Φ X
            ∂(gibbsMeasure P N)) := by
        rw [← integral_sub hint1 hint2]
        exact integral_congr_ae (Filter.Eventually.of_forall hdiff)
      rw [e1, hid']
    have hlin : c * (∫ z, Gc z * Ψ z) - c * (∫ z, ξc z * Ψ z) =
        c * (∫ z, (Gc z - ξc z) * Ψ z) := by
      have e2 : (∫ z, (Gc z - ξc z) * Ψ z) = (∫ z, Gc z * Ψ z) - (∫ z, ξc z * Ψ z) := by
        have e3 : (∫ z, (Gc z - ξc z) * Ψ z) = ∫ z, (Gc z * Ψ z - ξc z * Ψ z) :=
          integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
        rw [e3]
        exact integral_sub (hGL.integrable_mul hΨ) (hξc.integrable_mul hΨ)
      rw [e2]
      ring
    have hd : (∫ X, fluctuation ⟨ξc, hξc.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N)) -
        c * (∫ z, ξc z * Ψ z) = c * (∫ z, (Gc z - ξc z) * Ψ z) -
          (∫ X, fluctuation ⟨fun z => Gc z - ξc z, hg.integrable one_le_two⟩ X * Φ X
            ∂(gibbsMeasure P N)) := by
      rw [hsplit, ← hlin]
      ring
    rw [hd]
    have hC1 := abs_integral_mul_le_sqrt_integral_sq (μ := (volume : Measure UnitAddCircle))
      (X := fun z => Gc z - ξc z) (Y := Ψ) hg hΨ
    have hC2 := abs_integral_fluctuation_mul_le P N hg hΦ
    have hC1' : |∫ z, (Gc z - ξc z) * Ψ z| ≤
        Real.sqrt (∫ z, (Gc z - ξc z) ^ 2) * Real.sqrt (∫ z, Ψ z ^ 2) := hC1
    have habs := abs_sub (c * (∫ z, (Gc z - ξc z) * Ψ z))
      (∫ X, fluctuation ⟨fun z => Gc z - ξc z, hg.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N))
    have hc1 : |c * (∫ z, (Gc z - ξc z) * Ψ z)| ≤
        |c| * (Real.sqrt (∫ z, (Gc z - ξc z) ^ 2) * Real.sqrt (∫ z, Ψ z ^ 2)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hC1' (abs_nonneg c)
    calc |c * (∫ z, (Gc z - ξc z) * Ψ z) -
          (∫ X, fluctuation ⟨fun z => Gc z - ξc z, hg.integrable one_le_two⟩ X * Φ X
            ∂(gibbsMeasure P N))|
        ≤ |c * (∫ z, (Gc z - ξc z) * Ψ z)| +
          |∫ X, fluctuation ⟨fun z => Gc z - ξc z, hg.integrable one_le_two⟩ X * Φ X
            ∂(gibbsMeasure P N)| := habs
      _ ≤ |c| * (Real.sqrt (∫ z, (Gc z - ξc z) ^ 2) * Real.sqrt (∫ z, Ψ z ^ 2)) +
          2 * (N : ℝ) * Real.sqrt (∫ z, (Gc z - ξc z) ^ 2) *
            Real.sqrt (∫ X, Φ X ^ 2 ∂(gibbsMeasure P N)) := add_le_add hc1 hC2
      _ = M * Real.sqrt (∫ x, (Gc x - ξc x) ^ 2) := by
        rw [hMdef]
        ring
  -- Choose a smooth profile close to `ξc` and conclude.
  have hzero : |(∫ X, fluctuation ⟨ξc, hξc.integrable one_le_two⟩ X * Φ X ∂(gibbsMeasure P N)) -
      c * (∫ z, ξc z * Ψ z)| = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (abs_nonneg _)
    have hη : 0 < (ε / (M + 1)) ^ 2 := by positivity
    obtain ⟨Gc, hGc, hlt⟩ := happrox ((ε / (M + 1)) ^ 2) hη
    have hk := key Gc hGc
    have hs : Real.sqrt (∫ x, (Gc x - ξc x) ^ 2) ≤ ε / (M + 1) := by
      calc Real.sqrt (∫ x, (Gc x - ξc x) ^ 2) ≤ Real.sqrt ((ε / (M + 1)) ^ 2) :=
            Real.sqrt_le_sqrt hlt.le
        _ = ε / (M + 1) := Real.sqrt_sq (by positivity)
    have hMs : M * Real.sqrt (∫ x, (Gc x - ξc x) ^ 2) ≤ M * (ε / (M + 1)) :=
      mul_le_mul_of_nonneg_left hs hM
    have hfrac : M * (ε / (M + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have := abs_eq_zero.mp hzero
  linarith

/-- **Covariance of the statistic of an `L²` profile with the loop potential** (the covariance
identity of the mixed part of Proposition 5.6, before the variance is evaluated). For an `L²`
profile `ξ` on the circle of length `ℓ⁻¹` and a smooth mean-zero transport `ψ_h` of `ξ`'s
regularization, the covariance of `Fluct_N[ξ(ℓ⁻¹·)]` with `𝓛Φ_{ψ_h, a}` is `-N a ℓ ∫ ξ(ℓ⁻¹·)
ψ_h'(ℓ⁻¹·)`, the pairing
on the unit circle. -/
theorem gibbsCov_pullback_eq (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, (loopMasterProfile ℓ ψh hψh).val t = 0) :
    gibbsCov (gibbsMeasure P N) (fun X : Configuration N =>
        fluctuation ⟨loopMasterPullback (loopMasterLength ℓ) ξ.val,
          (memLp_real_of_complex (loopMasterPullback_memLp _ ξ)).integrable one_le_two⟩ X)
        (loopOperatorPotential P N ℓ a (loopMasterProfile ℓ ψh hψh)) =
      -((N : ℝ) * a * ℓ.val) * (∫ z : UnitAddCircle,
        loopMasterPullback (loopMasterLength ℓ) ξ.val z *
          loopMasterCircleDeriv (loopMasterPullback (loopMasterLength ℓ) ψh)
            (loopMasterPullback_smooth _ ψh hψh) z) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hloop := loop_equations_ibp P hPL N ℓ a (loopMasterProfile ℓ ψh hψh) hψh hmean
  have hΦ := hloop.2.1.1.1
  have hΦm := hloop.2.1.1.2
  have hψS := loopMasterPullback_smooth (loopMasterLength ℓ) ψh hψh
  have hΨ : MemLp (loopMasterCircleDeriv (loopMasterPullback (loopMasterLength ℓ) ψh) hψS)
      2 volume :=
    memLp_real_of_complex (memLp_unitCircle_of_isSmoothCircle (loopMasterCircleDeriv_smooth hψS))
  have hξc : MemLp (loopMasterPullback (loopMasterLength ℓ) ξ.val) 2 volume :=
    memLp_real_of_complex (loopMasterPullback_memLp _ ξ)
  refine gibbsCov_eq_of_smooth_approx P N hΦ hΦm hξc hΨ (-((N : ℝ) * a * ℓ.val)) ?_ ?_
  · intro Gc hGc
    exact gibbsCov_smooth_circle_eq hPL P N ℓ a ψh hψh hmean hGc
  · intro ε hε
    obtain ⟨δ, hδ, hlt⟩ := exists_pullback_regularize_sub_lt hρ (loopMasterLength ℓ) ξ hε
    exact ⟨loopMasterPullback (loopMasterLength ℓ)
        (cltRegCircle hρ (loopMasterLength ℓ) (half_pos hδ) ξ),
      loopMasterPullback_smooth _ _ (cltRegCircle_contDiff hρ _ (half_pos hδ) ξ),
      hlt (δ / 2) (half_pos hδ) (half_lt_self hδ)⟩

end Riesz1

end
