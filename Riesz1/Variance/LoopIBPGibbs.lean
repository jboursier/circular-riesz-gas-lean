/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPCutoff
public import Riesz1.Variance.LoopIBPPairs
public import Riesz1.Variance.LoopIBPHessian
public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.Variance.LoopScaleDifferential
public import Riesz1.Rigidity.NoExplosionUniform
public import Riesz1.HelfferSjostrand.SettingGibbs
import all Riesz1.Variance.LoopForceEnergy
import all Riesz1.Variance.LoopScale

/-!
# Gibbs-side estimates for the collision cutoffs

The estimates on the Gibbs law that the cutoff argument of Proposition 5.5 needs.

* At a configuration the lifted gap `hsUnitGap` is the Riesz gap divided by `N`.
* The strip where some gap is at most `u` has Gibbs mass `O(u^p)` for every `p > 0`, by Markov's
  inequality applied to the uniform inverse moments of `no_explosion_uniform`.
* The power sums of gaps lie in `L²` of the Gibbs law.
* The derivatives of the lifted energy are bounded by powers of the power sums of gaps.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace Riesz1

variable {N : ℕ+}

/-- At a configuration the lifted gap is the Riesz gap divided by `N`. -/
theorem hsUnitGap_liftConfiguration (X : Configuration N) (j : Fin (N : ℕ)) :
    hsUnitGap N j (WithLp.toLp 2 X.val) = gap X (j : ℕ) / (N : ℝ) := by
  rw [gap_div_eq X (j : ℕ)]
  have hj := cyclicLift_natCast X j
  unfold hsUnitGap
  by_cases hlast : (j : ℕ) + 1 = (N : ℕ)
  · have hnext : hsNext N j = ⟨0, N.pos⟩ := by
      apply Fin.ext
      simp only [hsNext]
      rw [hlast, Nat.mod_self]
    have hc : cyclicLift X (((j : ℕ) : ℤ) + 1) = X.val ⟨0, N.pos⟩ + 1 := by
      have h' : ((j : ℕ) : ℤ) + 1 = ((N : ℕ) : ℤ) := by exact_mod_cast hlast
      rw [h', cyclicLift_N]
    rw [hnext, hc, hj]
    simp only [hlast, ↓reduceIte]
    ring
  · have hlt : (j : ℕ) + 1 < (N : ℕ) := lt_of_le_of_ne (by exact_mod_cast j.isLt) hlast
    have hnext : hsNext N j = ⟨(j : ℕ) + 1, hlt⟩ := by
      apply Fin.ext
      simp only [hsNext]
      exact Nat.mod_eq_of_lt hlt
    have hc : cyclicLift X (((j : ℕ) : ℤ) + 1) = X.val ⟨(j : ℕ) + 1, hlt⟩ := by
      have h := cyclicLift_natCast X ⟨(j : ℕ) + 1, hlt⟩
      push_cast at h
      exact h
    rw [hnext, hc, hj]
    simp only [hlast, ↓reduceIte]
    ring

/-- Markov's inequality for one gap: the Gibbs mass of `{gap_j ≤ u}` is at most `C u^p`, with
the constant of the uniform inverse moment bound `no_explosion_uniform`. -/
theorem exists_gibbs_gap_le (P : Parameters) (hPL : External.PrekopaLeindler) {p : ℝ}
    (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (j : ℤ) {u : ℝ}, 0 < u →
      gibbsMeasure P N {X | gap X j ≤ u} ≤ ENNReal.ofReal (C * u ^ p) := by
  obtain ⟨C, hC, h⟩ := no_explosion_uniform P hp
  refine ⟨C, hC, fun N j u hu => ?_⟩
  obtain ⟨hI, hbound⟩ := h hPL N j
  have hmeas : Measurable (fun X : Configuration N => ENNReal.ofReal (gap X j ^ (-p))) :=
    ENNReal.measurable_ofReal.comp ((measurable_gap j).pow_const _)
  have hε0 : ENNReal.ofReal (u ^ (-p)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos hu _
  have hεtop : ENNReal.ofReal (u ^ (-p)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmarkov := meas_ge_le_lintegral_div (μ := gibbsMeasure P N) hmeas.aemeasurable hε0 hεtop
  have hsub : {X : Configuration N | gap X j ≤ u} ⊆
      {X : Configuration N | ENNReal.ofReal (u ^ (-p)) ≤ ENNReal.ofReal (gap X j ^ (-p))} := by
    intro X hX
    have hgpos := gap_pos X j
    have hle : u ^ (-p) ≤ gap X j ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos hgpos hX (by linarith)
    exact ENNReal.ofReal_le_ofReal hle
  have hdiv : (∫⁻ X, ENNReal.ofReal (gap X j ^ (-p)) ∂gibbsMeasure P N) /
      ENNReal.ofReal (u ^ (-p)) ≤ ENNReal.ofReal (C * u ^ p) := by
    refine (ENNReal.div_le_div_right hbound _).trans_eq ?_
    rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hu _)]
    congr 1
    rw [Real.rpow_neg hu.le, div_inv_eq_mul]
  exact (measure_mono hsub).trans (hmarkov.trans hdiv)

/-- The strip where some gap is at most `u` has Gibbs mass `O(u^p)`. -/
theorem exists_gibbs_strip_le (P : Parameters) (hPL : External.PrekopaLeindler) {p : ℝ}
    (hp : 0 < p) (N : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : ℝ}, 0 < u →
      gibbsMeasure P N {X | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ u} ≤
        ENNReal.ofReal (C * u ^ p) := by
  obtain ⟨C, hC, h⟩ := exists_gibbs_gap_le P hPL hp
  refine ⟨(N : ℝ) * C, mul_pos (by exact_mod_cast N.pos) hC, fun {u} hu => ?_⟩
  have hset : {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ u} =
      ⋃ j : Fin (N : ℕ), {X : Configuration N | gap X (j : ℕ) ≤ u} := by
    ext X
    simp only [mem_iUnion]
    rfl
  rw [hset]
  refine (measure_iUnion_fintype_le _ _).trans ?_
  have hterm : ∀ j : Fin (N : ℕ), gibbsMeasure P N {X : Configuration N | gap X (j : ℕ) ≤ u} ≤
      ENNReal.ofReal (C * u ^ p) := fun j => h N (j : ℕ) hu
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  apply le_of_eq
  congr 1
  ring

/-- Power sums of gaps lie in `L²` of the Gibbs law, for every positive exponent. -/
theorem memLp_two_gapPowerSum (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    {r : ℝ} (hr : 0 < r) :
    MemLp (fun X : Configuration N => gapPowerSum r X) 2 (gibbsMeasure P N) := by
  rw [memLp_two_iff_integrable_sq (measurable_gapPowerSum r).aestronglyMeasurable]
  have hI := integrable_gapPowerSum P hPL (by linarith : 0 < r * 2) N
  have hdom : Integrable (fun X : Configuration N => (N : ℝ) ^ (2 : ℝ) * gapPowerSum (r * 2) X)
      (gibbsMeasure P N) := hI.const_mul _
  refine Integrable.mono' hdom ((measurable_gapPowerSum r).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => ?_)
  have hpow : gapPowerSum r X ^ (2 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) * gapPowerSum (r * 2) X :=
    gapPowerSum_rpow_le X (by norm_num)
  rw [Real.rpow_two] at hpow
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (gapPowerSum_nonneg r X) 2)]
  exact hpow

/-- The second partial derivative of the field potential is `a ψ'(x_k/ℓ)` on the diagonal and
zero off it, so it is bounded by `|a| M` when `ψ'` is bounded by `M`. -/
theorem abs_partialDeriv_partialDeriv_loopScalePotential_le (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) {M : ℝ}
    (hM : ∀ u : ℝ, |deriv ψ.val u| ≤ M) {N : ℕ} (k l : Fin N) (x : Fin N → ℝ) :
    |partialDeriv (partialDeriv (loopScalePotential ℓ a ψ N) k) l x| ≤ |a| * M := by
  have hℓ : ℓ.val ≠ 0 := ℓ.property.1.ne'
  have hfun : partialDeriv (loopScalePotential ℓ a ψ N) k =
      fun y => a * ℓ.val * ψ.val (y k / ℓ.val) :=
    funext (partialDeriv_loopScalePotential ℓ a ψ k)
  rw [hfun]
  by_cases hlk : l = k
  · subst hlk
    change |deriv (fun t : ℝ => a * ℓ.val * ψ.val (Function.update x l t l / ℓ.val)) (x l)| ≤
      |a| * M
    simp only [Function.update_self]
    have hdiv : HasDerivAt (fun t : ℝ => t / ℓ.val) (ℓ.val)⁻¹ (x l) := by
      have := (hasDerivAt_id (x l)).div_const ℓ.val
      simpa [one_div] using this
    have h1 : HasDerivAt (fun t : ℝ => ψ.val (t / ℓ.val))
        (deriv ψ.val (x l / ℓ.val) * (ℓ.val)⁻¹) (x l) :=
      ((hψ.differentiable (by simp)) (x l / ℓ.val)).hasDerivAt.comp (x l) hdiv
    rw [(h1.const_mul (a * ℓ.val)).deriv]
    have hval : a * ℓ.val * (deriv ψ.val (x l / ℓ.val) * (ℓ.val)⁻¹) =
        a * deriv ψ.val (x l / ℓ.val) := by
      field_simp
    rw [hval, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg a)
  · have hkl : k ≠ l := fun h => hlk h.symm
    change |deriv (fun t : ℝ => a * ℓ.val * ψ.val (Function.update x l t k / ℓ.val)) (x l)| ≤
      |a| * M
    have hconst : (fun t : ℝ => a * ℓ.val * ψ.val (Function.update x l t k / ℓ.val)) =
        fun _ => a * ℓ.val * ψ.val (x k / ℓ.val) := by
      funext t
      rw [Function.update_of_ne hkl]
    rw [hconst, deriv_const]
    simp only [abs_zero]
    exact mul_nonneg (abs_nonneg a) ((abs_nonneg _).trans (hM 0))

/-- The derivative of the lifted energy in one coordinate is bounded by a power sum of gaps of
order `s + 1`. -/
theorem exists_abs_partialDeriv_energyLift_le (s : RieszExponent) (N : ℕ+) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Configuration N) (k : Fin (N : ℕ)),
      |partialDeriv (energyLift s (N : ℕ)) k X.val| ≤ C * gapPowerSum (s.val + 1) X := by
  obtain ⟨Cg, hCg, hgb⟩ := deriv_hurwitzKernel_bound s.val s.property.1 s.property.2
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  refine ⟨(N : ℝ) ^ (-s.val) * 2 * (N : ℝ) * Cg * (N : ℝ) ^ (s.val + 1), by positivity,
    fun X k => ?_⟩
  rw [partialDeriv_energyLift s.property.1 s.property.2 X.val
    (fun i j hij => coe_sub_ne_zero X hij) k]
  have hterm : ∀ j : Fin (N : ℕ),
      |if j = k then (0 : ℝ) else deriv (hurwitzKernel s.val) (X.val k - X.val j)|
        ≤ Cg * (N : ℝ) ^ (s.val + 1) * gapPowerSum (s.val + 1) X := by
    intro j
    by_cases hjk : j = k
    · simp only [hjk, ↓reduceIte, abs_zero]
      have hg := gapPowerSum_nonneg (s.val + 1) X
      positivity
    · simp only [hjk, ↓reduceIte]
      have hkj : k ≠ j := fun h => hjk h.symm
      have hne := coe_sub_ne_zero X hkj
      have h1 := hgb (X.val k - X.val j) hne
      have h2 := dist_rpow_le_gapPowerSum X hkj (r := s.val + 1) (by linarith [s.property.1])
      have hexp : (-s.val - 1) = -(s.val + 1) := by ring
      rw [hexp] at h1
      calc |deriv (hurwitzKernel s.val) (X.val k - X.val j)|
          ≤ Cg * dist ((X.val k - X.val j : ℝ) : UnitAddCircle) 0 ^ (-(s.val + 1)) := h1
        _ ≤ Cg * ((N : ℝ) ^ (s.val + 1) * gapPowerSum (s.val + 1) X) :=
            mul_le_mul_of_nonneg_left h2 hCg.le
        _ = Cg * (N : ℝ) ^ (s.val + 1) * gapPowerSum (s.val + 1) X := by ring
  have hsum := Finset.abs_sum_le_sum_abs
    (fun j : Fin (N : ℕ) => if j = k then (0 : ℝ) else deriv (hurwitzKernel s.val) (X.val k - X.val j))
    Finset.univ
  have hcard : ∑ j : Fin (N : ℕ), Cg * (N : ℝ) ^ (s.val + 1) * gapPowerSum (s.val + 1) X =
      (N : ℝ) * (Cg * (N : ℝ) ^ (s.val + 1) * gapPowerSum (s.val + 1) X) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbound : |∑ j : Fin (N : ℕ), (if j = k then (0 : ℝ) else
      deriv (hurwitzKernel s.val) (X.val k - X.val j))| ≤
      (N : ℝ) * (Cg * (N : ℝ) ^ (s.val + 1) * gapPowerSum (s.val + 1) X) :=
    hsum.trans ((Finset.sum_le_sum fun j _ => hterm j).trans hcard.le)
  have hpos : 0 < (N : ℝ) ^ (-s.val) := Real.rpow_pos_of_pos hNr _
  rw [abs_mul, abs_of_pos hpos, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc (N : ℝ) ^ (-s.val) * (2 * |∑ j : Fin (N : ℕ), (if j = k then (0 : ℝ) else
          deriv (hurwitzKernel s.val) (X.val k - X.val j))|)
      ≤ (N : ℝ) ^ (-s.val) * (2 * ((N : ℝ) * (Cg * (N : ℝ) ^ (s.val + 1) *
          gapPowerSum (s.val + 1) X))) := by gcongr
    _ = (N : ℝ) ^ (-s.val) * 2 * (N : ℝ) * Cg * (N : ℝ) ^ (s.val + 1) *
          gapPowerSum (s.val + 1) X := by ring

/-- The second derivative of the lifted energy is bounded by a power sum of gaps of order
`s + 2`. -/
theorem exists_abs_partialDeriv_partialDeriv_energyLift_le (s : RieszExponent) (N : ℕ+) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : Configuration N) (k l : Fin (N : ℕ)),
      |partialDeriv (partialDeriv (energyLift s (N : ℕ)) k) l X.val| ≤
        C * gapPowerSum (s.val + 2) X := by
  obtain ⟨C, hC, hb⟩ := exists_hessianSum_le s N
  refine ⟨C, hC, fun X k l => ?_⟩
  rw [partialDeriv_partialDeriv_energyLift_eq' s X.val (fun i j hij => coe_sub_ne_zero X hij) k l]
  exact hb X k l

/-- A continuous function with period `p > 0` is bounded. -/
theorem exists_abs_le_of_continuous_periodic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : Continuous f) (hper : Function.Periodic f p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, |f u| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := 0) (b := p)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun u => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hp u
  rw [hfy, ← Real.norm_eq_abs]
  exact (hM y ⟨hy.1, hy.2.le⟩).trans (le_max_left _ _)

/-- The derivative of a periodic function is periodic with the same period. -/
theorem periodic_deriv_of {ψ : ℝ → ℝ} {p : ℝ} (hper : Function.Periodic ψ p) :
    Function.Periodic (deriv ψ) p := by
  intro x
  have h := deriv_comp_add_const (f := ψ) (a := p) (x := x)
  rw [funext hper] at h
  exact h.symm

/-- The derivative of a smooth periodic profile is bounded. -/
theorem exists_abs_deriv_le_of_smooth_periodic {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hper : Function.Periodic ψ ℓ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℝ, |deriv ψ u| ≤ M :=
  exists_abs_le_of_continuous_periodic hℓ ((contDiff_infty_iff_deriv.mp hψ).2).continuous
    (periodic_deriv_of hper)

/-- The first partial derivative of the field potential is bounded by the profile bound. -/
theorem abs_partialDeriv_loopScalePotential_le (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) {M : ℝ} (hM : ∀ u : ℝ, |ψ.val u| ≤ M) {N : ℕ} (k : Fin N)
    (x : Fin N → ℝ) :
    |partialDeriv (loopScalePotential ℓ a ψ N) k x| ≤ |a| * ℓ.val * M := by
  rw [partialDeriv_loopScalePotential ℓ a ψ k x, abs_mul, abs_mul, abs_of_pos ℓ.property.1]
  exact mul_le_mul_of_nonneg_left (hM _) (mul_nonneg (abs_nonneg a) ℓ.property.1.le)

/-- Cauchy–Schwarz on a measurable set: `∫_S W ≤ (∫ W²)^{1/2} μ(S)^{1/2}` for nonnegative
square-integrable `W`. -/
theorem integral_indicator_le_sqrt_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {W : Ω → ℝ} {S : Set Ω} (hS : MeasurableSet S) (hW0 : ∀ x, 0 ≤ W x)
    (hW : MemLp W 2 μ) :
    ∫ x, S.indicator W x ∂μ ≤ (∫ x, W x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (μ.real S) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    have h := Real.HolderConjugate.conjExponent (p := (2 : ℝ)) (by norm_num)
    have h2 : Real.conjExponent 2 = 2 := by norm_num [Real.conjExponent]
    rw [h2] at h
    exact h
  have hind : ∀ x, S.indicator W x = W x * S.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ S <;> simp [hx]
  have hI : MemLp (S.indicator (fun _ => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hS.nullMeasurableSet
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2) hpq
    (f := W) (g := S.indicator (fun _ => (1 : ℝ)))
    (Filter.Eventually.of_forall hW0)
    (Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ S <;> simp [hx])
    (by rw [ENNReal.ofReal_ofNat]; exact hW) (by rw [ENNReal.ofReal_ofNat]; exact hI)
  have hint : ∫ x, S.indicator (fun _ => (1 : ℝ)) x ^ 2 ∂μ = μ.real S := by
    rw [← integral_indicator_one hS]
    congr 1
    funext x
    by_cases hx : x ∈ S <;> simp [hx]
  simp only [Real.rpow_two] at h
  rw [show (fun x => S.indicator W x) = fun x => W x * S.indicator (fun _ => (1 : ℝ)) x from
    funext hind]
  rw [hint] at h
  exact h

/-- The gaps at scale `2h` form a measurable set. -/
theorem measurableSet_strip {N : ℕ+} (u : ℝ) :
    MeasurableSet {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ u} := by
  have : {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ u} =
      ⋃ j : Fin (N : ℕ), {X : Configuration N | gap X (j : ℕ) ≤ u} := by
    ext X
    simp only [mem_iUnion, mem_ofPred_eq]
  rw [this]
  exact MeasurableSet.iUnion fun j => measurableSet_le (measurable_gap _) measurable_const

/-- A pointwise bound `|E_h| ≤ K (h⁻¹ + h⁻²) W 1_{S_{2h}}`, with `S_{2h}` the strip where some
gap is at most `2 h N`, gives an integral tending to zero as `h ↓ 0`. -/
theorem tendsto_integral_strip_error {N : ℕ+} (P : Parameters) (hPL : External.PrekopaLeindler)
    {W : Configuration N → ℝ} (hW0 : ∀ X, 0 ≤ W X) (hW : MemLp W 2 (gibbsMeasure P N))
    {E : ℝ → Configuration N → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      |E h X| ≤ K * (h⁻¹ + h⁻¹ ^ 2) *
        {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator W X) :
    Tendsto (fun h : ℝ => ∫ X, |E h X| ∂gibbsMeasure P N) (𝓝[>] 0) (𝓝 0) := by
  have hfin : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  obtain ⟨C, hC, hstrip⟩ := exists_gibbs_strip_le P hPL (p := 6) (by norm_num) N
  set μ := gibbsMeasure P N with hμ
  set D : ℝ := C * (2 * (N : ℝ)) ^ 6 with hD
  have hD0 : 0 ≤ D := by positivity
  -- the strip mass decays like `h ^ 6`
  have hmass : ∀ h : ℝ, 0 < h → μ.real {X : Configuration N | ∃ j : Fin (N : ℕ),
      gap X (j : ℕ) ≤ 2 * h * N} ≤ D * h ^ 6 := by
    intro h hh
    have hu : 0 < 2 * h * (N : ℝ) := by positivity
    have hm := hstrip hu
    have hreal : μ.real {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N} ≤
        C * (2 * h * (N : ℝ)) ^ (6 : ℝ) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hm
    have hpow : (2 * h * (N : ℝ)) ^ (6 : ℝ) = (2 * (N : ℝ)) ^ 6 * h ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hpow] at hreal
    calc μ.real _ ≤ C * ((2 * (N : ℝ)) ^ 6 * h ^ 6) := hreal
      _ = D * h ^ 6 := by rw [hD]; ring
  -- the square root of the strip mass
  set Wn : ℝ := (∫ X, W X ^ 2 ∂μ) ^ (1 / 2 : ℝ) with hWn
  have hWn0 : 0 ≤ Wn := Real.rpow_nonneg (integral_nonneg fun X => sq_nonneg _) _
  have hsqrt : ∀ h : ℝ, 0 < h → μ.real {X : Configuration N | ∃ j : Fin (N : ℕ),
      gap X (j : ℕ) ≤ 2 * h * N} ^ (1 / 2 : ℝ) ≤ Real.sqrt D * h ^ 3 := by
    intro h hh
    have hm := hmass h hh
    have hnn : 0 ≤ μ.real {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} := measureReal_nonneg
    calc μ.real _ ^ (1 / 2 : ℝ) ≤ (D * h ^ 6) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hnn hm (by norm_num)
      _ = Real.sqrt (D * h ^ 6) := (Real.sqrt_eq_rpow _).symm
      _ = Real.sqrt D * h ^ 3 := by
          rw [Real.sqrt_mul hD0, show h ^ 6 = (h ^ 3) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]
  -- the integral bound
  have hWint : Integrable W μ := hW.integrable (by norm_num)
  have hbound : ∀ h : ℝ, 0 < h → h ≤ 1 → ∫ X, |E h X| ∂μ ≤
      K * Real.sqrt D * Wn * (h ^ 2 + h) := by
    intro h hh h1
    have hstripm := measurableSet_strip (N := N) (2 * h * (N : ℝ))
    have hcs := integral_indicator_le_sqrt_mul μ hstripm hW0 hW
    have hpos : 0 ≤ K * (h⁻¹ + h⁻¹ ^ 2) := mul_nonneg hK (by positivity)
    have hint : ∫ X, |E h X| ∂μ ≤ ∫ X, K * (h⁻¹ + h⁻¹ ^ 2) *
        {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator W X ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => abs_nonneg _)
        ((hWint.indicator hstripm).const_mul _) (Filter.Eventually.of_forall
          fun X => hE h hh h1 X)
    rw [integral_const_mul] at hint
    have hstrip' := hcs.trans (mul_le_mul_of_nonneg_left (hsqrt h hh) hWn0)
    have hh3 : (h⁻¹ + h⁻¹ ^ 2) * h ^ 3 = h ^ 2 + h := by
      field_simp
    calc ∫ X, |E h X| ∂μ ≤ K * (h⁻¹ + h⁻¹ ^ 2) * ∫ X,
          {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator W X ∂μ :=
          hint
      _ ≤ K * (h⁻¹ + h⁻¹ ^ 2) * (Wn * (Real.sqrt D * h ^ 3)) :=
          mul_le_mul_of_nonneg_left hstrip' hpos
      _ = K * Real.sqrt D * Wn * (h ^ 2 + h) := by
          calc K * (h⁻¹ + h⁻¹ ^ 2) * (Wn * (Real.sqrt D * h ^ 3))
              = K * Real.sqrt D * Wn * ((h⁻¹ + h⁻¹ ^ 2) * h ^ 3) := by ring
            _ = K * Real.sqrt D * Wn * (h ^ 2 + h) := by rw [hh3]
  -- the squeeze
  have hlim : Tendsto (fun h : ℝ => K * Real.sqrt D * Wn * (h ^ 2 + h)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ => K * Real.sqrt D * Wn * (h ^ 2 + h)) := by fun_prop
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Filter.Eventually.of_forall fun h => integral_nonneg fun X => abs_nonneg _
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with h hh
    exact hbound h hh.1 hh.2.le

end Riesz1
