/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPErrors
public import Riesz1.Variance.LoopIBPTransfer
public import Riesz1.Variance.LoopIBPPeriodic
public import Riesz1.Variance.LoopIBPGibbs

/-!
# Integration identities for the diagonal field: the cutoff limit

Proposition 5.5, clauses 1 and 2 for `N ≥ 2`: for a smooth periodic
test `G` with bounded partial derivatives,
`∫ 𝓛Φ · G dμ = ∫ ∇Φ · ∇G dμ` on the Gibbs law.

The proof applies the Helffer–Sjöstrand identity (`rieszIBP`) to the collision cutoffs
`χ_h Φ`, splits the Langevin expression as `χ_h 𝓛Φ` plus an error (`langevin_cutoff_eq`), and lets
`h ↓ 0`: the bulk terms converge by dominated convergence, and the error terms vanish by the
strip estimate (`tendsto_integral_strip_error`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

variable {N : ℕ+}

/-- The field potential is periodic under integer translations of the lift, by the mean-zero
periodicity of its primitive. -/
theorem loopHS_periodic (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) (k : ℤ)
    (x : HsEuclidean N) :
    loopHS ℓ a ψ N (hsTranslate (k : ℝ) x) = loopHS ℓ a ψ N x := by
  have hper := (periodic_primitive hψ.continuous ψ.property.1 hmean).int_mul k
  have hof : (WithLp.ofLp (hsTranslate (k : ℝ) x) : Fin (N : ℕ) → ℝ) =
      fun i => WithLp.ofLp x i + (k : ℝ) := by
    funext i
    simp [hsTranslate_apply]
  unfold loopHS loopScalePotential
  rw [hof]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsh : (WithLp.ofLp x i + (k : ℝ)) / ℓ.val = WithLp.ofLp x i / ℓ.val + (k : ℝ) * ℓ.val⁻¹ := by
    ring
  rw [hsh]
  exact hper (WithLp.ofLp x i / ℓ.val)

/-- The configuration lifts continuously into the Euclidean lift. -/
theorem continuous_toLp_config (N : ℕ+) :
    Continuous (fun X : Configuration N => (WithLp.toLp 2 X.val : HsEuclidean N)) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin (N : ℕ) => ℝ)).comp continuous_subtype_val

/-- Partial derivatives of a smooth function are continuous along configurations. -/
theorem continuous_hsPartial_config {F : HsEuclidean N → ℝ} (hF : ContDiff ℝ ∞ F)
    (k : Fin (N : ℕ)) : Continuous (fun X : Configuration N => hsPartial F k (WithLp.toLp 2 X.val)) :=
  (contDiff_hsPartial hF k).continuous.comp (continuous_toLp_config N)

/-- The first partial derivatives of the Hamiltonian are continuous along configurations. -/
theorem continuous_hsPartial_rieszH_config (P : Parameters) (k : Fin (N : ℕ)) :
    Continuous (fun X : Configuration N => hsPartial (rieszH P N) k (WithLp.toLp 2 X.val)) := by
  have hfd : ContDiffOn ℝ 0 (fun y => fderiv ℝ (rieszH P N) y) (hsChamber N) :=
    (hsPairExpression_contDiffOn (rieszPairs P N)).fderiv_of_isOpen (isOpen_hsChamber N)
      (by simp)
  have hcont : ContinuousOn (fun y => fderiv ℝ (rieszH P N) y (EuclideanSpace.single k 1))
      (hsChamber N) :=
    (hfd.continuousOn).clm_apply continuousOn_const
  exact hcont.comp_continuous (continuous_toLp_config N) fun X =>
    mem_hsChamber_configuration X

/-- The Langevin expression `𝓛Φ` is continuous along configurations. -/
theorem continuous_loopLHS_config (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    Continuous (fun X : Configuration N => loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)) := by
  unfold loopLHS
  refine Continuous.sub (continuous_finsetSum _ fun k _ => ?_)
    (continuous_finsetSum _ fun k _ => ?_)
  · exact (continuous_hsPartial_rieszH_config P k).mul
      (continuous_hsPartial_config (contDiff_loopHS ℓ a ψ hψ N) k)
  · exact continuous_hsPartial_config (contDiff_hsPartial (contDiff_loopHS ℓ a ψ hψ N) k) k

/-- The error term of the cutoff expression is continuous along configurations. -/
theorem continuous_loopError_config (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (h : ℝ) :
    Continuous (fun X : Configuration N => loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)) := by
  unfold loopError
  have hΦ := contDiff_loopHS ℓ a ψ hψ N
  have hχ := contDiff_hsUnitGapCutoff N h
  have hΦc : Continuous (fun X : Configuration N => loopHS ℓ a ψ N (WithLp.toLp 2 X.val)) :=
    hΦ.continuous.comp (continuous_toLp_config N)
  have hHχ : Continuous (fun X : Configuration N => ∑ k : Fin (N : ℕ),
      hsPartial (rieszH P N) k (WithLp.toLp 2 X.val) *
        hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val)) :=
    continuous_finsetSum _ fun k _ =>
      (continuous_hsPartial_rieszH_config P k).mul (continuous_hsPartial_config hχ k)
  have hχχ : Continuous (fun X : Configuration N => ∑ k : Fin (N : ℕ),
      hsPartial (hsPartial (hsUnitGapCutoff N h) k) k (WithLp.toLp 2 X.val)) :=
    continuous_finsetSum _ fun k _ => continuous_hsPartial_config (contDiff_hsPartial hχ k) k
  have hχΦ : Continuous (fun X : Configuration N => ∑ k : Fin (N : ℕ),
      hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
        hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val)) :=
    continuous_finsetSum _ fun k _ =>
      (continuous_hsPartial_config hχ k).mul (continuous_hsPartial_config hΦ k)
  exact ((hΦc.mul (hHχ.sub hχχ)).sub (continuous_const.mul hχΦ))

/-- The Langevin expression is bounded by a multiple of `1 + gapPowerSum (s + 1)`. -/
theorem exists_abs_loopLHS_le (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (N : ℕ+) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : Configuration N,
      |loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)| ≤
        K * (1 + gapPowerSum ((parametersExponent P).val + 1) X) := by
  obtain ⟨CE, hCE, hEb⟩ := exists_abs_partialDeriv_energyLift_le (parametersExponent P) N
  obtain ⟨Mψ, hMψ0, hMψb⟩ := exists_abs_le_of_continuous_periodic (inv_pos.mpr ℓ.property.1)
    hψ.continuous ψ.property.1
  obtain ⟨M', hM'0, hM'b⟩ := exists_abs_deriv_le_of_smooth_periodic (inv_pos.mpr ℓ.property.1)
    hψ ψ.property.1
  have hβ : 0 ≤ P.val.1 := P.property.1.le
  set M1 := |a| * ℓ.val * Mψ with hM1
  have hM1' : 0 ≤ M1 := by
    have := ℓ.property.1
    positivity
  refine ⟨(N : ℝ) * (P.val.1 * CE * M1) + (N : ℝ) * (|a| * M'), by positivity, fun X => ?_⟩
  set x : HsEuclidean N := WithLp.toLp 2 X.val with hxdef
  set g := gapPowerSum ((parametersExponent P).val + 1) X with hgdef
  have hg0 : 0 ≤ g := gapPowerSum_nonneg _ X
  unfold loopLHS
  have hA : |∑ k : Fin (N : ℕ), hsPartial (rieszH P N) k x * hsPartial (loopHS ℓ a ψ N) k x| ≤
      (N : ℝ) * (P.val.1 * CE * g * M1) := by
    refine abs_sum_le_card_mul fun k => ?_
    rw [abs_mul]
    have h1 : |hsPartial (rieszH P N) k x| ≤ P.val.1 * CE * g := by
      have hHk' : hsPartial (rieszH P N) k x = P.val.1 *
          partialDeriv (energyLift (parametersExponent P) (N : ℕ)) k X.val :=
        hsPartial_hsPairExpression_of_mem_chamber N P.val.1 P.property.1 (parametersExponent P)
          (mem_hsChamber_configuration X) k
      rw [hHk', abs_mul, abs_of_nonneg hβ]
      exact (mul_le_mul_of_nonneg_left (hEb X k) hβ).trans_eq (by ring)
    have h2 : |hsPartial (loopHS ℓ a ψ N) k x| ≤ M1 := by
      rw [hxdef, hsPartial_loopHS ℓ a ψ hψ N k _]
      exact abs_partialDeriv_loopScalePotential_le ℓ a ψ hMψb k _
    exact mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (mul_nonneg hβ hCE) hg0)
  have hB : |∑ k : Fin (N : ℕ), hsPartial (hsPartial (loopHS ℓ a ψ N) k) k x| ≤
      (N : ℝ) * (|a| * M') := by
    refine abs_sum_le_card_mul fun k => ?_
    rw [hxdef, hsPartial_hsPartial_loopHS ℓ a ψ hψ N k k _]
    exact abs_partialDeriv_partialDeriv_loopScalePotential_le ℓ a ψ hψ hM'b k k _
  have hsplit := abs_sub (∑ k : Fin (N : ℕ), hsPartial (rieszH P N) k x *
      hsPartial (loopHS ℓ a ψ N) k x)
    (∑ k : Fin (N : ℕ), hsPartial (hsPartial (loopHS ℓ a ψ N) k) k x)
  have hM1g : (N : ℝ) * (P.val.1 * CE * g * M1) = (N : ℝ) * (P.val.1 * CE * M1) * g := by ring
  have hN1 : (0 : ℝ) ≤ (N : ℝ) * (P.val.1 * CE * M1) := by positivity
  have hN2 : (0 : ℝ) ≤ (N : ℝ) * (|a| * M') := by positivity
  nlinarith [hA, hB, hsplit, hM1g, hN1, hN2, hg0]

/-- At each configuration the cutoff equals one for all small scales. -/
theorem eventually_hsUnitGapCutoff_eq_one (N : ℕ+) (X : Configuration N) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), hsUnitGapCutoff N h (WithLp.toLp 2 X.val) = 1 := by
  have hpos : ∀ j : Fin (N : ℕ), 0 < hsUnitGap N j (WithLp.toLp 2 X.val) := fun j => by
    rw [hsUnitGap_liftConfiguration]
    exact div_pos (gap_pos X _) (by exact_mod_cast N.pos)
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ j : Fin (N : ℕ), 2 * h < hsUnitGap N j (WithLp.toLp 2 X.val) := by
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous fun h : ℝ => 2 * h := by fun_prop
    have ht : Tendsto (fun h : ℝ => 2 * h) (𝓝 0) (𝓝 (2 * 0)) := hc.tendsto 0
    rw [mul_zero] at ht
    exact ht.eventually (gt_mem_nhds (hpos j))
  filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h hh hh0
  exact hsUnitGapCutoff_eq_one_of_le (show (0 : ℝ) < h from hh0) fun j => (hh j).le

/-- A continuous integrand against the cutoff converges by dominated convergence. -/
theorem tendsto_cutoff_integral (P : Parameters) (N : ℕ+) {g : Configuration N → ℝ}
    (hg : Continuous g) {B : Configuration N → ℝ} (hB : Integrable B (gibbsMeasure P N))
    (hgB : ∀ X, |g X| ≤ B X) :
    Tendsto (fun h : ℝ => ∫ X, hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g X ∂gibbsMeasure P N)
      (𝓝[>] 0) (𝓝 (∫ X, g X ∂gibbsMeasure P N)) := by
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hB ?_
  · refine Filter.Eventually.of_forall fun h => ?_
    exact (((contDiff_hsUnitGapCutoff N h).continuous.comp (continuous_toLp_config N)).mul hg
      ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with h hh
    refine Filter.Eventually.of_forall fun X => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hsUnitGapCutoff_nonneg N h _)]
    have h1 := hsUnitGapCutoff_le_one N h (WithLp.toLp 2 X.val)
    have h0 := hsUnitGapCutoff_nonneg N h (WithLp.toLp 2 X.val)
    calc hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * |g X| ≤ 1 * |g X| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = |g X| := one_mul _
      _ ≤ B X := hgB X
  · refine Filter.Eventually.of_forall fun X => ?_
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_hsUnitGapCutoff_eq_one N X] with h hh
    rw [hh, one_mul]

/-- A bounded-by-strip error term tends to zero in integral. -/
theorem tendsto_integral_zero_of_strip (P : Parameters) (hPL : External.PrekopaLeindler)
    (N : ℕ+) {W : Configuration N → ℝ} (hW0 : ∀ X, 0 ≤ W X) (hW : MemLp W 2 (gibbsMeasure P N))
    {E : ℝ → Configuration N → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      |E h X| ≤ K * (h⁻¹ + h⁻¹ ^ 2) *
        {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator W X) :
    Tendsto (fun h : ℝ => ∫ X, E h X ∂gibbsMeasure P N) (𝓝[>] 0) (𝓝 0) := by
  have key := tendsto_integral_strip_error P hPL hW0 hW hK hE
  refine squeeze_zero_norm' ?_ key
  filter_upwards [self_mem_nhdsWithin] with h hh
  have := norm_integral_le_integral_norm (μ := gibbsMeasure P N) (E h)
  simpa [Real.norm_eq_abs] using this

/-- The first partial derivative of the cutoff is bounded by the strip indicator. -/
theorem abs_hsPartial_hsUnitGapCutoff_strip_le (N : ℕ+) {C : ℝ}
    (hC : ∀ t, |deriv loopStep t| ≤ C) {h : ℝ} (hh : 0 < h) (k : Fin (N : ℕ))
    (X : Configuration N) :
    |hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val)| ≤
      (N : ℝ) * (2 * C * h⁻¹) *
        {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
          (fun _ => (1 : ℝ)) X := by
  by_cases hX : ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N
  · rw [indicator_of_mem (show X ∈ {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} from hX), mul_one]
    have := abs_hsPartial_hsUnitGapCutoff_le N hC hh k (WithLp.toLp 2 X.val)
    have e : 2 * C / h = 2 * C * h⁻¹ := by ring
    rw [e] at this
    exact this
  · rw [indicator_of_notMem (show X ∉ {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} from hX), mul_zero, abs_nonpos_iff]
    have hx : ∀ j : Fin (N : ℕ), 2 * h < hsUnitGap N j (WithLp.toLp 2 X.val) := by
      intro j
      rw [hsUnitGap_liftConfiguration, lt_div_iff₀ (by exact_mod_cast N.pos : (0 : ℝ) < N)]
      exact not_le.mp (not_exists.mp hX j)
    exact hsPartial_hsUnitGapCutoff_eq_zero hh hx k

/-- Clauses 1 and 2 of Proposition 5.5 in the form that the cutoff argument
gives: the Langevin expression of `Φ` against a smooth periodic `G` with bounded partial
derivatives equals the Dirichlet pairing. -/
theorem loopLHS_integral_eq (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0)
    (G : HsEuclidean N → ℝ) (hG : ContDiff ℝ ∞ G)
    (hGper : ∀ (k : ℤ) (x : HsEuclidean N), G (hsTranslate (k : ℝ) x) = G x)
    (MG : ℝ) (hMG : ∀ x, |G x| ≤ MG)
    (hdG : ∀ (k : Fin (N : ℕ)) (x : HsEuclidean N), |hsPartial G k x| ≤ MG) :
    ∫ X : Configuration N, loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) *
        G (WithLp.toLp 2 X.val) ∂gibbsMeasure P N =
      ∫ X : Configuration N, (∑ k : Fin (N : ℕ), hsPartial (loopHS ℓ a ψ N) k
        (WithLp.toLp 2 X.val) * hsPartial G k (WithLp.toLp 2 X.val)) ∂gibbsMeasure P N := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  have hs : 0 < (parametersExponent P).val + 1 := by
    have := (parametersExponent P).property.1
    linarith
  have hI1 : Integrable (fun X : Configuration N =>
      1 + gapPowerSum ((parametersExponent P).val + 1) X) (gibbsMeasure P N) :=
    (integrable_const (1 : ℝ)).add (integrable_gapPowerSum P hPL hs N)
  obtain ⟨KL, hKL0, hKL⟩ := exists_abs_loopLHS_le P ℓ a ψ hψ N
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_loopError_bound P ℓ a ψ hψ hmean N
  obtain ⟨M0, hM0, hM0b⟩ := exists_abs_loopHS_le ℓ a ψ hψ hmean N
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_deriv_loopStep
  have hC : ∀ t, |deriv loopStep t| ≤ C₀ := fun t => (hC₀b t).1
  obtain ⟨Mψ, hMψ0, hMψb⟩ := exists_abs_le_of_continuous_periodic (inv_pos.mpr ℓ.property.1)
    hψ.continuous ψ.property.1
  set M1 := |a| * ℓ.val * Mψ with hM1
  have hΦk : ∀ (k : Fin (N : ℕ)) (x : HsEuclidean N), |hsPartial (loopHS ℓ a ψ N) k x| ≤ M1 :=
    fun k x => by
      rw [hsPartial_loopHS ℓ a ψ hψ N k x]
      exact abs_partialDeriv_loopScalePotential_le ℓ a ψ hMψb k _
  have hΦ : ContDiff ℝ ∞ (loopHS ℓ a ψ N) := contDiff_loopHS ℓ a ψ hψ N
  have hΦper : ∀ (k : ℤ) (x : HsEuclidean N),
      loopHS ℓ a ψ N (hsTranslate (k : ℝ) x) = loopHS ℓ a ψ N x :=
    loopHS_periodic ℓ a ψ hψ hmean N
  have hGc : Continuous (fun X : Configuration N => G (WithLp.toLp 2 X.val)) :=
    hG.continuous.comp (continuous_toLp_config N)
  -- the scalar pieces, as functions of configurations
  set g1 : Configuration N → ℝ := fun X =>
    loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val) with hg1def
  set g4 : Configuration N → ℝ := fun X => ∑ k : Fin (N : ℕ),
    hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) * hsPartial G k (WithLp.toLp 2 X.val)
    with hg4def
  have hg1c : Continuous g1 :=
    (continuous_loopLHS_config P ℓ a ψ hψ).mul hGc
  have hg4c : Continuous g4 := continuous_finsetSum _ fun k _ =>
    (continuous_hsPartial_config (contDiff_loopHS ℓ a ψ hψ N) k).mul
      (continuous_hsPartial_config hG k)
  have hg1B : ∀ X, |g1 X| ≤ KL * MG * (1 + gapPowerSum ((parametersExponent P).val + 1) X) := by
    intro X
    rw [hg1def, abs_mul]
    have h1 := hKL X
    have h2 := hMG (WithLp.toLp 2 X.val)
    have h0 : 0 ≤ 1 + gapPowerSum ((parametersExponent P).val + 1) X :=
      by have := gapPowerSum_nonneg ((parametersExponent P).val + 1) X; linarith
    calc |loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)| * |G (WithLp.toLp 2 X.val)|
        ≤ (KL * (1 + gapPowerSum ((parametersExponent P).val + 1) X)) * MG :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hKL0 h0)
      _ = KL * MG * (1 + gapPowerSum ((parametersExponent P).val + 1) X) := by ring
  have hg1I : Integrable (fun X : Configuration N =>
      KL * MG * (1 + gapPowerSum ((parametersExponent P).val + 1) X)) (gibbsMeasure P N) :=
    hI1.const_mul _
  have hg4B : ∀ X, |g4 X| ≤ (N : ℝ) * (M1 * MG) := by
    intro X
    have := abs_sum_le_card_mul (M := (N : ℕ)) (f := fun k : Fin (N : ℕ) =>
      hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) * hsPartial G k (WithLp.toLp 2 X.val))
      (B := M1 * MG) fun k => by
        rw [abs_mul]
        exact mul_le_mul (hΦk k (WithLp.toLp 2 X.val)) (hdG k (WithLp.toLp 2 X.val))
          (abs_nonneg _) (le_trans (abs_nonneg _) (hΦk k (WithLp.toLp 2 X.val)))
    simpa [hg4def] using this
  have hg4I : Integrable g4 (gibbsMeasure P N) := by
    refine Integrable.mono' (integrable_const ((N : ℝ) * (M1 * MG))) hg4c.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    exact hg4B X
  have hMG0 : 0 ≤ MG := (abs_nonneg _).trans (hMG 0)
  have hχc : ∀ h : ℝ, Continuous (fun X : Configuration N =>
      hsUnitGapCutoff N h (WithLp.toLp 2 X.val)) := fun h =>
    (contDiff_hsUnitGapCutoff N h).continuous.comp (continuous_toLp_config N)
  have hΦc : Continuous (fun X : Configuration N => loopHS ℓ a ψ N (WithLp.toLp 2 X.val)) :=
    hΦ.continuous.comp (continuous_toLp_config N)
  have hu : ∀ h : ℝ, 0 < h → 0 ≤ h⁻¹ + h⁻¹ ^ 2 := fun h hh =>
    add_nonneg (inv_nonneg.mpr hh.le) (sq_nonneg _)
  -- the integrable integrands of the identity
  have hint_of : ∀ {f B : Configuration N → ℝ}, Continuous f → Integrable B (gibbsMeasure P N) →
      (∀ X, |f X| ≤ B X) → Integrable f (gibbsMeasure P N) := fun {f B} hf hB hfB =>
    Integrable.mono' hB hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hfB X)
  -- the strip bound of the error `Φ` times `G` against the strip indicator
  have hE2 : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      |loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val)| ≤
        (K₁ * MG) * (h⁻¹ + h⁻¹ ^ 2) * {X : Configuration N | ∃ j : Fin (N : ℕ),
          gap X (j : ℕ) ≤ 2 * h * N}.indicator (fun X : Configuration N =>
            1 + gapPowerSum ((parametersExponent P).val + 1) X) X := by
    intro h hh _ X
    rw [abs_mul]
    have h1 := hK₁ h hh X
    have h2 := hMG (WithLp.toLp 2 X.val)
    have hind0 : 0 ≤ {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
        (fun X : Configuration N => 1 + gapPowerSum ((parametersExponent P).val + 1) X) X :=
      indicator_nonneg (fun Y _ => by
        have := gapPowerSum_nonneg ((parametersExponent P).val + 1) Y
        linarith) X
    calc |loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)| * |G (WithLp.toLp 2 X.val)|
        ≤ (K₁ * (h⁻¹ + h⁻¹ ^ 2) * {X : Configuration N | ∃ j : Fin (N : ℕ),
            gap X (j : ℕ) ≤ 2 * h * N}.indicator (fun X : Configuration N =>
              1 + gapPowerSum ((parametersExponent P).val + 1) X) X) * MG :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (mul_nonneg hK₁0 (hu h hh)) hind0)
      _ = (K₁ * MG) * (h⁻¹ + h⁻¹ ^ 2) * {X : Configuration N | ∃ j : Fin (N : ℕ),
            gap X (j : ℕ) ≤ 2 * h * N}.indicator (fun X : Configuration N =>
              1 + gapPowerSum ((parametersExponent P).val + 1) X) X := by ring
  have hWf : MemLp (fun X : Configuration N => 1 + gapPowerSum ((parametersExponent P).val + 1) X)
      2 (gibbsMeasure P N) :=
    (memLp_const (1 : ℝ)).add (memLp_two_gapPowerSum P hPL N hs)
  have hT2 : Tendsto (fun h : ℝ => ∫ X, loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) *
      G (WithLp.toLp 2 X.val) ∂gibbsMeasure P N) (𝓝[>] 0) (𝓝 0) :=
    tendsto_integral_zero_of_strip P hPL N (fun X => by
        have := gapPowerSum_nonneg ((parametersExponent P).val + 1) X
        linarith) hWf (mul_nonneg hK₁0 hMG0) hE2
  -- the strip bound of the cross term `Φ Σ ∂_kχ ∂_kG`
  have hE3 : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      |loopHS ℓ a ψ N (WithLp.toLp 2 X.val) * ∑ k : Fin (N : ℕ),
          hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
            hsPartial G k (WithLp.toLp 2 X.val)| ≤
        (M0 * (N : ℝ) ^ 2 * (2 * C₀) * MG) * (h⁻¹ + h⁻¹ ^ 2) *
          {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
            (fun _ => (1 : ℝ)) X := by
    intro h hh _ X
    have hind0 : 0 ≤ {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
        (fun _ => (1 : ℝ)) X := indicator_nonneg (fun _ _ => zero_le_one) X
    have hS : |∑ k : Fin (N : ℕ), hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
        hsPartial G k (WithLp.toLp 2 X.val)| ≤
        (N : ℝ) * ((N : ℝ) * (2 * C₀ * h⁻¹) * {X : Configuration N | ∃ j : Fin (N : ℕ),
          gap X (j : ℕ) ≤ 2 * h * N}.indicator (fun _ => (1 : ℝ)) X * MG) := by
      refine abs_sum_le_card_mul fun k => ?_
      rw [abs_mul]
      exact mul_le_mul (abs_hsPartial_hsUnitGapCutoff_strip_le N hC hh k X)
        (hdG k (WithLp.toLp 2 X.val)) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hC₀) (inv_nonneg.mpr hh.le))) hind0)
    rw [abs_mul]
    calc |loopHS ℓ a ψ N (WithLp.toLp 2 X.val)| * |∑ k : Fin (N : ℕ),
          hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) * hsPartial G k (WithLp.toLp 2 X.val)|
        ≤ M0 * ((N : ℝ) * ((N : ℝ) * (2 * C₀ * h⁻¹) * {X : Configuration N | ∃ j : Fin (N : ℕ),
          gap X (j : ℕ) ≤ 2 * h * N}.indicator (fun _ => (1 : ℝ)) X * MG)) :=
          mul_le_mul (hM0b _) hS (abs_nonneg _) hM0
      _ = (M0 * (N : ℝ) ^ 2 * (2 * C₀) * MG) * h⁻¹ * {X : Configuration N | ∃ j : Fin (N : ℕ),
          gap X (j : ℕ) ≤ 2 * h * N}.indicator (fun _ => (1 : ℝ)) X := by ring
      _ ≤ (M0 * (N : ℝ) ^ 2 * (2 * C₀) * MG) * (h⁻¹ + h⁻¹ ^ 2) *
          {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator
            (fun _ => (1 : ℝ)) X := by
          apply mul_le_mul_of_nonneg_right _ hind0
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (mul_nonneg hM0 (by positivity))
            (by positivity)) hMG0)
          linarith [sq_nonneg h⁻¹]
  have hW1 : MemLp (fun _ : Configuration N => (1 : ℝ)) 2 (gibbsMeasure P N) := memLp_const 1
  have hT3 : Tendsto (fun h : ℝ => ∫ X, loopHS ℓ a ψ N (WithLp.toLp 2 X.val) *
      ∑ k : Fin (N : ℕ), hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
        hsPartial G k (WithLp.toLp 2 X.val) ∂gibbsMeasure P N) (𝓝[>] 0) (𝓝 0) :=
    tendsto_integral_zero_of_strip P hPL N (fun _ => zero_le_one) hW1
      (mul_nonneg (mul_nonneg (mul_nonneg hM0 (by positivity)) (by positivity)) hMG0) hE3
  -- the limits of the bulk terms
  have hT1 := tendsto_cutoff_integral P N hg1c hg1I hg1B
  have hT4 := tendsto_cutoff_integral P N hg4c (integrable_const ((N : ℝ) * (M1 * MG)))
    (fun X => (hg4B X).trans_eq rfl)
  -- the pointwise identities behind the integral identity at scale `h`
  have hid : ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∫ X, hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g1 X ∂gibbsMeasure P N +
          ∫ X, loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val)
            ∂gibbsMeasure P N =
        ∫ X, loopHS ℓ a ψ N (WithLp.toLp 2 X.val) * ∑ k : Fin (N : ℕ),
            hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
              hsPartial G k (WithLp.toLp 2 X.val) ∂gibbsMeasure P N +
          ∫ X, hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g4 X ∂gibbsMeasure P N := by
    intro h hh hh1
    have hχd : Differentiable ℝ (hsUnitGapCutoff N h) :=
      (contDiff_hsUnitGapCutoff N h).differentiable (by simp)
    have hΦd : Differentiable ℝ (loopHS ℓ a ψ N) := hΦ.differentiable (by simp)
    set hfT := hsUnitGapCutoffTest hh (loopHS ℓ a ψ N) hΦ hΦper with hfTdef
    have hibp := rieszIBP P N hN hfT G hG hGper
    have hL : ∀ X : Configuration N,
        (inner ℝ (gradient (hsPairExpression (rieszPairs P N)) (WithLp.toLp 2 X.val))
            (gradient hfT.toFun (WithLp.toLp 2 X.val)) -
          Laplacian.laplacian hfT.toFun (WithLp.toLp 2 X.val)) * G (WithLp.toLp 2 X.val) =
        hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g1 X +
          loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val) := by
      intro X
      have key := langevin_cutoff_eq P N ℓ a ψ hψ h (WithLp.toLp 2 X.val)
      change (inner ℝ (gradient (rieszH P N) (WithLp.toLp 2 X.val))
          (gradient (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val)) -
        Laplacian.laplacian (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y)
          (WithLp.toLp 2 X.val)) * G (WithLp.toLp 2 X.val) = _
      rw [key, hg1def]
      ring
    have hR : ∀ X : Configuration N,
        inner ℝ (gradient hfT.toFun (WithLp.toLp 2 X.val)) (gradient G (WithLp.toLp 2 X.val)) =
        loopHS ℓ a ψ N (WithLp.toLp 2 X.val) * ∑ k : Fin (N : ℕ),
            hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
              hsPartial G k (WithLp.toLp 2 X.val) +
          hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g4 X := by
      intro X
      rw [inner_gradient_eq_sum_hsPartial, hg4def]
      have hd : ∀ k : Fin (N : ℕ), hsPartial hfT.toFun k (WithLp.toLp 2 X.val) =
          hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) * loopHS ℓ a ψ N (WithLp.toLp 2 X.val) +
            hsUnitGapCutoff N h (WithLp.toLp 2 X.val) *
              hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) := fun k =>
        hsPartial_mul (hχd _) (hΦd _) k
      simp only [hd]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hWnn : ∀ X : Configuration N, 0 ≤ 1 + gapPowerSum ((parametersExponent P).val + 1) X :=
      fun X => by
        have := gapPowerSum_nonneg ((parametersExponent P).val + 1) X
        linarith
    have hsplitL : ∫ X, (hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g1 X +
          loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val))
            ∂gibbsMeasure P N =
        ∫ X, hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g1 X ∂gibbsMeasure P N +
          ∫ X, loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val)
            ∂gibbsMeasure P N := by
      refine integral_add ?_ ?_
      · refine hint_of ((hχc h).mul hg1c) hg1I (fun X => ?_)
        have h1 := hsUnitGapCutoff_le_one N h (WithLp.toLp 2 X.val)
        have h0 := hsUnitGapCutoff_nonneg N h (WithLp.toLp 2 X.val)
        rw [abs_mul, abs_of_nonneg h0]
        calc hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * |g1 X|
            ≤ 1 * |g1 X| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = |g1 X| := one_mul _
          _ ≤ KL * MG * (1 + gapPowerSum ((parametersExponent P).val + 1) X) := hg1B X
      · refine hint_of ((continuous_loopError_config P ℓ a ψ hψ h).mul hGc)
          (hI1.const_mul ((K₁ * MG) * (h⁻¹ + h⁻¹ ^ 2))) (fun X => ?_)
        refine (hE2 h hh hh1 X).trans ?_
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg hK₁0 hMG0) (hu h hh))
        exact indicator_le_self' (fun Y _ => hWnn Y) X
    have hsplitR : ∫ X, (loopHS ℓ a ψ N (WithLp.toLp 2 X.val) * ∑ k : Fin (N : ℕ),
            hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
              hsPartial G k (WithLp.toLp 2 X.val) +
          hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g4 X) ∂gibbsMeasure P N =
        ∫ X, loopHS ℓ a ψ N (WithLp.toLp 2 X.val) * ∑ k : Fin (N : ℕ),
            hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
              hsPartial G k (WithLp.toLp 2 X.val) ∂gibbsMeasure P N +
          ∫ X, hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g4 X ∂gibbsMeasure P N := by
      refine integral_add ?_ ?_
      · -- the cross term is bounded globally by the derivative bound of the cutoff
        refine hint_of ((hΦc).mul (continuous_finsetSum _ fun k _ =>
          ((continuous_hsPartial_config (contDiff_hsUnitGapCutoff N h) k).mul
            (continuous_hsPartial_config hG k)))) (integrable_const
            (M0 * ((N : ℝ) * ((N : ℝ) * (2 * C₀ * h⁻¹) * MG)))) (fun X => ?_)
        rw [abs_mul]
        have hS : |∑ k : Fin (N : ℕ), hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
            hsPartial G k (WithLp.toLp 2 X.val)| ≤
            (N : ℝ) * ((N : ℝ) * (2 * C₀ * h⁻¹) * MG) := by
          refine abs_sum_le_card_mul fun k => ?_
          rw [abs_mul]
          have e : 2 * C₀ / h = 2 * C₀ * h⁻¹ := by ring
          have hχ' := abs_hsPartial_hsUnitGapCutoff_le N hC hh k (WithLp.toLp 2 X.val)
          rw [e] at hχ'
          exact mul_le_mul hχ' (hdG k (WithLp.toLp 2 X.val)) (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hC₀)
              (inv_nonneg.mpr hh.le)))
        exact mul_le_mul (hM0b _) hS (abs_nonneg _) hM0
      · refine hint_of ((hχc h).mul hg4c) (integrable_const ((N : ℝ) * (M1 * MG))) (fun X => ?_)
        have h1 := hsUnitGapCutoff_le_one N h (WithLp.toLp 2 X.val)
        have h0 := hsUnitGapCutoff_nonneg N h (WithLp.toLp 2 X.val)
        rw [abs_mul, abs_of_nonneg h0]
        calc hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * |g4 X|
            ≤ 1 * ((N : ℝ) * (M1 * MG)) :=
              mul_le_mul h1 (hg4B X) (abs_nonneg _) zero_le_one
          _ = (N : ℝ) * (M1 * MG) := one_mul _
    calc ∫ X, hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g1 X ∂gibbsMeasure P N +
          ∫ X, loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val)
            ∂gibbsMeasure P N
        = ∫ X, (hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g1 X +
            loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val))
              ∂gibbsMeasure P N := hsplitL.symm
      _ = ∫ X, (inner ℝ (gradient (hsPairExpression (rieszPairs P N)) (WithLp.toLp 2 X.val))
            (gradient hfT.toFun (WithLp.toLp 2 X.val)) -
          Laplacian.laplacian hfT.toFun (WithLp.toLp 2 X.val)) * G (WithLp.toLp 2 X.val)
            ∂gibbsMeasure P N := integral_congr_ae (Filter.Eventually.of_forall fun X => (hL X).symm)
      _ = ∫ X, inner ℝ (gradient hfT.toFun (WithLp.toLp 2 X.val)) (gradient G (WithLp.toLp 2 X.val))
            ∂gibbsMeasure P N := hibp
      _ = ∫ X, (loopHS ℓ a ψ N (WithLp.toLp 2 X.val) * ∑ k : Fin (N : ℕ),
            hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
              hsPartial G k (WithLp.toLp 2 X.val) +
          hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g4 X) ∂gibbsMeasure P N :=
            integral_congr_ae (Filter.Eventually.of_forall hR)
      _ = _ := hsplitR
  -- the scalar limit
  have heq : (fun h : ℝ => ∫ X, loopHS ℓ a ψ N (WithLp.toLp 2 X.val) * ∑ k : Fin (N : ℕ),
            hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
              hsPartial G k (WithLp.toLp 2 X.val) ∂gibbsMeasure P N +
          ∫ X, hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g4 X ∂gibbsMeasure P N) =ᶠ[𝓝[>] 0]
        (fun h : ℝ => ∫ X, hsUnitGapCutoff N h (WithLp.toLp 2 X.val) * g1 X ∂gibbsMeasure P N +
          ∫ X, loopError P N ℓ a ψ h (WithLp.toLp 2 X.val) * G (WithLp.toLp 2 X.val)
            ∂gibbsMeasure P N) := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with h hh
    exact (hid h hh.1 hh.2.le).symm
  have hlim := tendsto_nhds_unique (hT1.add (hT2)) (Tendsto.congr' heq (hT3.add hT4))
  have hfinal : ∫ X, g1 X ∂gibbsMeasure P N = ∫ X, g4 X ∂gibbsMeasure P N := by
    simpa using hlim
  exact hfinal

end Riesz1
