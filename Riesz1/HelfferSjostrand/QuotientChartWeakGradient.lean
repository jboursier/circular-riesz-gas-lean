/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartGibbs
public import Riesz1.HelfferSjostrand.QuotientChartUnfolding
public import Riesz1.HelfferSjostrand.SobolevWeakGradient
public import Riesz1.ToMathlib.EllipticRegularity.Exhaustion

/-!
# Ordinary weak gradients in quotient charts

The inverse-density periodized identity unfolds to ordinary Lebesgue
integration. The representatives are the actual completed value and gradient
pulled back by the chamber projection, including across rotation seams.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff ENNReal

namespace Riesz1

namespace Internal

/-- The ambient quotient projection is unchanged by integer rotations. -/
theorem hs_quotient_mk_translate {N : ℕ+} (k : ℤ) (x : HsEuclidean N) :
    (QuotientAddGroup.mk (hsTranslate (k : ℝ) x) : HsCylinder N) = QuotientAddGroup.mk x := by
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (hsPeriodLattice_mem_iff _).mpr
  refine ⟨k, fun i => ?_⟩
  change x i + (k : ℝ) - x i = (k : ℝ)
  ring

/-- Unfolding the completed weak identity, with ambient cylinder
extensions only used to write Euclidean functions on the whole space. -/
theorem hsSobolev_cover_weakGradient {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (V : HsCylinder N → ℝ) (G : HsCylinder N → HsEuclidean N)
    (hV : ∀ x : HsConfiguration N, V x.val = hsSobolevValue _ f x)
    (hG : ∀ x : HsConfiguration N, G x.val = hsSobolevGradient _ f x)
    (v : HsEuclidean N) :
    HasWeakDirectionalDerivativeOn (hsChamber N)
      (fun x => V (QuotientAddGroup.mk x))
      (fun x => inner ℝ (G (QuotientAddGroup.mk x)) v) v := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let u : HsEuclidean N → ℝ := fun x => V (QuotientAddGroup.mk x)
  let g : HsEuclidean N → ℝ := fun x => inner ℝ (G (QuotientAddGroup.mk x)) v
  have hVL : MemLp (fun x : HsConfiguration N => V x.val) 2 μ := by
    simpa only [hV] using (Lp.memLp (hsSobolevValue μ f))
  have hGL : MemLp (fun x : HsConfiguration N => G x.val) 2 μ := by
    simpa only [hG] using (Lp.memLp (hsSobolevGradient μ f))
  have hu : LocallyIntegrableOn u (hsChamber N) :=
    (locallySquareIntegrableOn_gibbs_quotient_mk χ hc hVL).locallyIntegrableOn
      (isOpen_hsChamber N)
  have hGlocal := (locallySquareIntegrableOn_gibbs_quotient_mk χ hc hGL).locallyIntegrableOn
    (isOpen_hsChamber N)
  have hg : LocallyIntegrableOn g (hsChamber N) := by
    have hh := (InnerProductSpace.toDual ℝ (HsEuclidean N) v).locallyIntegrableOn_comp hGlocal
    change LocallyIntegrableOn (fun x => inner ℝ v (G (QuotientAddGroup.mk x)))
      (hsChamber N) at hh
    simpa only [g, real_inner_comm] using hh
  refine ⟨hu, hg, ?_⟩
  intro ψ hψ hψc hψU
  let η := fun y => ψ y * Real.exp (hsPairExpression χ y)
  let ρ := fun y => fderiv ℝ ψ y v * Real.exp (hsPairExpression χ y)
  have hη : Continuous η := WeightedSobolev.continuous_cutoff_mul (isOpen_hsChamber N)
    hψ.continuous hψU (Real.continuous_exp.comp_continuousOn
      (hsPairExpression_contDiffOn χ).continuousOn)
  have hρ : Continuous ρ := WeightedSobolev.continuous_cutoff_mul (isOpen_hsChamber N)
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    ((tsupport_fderiv_apply_subset ℝ v).trans hψU)
    (Real.continuous_exp.comp_continuousOn (hsPairExpression_contDiffOn χ).continuousOn)
  have hηc : HasCompactSupport η := hψc.mul_right
  have hρc : HasCompactSupport ρ := (hψc.fderiv_apply ℝ v).mul_right
  have hηU : tsupport η ⊆ hsChamber N := tsupport_mul_subset_left.trans hψU
  have hρU : tsupport ρ ⊆ hsChamber N := tsupport_mul_subset_left.trans
    ((tsupport_fderiv_apply_subset ℝ v).trans hψU)
  have hup (k : ℤ) (x : HsEuclidean N) : u (hsTranslate (k : ℝ) x) = u x := by
    exact congrArg V (hs_quotient_mk_translate k x)
  have hgp (k : ℤ) (x : HsEuclidean N) : g (hsTranslate (k : ℝ) x) = g x := by
    exact congrArg (fun q => inner ℝ (G q) v) (hs_quotient_mk_translate k x)
  have huv (x : HsConfiguration N) : hsSmoothValue u x = hsSobolevValue μ f x := by
    change V (QuotientAddGroup.mk (hsLiftPoint N x)) = _
    rw [← show x.val = (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) from
      (congrArg Subtype.val (hsChamberProjection_liftPoint x)).symm]
    exact hV x
  have hgv (x : HsConfiguration N) : hsSmoothValue g x =
      inner ℝ (hsSobolevGradient μ f x) v := by
    change inner ℝ (G (QuotientAddGroup.mk (hsLiftPoint N x))) v = _
    rw [← show x.val = (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) from
      (congrArg Subtype.val (hsChamberProjection_liftPoint x)).symm, hG]
  have hleft := hsGibbsIntegral_periodized_test_locallyIntegrable χ hc hη hηc hηU hg hgp
  have hright := hsGibbsIntegral_periodized_test_locallyIntegrable χ hc hρ hρc hρU hu hup
  have hweak := hsSobolev_weakGradient hN χ hc f hψ hψc hψU v
  simp only [hgv] at hleft
  simp only [huv, mul_comm (hsSmoothValue _ _)] at hright
  change _ = -(∫ x, hsSobolevValue μ f x * hsSmoothValue
    (vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ρ hρc) x ∂μ) at hweak
  rw [hleft, hright] at hweak
  have hcancel (t z : ℝ) : Real.exp t * (Real.exp (-t) * z) = z := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have heη (x : HsEuclidean N) : η x * (Real.exp (-hsPairExpression χ x) * g x) = ψ x * g x := by
    dsimp [η]
    rw [mul_assoc, hcancel]
  have heρ (x : HsEuclidean N) : ρ x * (Real.exp (-hsPairExpression χ x) * u x) =
      fderiv ℝ ψ x v * u x := by
    dsimp [ρ]
    rw [mul_assoc, hcancel]
  simp only [heη, heρ] at hweak
  have hZ : ((hsPartitionFunction χ)⁻¹).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr (hsPartitionFunction_lt_top χ hc).ne,
      ENNReal.inv_ne_top.mpr (hsPartitionFunction_pos χ).ne'⟩
  have he : ((hsPartitionFunction χ)⁻¹).toReal * (∫ x, ψ x * g x) =
      ((hsPartitionFunction χ)⁻¹).toReal * (-(∫ x, fderiv ℝ ψ x v * u x)) := by
    simpa only [mul_neg] using hweak
  simpa only [smul_eq_mul] using mul_left_cancel₀ hZ he

end Internal

/-- The chart clause for the Gibbs completion.
On every chart domain the actual completed value and gradient have locally
Lebesgue L² representatives and obey the ordinary weak-gradient identity.
Injectivity of the projection is unnecessary for this local assertion. -/
theorem hsSobolev_chart_weakGradient {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (U : Set (HsEuclidean N)) (hU : U ⊆ hsChamber N) :
    ∃ (V : HsEuclidean N → ℝ) (G : HsEuclidean N → HsEuclidean N),
      (∀ x : U,
        V x.val = hsSobolevValue _ f (hsChamberProjection ⟨x.val, hU x.property⟩) ∧
        G x.val = hsSobolevGradient _ f (hsChamberProjection ⟨x.val, hU x.property⟩)) ∧
      LocallySquareIntegrableOn U V ∧ LocallySquareIntegrableOn U G ∧
      ∀ v, HasWeakDirectionalDerivativeOn U V (fun x => inner ℝ (G x) v) v := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let V : HsCylinder N → ℝ := Function.extend Subtype.val (hsSobolevValue μ f) (fun _ => 0)
  let G : HsCylinder N → HsEuclidean N :=
    Function.extend Subtype.val (hsSobolevGradient μ f) (fun _ => 0)
  have hV : ∀ x : HsConfiguration N, V x.val = hsSobolevValue μ f x :=
    Subtype.val_injective.extend_apply _ _
  have hG : ∀ x : HsConfiguration N, G x.val = hsSobolevGradient μ f x :=
    Subtype.val_injective.extend_apply _ _
  have hVL : MemLp (fun x : HsConfiguration N => V x.val) 2 μ := by
    simpa only [hV] using Lp.memLp (hsSobolevValue μ f)
  have hGL : MemLp (fun x : HsConfiguration N => G x.val) 2 μ := by
    simpa only [hG] using Lp.memLp (hsSobolevGradient μ f)
  refine ⟨(fun x => V (QuotientAddGroup.mk x)), (fun x => G (QuotientAddGroup.mk x)),
    ?_, (locallySquareIntegrableOn_gibbs_quotient_mk χ hc hVL).mono hU,
    (locallySquareIntegrableOn_gibbs_quotient_mk χ hc hGL).mono hU, ?_⟩
  · intro x
    exact ⟨hV (hsChamberProjection ⟨x.val, hU x.property⟩),
      hG (hsChamberProjection ⟨x.val, hU x.property⟩)⟩
  · intro v
    exact (Internal.hsSobolev_cover_weakGradient hN χ hc f V G hV hG v).mono hU

/-- Ordinary chart integration by parts for the actual completed
representatives, with both sides expressed as Lebesgue chart integrals.
The chart may cross an integer rotation seam. -/
theorem hsSobolev_chart_integral {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {U : Set (HsEuclidean N)} (hUo : IsOpen U) (hU : U ⊆ hsChamber N)
    {ψ : HsEuclidean N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (v : HsEuclidean N) :
    (∫ x : U, ψ x.val * inner ℝ
      (hsSobolevGradient _ f (hsChamberProjection ⟨x.val, hU x.property⟩)) v
        ∂Measure.comap (Subtype.val : U → HsEuclidean N) volume) =
      -(∫ x : U, hsSobolevValue _ f (hsChamberProjection ⟨x.val, hU x.property⟩) *
        fderiv ℝ ψ x.val v
          ∂Measure.comap (Subtype.val : U → HsEuclidean N) volume) := by
  obtain ⟨V, G, hrep, _, _, hweak⟩ := hsSobolev_chart_weakGradient hN χ hc f U hU
  have hl : (∫ x : U, ψ x.val * inner ℝ
      (hsSobolevGradient _ f (hsChamberProjection ⟨x.val, hU x.property⟩)) v
        ∂Measure.comap (Subtype.val : U → HsEuclidean N) volume) =
      ∫ x, ψ x * inner ℝ (G x) v := by
    calc
      _ = ∫ x : U, ψ x.val * inner ℝ (G x.val) v
          ∂Measure.comap (Subtype.val : U → HsEuclidean N) volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [(hrep x).2]
      _ = ∫ x in U, ψ x * inner ℝ (G x) v :=
        integral_subtype_comap (μ := (volume : Measure (HsEuclidean N))) hUo.measurableSet
          (fun x => ψ x * inner ℝ (G x) v)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun hs => hx (hψU hs)), zero_mul])
  have hr : (∫ x : U, hsSobolevValue _ f (hsChamberProjection ⟨x.val, hU x.property⟩) *
      fderiv ℝ ψ x.val v ∂Measure.comap (Subtype.val : U → HsEuclidean N) volume) =
      ∫ x, fderiv ℝ ψ x v * V x := by
    calc
      _ = ∫ x : U, fderiv ℝ ψ x.val v * V x.val
          ∂Measure.comap (Subtype.val : U → HsEuclidean N) volume := by
        apply integral_congr_ae
        filter_upwards with x
        rw [(hrep x).1, mul_comm]
      _ = ∫ x in U, fderiv ℝ ψ x v * V x :=
        integral_subtype_comap (μ := (volume : Measure (HsEuclidean N))) hUo.measurableSet
          (fun x => fderiv ℝ ψ x v * V x)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [fderiv_of_notMem_tsupport ℝ (fun hs => hx (hψU hs)), zero_apply, zero_mul])
  rw [hl, hr]
  simpa only [smul_eq_mul] using (hweak v).2.2 ψ hψ hψc hψU

/-- The value and gradient of every completed element are locally
Lebesgue-integrable as actual functions on each Euclidean chart. -/
theorem hsSobolev_chart_locallyIntegrable {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {U : Set (HsEuclidean N)} (hUo : IsOpen U) (hU : U ⊆ hsChamber N) :
    LocallyIntegrable
      (fun x : U => hsSobolevValue _ f (hsChamberProjection ⟨x.val, hU x.property⟩))
      (Measure.comap (Subtype.val : U → HsEuclidean N) volume) ∧
    LocallyIntegrable
      (fun x : U => hsSobolevGradient _ f (hsChamberProjection ⟨x.val, hU x.property⟩))
      (Measure.comap (Subtype.val : U → HsEuclidean N) volume) := by
  obtain ⟨V, G, hrep, hVL, hGL, _⟩ := hsSobolev_chart_weakGradient hN χ hc f U hU
  have hv := (locallyIntegrable_comap hUo.measurableSet).mpr (hVL.locallyIntegrableOn hUo)
  have hg := (locallyIntegrable_comap hUo.measurableSet).mpr (hGL.locallyIntegrableOn hUo)
  constructor
  · convert hv using 1
    funext x
    exact (hrep x).1.symm
  · convert hg using 1
    funext x
    exact (hrep x).2.symm

/-- The chart clause, assembled with literal
Lebesgue pullbacks and the ordinary weak-gradient identity. -/
theorem hsSobolev_chart {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {U : Set (HsEuclidean N)} (hUo : IsOpen U) (hU : U ⊆ hsChamber N) :
    let q : U → HsConfiguration N := fun x => hsChamberProjection ⟨x.val, hU x.property⟩
    let ν := Measure.comap (Subtype.val : U → HsEuclidean N) volume
    LocallyIntegrable (fun x => hsSobolevValue _ f (q x)) ν ∧
    LocallyIntegrable (fun x => hsSobolevGradient _ f (q x)) ν ∧
    ∀ ψ : HsEuclidean N → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : HsEuclidean N,
        (∫ x : U, ψ x.val * inner ℝ (hsSobolevGradient _ f (q x)) v ∂ν) =
          -(∫ x : U, hsSobolevValue _ f (q x) * fderiv ℝ ψ x.val v ∂ν) := by
  obtain ⟨hv, hg⟩ := hsSobolev_chart_locallyIntegrable hN χ hc f hUo hU
  exact ⟨hv, hg, fun _ hψ hψc hψU v =>
    hsSobolev_chart_integral hN χ hc f hUo hU hψ hψc hψU v⟩

end Riesz1
