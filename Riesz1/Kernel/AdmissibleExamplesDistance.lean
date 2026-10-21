/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesPowerSobolev
public import Riesz1.Kernel.FundamentalSeries
public import Riesz1.ToMathlib.HurwitzKernel.SeriesDerivativesPower
public import Riesz1.ToMathlib.FourierSmoothCell

/-!
# The smooth cell remainder of a distance power

Supporting the distance-power and excluded-endpoint clauses of the admissible examples.
Removing the Riesz singularity gives a smooth function on a closed fundamental cell.
Its endpoint values agree, though its endpoint derivatives need not agree.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

namespace Internal

/-- The distance power minus the Riesz kernel has a unique smooth extension on the
central real cell. Its two endpoint values agree by evenness. -/
lemma exists_smooth_power_remainder_cell (a : RieszExponent) :
    ∃ H : ℝ → ℝ,
      (∀ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), ContDiffAt ℝ ∞ H x) ∧
      H (-(1 / 2)) = H (1 / 2) ∧
      ∀ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), x ≠ 0 →
        H x = |x| ^ (-a.val) - rieszRepresentative a (x : UnitAddCircle) := by
  classical
  obtain ⟨h, hcd, heq⟩ := exists_smooth_hurwitzZetaEven_re_remainder a.val a.2.1 a.2.2
  let H : ℝ → ℝ := fun x => if x = 0 then -h 0
    else |x| ^ (-a.val) - rieszRepresentative a (x : UnitAddCircle)
  have hH : ∀ x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), ContDiffAt ℝ ∞ H x := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      apply ((hcd 0 (by constructor <;> norm_num)).contDiffAt
        (isOpen_Ioo.mem_nhds (by constructor <;> norm_num))).neg.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds
        (show (0 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) by constructor <;> norm_num)] with y hy
      dsimp only [H]
      split_ifs with hy0
      · simp [hy0]
      · have he := heq y hy hy0
        change h y = rieszRepresentative a (y : UnitAddCircle) - |y| ^ (-a.val) at he
        linarith
    · have hnorm : ‖(x : UnitAddCircle)‖ = |x| :=
        (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr (by
          rw [abs_one, abs_le]
          exact hx)
      have hcx : (x : UnitAddCircle) ≠ 0 := by
        intro hc
        rw [hc, norm_zero] at hnorm
        exact hx0 (abs_eq_zero.mp hnorm.symm)
      have hg : ContDiffAt ℝ ∞ (fun y : ℝ => rieszRepresentative a (y : UnitAddCircle)) x :=
        ((fundamental_series a).2.1 x hcx).contDiffAt (isOpen_nonInt.mem_nhds hcx)
      apply ((contDiffAt_abs_rpow a.val hx0).sub hg).congr_of_eventuallyEq
      filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds hx0] with y hy
      simp only [id_eq] at hy
      simp only [H, hy, ↓reduceIte]
  refine ⟨H, hH, ?_, fun x _ hx0 => by simp only [H, hx0, ↓reduceIte]⟩
  have hsym := (fundamental_series a).2.2.1 (1 / 2)
  norm_num only [H, show -(1 / 2 : ℝ) ≠ 0 by norm_num,
    show (1 / 2 : ℝ) ≠ 0 by norm_num, ↓reduceIte, abs_neg]
  dsimp only at hsym
  rw [hsym]


/-- The distance power differs almost everywhere from `g_a` by a continuous periodic
remainder in every circle Sobolev space of index below 1/2. -/
lemma exists_distance_power_sobolev_remainder (a : RieszExponent) {r : ℝ} (hr : r < 1 / 2) :
    ∃ h : UnitAddCircle → ℂ, CircleSobolev r h ∧
      (fun x : UnitAddCircle => ((dist x 0 ^ (-a.val) : ℝ) : ℂ)) =ᵐ[volume]
        (fun x => (rieszRepresentative a x : ℂ) + h x) := by
  obtain ⟨H, hcd, he, hform⟩ := exists_smooth_power_remainder_cell a
  let h : UnitAddCircle → ℂ := AddCircle.liftIco 1 (-(1 / 2 : ℝ)) (fun x => (H x : ℂ))
  have hc : Continuous h := by
    apply AddCircle.liftIco_continuous
    · norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring]
      exact congrArg Complex.ofReal he
    · intro x hx
      exact (Complex.continuous_ofReal.continuousAt.comp
        (hcd x (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hx)).continuousAt).continuousWithinAt
  obtain ⟨K, hK, hdec⟩ := exists_fourierCoeff_liftIco_bound
    (f := fun x => (H x : ℂ)) (a := -(1 / 2 : ℝ))
    (fun x hx => (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (hcd x (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hx))).of_le (by exact_mod_cast le_top))
    (by simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using congrArg Complex.ofReal he)
  have hs : CircleSobolev r h := by
    apply circleSobolev_of_coeff_decay (g := -1) (K := K) (by linarith)
      (ContinuousMap.memLp volume ℂ ⟨h, hc⟩) (k₀ := 1) le_rfl
    intro k hk
    exact hdec k (by intro h0; simp [h0] at hk)
  refine ⟨h, hs, ?_⟩
  have hae : ∀ᵐ x : UnitAddCircle ∂volume, x ≠ 0 := by
    simp only [ae_iff, not_not]
    change volume ({(0 : UnitAddCircle)} : Set UnitAddCircle) = 0
    have hmp := AddCircle.measurePreserving_mk 1 (-(1 / 2 : ℝ))
    rw [← hmp.measure_preimage (measurableSet_singleton _).nullMeasurableSet,
      Measure.restrict_apply' measurableSet_Ioc]
    refine measure_mono_null (t := {(0 : ℝ)}) ?_ (measure_singleton _)
    rintro y ⟨hy1, hy2⟩
    have hz : (0 : ℝ) ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := by norm_num
    have heq : (y : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := hy1
    rw [AddCircle.coe_eq_coe_iff_of_mem_Ioc hy2 hz] at heq
    exact heq
  filter_upwards [hae] with x hx0
  let z := (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).val
  have hz : z ∈ Ico (-(1 / 2 : ℝ)) (1 / 2) := by
    simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using
      (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) x).property
  have hzx : (z : UnitAddCircle) = x := AddCircle.coe_equivIco
  have hz0 : z ≠ 0 := by intro h0; apply hx0; rw [← hzx, h0, AddCircle.coe_zero]
  have hd : dist x 0 = |z| := by
    rw [dist_zero_right, ← hzx]
    exact (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr (by
      rw [abs_one, abs_le]
      exact ⟨hz.1, hz.2.le⟩)
  have hhz : h x = (H z : ℂ) := by
    rw [← hzx]
    exact AddCircle.liftIco_coe_apply (by
      simpa only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring] using hz)
  rw [hd, hhz, hform z ⟨hz.1, hz.2.le⟩ hz0, hzx]
  push_cast
  ring

/-- Almost everywhere equal representatives have the same Sobolev membership. -/
lemma circleSobolev_congr_ae {r : ℝ} {f g : UnitAddCircle → ℂ} (he : f =ᵐ[volume] g) :
    CircleSobolev r f ↔ CircleSobolev r g := by
  have go {F G : UnitAddCircle → ℂ} (hFG : F =ᵐ[volume] G)
      (hF : CircleSobolev r F) : CircleSobolev r G := by
    obtain ⟨hFL2, hfin⟩ := hF
    have hGL2 := (memLp_congr_ae hFG).mp hFL2
    refine ⟨hGL2, ?_⟩
    rw [circleSobolevSq_congr_ae hGL2 hFL2 hFG.symm]
    exact hfin
  exact ⟨go he, go he.symm⟩

/-- The zero function belongs to every Sobolev space. -/
lemma circleSobolev_zero (r : ℝ) : CircleSobolev r (0 : UnitAddCircle → ℂ) := by
  refine ⟨MemLp.zero, ?_⟩
  simp [circleSobolevSq, fourierCoeff]

/-- Adding a Sobolev remainder preserves membership. -/
lemma circleSobolev_add {r : ℝ} {f g : UnitAddCircle → ℂ}
    (hf : CircleSobolev r f) (hg : CircleSobolev r g) : CircleSobolev r (f + g) := by
  have hneg := circleSobolev_sub (circleSobolev_zero r) hg
  simpa only [zero_sub, sub_neg_eq_add] using circleSobolev_sub hf hneg

/-- Square integrability alone gives finiteness of the index-zero Fourier energy. -/
lemma circleSobolev_zero_of_memLp {f : UnitAddCircle → ℂ} (hf : MemLp f 2 volume) :
    CircleSobolev 0 f := by
  have hfH : MemLp f 2 AddCircle.haarAddCircle := by
    rwa [← volume_eq_haar_circle]
  have hs := (hasSum_sq_fourierCoeff (hfH.toLp f)).summable
  have he := _root_.fourierCoeff_congr_ae hfH.coeFn_toLp
  simp only [he] at hs
  apply circleSobolev_of_summable_summand hf
  refine Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) (fun k => ?_) hs
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

/-- The half-power of circle distance is not square integrable. -/
lemma not_memLp_distance_half_power :
    ¬ MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) 2 volume := by
  intro hf
  let a : RieszExponent := ⟨1 / 2, by constructor <;> norm_num⟩
  obtain ⟨h, hh, he⟩ := exists_distance_power_sobolev_remainder a (r := 0) (by norm_num)
  have hsub := circleSobolev_sub (circleSobolev_zero_of_memLp hf) hh
  have he' :
      ((fun x : UnitAddCircle => ((dist x 0 ^ (-a.val) : ℝ) : ℂ)) - h) =ᵐ[volume]
        (fun x => (rieszRepresentative a x : ℂ)) := by
    filter_upwards [he] with x hx
    simp only [Pi.sub_apply]
    rw [hx, add_sub_cancel_right]
  have hg := (circleSobolev_congr_ae he').mp hsub
  have hbad := riesz_sobolev_exponent_lt a hg
  norm_num [a] at hbad

end Internal

/-- The exact distance-power Sobolev threshold in the Riesz exponent range. In particular,
the critical distance power is excluded. -/
theorem circleSobolev_distance_power_iff (s a : RieszExponent) :
    CircleSobolev ((1 - s.val) / 2)
      (fun x : UnitAddCircle => ((dist x 0 ^ (-a.val) : ℝ) : ℂ)) ↔ a.val < s.val / 2 := by
  obtain ⟨h, hh, he⟩ := Internal.exists_distance_power_sobolev_remainder a
    (r := (1 - s.val) / 2) (by linarith [s.2.1])
  constructor
  · intro hf
    have hsub := circleSobolev_sub hf hh
    have hsubeq :
        ((fun x : UnitAddCircle => ((dist x 0 ^ (-a.val) : ℝ) : ℂ)) - h) =ᵐ[volume]
          (fun x => (rieszRepresentative a x : ℂ)) := by
      filter_upwards [he] with x hx
      simp only [Pi.sub_apply]
      rw [hx, add_sub_cancel_right]
    exact (circleSobolev_riesz_iff s a).mp
      ((Internal.circleSobolev_congr_ae hsubeq).mp hsub)
  · intro ha
    exact (Internal.circleSobolev_congr_ae he).mpr
      (Internal.circleSobolev_add (circleSobolev_riesz_of_lt s a ha) hh)

/-- Every distance power of exponent at least 1/2 fails the L² carrier requirement. -/
theorem not_memLp_distance_power_of_half_le {a : ℝ} (ha : 1 / 2 ≤ a) :
    ¬ MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) 2 volume := by
  intro hf
  apply Internal.not_memLp_distance_half_power
  apply hf.mono
  · exact (Complex.measurable_ofReal.comp
      ((continuous_id.dist continuous_const).measurable.pow_const (-(1 / 2 : ℝ)))).aestronglyMeasurable
  · apply ae_of_all
    intro x
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg dist_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)]
    by_cases hx : x = 0
    · subst x
      simp only [dist_self]
      rw [Real.zero_rpow (by norm_num : -(1 / 2 : ℝ) ≠ 0),
        Real.zero_rpow (by linarith : -a ≠ 0)]
    · apply Real.rpow_le_rpow_of_exponent_ge (dist_pos.mpr hx)
      · have hd := AddCircle.norm_le_half_period 1 (x := x) one_ne_zero
        rw [dist_zero_right]
        norm_num only [abs_one] at hd
        linarith
      · linarith

/-- The sharp Sobolev threshold for every positive distance-power exponent, with no upper
restriction on that exponent (the Sobolev obstruction). -/
theorem circleSobolev_distance_power_real_iff (s : RieszExponent) {a : ℝ} (ha : 0 < a) :
    CircleSobolev ((1 - s.val) / 2)
      (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) ↔ a < s.val / 2 := by
  by_cases ha1 : a < 1
  · exact circleSobolev_distance_power_iff s ⟨a, ha, ha1⟩
  · constructor
    · rintro ⟨hf, _⟩
      exact False.elim (not_memLp_distance_power_of_half_le (by linarith) hf)
    · intro hlt
      exfalso
      linarith [s.2.2]

/-- The distance power at `a = s/2` is excluded from `H^{(1-s)/2}`. -/
theorem not_circleSobolev_distance_power_endpoint (s : RieszExponent) :
    ¬ CircleSobolev ((1 - s.val) / 2)
      (fun x : UnitAddCircle => ((dist x 0 ^ (-(s.val / 2)) : ℝ) : ℂ)) := by
  let a : RieszExponent := ⟨s.val / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩
  intro h
  have hh := (circleSobolev_distance_power_iff s a).mp h
  exact (lt_irrefl (s.val / 2)) hh

end Riesz1
