/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Bridges.ExplicitFormulasCentred
public import Riesz1.Kernel.TransportScaledLattice
public import Riesz1.Frozen.TransportRegularity

/-!
# Transport regularity of proper arc indicators

The macroscopic A2–A3 construction. The representative is the
explicit transport, translated to the chosen centre. Its two marks are the arc
endpoints, and its second derivative has the required distance envelope with exponent zero.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1
namespace Internal

lemma contDiffAt_periodicZeta_of_ne_zero (s : RieszExponent) {t : ℝ}
    (ht : (t : UnitAddCircle) ≠ 0) :
    ContDiffAt ℝ ∞ (fun u : ℝ => periodicZeta s (u : UnitAddCircle)) t := by
  have hn : ∀ k : ℤ, t ≠ k := by
    intro k hk
    apply ht
    rw [hk]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨k, by simp⟩
  have hcd : ContDiffOn ℝ ∞ (fun u : ℝ => periodicZeta s (u : UnitAddCircle))
      {u : ℝ | ∀ k : ℤ, u ≠ k} := by
    apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_not_int).mpr
    refine ⟨fun u hu => (hasDerivAt_periodicZeta_of_not_int s hu).differentiableAt.differentiableWithinAt,
      ?_⟩
    exact ((contDiffOn_const.mul (show ContDiffOn ℝ ∞ (periodicKernel s.val)
      {u : ℝ | ∀ k : ℤ, u ≠ k} from fun u hu =>
        (contDiffAt_periodicKernel_of_not_int s.2.1 s.2.2 hu).contDiffWithinAt))).congr
      fun u hu => (hasDerivAt_periodicZeta_of_not_int s hu).deriv
  exact hcd.contDiffAt (isOpen_not_int.mem_nhds hn)

lemma exists_deriv_periodicKernel_circle_bound (s : RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (t : UnitAddCircle) ≠ 0 →
      |deriv (periodicKernel s.val) t| ≤ C * dist (t : UnitAddCircle) 0 ^ (s.val - 2) := by
  obtain ⟨C, hC, hb⟩ := norm_iteratedDeriv_periodicKernel_le s.2.1 s.2.2 (m := 1) le_rfl
  refine ⟨C, hC, fun t ht => ?_⟩
  have hn : ∀ k : ℤ, t ≠ k := by
    intro k hk
    apply ht
    rw [hk]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨k, by simp⟩
  have hd : dist (t : UnitAddCircle) 0 = min (Int.fract t) (1 - Int.fract t) := by
    rw [dist_zero_right, UnitAddCircle.norm_eq, abs_sub_round_eq_min]
  simpa [iteratedDeriv_one, Real.norm_eq_abs, hd, show s.val - 1 - 1 = s.val - 2 by ring] using hb t hn

lemma hasDerivAt_transportFormula_lift (s : RieszExponent) (β a : ℝ) {t : ℝ}
    (hp : ((t + a : ℝ) : UnitAddCircle) ≠ 0)
    (hm : ((t - a : ℝ) : UnitAddCircle) ≠ 0) :
    HasDerivAt (fun u : ℝ => transportFormula s β a (u : UnitAddCircle))
      (-(s.val * (periodicKernel s.val (t + a) - periodicKernel s.val (t - a))) /
        (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2))) t := by
  have hn {u : ℝ} (hu : (u : UnitAddCircle) ≠ 0) : ∀ k : ℤ, u ≠ k := by
    intro k hk
    apply hu
    rw [hk]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨k, by simp⟩
  have hd := (((hasDerivAt_periodicZeta_of_not_int s (hn hp)).comp_add_const t a).sub
    ((hasDerivAt_periodicZeta_of_not_int s (hn hm)).comp_sub_const t a)).neg.div_const
      (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2))
  convert hd using 1
  · funext u
    simp only [transportFormula, AddCircle.coe_add, AddCircle.coe_sub, Pi.neg_apply, Pi.sub_apply]
  · ring

lemma deriv_deriv_transportFormula_lift (s : RieszExponent) (β a : ℝ) {t : ℝ}
    (hp : ((t + a : ℝ) : UnitAddCircle) ≠ 0)
    (hm : ((t - a : ℝ) : UnitAddCircle) ≠ 0) :
    deriv (deriv (fun u : ℝ => transportFormula s β a (u : UnitAddCircle))) t =
      -(s.val * (deriv (periodicKernel s.val) (t + a) -
        deriv (periodicKernel s.val) (t - a))) /
        (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2)) := by
  have hn {u : ℝ} (hu : (u : UnitAddCircle) ≠ 0) : ∀ k : ℤ, u ≠ k := by
    intro k hk
    apply hu
    rw [hk]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨k, by simp⟩
  have he : deriv (fun u : ℝ => transportFormula s β a (u : UnitAddCircle)) =ᶠ[𝓝 t]
      (fun u => -(s.val * (periodicKernel s.val (u + a) - periodicKernel s.val (u - a))) /
        (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2))) := by
    have hpo : IsOpen {u : ℝ | ((u + a : ℝ) : UnitAddCircle) ≠ 0} :=
      isOpen_ne_fun (AddCircle.continuous_mk' 1 |>.comp (continuous_id.add continuous_const)) continuous_const
    have hmo : IsOpen {u : ℝ | ((u - a : ℝ) : UnitAddCircle) ≠ 0} :=
      isOpen_ne_fun (AddCircle.continuous_mk' 1 |>.comp (continuous_id.sub continuous_const)) continuous_const
    filter_upwards [hpo.mem_nhds hp, hmo.mem_nhds hm] with u hu hv
    exact (hasDerivAt_transportFormula_lift s β a hu hv).deriv
  rw [he.deriv_eq]
  exact (((((contDiffAt_periodicKernel_of_not_int s.2.1 s.2.2 (hn hp)).differentiableAt
    (by simp)).hasDerivAt.comp_add_const t a).sub
    (((contDiffAt_periodicKernel_of_not_int s.2.1 s.2.2 (hn hm)).differentiableAt
      (by simp)).hasDerivAt.comp_sub_const t a)).const_mul s.val).neg.div_const _ |>.deriv

lemma contDiffAt_transportFormula_lift (s : RieszExponent) (β a : ℝ) {t : ℝ}
    (hp : ((t + a : ℝ) : UnitAddCircle) ≠ 0)
    (hm : ((t - a : ℝ) : UnitAddCircle) ≠ 0) :
    ContDiffAt ℝ ∞ (fun u : ℝ => transportFormula s β a (u : UnitAddCircle)) t := by
  have h := ((((contDiffAt_periodicZeta_of_ne_zero s hp).comp t
    (contDiffAt_id.add contDiffAt_const)).sub
      ((contDiffAt_periodicZeta_of_ne_zero s hm).comp t
        (contDiffAt_id.sub contDiffAt_const))).neg).div_const
          (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2))
  simpa only [transportFormula, Function.comp_def, id_eq, AddCircle.coe_add, AddCircle.coe_sub] using h

lemma exists_transportFormula_second_deriv_bound (s : RieszExponent) (β : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a t : ℝ,
      ((t + a : ℝ) : UnitAddCircle) ≠ 0 → ((t - a : ℝ) : UnitAddCircle) ≠ 0 →
      |deriv (deriv (fun u : ℝ => transportFormula s β a (u : UnitAddCircle))) t| ≤
        C * (dist ((t + a : ℝ) : UnitAddCircle) 0 ^ (s.val - 2) +
          dist ((t - a : ℝ) : UnitAddCircle) 0 ^ (s.val - 2)) := by
  obtain ⟨K, hK, hb⟩ := exists_deriv_periodicKernel_circle_bound s
  let q := |s.val / (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2))|
  refine ⟨q * K + 1, by dsimp [q]; positivity, fun a t hp hm => ?_⟩
  rw [deriv_deriv_transportFormula_lift s β a hp hm]
  have hsum : 0 ≤ dist ((t + a : ℝ) : UnitAddCircle) 0 ^ (s.val - 2) +
      dist ((t - a : ℝ) : UnitAddCircle) 0 ^ (s.val - 2) := by positivity
  calc
    |-(s.val * (deriv (periodicKernel s.val) (t + a) -
        deriv (periodicKernel s.val) (t - a))) /
        (4 * Real.pi * β * s.val * Real.tan (Real.pi * s.val / 2))|
      = q * |deriv (periodicKernel s.val) (t + a) -
        deriv (periodicKernel s.val) (t - a)| := by dsimp [q]; rw [abs_div, abs_neg, abs_mul, abs_div]; ring
    _ ≤ q * (|deriv (periodicKernel s.val) (t + a)| +
        |deriv (periodicKernel s.val) (t - a)|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
    _ ≤ q * (K * dist ((t + a : ℝ) : UnitAddCircle) 0 ^ (s.val - 2) +
        K * dist ((t - a : ℝ) : UnitAddCircle) 0 ^ (s.val - 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hb _ hp) (hb _ hm)) (abs_nonneg _)
    _ ≤ (q * K + 1) * (dist ((t + a : ℝ) : UnitAddCircle) 0 ^ (s.val - 2) +
        dist ((t - a : ℝ) : UnitAddCircle) 0 ^ (s.val - 2)) := by nlinarith

lemma fourierCoeff_transportFormula (s : RieszExponent) (β a : ℝ) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (transportFormula s β a x : ℂ)) k =
      transportSeriesCoeff s.val β a k := by
  rw [show (fun x : UnitAddCircle => (transportFormula s β a x : ℂ)) =
    fun x => ∑' n : ℤ, transportSeriesCoeff s.val β a n * fourier n x from
      funext fun x => transportFormula_coe β a x]
  exact fourierCoeff_tsum_fourier _ (summable_norm_transportSeriesCoeff s.2.1 β a) k

end Internal

/-- The A2–A3 clauses for every proper arc at scale one.
The bound is chosen before the radius and centre, and the marks are exactly its endpoints. -/
theorem transportRegularity_arcIndicator (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a < 1 / 2 → ∀ c : ℝ,
      TransportRegularity P unitLength
        ⟨arcIndicator (c : UnitAddCircle) a, memLp_arcIndicator _ a⟩
        ⟨2, by norm_num⟩ ![c - a, c + a] 0 C := by
  let s := parametersExponent P
  obtain ⟨C, hC, hb⟩ := Internal.exists_transportFormula_second_deriv_bound s P.val.1
  refine ⟨C, hC, fun a ha0 ha1 c => ?_⟩
  dsimp only [TransportRegularity, unitLength, Circle, arclength]
  constructor
  · intro i j hij
    have he : ((c - a : ℝ) : UnitAddCircle) ≠ ((c + a : ℝ) : UnitAddCircle) := by
      intro he
      have hreal := (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (p := (1 : ℝ)) (a := c - 1 / 2)
        (show c - a ∈ Ico (c - 1 / 2) (c - 1 / 2 + 1) by constructor <;> linarith)
        (show c + a ∈ Ico (c - 1 / 2) (c - 1 / 2 + 1) by constructor <;> linarith)).mp he
      linarith
    fin_cases i <;> fin_cases j
    · rfl
    · exact (he hij).elim
    · exact (he hij.symm).elim
    · rfl
  · let φ : UnitAddCircle → ℝ := fun x => transportFormula s P.val.1 a (x - (c : UnitAddCircle))
    have hmem : MemLp (fun x => (φ x : ℂ)) 2 volume :=
      memLp_sub_centre (memLp_of_continuous_circle (continuous_transportFormula _ _)) _
    refine ⟨⟨φ, hmem⟩, ?_, ?_⟩
    · intro k
      change fourierCoeff (fun x => (φ x : ℂ)) k = _
      rw [show (fun x => (φ x : ℂ)) = fun x =>
        (transportFormula s P.val.1 a (x - (c : UnitAddCircle)) : ℂ) from rfl,
        fourierCoeff_sub_centre (fun x : UnitAddCircle => (transportFormula s P.val.1 a x : ℂ)),
        Internal.fourierCoeff_transportFormula]
      change fourier (-k) (c : UnitAddCircle) * transportSeriesCoeff s.val P.val.1 a k =
        transportCoeffs P ⟨1, zero_lt_one⟩
          ⟨fun t : UnitAddCircle => arcIndicator (c : UnitAddCircle) a t,
            memLp_arcIndicator (c : UnitAddCircle) a⟩ k
      rw [transportCoeffs_arcIndicator_centre P ha1 (c : UnitAddCircle) k]
      congr 1
      exact ((transportCoeffs_indicatorArc s P.val.1 a P.property.1 k).trans
        (transportCoeffs_centered s P.val.1 a P.property.1 ha0 ha1 k)).symm
    · dsimp only
      intro x hx
      change ∀ j : Fin 2, (x : UnitAddCircle) ≠ ((![c - a, c + a] j : ℝ) : UnitAddCircle) at hx
      have hp : ((x - c + a : ℝ) : UnitAddCircle) ≠ 0 := by
        intro he
        apply hx 0
        simp only [Matrix.cons_val_zero] at *
        have hh : ((x - (c - a) : ℝ) : UnitAddCircle) = 0 := by
          rwa [show x - (c - a) = x - c + a by ring]
        rwa [AddCircle.coe_sub, sub_eq_zero] at hh
      have hm : ((x - c - a : ℝ) : UnitAddCircle) ≠ 0 := by
        intro he
        apply hx 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at *
        have hh : ((x - (c + a) : ℝ) : UnitAddCircle) = 0 := by
          rwa [show x - (c + a) = x - c - a by ring]
        rwa [AddCircle.coe_sub, sub_eq_zero] at hh
      have helift : (fun x : ℝ => φ (x : UnitAddCircle)) =
          fun x : ℝ => transportFormula s P.val.1 a ((x - c : ℝ) : UnitAddCircle) := by
        funext x
        simp only [φ, AddCircle.coe_sub]
      rw [helift]
      refine ⟨((Internal.contDiffAt_transportFormula_lift s P.val.1 a hp hm).comp x
        (contDiffAt_id.sub contDiffAt_const)).of_le (by simp), ?_⟩
      have hd : deriv (fun x : ℝ => transportFormula s P.val.1 a ((x - c : ℝ) : UnitAddCircle)) =
          fun x : ℝ => deriv (fun u : ℝ => transportFormula s P.val.1 a (u : UnitAddCircle)) (x - c) :=
        funext fun x => deriv_comp_sub_const (fun u : ℝ => transportFormula s P.val.1 a (u : UnitAddCircle)) c x
      rw [hd, deriv_comp_sub_const]
      change |deriv (deriv (fun u : ℝ => transportFormula s P.val.1 a (u : UnitAddCircle))) (x - c)| ≤
        C * ((if dist (x : UnitAddCircle) 0 ≤ 1 then
          ∑ j : Fin 2, dist (x : UnitAddCircle) ((![c - a, c + a] j : ℝ) : UnitAddCircle) ^
            (-2 + P.val.2 - 0) else 0) +
          (if 1 ≤ dist (x : UnitAddCircle) 0 then dist (x : UnitAddCircle) 0 ^ (-3 + P.val.2) else 0))
      have hdist : dist (x : UnitAddCircle) 0 ≤ 1 := by
        rw [dist_zero_right]
        exact (AddCircle.norm_le_half_period (p := (1 : ℝ)) one_ne_zero).trans (by norm_num)
      have hfar : ¬ 1 ≤ dist (x : UnitAddCircle) 0 := by
        rw [dist_zero_right]
        have hh := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := (x : UnitAddCircle)) one_ne_zero
        norm_num at hh
        linarith
      simp only [hdist, hfar, ↓reduceIte, add_zero, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
      have hd₁ : dist ((x - c + a : ℝ) : UnitAddCircle) 0 =
          dist (x : UnitAddCircle) ((c - a : ℝ) : UnitAddCircle) := by
        rw [dist_eq_norm, sub_zero, dist_eq_norm, ← AddCircle.coe_sub]
        congr 2
        ring
      have hd₂ : dist ((x - c - a : ℝ) : UnitAddCircle) 0 =
          dist (x : UnitAddCircle) ((c + a : ℝ) : UnitAddCircle) := by
        rw [dist_eq_norm, sub_zero, dist_eq_norm, ← AddCircle.coe_sub]
        congr 2
        ring
      have hh := hb a (x - c) hp hm
      rw [hd₁, hd₂] at hh
      simpa only [s, parametersExponent, show -2 + P.val.2 = P.val.2 - 2 by ring] using hh

end Riesz1
