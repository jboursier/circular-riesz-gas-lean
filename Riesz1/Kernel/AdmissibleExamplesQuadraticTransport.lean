/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesDistanceRemainder
public import Riesz1.Kernel.AdmissibleExamplesIndicatorTransport
public import Riesz1.ToMathlib.CircleContinuousPrimitive

/-!
# Transport of the quadratic cell corner

The antipodal derivative jump in a distance power is carried by the squared
central coordinate. Its transport derivative is a translated, centered periodic
zeta function. This handles the corner without extending a smooth-test singular integral.
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1
namespace Internal

lemma memLp_quadraticCell :
    MemLp (fun x : UnitAddCircle => (quadraticCell x : ℂ)) 2 volume :=
  memLp_of_continuous_circle (Complex.continuous_ofReal.comp continuous_quadraticCell)

/-- Two integrations by parts retain the first-derivative seam jump of the quadratic. -/
lemma fourierCoeff_quadraticCell {k : ℤ} (hk : k ≠ 0) :
    fourierCoeff (fun x : UnitAddCircle => (quadraticCell x : ℂ)) k =
      fourier (-k) ((-(1 / 2 : ℝ)) : UnitAddCircle) /
        ((2 * Real.pi ^ 2 * (k : ℝ) ^ 2 : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ 2
  let g : ℝ → ℂ := fun x => 2 * (x : ℂ)
  have hd (x : ℝ) : HasDerivAt f (g x) x := by
    simpa only [f, g, Complex.ofRealCLM_apply, Complex.ofReal_one, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by rfl, pow_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).fun_pow 2
  have hgd (x : ℝ) : HasDerivAt g 2 x := by
    simpa only [g, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul 2
  have hF := fourierCoeffOn_of_hasDerivAt (show -(1 / 2 : ℝ) < -(1 / 2) + 1 by norm_num)
    hk (fun x _ => hd x) ((by fun_prop : Continuous g).intervalIntegrable _ _)
  have hG := fourierCoeffOn_of_hasDerivAt (show -(1 / 2 : ℝ) < -(1 / 2) + 1 by norm_num)
    hk (fun x _ => hgd x) (f' := fun _ => (2 : ℂ)) intervalIntegrable_const
  have hc2 : fourierCoeffOn (show -(1 / 2 : ℝ) < -(1 / 2) + 1 by norm_num)
      (fun _ => (2 : ℂ)) k = 0 := by
    rw [← fourierCoeff_liftIco_eq]
    change fourierCoeff (fun _ : UnitAddCircle => (2 : ℂ)) k = 0
    rw [show (fun _ : UnitAddCircle => (2 : ℂ)) = fun x => (2 : ℂ) * (1 : ℂ) by simp,
      fourierCoeff.const_mul, fourierCoeff_one]
    simp [hk]
  have hfun : (fun x : UnitAddCircle => (quadraticCell x : ℂ)) =
      AddCircle.liftIco 1 (-(1 / 2 : ℝ)) f := by
    funext x
    rw [quadraticCell, ← AddCircle.liftIco_comp_apply (f := fun t : ℝ => t ^ 2)
      (g := fun t : ℝ => (t : ℂ))]
    congr 1
    funext t
    simp [f]
  rw [hfun]
  rw [fourierCoeff_liftIco_eq, hF, hG, hc2]
  norm_num [f, g]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The signed transport kernel has the expected singularity at the origin. -/
lemma exists_periodicKernel_circle_bound (s : RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, (t : UnitAddCircle) ≠ 0 →
      |periodicKernel s.val t| ≤ C * dist (t : UnitAddCircle) 0 ^ (s.val - 1) := by
  let M := ∑' j : ℕ, (1 - s.val) * ((j : ℝ) + 1 / 2) ^ (s.val - 2)
  have hM : 0 ≤ M := tsum_nonneg fun j => mul_nonneg (by linarith [s.2.2]) (by positivity)
  refine ⟨1 + M, by positivity, fun t ht => ?_⟩
  have hn : ∀ n : ℤ, t ≠ n := by
    intro n h
    apply ht
    rw [h]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨n, by simp⟩
  obtain ⟨n, hz, he⟩ := exists_nearest_int hn
  have hd : dist (t : UnitAddCircle) 0 = |t - n| := by
    rw [dist_zero_right, UnitAddCircle.norm_eq, abs_sub_round_eq_min, he]
  have hz0 : 0 < |t - n| := abs_pos.mpr hz.2
  have hz1 : |t - n| ≤ 1 / 2 := by
    rw [← hd, dist_zero_right]
    simpa only [abs_one] using AddCircle.norm_le_half_period 1 (x := (t : UnitAddCircle)) one_ne_zero
  have hzN : ∀ m : ℤ, t - n ≠ m := by
    intro m hm
    apply hn (m + n)
    push_cast
    linarith
  have hb : |periodicKernel s.val (t - n)| ≤ |t - n| ^ (s.val - 1) + M :=
    le_of_tendsto (tendsto_symmetric_signPow s.2.1 s.2.2 hzN |>.abs)
      (Eventually.of_forall fun N => abs_sum_signPow_le s.2.1 s.2.2 hz1 N)
  have hper : periodicKernel s.val (t - n) = periodicKernel s.val t := by
    have h := periodicKernel_add_int s.val (t - n) n
    simpa using h.symm
  have hp : 1 ≤ |t - n| ^ (s.val - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz0 (by linarith) (by linarith [s.2.2])
  rw [hper] at hb
  rw [hd]
  nlinarith

/-- Coefficient identification for the periodic primitive of the translated zeta function. -/
lemma quadratic_transport_coeff (P : Parameters) (H : UnitAddCircle → ℝ)
    (hH0 : fourierCoeff (fun x => (H x : ℂ)) 0 = 0)
    (hHcoeff : ∀ k : ℤ, k ≠ 0 → (2 * Real.pi * Complex.I * (k : ℂ)) *
      fourierCoeff (fun x => (H x : ℂ)) k =
        fourierCoeff (fun x => (periodicZeta (parametersExponent P)
          (x - ((-(1 / 2 : ℝ)) : UnitAddCircle)) : ℂ)) k) :
    ∀ k, fourierCoeff (fun x =>
      ((2 / (4 * Real.pi * P.val.1 * P.val.2 * Real.tan (Real.pi * P.val.2 / 2)) * H x : ℝ) : ℂ)) k =
        transportCoeffs P unitLength ⟨quadraticCell, memLp_quadraticCell⟩ k := by
  let s := parametersExponent P
  let c : UnitAddCircle := (-(1 / 2 : ℝ))
  let T : ℝ := 4 * Real.pi * P.val.1 * s.val * Real.tan (Real.pi * s.val / 2)
  let q : ℝ := 2 / T
  intro k
  change fourierCoeff (fun x => ((q * H x : ℝ) : ℂ)) k = _
  simp only [Complex.ofReal_mul]
  rw [fourierCoeff.const_mul]
  by_cases hk : k = 0
  · subst k
    simp only [hH0, mul_zero, transportCoeffs, ↓reduceIte]
  · have hω : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero, hk]
    apply mul_left_cancel₀ hω
    rw [show (2 * Real.pi * Complex.I * (k : ℂ)) *
        ((q : ℂ) * fourierCoeff (fun x => (H x : ℂ)) k) =
      (q : ℂ) * ((2 * Real.pi * Complex.I * (k : ℂ)) *
        fourierCoeff (fun x => (H x : ℂ)) k) by ring,
      hHcoeff k hk]
    change (q : ℂ) * fourierCoeff (fun x => (periodicZeta s (x - c) : ℂ)) k = _
    rw [fourierCoeff_sub_centre (fun x : UnitAddCircle => (periodicZeta s x : ℂ)),
      fourierCoeff_periodicZeta]
    simp only [hk, ↓reduceIte]
    have hreal : q * (periodicZetaConst s.val * |(k : ℝ)| ^ (-(1 + s.val))) =
        -(|2 * Real.pi * (k : ℝ)| ^ (1 - s.val) /
          (4 * Real.pi ^ 2 * P.val.1 * rieszConstant s * (k : ℝ) ^ 2)) := by
      have he := transport_real_identity s P.val.1 P.2.1 k hk
      dsimp [q, T]
      linear_combination -he
    have hrealc := congrArg (fun t : ℝ => (t : ℂ)) hreal
    push_cast at hrealc
    rw [transportCoeffs, ite_eq_right hk]
    change (q : ℂ) * (fourier (-k) c *
        ((periodicZetaConst s.val : ℂ) * (|(k : ℝ)| ^ (-(1 + s.val)) : ℝ))) =
      (2 * Real.pi * Complex.I * (k : ℂ)) *
        (-((|2 * Real.pi * (k : ℝ) / 1| ^ (1 - s.val) : ℝ) : ℂ) /
          ((2 * P.val.1 * rieszConstant s : ℝ) * (2 * Real.pi * Complex.I * (k : ℂ) / 1)) *
            fourierCoeff (fun x : UnitAddCircle => (quadraticCell x : ℂ)) k)
    rw [fourierCoeff_quadraticCell hk]
    simp only [div_one]
    calc
      (q : ℂ) * (fourier (-k) c * ((periodicZetaConst s.val : ℂ) *
          (|(k : ℝ)| ^ (-(1 + s.val)) : ℝ))) =
        fourier (-k) c * ((q : ℂ) * ((periodicZetaConst s.val : ℂ) *
          (|(k : ℝ)| ^ (-(1 + s.val)) : ℝ))) := by ring
      _ = _ := by
        rw [hrealc]
        push_cast
        field_simp
        ring

/-- A primitive of the translated periodic zeta function is `C²` off the antipode,
with its second derivative bounded by `C d^(s-1)`. -/
lemma zeta_primitive_regularity (s : RieszExponent) (q m : ℝ) (H : UnitAddCircle → ℝ)
    (hHd : ∀ x : ℝ, HasDerivAt (fun t : ℝ => H (t : UnitAddCircle))
      (periodicZeta s ((x : UnitAddCircle) - ((-(1 / 2 : ℝ)) : UnitAddCircle)) - m) x) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      (x : UnitAddCircle) ≠ ((-(1 / 2 : ℝ)) : UnitAddCircle) →
      ContDiffAt ℝ 2 (fun t : ℝ => q * H (t : UnitAddCircle)) x ∧
      |deriv (deriv (fun t : ℝ => q * H (t : UnitAddCircle))) x| ≤
        C * dist (x : UnitAddCircle) ((-(1 / 2 : ℝ)) : UnitAddCircle) ^ (s.val - 1) := by
  let c : UnitAddCircle := (-(1 / 2 : ℝ))
  let f : UnitAddCircle → ℝ := fun x => periodicZeta s (x - c)
  let psi : UnitAddCircle → ℝ := fun x => q * H x
  have hpsid (x : ℝ) : HasDerivAt (fun t : ℝ => psi (t : UnitAddCircle))
      (q * (f (x : UnitAddCircle) - m)) x := (hHd x).const_mul q
  have hder : deriv (fun t : ℝ => psi (t : UnitAddCircle)) =
      fun x : ℝ => q * (f (x : UnitAddCircle) - m) := funext fun x => (hpsid x).deriv
  let U : Set ℝ := {x : ℝ | (x : UnitAddCircle) ≠ c}
  have hU : IsOpen U := isOpen_ne_fun (AddCircle.continuous_mk' 1) continuous_const
  have hpoint (x : ℝ) (hx : x ∈ U) : ((x + 1 / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
    intro he
    apply hx
    rw [AddCircle.coe_add, add_eq_zero_iff_eq_neg] at he
    simpa only [c, AddCircle.coe_neg] using he
  have hfd (x : ℝ) (hx : x ∈ U) :
      HasDerivAt (fun t : ℝ => f (t : UnitAddCircle))
        (s.val * periodicKernel s.val (x + 1 / 2)) x := by
    have hn : ∀ n : ℤ, x + 1 / 2 ≠ n := by
      intro n hn
      apply hpoint x hx
      rw [hn]
      exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨n, by simp⟩
    have hd := (hasDerivAt_periodicZeta_of_not_int s hn).comp_add_const x (1 / 2)
    simpa only [f, c, sub_neg_eq_add, AddCircle.coe_neg, AddCircle.coe_add] using hd
  have hcd : ContDiffOn ℝ ∞ (fun t : ℝ => psi (t : UnitAddCircle)) U := by
    apply (contDiffOn_infty_iff_deriv_of_isOpen hU).mpr
    refine ⟨fun x _ => (hpsid x).differentiableAt.differentiableWithinAt, ?_⟩
    rw [hder]
    intro x hx
    have hh : ContDiffAt ℝ ∞ (fun t : ℝ => q *
        (periodicZeta s ((t + 1 / 2 : ℝ) : UnitAddCircle) - m)) x :=
      contDiffAt_const.mul (((contDiffAt_periodicZeta_of_ne_zero s (hpoint x hx)).comp x
        (contDiffAt_id.add contDiffAt_const)).sub contDiffAt_const)
    simpa only [f, c, AddCircle.coe_add, sub_neg_eq_add] using hh.contDiffWithinAt
  obtain ⟨K, hK, hb⟩ := exists_periodicKernel_circle_bound s
  refine ⟨|q * s.val| * K + 1, by positivity, fun x hx => ?_⟩
  have hxU : x ∈ U := hx
  refine ⟨(hcd.contDiffAt (hU.mem_nhds hxU)).of_le (by simp), ?_⟩
  rw [hder, ((hfd x hxU).sub_const m |>.const_mul q).deriv]
  have hdist : dist ((x + 1 / 2 : ℝ) : UnitAddCircle) 0 =
      dist (x : UnitAddCircle) c := by
    rw [dist_eq_norm, sub_zero, dist_eq_norm]
    simp only [AddCircle.coe_add, c, sub_neg_eq_add]
  have hh := hb (x + 1 / 2) (hpoint x hxU)
  rw [hdist] at hh
  rw [show q * (s.val * periodicKernel s.val (x + 1 / 2)) =
    (q * s.val) * periodicKernel s.val (x + 1 / 2) by ring, abs_mul]
  have hn : 0 ≤ dist (x : UnitAddCircle) c ^ (s.val - 1) := by positivity
  change _ ≤ (|q * s.val| * K + 1) * dist (x : UnitAddCircle) c ^ (s.val - 1)
  nlinarith [abs_nonneg (q * s.val)]

/-- The quadratic corner has its actual transport, `C²` off the antipode,
with a second derivative bounded by `C d^(s-1)`. -/
lemma exists_quadratic_transport (P : Parameters) :
    ∃ psi : UnitAddCircle → ℝ, Continuous psi ∧
      (∀ k, fourierCoeff (fun x => (psi x : ℂ)) k =
        transportCoeffs P unitLength ⟨quadraticCell, memLp_quadraticCell⟩ k) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
        (x : UnitAddCircle) ≠ ((-(1 / 2 : ℝ)) : UnitAddCircle) →
        ContDiffAt ℝ 2 (fun t : ℝ => psi (t : UnitAddCircle)) x ∧
        |deriv (deriv (fun t : ℝ => psi (t : UnitAddCircle))) x| ≤
          C * dist (x : UnitAddCircle) ((-(1 / 2 : ℝ)) : UnitAddCircle) ^ (P.val.2 - 1) := by
  let s := parametersExponent P
  let f : UnitAddCircle → ℝ := fun x => periodicZeta s (x - ((-(1 / 2 : ℝ)) : UnitAddCircle))
  have hshift : Continuous (fun x : UnitAddCircle => x - ((-(1 / 2 : ℝ)) : UnitAddCircle)) :=
    continuous_id.sub continuous_const
  have hVc : Continuous (periodicZeta s) :=
    isQuotientMap_quotient_mk'.continuous_iff.mpr (periodicZeta_continuous s)
  have hfc : Continuous f := hVc.comp hshift
  obtain ⟨H, hHc, hH0, hHd, hHcoeff⟩ := exists_continuous_centered_primitive (f := f) hfc
  let q : ℝ := 2 / (4 * Real.pi * P.val.1 * P.val.2 * Real.tan (Real.pi * P.val.2 / 2))
  have hcoeff : ∀ k, fourierCoeff (fun x => ((q * H x : ℝ) : ℂ)) k =
      transportCoeffs P unitLength ⟨quadraticCell, memLp_quadraticCell⟩ k := by
    apply quadratic_transport_coeff P H hH0
    intro k hk
    exact hHcoeff k hk
  obtain ⟨C, hC, hb⟩ := zeta_primitive_regularity s q
    (∫ t in (0 : ℝ)..1, f (t : UnitAddCircle)) H (fun x => hHd x)
  refine ⟨fun x => q * H x, hHc.const_mul q, hcoeff, C, hC, ?_⟩
  intro x hx
  exact hb x hx

end Internal
end Riesz1
