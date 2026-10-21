/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibleExamplesQuadraticTransport
public import Riesz1.Kernel.AdmissibleExamplesSmoothTransport

/-!
# Transport regularity of subcritical distance powers

The distance power is decomposed into its Riesz singularity, one quadratic corner
at the antipode, and a cubic-decay remainder. Their actual transports add,
and their second derivative estimates give the two-mark envelope.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- The transport is linear, including across almost everywhere changes of
representative. This helper is internal. Its decomposition hypothesis is discharged below. -/
lemma transportCoeffs_unit_linear_combination (P : Parameters)
    {f g q h : UnitAddCircle → ℝ} (A : ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 volume)
    (hg : MemLp (fun x => (g x : ℂ)) 2 volume)
    (hq : MemLp (fun x => (q x : ℂ)) 2 volume)
    (hh : MemLp (fun x => (h x : ℂ)) 2 volume)
    (he : (fun x => (f x : ℂ)) =ᵐ[volume]
      fun x => (g x : ℂ) + (A : ℂ) * (q x : ℂ) + (h x : ℂ)) (k : ℤ) :
    transportCoeffs P unitLength ⟨f, hf⟩ k =
      transportCoeffs P unitLength ⟨g, hg⟩ k +
        (A : ℂ) * transportCoeffs P unitLength ⟨q, hq⟩ k +
        transportCoeffs P unitLength ⟨h, hh⟩ k := by
  simp only [unitLength, Circle, arclength] at *
  have hgi : Integrable (fun x => (g x : ℂ)) AddCircle.haarAddCircle := by
    rw [← volume_eq_haar_circle]
    exact hg.integrable (by norm_num)
  have hqi : Integrable (fun x => (q x : ℂ)) AddCircle.haarAddCircle := by
    rw [← volume_eq_haar_circle]
    exact hq.integrable (by norm_num)
  have hhi : Integrable (fun x => (h x : ℂ)) AddCircle.haarAddCircle := by
    rw [← volume_eq_haar_circle]
    exact hh.integrable (by norm_num)
  have hsum : fourierCoeff (fun x => (f x : ℂ)) k =
      fourierCoeff (fun x => (g x : ℂ)) k +
        (A : ℂ) * fourierCoeff (fun x => (q x : ℂ)) k +
        fourierCoeff (fun x => (h x : ℂ)) k := by
    rw [fourierCoeff_congr_ae he k]
    change fourierCoeff (((fun x => (g x : ℂ)) +
      (fun x => (A : ℂ) * (q x : ℂ))) + (fun x => (h x : ℂ))) k = _
    rw [congrFun (fourierCoeff.add (hgi.add (hqi.const_mul (A : ℂ))) hhi) k]
    simp only [Pi.add_apply]
    rw [congrFun (fourierCoeff.add hgi (hqi.const_mul (A : ℂ))) k]
    simp only [Pi.add_apply]
    rw [fourierCoeff.const_mul]
  by_cases hk : k = 0
  · simp [transportCoeffs, hk]
  · simp only [transportCoeffs, hk, ↓reduceIte, coeff]
    rw [hsum]
    ring

/-- The distance from any point of the unit circle to any other point is at most a half. -/
lemma unit_circle_dist_le_half (x y : UnitAddCircle) : dist x y ≤ 1 / 2 := by
  rw [dist_eq_norm]
  simpa only [abs_one] using AddCircle.norm_le_half_period 1 (x := x - y) one_ne_zero

end Internal

/-- The (A2) and (A3) clauses of Assumption 1.1 for subcritical distance powers.
The two fixed marks are zero and the antipode. The singularity exponent is the power. -/
theorem transportRegularity_distance_power (P : Parameters) {a : ℝ}
    (ha0 : 0 < a) (ha : a < P.val.2 / 2) :
    ∃ hf : MemLp (fun x : UnitAddCircle => ((dist x 0 ^ (-a) : ℝ) : ℂ)) 2 volume,
      ∃ C : ℝ, 0 < C ∧ TransportRegularity P unitLength
        ⟨fun x => dist x 0 ^ (-a), hf⟩ ⟨2, by norm_num⟩ ![0, -(1 / 2)] a C := by
  let ae : RieszExponent := ⟨a, ha0, by linarith [P.2.2.2]⟩
  have hf := ((circleSobolev_distance_power_real_iff (parametersExponent P) ha0).mpr ha).1
  obtain ⟨A, h, hhc, he, K, hK, hdec⟩ := Internal.exists_distance_power_matched_remainder ae
  have hhL2 : MemLp (fun x => (h x : ℂ)) 2 volume :=
    memLp_of_continuous_circle (Complex.continuous_ofReal.comp hhc)
  obtain ⟨psih, hpsihc, hpsihcoeff, hpsihcd, B, hB, hBh⟩ :=
    Internal.exists_C2_transport_of_cubic_decay P hhL2 hK.le hdec
  obtain ⟨psiq, hpsiqc, hpsiqcoeff, Cq, hCq, hCqb⟩ := Internal.exists_quadratic_transport P
  obtain ⟨hgL2, Cg, hCg, htrg⟩ := transportRegularity_riesz P ae ha
  dsimp only [TransportRegularity, unitLength, Circle, arclength] at htrg
  obtain ⟨_, psig, hpsigcoeff, hpsigpoint⟩ := htrg
  simp only [unitLength, Circle, arclength] at *
  let psi : UnitAddCircle → ℝ := fun x => psig.val x + A * psiq x + psih x
  have hqL2 := memLp_of_continuous_circle (Complex.continuous_ofReal.comp hpsiqc)
  have hhl2 := memLp_of_continuous_circle (Complex.continuous_ofReal.comp hpsihc)
  have hpsiL2 : MemLp (fun x => (psi x : ℂ)) 2 volume := by
    convert (psig.property.add (hqL2.const_mul (A : ℂ))).add hhl2 using 1
    funext x
    simp only [psi, Complex.ofReal_add, Complex.ofReal_mul, Pi.add_apply, Function.comp_apply]
  refine ⟨hf, Cg + |A| * Cq + B + 1, by positivity, ?_⟩
  dsimp only [TransportRegularity, unitLength, Circle, arclength]
  have hmarks : ((0 : ℝ) : UnitAddCircle) ≠ ((-(1 / 2 : ℝ)) : UnitAddCircle) := by
    intro heq
    have hr := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1 : ℝ)) (a := -(1 / 2 : ℝ))
      (show (0 : ℝ) ∈ Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) by norm_num)
      (show -(1 / 2 : ℝ) ∈ Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) by norm_num)).mp heq
    norm_num at hr
  refine ⟨?_, ⟨⟨psi, hpsiL2⟩, ?_, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact (hmarks hij).elim
    · exact (hmarks hij.symm).elim
    · rfl
  · intro k
    change fourierCoeff (fun x => (psi x : ℂ)) k = _
    have hsum := Internal.transportCoeffs_unit_linear_combination P A hf hgL2
      Internal.memLp_quadraticCell hhL2 he k
    simp only [unitLength, Circle, arclength] at hsum
    have hgI : Integrable (fun x => (psig.val x : ℂ)) AddCircle.haarAddCircle := by
      rw [← volume_eq_haar_circle]
      exact psig.property.integrable (by norm_num)
    have hqI : Integrable (fun x => (psiq x : ℂ)) AddCircle.haarAddCircle :=
      integrable_of_continuous_circle (Complex.continuous_ofReal.comp hpsiqc)
    have hhI : Integrable (fun x => (psih x : ℂ)) AddCircle.haarAddCircle :=
      integrable_of_continuous_circle (Complex.continuous_ofReal.comp hpsihc)
    have hcpsi : fourierCoeff (fun x => (psi x : ℂ)) k =
        fourierCoeff (fun x => (psig.val x : ℂ)) k +
          (A : ℂ) * fourierCoeff (fun x => (psiq x : ℂ)) k +
          fourierCoeff (fun x => (psih x : ℂ)) k := by
      simp only [psi, Complex.ofReal_add, Complex.ofReal_mul]
      change fourierCoeff (((fun x => (psig.val x : ℂ)) +
        (fun x => (A : ℂ) * (psiq x : ℂ))) + (fun x => (psih x : ℂ))) k = _
      rw [congrFun (fourierCoeff.add (hgI.add (hqI.const_mul (A : ℂ))) hhI) k]
      simp only [Pi.add_apply]
      rw [congrFun (fourierCoeff.add hgI (hqI.const_mul (A : ℂ))) k]
      simp only [Pi.add_apply]
      rw [fourierCoeff.const_mul]
    refine hcpsi.trans (Eq.trans ?_ hsum.symm)
    exact congrArg₂ (fun z w : ℂ => z + w)
      (congrArg₂ (fun z w : ℂ => z + (A : ℂ) * w) (hpsigcoeff k) (hpsiqcoeff k))
      (hpsihcoeff k)
  · intro x hx
    change ∀ j : Fin 2, (x : UnitAddCircle) ≠ ((![0, -(1 / 2)] j : ℝ) : UnitAddCircle) at hx
    have hx0 : (x : UnitAddCircle) ≠ 0 := by simpa using hx 0
    have hxq : (x : UnitAddCircle) ≠ ((-(1 / 2 : ℝ)) : UnitAddCircle) := by simpa using hx 1
    have hnear : dist (x : UnitAddCircle) 0 ≤ 1 :=
      (Internal.unit_circle_dist_le_half _ _).trans (by norm_num)
    have hfar : ¬ 1 ≤ dist (x : UnitAddCircle) 0 := by
      have hh := Internal.unit_circle_dist_le_half (x : UnitAddCircle) 0
      linarith
    obtain ⟨hgcd, hgb⟩ := hpsigpoint x (fun _ => hx0)
    obtain ⟨hqcd, hqb⟩ := hCqb x hxq
    have hhcd := hpsihcd.contDiffAt (x := x)
    change |deriv (deriv (fun t : ℝ => psig.val (t : UnitAddCircle))) x| ≤
      Cg * ((if dist (x : UnitAddCircle) 0 ≤ 1 then
        ∑ _j : Fin 1, dist (x : UnitAddCircle) 0 ^ (-2 + P.val.2 - a) else 0) +
        (if 1 ≤ dist (x : UnitAddCircle) 0 then dist (x : UnitAddCircle) 0 ^ (-3 + P.val.2) else 0)) at hgb
    have hgB : |deriv (deriv (fun t : ℝ => psig.val (t : UnitAddCircle))) x| ≤
        Cg * dist (x : UnitAddCircle) 0 ^ (-2 + P.val.2 - a) := by
      simpa only [hnear, hfar, ↓reduceIte, Fin.sum_univ_one, add_zero] using hgb
    have hqAcd : ContDiffAt ℝ 2 (fun t : ℝ => A * psiq (t : UnitAddCircle)) x :=
      contDiffAt_const.mul hqcd
    refine ⟨(hgcd.add hqAcd).add hhcd, ?_⟩
    have hdd : deriv (deriv (fun t : ℝ => psi (t : UnitAddCircle))) x =
        deriv (deriv (fun t : ℝ => psig.val (t : UnitAddCircle))) x +
          A * deriv (deriv (fun t : ℝ => psiq (t : UnitAddCircle))) x +
          deriv (deriv (fun t : ℝ => psih (t : UnitAddCircle))) x := by
      have hi := iteratedDeriv_fun_add (n := 2) (hgcd.add hqAcd) hhcd
      rw [iteratedDeriv_fun_add hgcd hqAcd, iteratedDeriv_const_mul A hqcd] at hi
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero, psi] using hi
    have hdqp : 0 < dist (x : UnitAddCircle) ((-(1 / 2 : ℝ)) : UnitAddCircle) := dist_pos.mpr hxq
    have hdq1 : dist (x : UnitAddCircle) ((-(1 / 2 : ℝ)) : UnitAddCircle) ≤ 1 :=
      (Internal.unit_circle_dist_le_half _ _).trans (by norm_num)
    have hpow : dist (x : UnitAddCircle) ((-(1 / 2 : ℝ)) : UnitAddCircle) ^ (P.val.2 - 1) ≤
        dist (x : UnitAddCircle) ((-(1 / 2 : ℝ)) : UnitAddCircle) ^ (-2 + P.val.2 - a) :=
      Real.rpow_le_rpow_of_exponent_ge hdqp hdq1 (by linarith)
    have hone : 1 ≤ dist (x : UnitAddCircle) ((-(1 / 2 : ℝ)) : UnitAddCircle) ^ (-2 + P.val.2 - a) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdqp hdq1 (by linarith [P.2.2.2])
    have hqb' := hqb.trans (mul_le_mul_of_nonneg_left hpow hCq.le)
    rw [hdd]
    change _ ≤ (Cg + |A| * Cq + B + 1) *
      ((if dist (x : UnitAddCircle) 0 ≤ 1 then
        ∑ j : Fin 2, dist (x : UnitAddCircle) ((![0, -(1 / 2)] j : ℝ) : UnitAddCircle) ^
          (-2 + P.val.2 - a) else 0) +
        (if 1 ≤ dist (x : UnitAddCircle) 0 then dist (x : UnitAddCircle) 0 ^ (-3 + P.val.2) else 0))
    simp only [hnear, hfar, ↓reduceIte, add_zero, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, AddCircle.coe_zero, AddCircle.coe_neg]
    have htri := (abs_add_le
      (deriv (deriv (fun t : ℝ => psig.val (t : UnitAddCircle))) x +
        A * deriv (deriv (fun t : ℝ => psiq (t : UnitAddCircle))) x)
      (deriv (deriv (fun t : ℝ => psih (t : UnitAddCircle))) x)).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    rw [abs_mul] at htri
    have hp0 : 0 ≤ dist (x : UnitAddCircle) 0 ^ (-2 + P.val.2 - a) := by positivity
    have hpq : 0 ≤ dist (x : UnitAddCircle) ((-(1 / 2 : ℝ)) : UnitAddCircle) ^ (-2 + P.val.2 - a) := by positivity
    nlinarith [hBh x, mul_le_mul_of_nonneg_left hqb' (abs_nonneg A),
      mul_le_mul_of_nonneg_left hone hB.le, mul_nonneg hCg.le hpq,
      mul_nonneg (mul_nonneg (abs_nonneg A) hCq.le) hp0, mul_nonneg hB.le hp0]

end Riesz1
