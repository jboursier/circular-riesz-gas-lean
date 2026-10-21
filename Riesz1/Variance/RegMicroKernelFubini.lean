/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelKernel
public import Riesz1.Kernel.TransportScaledFubini
public import Riesz1.Kernel.TransportScaledLattice
public import Riesz1.Kernel.TransportSingular

/-!
# Borel version and Fubini identity for the inverse-transport kernel

This file prepares the convolution step in the proof of Lemma 5.3. The kernel
`P_L` of `Riesz1.inverseKernel` is `L`-periodic, integrable on a period, and `C |t|^{-s}` in
size near the origin. Its Borel version `inverseKernelRep` agrees with it off the lattice `Lℤ`,
which is a countable set. The main result is the Fourier identity of the convolution with a
period-integrable function `g` against the character `charE L k`:
`∫_C (∫_C g(y) P_L(x - y) dy) e_k(x) dx = (∫_C g e_k)(∫_C P_L e_k)`, on the cell `C = (-L/2, L/2]`.
The proof follows `Riesz1.integral_kernel_charE` for the transport kernel.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

open Classical in
/-- The inverse-transport kernel with its values on the lattice `Lℤ` replaced by `0`. It is a
Borel version of `inverseKernel`. -/
@[expose] noncomputable def inverseKernelRep (P : Parameters) (L : ℝ) : ℝ → ℝ :=
  {t : ℝ | ∀ k : ℤ, t ≠ k * L}.piecewise (inverseKernel P L) (fun _ => 0)

open Classical in
/-- Off the lattice `Lℤ`, `inverseKernelRep` equals `inverseKernel`. -/
lemma inverseKernelRep_of_ne {P : Parameters} {L t : ℝ} (ht : ∀ k : ℤ, t ≠ k * L) :
    inverseKernelRep P L t = inverseKernel P L t :=
  Set.piecewise_eq_of_mem _ _ _ ht

/-- `inverseKernel` is `C^∞` off the lattice `Lℤ`. -/
lemma contDiffAt_inverseKernel (P : Parameters) {L t : ℝ} (hL : 0 < L)
    (ht : ∀ k : ℤ, t ≠ k * L) : ContDiffAt ℝ ∞ (inverseKernel P L) t := by
  have hsmooth := (fundamental_series (parametersExponent P)).2.1
  have hmem : t / L ∈ {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    unitAddCircle_ne_zero_of_not_lattice hL ht
  have hg : ContDiffAt ℝ ∞ (fun x : ℝ => rieszRepresentative (parametersExponent P) x) (t / L) :=
    (hsmooth (t / L) hmem).contDiffAt (isOpen_unitAddCircle_ne_zero.mem_nhds hmem)
  have hdiv : ContDiffAt ℝ ∞ (fun x : ℝ => x / L) t := contDiffAt_id.div_const L
  have hcomp : ContDiffAt ℝ ∞
      (fun x : ℝ => rieszRepresentative (parametersExponent P) ((x / L : ℝ) : UnitAddCircle)) t :=
    ContDiffAt.comp (g := fun x : ℝ => rieszRepresentative (parametersExponent P) (x : UnitAddCircle))
      t hg hdiv
  exact contDiffAt_const.mul hcomp

open Classical in
/-- The Borel version `inverseKernelRep` is measurable. -/
lemma measurable_inverseKernelRep (P : Parameters) {L : ℝ} (hL : 0 < L) :
    Measurable (inverseKernelRep P L) := by
  unfold inverseKernelRep
  exact ContinuousOn.measurable_piecewise
    (fun _ hr => (contDiffAt_inverseKernel P hL hr).continuousAt.continuousWithinAt)
    continuousOn_const (isOpen_lattice_compl hL).measurableSet

/-- The lattice `Lℤ` is a countable set, so `inverseKernelRep` equals `inverseKernel` almost
everywhere. -/
lemma inverseKernelRep_ae_eq (P : Parameters) (L : ℝ) :
    inverseKernelRep P L =ᵐ[volume] inverseKernel P L := by
  have hcount : (Set.range fun k : ℤ => (k : ℝ) * L).Countable := Set.countable_range _
  filter_upwards [hcount.ae_notMem volume] with t ht
  exact inverseKernelRep_of_ne fun k h => ht ⟨k, h.symm⟩

/-- For fixed `y`, `inverseKernelRep (x - y)` agrees with `inverseKernel (x - y)` for almost every
`x`, since the exceptional set `{x | x - y ∈ Lℤ}` is countable. -/
lemma ae_inverseKernelRep_sub (P : Parameters) (L y : ℝ) :
    ∀ᵐ x : ℝ, inverseKernelRep P L (x - y) = inverseKernel P L (x - y) := by
  have hcount : (Set.range fun k : ℤ => y + k * L).Countable := Set.countable_range _
  filter_upwards [hcount.ae_notMem volume] with x hx
  exact inverseKernelRep_of_ne fun k h => hx ⟨k, by linarith⟩

/-- The distance from `t` to the lattice `Lℤ` is `|t|` on the open cell `|t| < L/2`. -/
lemma latticeDist_eq_abs_of_abs_lt {L t : ℝ} (hL : 0 < L) (ht : |t| < L / 2) :
    latticeDist L t = |t| := by
  have hround : round (t / L) = 0 := by
    rw [round_eq_zero_iff]
    constructor
    · have : -(L / 2) < t := (abs_lt.1 ht).1
      have h2 : -(1 / 2 : ℝ) < t / L := by
        rw [lt_div_iff₀ hL]
        linarith
      exact h2.le
    · have : t < L / 2 := (abs_lt.1 ht).2
      rw [div_lt_iff₀ hL]
      linarith
  unfold latticeDist
  rw [hround]
  simp

/-- Off the lattice and inside the cell, `|P_L(t)| ≤ C |t|^{-s}` with `C` independent of `L`. -/
lemma abs_inverseKernel_le_cell (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ L t : ℝ, 0 < L → |t| < L / 2 → t ≠ 0 →
      |inverseKernel P L t| ≤ C * |t| ^ (-P.val.2) := by
  obtain ⟨C, hC, hb⟩ := inverseKernel_iteratedDeriv_bound P 0
  refine ⟨C, hC, fun L t hL ht ht0 => ?_⟩
  have hlat : ∀ k : ℤ, t ≠ k * L := by
    intro k hk
    rcases eq_or_ne k 0 with rfl | hk0
    · simp only [Int.cast_zero, zero_mul] at hk
      exact ht0 hk
    · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
        exact_mod_cast h1
      have hT : |t| = |(k : ℝ)| * L := by rw [hk, abs_mul, abs_of_pos hL]
      nlinarith
  have h := hb L t hL hlat
  rw [iteratedDeriv_zero, latticeDist_eq_abs_of_abs_lt hL ht, Nat.cast_zero, sub_zero] at h
  exact h

/-- The kernel `P_L` is integrable on the cell `(-L/2, L/2]`. -/
lemma integrableOn_inverseKernel_cell (P : Parameters) {L : ℝ} (hL : 0 < L) :
    IntegrableOn (inverseKernel P L) (Ioc (-(L / 2)) (L / 2)) := by
  obtain ⟨C, hC, hb⟩ := abs_inverseKernel_le_cell P
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hB : IntegrableOn (fun t : ℝ => C * |t| ^ (-P.val.2)) (Ioc (-(L / 2)) (L / 2)) :=
    (((intervalIntegrable_abs_rpow (by linarith [P.property.2.2]) (-(L / 2)) (L / 2)).const_mul C)
      |> (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1)
  have hmeas : AEStronglyMeasurable (inverseKernel P L)
      (volume.restrict (Ioc (-(L / 2)) (L / 2))) :=
    ((measurable_inverseKernelRep P hL).aestronglyMeasurable.congr
      (inverseKernelRep_ae_eq P L)).restrict
  refine Integrable.mono' hB hmeas ?_
  have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 ∧ t ≠ L / 2 :=
    ((Set.countable_singleton (0 : ℝ)).ae_notMem volume).and
      ((Set.countable_singleton (L / 2)).ae_notMem volume)
  filter_upwards [ae_restrict_of_ae hnull, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  obtain ⟨ht0, htL⟩ := ht
  have hlt : |t| < L / 2 := by
    obtain ⟨h1, h2⟩ := hmem
    rw [abs_lt]
    exact ⟨by linarith, lt_of_le_of_ne h2 htL⟩
  rw [Real.norm_eq_abs]
  exact hb L t hL hlt ht0

/-- The kernel `P_L` is interval integrable on every bounded interval, by periodicity. -/
lemma intervalIntegrable_inverseKernel (P : Parameters) {L : ℝ} (hL : 0 < L) (a b : ℝ) :
    IntervalIntegrable (inverseKernel P L) volume a b := by
  have hcell : IntervalIntegrable (inverseKernel P L) volume (-(L / 2)) (-(L / 2) + L) := by
    rw [show -(L / 2) + L = L / 2 by ring]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      (integrableOn_inverseKernel_cell P hL)
  exact (inverseKernel_periodic P hL).intervalIntegrable hL.ne' hcell a b

/-- The integral of `|P_L(x - y)|` over the cell does not depend on `y`. -/
lemma setIntegral_abs_inverseKernelRep_sub (P : Parameters) {L : ℝ} (hL : 0 < L) (y : ℝ) :
    ∫ x in Ioc (-(L / 2)) (L / 2), |inverseKernelRep P L (x - y)| =
      ∫ x in Ioc (-(L / 2)) (L / 2), |inverseKernel P L x| := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have h1 : ∫ x in Ioc (-(L / 2)) (L / 2), |inverseKernelRep P L (x - y)| =
      ∫ x in Ioc (-(L / 2)) (L / 2), |inverseKernel P L (x - y)| := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [ae_inverseKernelRep_sub P L y] with x hx _
    rw [hx]
  have hper : Function.Periodic (fun x => |inverseKernel P L x|) L :=
    fun r => by simp only [inverseKernel_periodic P hL r]
  rw [h1, ← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
  exact integral_comp_sub_periodic hper y

/-- **Integrability of the convolution product.** For `g` integrable on the cell, the function
`(x, y) ↦ g(y) P_L(x - y)` is integrable on the product of the cell with itself. -/
lemma integrable_inverseKernelRep_prod (P : Parameters) {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc (-(L / 2)) (L / 2))) :
    Integrable (fun p : ℝ × ℝ => g p.2 * inverseKernelRep P L (p.1 - p.2))
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2 * inverseKernelRep P L (p.1 - p.2))
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) :=
    (hg.aestronglyMeasurable.comp_snd).mul
      ((((measurable_inverseKernelRep P hL).comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable)
  rw [integrable_prod_iff' hmeas]
  refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
  · have hKshift : IntegrableOn (fun x => inverseKernel P L (x - y)) (Ioc (-(L / 2)) (L / 2)) := by
      have h := (intervalIntegrable_inverseKernel P hL (-(L / 2) - y) (L / 2 - y)).comp_sub_right y
      rw [sub_add_cancel, sub_add_cancel] at h
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      exact h
    have hx : Integrable (fun x => inverseKernelRep P L (x - y))
        (volume.restrict (Ioc (-(L / 2)) (L / 2))) :=
      Integrable.congr hKshift (by
        filter_upwards [ae_restrict_of_ae (ae_inverseKernelRep_sub P L y)] with x hx
        exact hx.symm)
    exact hx.const_mul (g y)
  · have hN : ∀ y : ℝ, ∫ x in Ioc (-(L / 2)) (L / 2), ‖g y * inverseKernelRep P L (x - y)‖ =
        ‖g y‖ * ∫ x in Ioc (-(L / 2)) (L / 2), |inverseKernel P L x| := by
      intro y
      simp_rw [norm_mul, Real.norm_eq_abs]
      rw [MeasureTheory.integral_const_mul, setIntegral_abs_inverseKernelRep_sub P hL y]
    have hfun : (fun y : ℝ => ∫ x in Ioc (-(L / 2)) (L / 2), ‖g y * inverseKernelRep P L (x - y)‖) =
        fun y => ‖g y‖ * ∫ x in Ioc (-(L / 2)) (L / 2), |inverseKernel P L x| := funext hN
    rw [hfun]
    exact hg.norm.mul_const _

/-- **Fourier coefficient of the convolution with `P_L`.** For `g` integrable on the cell
`C = (-L/2, L/2]` and every integer `k`,
`∫_C (∫_C g(y) P_L(x - y) dy) e_k(x) dx = (∫_C g e_k) (∫_C P_L e_k)`. -/
lemma integral_inverseKernel_charE (P : Parameters) {L : ℝ} (hL : 0 < L) (k : ℤ)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc (-(L / 2)) (L / 2))) :
    ∫ x in Ioc (-(L / 2)) (L / 2),
        ((∫ y in Ioc (-(L / 2)) (L / 2), g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) * charE L k x =
      (∫ y in Ioc (-(L / 2)) (L / 2), (g y : ℂ) * charE L k y) *
        ∫ u in Ioc (-(L / 2)) (L / 2), (inverseKernel P L u : ℂ) * charE L k u := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  have hEc : Continuous (charE L k) := by
    unfold charE
    fun_prop
  have hF : Function.Periodic (fun u : ℝ => (inverseKernel P L u : ℂ) * charE L k u) L :=
    fun u => by simp only [inverseKernel_periodic P hL u, charE_add_period hL.ne' k u]
  have step1 : ∀ x : ℝ, ((∫ y in Ioc (-(L / 2)) (L / 2), g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) *
      charE L k x = ∫ y in Ioc (-(L / 2)) (L / 2), ((g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) *
        charE L k x := by
    intro x
    rw [← integral_complex_ofReal, ← MeasureTheory.integral_mul_const]
  have hint : Integrable (Function.uncurry fun x y =>
      ((g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) * charE L k x)
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
        (volume.restrict (Ioc (-(L / 2)) (L / 2)))) := by
    have h1 : Integrable (fun p : ℝ × ℝ => ((g p.2 * inverseKernelRep P L (p.1 - p.2) : ℝ) : ℂ))
        ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
          (volume.restrict (Ioc (-(L / 2)) (L / 2)))) :=
      (integrable_inverseKernelRep_prod P hL hg).ofReal
    have hE : AEStronglyMeasurable (fun p : ℝ × ℝ => charE L k p.1)
        ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod
          (volume.restrict (Ioc (-(L / 2)) (L / 2)))) :=
      (hEc.measurable.comp measurable_fst).aestronglyMeasurable
    exact h1.mul_bdd hE (Eventually.of_forall fun p => (norm_charE L k p.1).le)
  have step3 : ∀ y : ℝ, ∫ x in Ioc (-(L / 2)) (L / 2),
      ((g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) * charE L k x =
      ((g y : ℂ) * charE L k y) *
        ∫ u in Ioc (-(L / 2)) (L / 2), (inverseKernel P L u : ℂ) * charE L k u := by
    intro y
    have ha : ∀ᵐ x ∂(volume.restrict (Ioc (-(L / 2)) (L / 2))),
        ((g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) * charE L k x =
          ((g y : ℂ) * charE L k y) * ((inverseKernel P L (x - y) : ℂ) * charE L k (x - y)) := by
      filter_upwards [ae_restrict_of_ae (ae_inverseKernelRep_sub P L y)] with x hx
      rw [hx, charE_mul L k x y]
      push_cast
      ring
    rw [integral_congr_ae ha, MeasureTheory.integral_const_mul,
      ← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle]
    congr 1
    have hsh := integral_comp_sub_periodic hF y
    simpa only using hsh
  calc ∫ x in Ioc (-(L / 2)) (L / 2),
        ((∫ y in Ioc (-(L / 2)) (L / 2), g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) * charE L k x
      = ∫ x in Ioc (-(L / 2)) (L / 2), ∫ y in Ioc (-(L / 2)) (L / 2),
          ((g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) * charE L k x := by
        simp_rw [step1]
    _ = ∫ y in Ioc (-(L / 2)) (L / 2), ∫ x in Ioc (-(L / 2)) (L / 2),
          ((g y * inverseKernelRep P L (x - y) : ℝ) : ℂ) * charE L k x :=
        integral_integral_swap hint
    _ = ∫ y in Ioc (-(L / 2)) (L / 2), ((g y : ℂ) * charE L k y) *
          ∫ u in Ioc (-(L / 2)) (L / 2), (inverseKernel P L u : ℂ) * charE L k u := by
        simp_rw [step3]
    _ = _ := MeasureTheory.integral_mul_const _ _

end Riesz1

end
