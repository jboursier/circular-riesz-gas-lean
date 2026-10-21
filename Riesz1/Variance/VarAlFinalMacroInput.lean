/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlFinalMacroFamilies
public import Riesz1.Variance.QuantitativeVarianceInput
public import Riesz1.CLT.ErrorOneTransfer
public import Riesz1.CLT.ErrorOneBridge
import all Riesz1.ToMathlib.CirclePullback
import all Riesz1.Variance.LoopMaster
import all Riesz1.Variance.LoopIBPMoments
import all Riesz1.Variance.LoopScale

/-!
# Macroscopic loop variance on the optimal-scaling test carrier

The macroscopic branch of Proposition 5.9, uniformly over the
original test and both families, using precisely `OptimalScalingTest`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz1.Internal

/-- The transport multiplier is linear on real L² representatives. -/
theorem varAlFinal_transport_sub (P : Parameters) (L : Length)
    (f g : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) (k : ℤ) :
    transportCoeffs P L (subCircleL2 f g) k =
      transportCoeffs P L f k - transportCoeffs P L g k := by
  by_cases hk : k = 0
  · simp only [transportCoeffs, hk, ite_true, sub_self]
  · simp only [transportCoeffs, hk, ite_false]
    dsimp only [subCircleL2]
    rw [coeff_sub_real_L2 L f g k]
    ring

/-- Identify an arbitrary smooth regularized transport at a scale of
value one with the convolution of its unit-circle representative. -/
theorem varAlFinal_macro_transfer (P : Parameters) (N : ℕ+) (a : Scale) (ha : a.val = 1)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (f : {f : Circle (loopMasterLength a) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength a))})
    (q : {g : Circle unitLength → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)})
    (hq : ∀ k, coeff unitLength ⟨(fun x => (q.val x : ℂ)),
      complexL2Integrable _ _ q.property⟩ k = transportCoeffs P (loopMasterLength a) f k)
    (ψ : Circle (loopMasterLength a) → ℝ)
    (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength a))))
    (htr : ∀ k, coeff (loopMasterLength a) ⟨(fun x => (ψ x : ℂ)),
      complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
        transportCoeffs P (loopMasterLength a)
          (loopMasterLengthTest _ (cltRegCircle hρ _ hh f)
            (cltRegCircle_contDiff hρ _ hh f)) k)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∃ hi : Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
        (loopScaleField 1 (circleMollify ρ 1 h
          (fun t : ℝ => q.val (t : Circle unitLength)))) X.val) (gibbsMeasure P N),
      variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal B) :
    ∃ hi : Integrable (loopOnConfiguration (parametersExponent P) N a
        (loopMasterProfile a ψ hψ)) (gibbsMeasure P N),
      variance (gibbsMeasure P N) _ hi < ⊤ ∧
        (variance (gibbsMeasure P N) _ hi).toReal ≤ B := by
  have hL : (loopMasterLength a).val = 1 := by change a.val⁻¹ = 1; rw [ha, inv_one]
  obtain ⟨q', hq'v, _, hq'f⟩ := exists_transfer_of_val_one (loopMasterLength a) hL q
  have hq' : ∀ k, coeff (loopMasterLength a) ⟨(fun x => (q'.val x : ℂ)),
      complexL2Integrable _ _ q'.property⟩ k = transportCoeffs P (loopMasterLength a) f k :=
    fun k => (hq'f k).trans (hq k)
  have heq (x : ℝ) : ψ (x : Circle (loopMasterLength a)) =
      circleMollify ρ 1 h (fun t : ℝ => q.val (t : Circle unitLength)) x := by
    have he := errorOne_eq_circleMollify_of_coeff P (loopMasterLength a) hρ hh f q'.val
      q'.property hq' (loopMasterLengthTest _ (cltRegCircle hρ _ hh f)
        (cltRegCircle_contDiff hρ _ hh f))
      (fun x => cltRegCircle_coe hρ _ hh f x) (loopMasterLengthTest _ ψ hψ)
      (continuous_circle_of_lift _ hψ.continuous) htr x
    exact he.trans (circleMollify_eq_of_val_one ρ _ hL h q'.val q.val hq'v x)
  have hfun : loopOnConfiguration (parametersExponent P) N a (loopMasterProfile a ψ hψ) =
      fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
        (loopScaleField 1 (circleMollify ρ 1 h
          (fun t : ℝ => q.val (t : Circle unitLength)))) X.val := by
    funext X
    change loopFunctional P.val.2 (N : ℕ)
      (loopScaleField a.val (fun x : ℝ => ψ (x : Circle (loopMasterLength a)))) X.val = _
    rw [funext heq, ha]
  obtain ⟨hi, hv⟩ := hb
  rw [hfun]
  have hfinite : variance (gibbsMeasure P N) _ hi < ⊤ := hv.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, hfinite, ?_⟩
  exact (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).mpr hv |>.trans
    (ENNReal.toReal_ofReal hB).le

/-- The macroscopic branch of `VarAlVarianceInput`, with the common
coefficient before the scale sequence, particle count, both radii, and
every member of the actual `OptimalScalingTest` relation. -/
theorem varAlFinal_macro_optimalScalingTest
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (hα : P.val.2 - 1 ≤ α) (hα2 : α < P.val.2 / 2)
    (hη : 0 < d.1) (hB : 0 < d.2.1) (hC₀ : 0 < d.2.2.1)
    (hprim : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩
      d.2.2.2.1 d.2.2.2.2 α d.2.2.1)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, (∀ M, (ell M).val = 1) →
      ∀ (N : ℕ+) (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (h : ℝ) (hh : 0 < h), (cltK N (ell N))⁻¹ ≤ h → h ≤ 1 →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N)) ⟨(fun x => (ψ x : ℂ)),
            complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltRegCircle hρ _ hh f)
                  (cltRegCircle_contDiff hρ _ hh f)) k) →
          ∃ hi : Integrable (loopOnConfiguration (parametersExponent P) N (ell N)
              (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ hi < ⊤ ∧
            (variance (gibbsMeasure P N) _ hi).toReal ≤
              C * cltK N (ell N) ^ (ε + max 1 (2 * (1 - P.val.2 + α))) := by
  obtain ⟨Co, hCo, ho⟩ := varAl_loop_variance_macroscopic hBE hPL P p α d hα hα2
    hη hB hC₀ hprim hreg ρ hρ hε
  obtain ⟨Cf, hCf, q, hqc, hqf, hfamily⟩ := varAlFinal_macro_transport_families hBE hPL
    P p α d hα hα2 hη hB hC₀ hprim hreg ρ hρ hε
  let C := max Co Cf
  have hC : 0 < C := hCo.trans_le (le_max_left _ _)
  refine ⟨C, hC, fun ell hell N r v f hv h hh hKh hh1 ψ hψ htr => ?_⟩
  let a := ell N
  let L := loopMasterLength a
  let ξ := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
    {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
  have ha : a.val = 1 := hell N
  have hL : L.val = 1 := by change a.val⁻¹ = 1; rw [ha, inv_one]
  have hK : cltK N a = (N : ℝ) := by change (N : ℝ) * a.val = _; rw [ha, mul_one]
  have hhN : (N : ℝ)⁻¹ ≤ h := by
    change (cltK N a)⁻¹ ≤ h at hKh
    rwa [hK] at hKh
  let D := (N : ℝ) ^ (ε + max 1 (2 * (1 - P.val.2 + α)))
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hξ (k : ℤ) : transportCoeffs P L ξ k =
      transportCoeffs P unitLength ⟨p.val, p.property⟩ k :=
    transportCoeffs_periodizedProfile_eq_unit P p L hL ξ.property k
  have hbound (q₀ : {g : Circle unitLength → ℝ //
      MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)})
      (hcoef : ∀ k, coeff unitLength ⟨(fun x => (q₀.val x : ℂ)),
        complexL2Integrable _ _ q₀.property⟩ k = transportCoeffs P L f k)
      {B : ℝ} (hBC : B ≤ C)
      (hb : ∃ hi : Integrable (fun X : Configuration N => loopFunctional P.val.2 (N : ℕ)
          (loopScaleField 1 (circleMollify ρ 1 h
            (fun t : ℝ => q₀.val (t : Circle unitLength)))) X.val) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hi ≤ ENNReal.ofReal (B * D)) :
      ∃ hi : Integrable (loopOnConfiguration (parametersExponent P) N a
          (loopMasterProfile a ψ hψ)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hi < ⊤ ∧
          (variance (gibbsMeasure P N) _ hi).toReal ≤ C * cltK N a ^
            (ε + max 1 (2 * (1 - P.val.2 + α))) := by
    apply varAlFinal_macro_transfer P N a ha hρ hh f q₀ hcoef ψ hψ htr
      (mul_nonneg hC.le (Real.rpow_nonneg (cltK_pos N a).le _))
    obtain ⟨hi, hv⟩ := hb
    exact ⟨hi, hv.trans (ENNReal.ofReal_le_ofReal (by rw [hK]; exact mul_le_mul_of_nonneg_right hBC hD))⟩
  rcases hv with ⟨_, rfl⟩ | ⟨t, ht, ht1, _, hcases⟩
  · exact hbound q (fun k => (hqf k).trans (hξ k).symm) (le_max_left _ _)
      (ho N h hhN hh1 q hqf)
  · obtain ⟨φ, χ, _, _, hfφ, hfχ, hvar⟩ := hfamily t ht ht1
    let g := loopMasterLengthTest L (cltRegCircle hρ L ht ξ)
      (cltRegCircle_contDiff hρ L ht ξ)
    have hg (k : ℤ) : transportCoeffs P L g k =
        transportCoeffs P unitLength ⟨p.val, p.property⟩ k *
          (mollifierFT ρ (t * k) : ℂ) := by
      have he := errorOne_transportCoeffs_smooth P L hρ ht ξ g
        (fun x => cltRegCircle_coe hρ L ht ξ x) k
      simpa only [hξ, hL, div_one] using he
    rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hbound φ (fun k => (hfφ k).trans (hg k).symm) (le_max_right _ _)
        (hvar φ (Or.inl rfl) N h hhN hh1)
    · exact hbound χ (fun k => (hfχ k).trans (by
        change transportCoeffs P unitLength ⟨p.val, p.property⟩ k -
          transportCoeffs P unitLength ⟨p.val, p.property⟩ k *
            (mollifierFT ρ (t * k) : ℂ) = transportCoeffs P L (subCircleL2 ξ g) k
        rw [varAlFinal_transport_sub, hξ, hg]))
        (le_max_right _ _) (hvar χ (Or.inr rfl) N h hhN hh1)

/-- Discharge the macroscopic portion of `VarAlVarianceInput` from
`External.BakryEmery` and `External.PrekopaLeindler`. All profile assumptions
are extracted after the coefficient from the `Admissible` predicate. -/
theorem varAlVarianceInput_macroscopic_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales, Admissible P p ell α d →
      (∀ M, (ell M).val = 1) →
      ∀ (N : ℕ+) (r : ℝ) (v : Profile)
        (f : {f : Circle (loopMasterLength (ell N)) → ℝ //
          MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength (ell N)))}),
        OptimalScalingTest p ell N hρ r v f →
        ∀ (h : ℝ) (hh : 0 < h), (cltK N (ell N))⁻¹ ≤ h → h ≤ 1 →
        ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
          (hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N))))),
          (∀ k, coeff (loopMasterLength (ell N)) ⟨(fun x => (ψ x : ℂ)),
            complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltRegCircle hρ _ hh f)
                  (cltRegCircle_contDiff hρ _ hh f)) k) →
          ∃ hi : Integrable (loopOnConfiguration (parametersExponent P) N (ell N)
              (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
            variance (gibbsMeasure P N) _ hi < ⊤ ∧
            (variance (gibbsMeasure P N) _ hi).toReal ≤
              C * cltK N (ell N) ^ (ε + max 1 (2 * (1 - P.val.2 + α))) := by
  classical
  let H := ∃ ell : Scales, Admissible P p ell α d ∧ ∀ M, (ell M).val = 1
  by_cases hex : H
  · obtain ⟨ell₀, hadm, hone⟩ := hex
    obtain ⟨hα, hα2, hη, _, hB, hC₀, hcases⟩ := hadm
    have hdata : PrimitiveRegularity unitLength d.1 P.val.2 d.2.1 ⟨p.val, p.property⟩ ∧
        TransportRegularity P unitLength ⟨p.val, p.property⟩
          d.2.2.2.1 d.2.2.2.2 α d.2.2.1 := by
      rcases hcases with ⟨_, hprim, hreg⟩ | ⟨_, hlim, _⟩
      · exact ⟨hprim, hreg⟩
      · have hc : Filter.Tendsto
            (fun k : ℕ => (ell₀ ⟨k + 1, Nat.succ_pos k⟩).val)
            Filter.atTop (nhds (1 : ℝ)) := by
          have heq : (fun k : ℕ => (ell₀ ⟨k + 1, Nat.succ_pos k⟩).val) =
              fun _ : ℕ => (1 : ℝ) := funext (fun k => hone _)
          rw [heq]
          exact tendsto_const_nhds
        have hh := tendsto_nhds_unique hc hlim
        norm_num at hh
    obtain ⟨C, hC, hall⟩ := varAlFinal_macro_optimalScalingTest hBE hPL P p α d hα hα2
      hη hB hC₀ hdata.1 hdata.2 ρ hρ hε
    exact ⟨C, hC, fun ell _ hell => hall ell hell⟩
  · refine ⟨1, one_pos, fun ell hadm hone => ?_⟩
    exact False.elim (hex ⟨ell, hadm, hone⟩)

end Riesz1.Internal

end
