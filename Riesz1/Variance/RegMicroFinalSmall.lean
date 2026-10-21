/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFinalFar
public import Riesz1.Variance.RegMicroFinalNear
public import Riesz1.ToMathlib.VarianceAddFinite

/-!
# Small-radius microscopic variance on the original statistic

Assembly of Lemma 5.3, for the nonexceptional
exponents and radii below the fixed cutoff. The analytic inputs are
the kernel conclusion and the regularity predicates.
The conclusion concerns the original mixed regularization error,
with its second moment and extended variance, rather than a chosen
pointwise representative.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- A continuous circle function which vanishes almost everywhere beyond
radius `R` vanishes pointwise strictly beyond it. -/
theorem regMicro_continuous_zero_of_ae_support (L : Length) (R : ℝ)
    (g : Circle L → ℝ) (hc : Continuous g)
    (hsupp : ∀ᵐ z ∂arclength L, R ≤ dist z 0 → g z = 0)
    {z : Circle L} (hz : R < dist z 0) : g z = 0 := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have : (arclength L).IsOpenPosMeasure := by
    change (volume : Measure (Circle L)).IsOpenPosMeasure
    infer_instance
  let U := {z : Circle L | R < dist z 0}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have heq : g =ᵐ[(arclength L).restrict U] fun _ => 0 := by
    change ∀ᵐ x ∂(arclength L).restrict U, g x = 0
    rw [ae_restrict_iff' hU.measurableSet]
    filter_upwards [hsupp] with x hx hmem
    exact hx hmem.le
  exact Measure.eqOn_open_of_ae_eq heq hU hc.continuousOn continuous_const.continuousOn hz

/-- The complete small-radius near/far estimate for the actual original
error. The common kernel bound and cutoff radius precede every scale,
test and particle number. Compact support is needed only almost
everywhere. A bounded circle also suffices. -/
theorem regMicro_small_radius_of_kernel
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (α ε : ℝ) (hα0 : P.val.2-1 ≤ α) (hα1 : α < P.val.2/2)
    (hα : α ≠ 0) (hε : 0 < ε)
    (n : ℕ+) (η B₀ C₀ : ℝ) (hη : 0 < η) (hB₀ : 0 ≤ B₀) (hC₀ : 0 ≤ C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ)
    (C H r₀ R : ℝ) (hC : 0 ≤ C) (hr₀ : 0 < r₀) (hrsmall : r₀ < 1/8) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ)*ℓ.val →
      let L := observationLength ℓ
      let K := (N : ℝ)*ℓ.val
      ∀ (a : Fin (n : ℕ) → ℝ),
        (∀ i j, i ≠ j → 4*r₀ ≤ dist (a i : Circle L) (a j : Circle L)) →
      ∀ f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)},
        PrimitiveRegularity L η P.val.2 B₀ f → TransportRegularity P L f n a α C₀ →
        MicroKernelBounds P ρ α C H n a L f →
        K⁻¹ ≤ H → K⁻¹ ≤ r₀/8 →
        (L.val/2 ≤ R ∨ ∀ᵐ z ∂arclength L, R ≤ dist z 0 →
          f.val z-cltRegCircle hρ L (show 0<K⁻¹ from
            inv_pos.mpr (mul_pos (by exact_mod_cast N.pos) ℓ.property.1)) f z = 0) →
      ∃ hE : MemLp (mixedStat P N ℓ (subCircleL2 f (mixedReg hρ N ℓ f))) 2 (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
          ENNReal.ofReal (D*K^ε*(K^(2*α)+K^(3*P.val.2-2))) := by
  obtain ⟨Dₘ, Dⱼ, Dᵣ, hDₘ, hDⱼ, hDᵣ, hder⟩ := regMicro_far_derivatives_of_kernel n
  let q := 2-P.val.2+α
  let A := C*(1+(n : ℝ)*Dₘ/2*4^q)
  let B := C*r₀^(-1-α)
  let F := A+Dⱼ/r₀*B*(2*r₀)^q
  let G := A*r₀^(-q)+(n : ℝ)*Dᵣ/r₀*B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  obtain ⟨Dnear, hDnear, hnear⟩ := regMicro_near_variance_of_kernel P n α hα
    (by linarith [P.property.2.2])
  obtain ⟨Dfar, hDfar, hfar⟩ := regMicro_far_variance_of_derivatives hBE hPL P α ε hα0 hε
    n r₀ (R+1) F G hr₀ (by linarith) hF hG
  refine ⟨2*(Dnear*C^2+Dfar), by positivity, fun N ℓ hK => ?_⟩
  dsimp only
  intro a hsep f hprim hreg hkernel hH hsmall hsupp
  let L := observationLength ℓ
  let K := (N : ℝ)*ℓ.val
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hh : 0 < K⁻¹ := inv_pos.mpr hK0
  have hL : 1 ≤ L.val := (one_le_inv₀ ℓ.property.1).mpr ℓ.property.2
  have hh1 : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hsep' : ∀ i j, i ≠ j → 8*K⁻¹ ≤ dist (a i : Circle L) (a j : Circle L) := by
    intro i j hij
    exact (by linarith : 8*K⁻¹ ≤ 4*r₀).trans (hsep i j hij)
  obtain ⟨ψ, hc, hcoeff, hecell, hfc, hrc, hfd, hrd⟩ := hder P L η B₀ hη hB₀ f a α C₀
    hα0 hα1 hC₀ hprim hreg ρ hρ C H hC hkernel r₀ K⁻¹ hr₀ (by linarith) (by linarith)
    hh (by linarith) hh1 hH (by linarith) (by linarith) hsep hsep'
  let m := (∫ y in Ioc (-(L.val/2)) (L.val/2), f.val (y : Circle L))/L.val
  let e := fun z : Circle L => m+inverseConvCircle P L
    (deriv (fun t : ℝ => ψ.val (t : Circle L))) z-cltRegCircle hρ L hh f z
  have he := regMicro_error_memLp_of_kernel P L f ψ n a α C H ρ hρ K⁻¹ hh hc hcoeff hkernel
  have hrcircle : Continuous (microFarRemainder L.val r₀ K⁻¹ a e) :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 hrc.continuous
  have hsupp' : L.val/2 ≤ R+1 ∨ ∀ z, R+1 ≤ dist z 0 →
      microFarRemainder L.val r₀ K⁻¹ a e z = 0 := by
    rcases hsupp with hb | hs
    · exact Or.inl (by linarith)
    · refine Or.inr fun z hz => regMicro_continuous_zero_of_ae_support L R
        (microFarRemainder L.val r₀ K⁻¹ a e) hrcircle ?_ (by linarith)
      filter_upwards [he.1, hs] with z hez hsz hd
      change e z = _ at hez
      have hz0 : e z = 0 := hez.trans (hsz hd)
      simp only [microFarRemainder, hz0, mul_zero]
  obtain ⟨hFarI, hFarV⟩ := hfar N ℓ hK a e hfc hrc hsupp' hfd hrd
  obtain ⟨hNearI, hNearV⟩ := hnear hPL N ℓ hK ρ hρ C H hC hH a hsep' f hkernel ψ hc hcoeff
  let far := fun z : Circle L => (∑ j, microFarError L.val r₀ K⁻¹ a e j z)+
    microFarRemainder L.val r₀ K⁻¹ a e z
  let S := fun X : Configuration N => ∑ i : Fin (N : ℕ), e ((X.val i/ℓ.val : ℝ) : Circle L)
  let U := fun X : Configuration N => ∑ i : Fin (N : ℕ),
    microNearError L.val K⁻¹ a e ((X.val i/ℓ.val : ℝ) : Circle L)
  let V := fun X : Configuration N => ∑ i : Fin (N : ℕ), far ((X.val i/ℓ.val : ℝ) : Circle L)
  have hfarcont : Continuous far := by
    apply Continuous.add _ hrcircle
    apply continuous_finsetSum
    intro j _
    exact (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 (hfc j).continuous
  have hfarLp : MemLp (fun z => (far z : ℂ)) 2 (arclength L) := by
    have : Fact (0 < L.val) := ⟨L.property⟩
    exact (Complex.continuous_ofReal.comp hfarcont).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hVLp : MemLp V 2 (gibbsMeasure P N) := regMicro_plainSum_memLp P N ℓ far hfarLp
  have hSLp : MemLp S 2 (gibbsMeasure P N) := regMicro_plainSum_memLp P N ℓ e he.2
  have hsum (X : Configuration N) : U X+V X = S X := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [far]
    have hp := micro_near_far_decomposition L.val r₀ K⁻¹ a e
      ((X.val i/ℓ.val : ℝ) : Circle L)
    linarith only [hp]
  have hULp : MemLp U 2 (gibbsMeasure P N) :=
    (hSLp.sub hVLp).ae_eq (Eventually.of_forall fun X => by
      change S X-V X = U X
      linarith only [hsum X])
  have hSV : variance (gibbsMeasure P N) S (hSLp.integrable one_le_two) ≤
      ENNReal.ofReal ((2*(Dnear*C^2+Dfar))*K^ε*(K^(2*α)+K^(3*P.val.2-2))) := by
    have hv := variance_add_le_two (gibbsMeasure P N) hULp hVLp
    have hμ : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
    have hEq := auxiliary_variance_congr (hSLp.integrable one_le_two)
      ((hULp.add hVLp).integrable one_le_two) (Eventually.of_forall fun X => (hsum X).symm)
    rw [hEq]
    apply hv.trans
    have hp : K^(2*α) ≤ K^ε*(K^(2*α)+K^(3*P.val.2-2)) := by
      have hpow := Real.one_le_rpow hK hε.le
      have htail := Real.rpow_nonneg hK0.le (3*P.val.2-2)
      nlinarith [Real.rpow_nonneg hK0.le (2*α)]
    have hnearV' := hNearV.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ Dnear*C^2)))
    calc
      _ ≤ 2*(ENNReal.ofReal (Dnear*C^2*(K^ε*(K^(2*α)+K^(3*P.val.2-2))))+
          ENNReal.ofReal (Dfar*K^ε*(K^(2*α)+K^(3*P.val.2-2)))) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hnearV' hFarV) zero_le
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  let E := subCircleL2 f (mixedReg hρ N ℓ f)
  have hELp : MemLp (mixedStat P N ℓ E) 2 (gibbsMeasure P N) :=
    memLp_fluctuation P N (memLp_real_of_complex (loopMasterPullback_memLp _ E))
  have hplain := regMicro_plainSum_memLp P N ℓ E.val E.property
  refine ⟨hELp, ?_⟩
  have heE : e =ᵐ[arclength L] E.val := he.1
  exact (regMicro_mixedStat_variance P N ℓ E (hELp.integrable one_le_two)
    (hplain.integrable one_le_two)).trans_le
      ((auxiliary_variance_congr _ _ (regMicro_plainSum_ae_eq P N ℓ heE).symm).trans_le hSV)

end Riesz1.Internal
