/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Identity
public import Riesz1.Variance.RegUniformDerivatives
public import Riesz1.Variance.RegUniformFirstTransport
public import Riesz1.Variance.RegUniformTransport
public import Riesz1.Variance.RegMicroKernelSupport
public import Riesz1.Kernel.AdmissibilityRegularityMembership
public import Riesz1.Kernel.TransportScaledConvolution
public import Riesz1.ToMathlib.CircleCoeffUniqueness
public import Riesz1.ToMathlib.MollifierPointwise.Circle
public import Riesz1.Frozen.Admissible

/-!
# Analytic bounds for the regularized profile and its transport

The analytic input of the first error term of Theorem 3. For the scale profile
`scaleProfile p ℓ` (the periodization of `p` on the observation circle `Circle (ℓ⁻¹)`), the
regularized profile `R = cltRegLine` and the transport `Ψ = loopMasterProfile` satisfy uniform
bounds in the smoothing radius `δ = cltDelta`. The bridges to the mollified transport and to the
circle integrals are proved here. The derivative bounds of Theorem 3 are assembled from
Lemma 5.1 in `ErrorOneBounds` and `ErrorOneCases`.

The scale profile is the same periodization for every `ℓ`, including `ℓ = 1`. At `ℓ = 1` it agrees
with `p` except at the single point `1/2` modulo `1`, where the central zero extension vanishes.
So it is an `L²` representative of `p`: all Fourier coefficients, transports and regularizations
agree with those of `p`, and no compactness of `p` is used at scale one.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Riesz1

namespace Internal

/-- The scale-`ℓ` profile of `p` on the observation circle `Circle (loopMasterLength ℓ)`, the
periodization of `p` at period `ℓ⁻¹` (`observationLength ℓ` and `loopMasterLength ℓ` are equal
lengths). See the module documentation for the choice at scale one. -/
noncomputable def scaleProfile (p : Profile) (ℓ : Ioc (0 : ℝ) 1) :
    {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))} :=
  ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩

end Internal

namespace Internal

/-- The line profile `cltRegLine` is the circle convolution of the scale profile. -/
lemma errorOne_cltRegLine_eq {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (P : Parameters) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun x => (f x : ℂ)) 2 (arclength (loopMasterLength ℓ))}) (x : ℝ) :
    cltRegLine hρ P N ℓ ξ x = circleMollify ρ (loopMasterLength ℓ).val (cltDelta P N ℓ)
      (fun t : ℝ => ξ.val (t : Circle (loopMasterLength ℓ))) x :=
  cltRegCircle_coe hρ (loopMasterLength ℓ) (cltDelta_pos P N ℓ) ξ x

/-- At length one, the periodization of `p` and `p` have the same circle convolution.
The two integrands agree off the single point `1/2` of the central cell. -/
lemma errorOne_circleMollify_periodized_eq_unit (p : Profile) (L : Length) (hL : L.val = 1)
    (ρ : ℝ → ℝ) (h x : ℝ) :
    circleMollify ρ L.val h (fun t : ℝ => periodizedProfile p L (t : Circle L)) x =
      circleMollify ρ 1 h (fun t : ℝ => p.val (t : UnitAddCircle)) x := by
  obtain ⟨v, hv⟩ := L
  change v = 1 at hL
  subst hL
  unfold circleMollify
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(ae_iff.2 (by simp) : ∀ᵐ y : ℝ, y ≠ 1 / 2)] with y hyend hy
  rw [Set.uIoc_of_le (by norm_num)] at hy
  have hcell : -(1 / 2 : ℝ) < y ∧ y ≤ 1 / 2 := hy
  have hyabs : |y| < 1 / 2 := abs_lt.mpr ⟨hcell.1, lt_of_le_of_ne hcell.2 hyend⟩
  have hper : periodizedProfile p ⟨1, hv⟩ (y : Circle ⟨1, hv⟩) = p.val (y : UnitAddCircle) := by
    rw [regMicroKernel_periodized_coe_eq p ⟨1, hv⟩ le_rfl
      ⟨by show -(1 : ℝ) / 2 ≤ y; linarith [hcell.1],
        by show y < (1 : ℝ) / 2; exact lt_of_le_of_ne hcell.2 hyend⟩]
    unfold zeroExtension
    simp only [hyabs, ↓reduceIte]
  simp only [hper]

/-- Smoothing multiplies the transport coefficients by the mollifier multiplier. -/
lemma errorOne_transportCoeffs_smooth (P : Parameters) (L : Length) {ρ : ℝ → ℝ}
    (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (ξ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (g : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (hg : ∀ x : ℝ, g.val (x : Circle L) =
      circleMollify ρ L.val h (fun t : ℝ => ξ.val (t : Circle L)) x) (k : ℤ) :
    transportCoeffs P L g k =
      transportCoeffs P L ξ k * (mollifierFT ρ (h * k / L.val) : ℂ) := by
  obtain ⟨gξ, _, _, hgv, hgf⟩ := Internal.exists_circleMollify_L2 hρ L hh ξ
  have heq : g = gξ := by
    apply Subtype.ext
    funext y
    induction y using QuotientAddGroup.induction_on with
    | H x => rw [hg x, hgv x]
  rw [heq]
  by_cases hk : k = 0
  · simp only [transportCoeffs, hk, ite_true, zero_mul]
  · simp only [transportCoeffs, hk, ite_false]
    rw [hgf k]
    ring

/-- A continuous transport with the coefficients of the smoothed transport is the smoothed
transport, pointwise on the line. -/
lemma errorOne_eq_circleMollify_of_coeff (P : Parameters) (L : Length) {ρ : ℝ → ℝ}
    (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (ξ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (ψ0 : Circle L → ℝ) (hψ0m : MemLp (fun x => (ψ0 x : ℂ)) 2 (arclength L))
    (hψ0 : ∀ k : ℤ, coeff L ⟨(fun x => (ψ0 x : ℂ)), complexL2Integrable L _ hψ0m⟩ k =
      transportCoeffs P L ξ k)
    (g : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (hg : ∀ x : ℝ, g.val (x : Circle L) =
      circleMollify ρ L.val h (fun t : ℝ => ξ.val (t : Circle L)) x)
    (ψc : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (hψc : Continuous ψc.val)
    (htr : ∀ k : ℤ, coeff L ⟨(fun x => (ψc.val x : ℂ)), complexL2Integrable L _ ψc.property⟩ k =
      transportCoeffs P L g k) (x : ℝ) :
    ψc.val (x : Circle L) = circleMollify ρ L.val h (fun t : ℝ => ψ0 (t : Circle L)) x := by
  obtain ⟨m, hmc, _, hmv, hmf⟩ :=
    Internal.exists_circleMollify_L2 hρ L hh ⟨ψ0, hψ0m⟩
  have hcoef : ∀ k : ℤ,
      coeff L ⟨(fun y => (ψc.val y : ℂ)), complexL2Integrable L _ ψc.property⟩ k =
        coeff L ⟨(fun y => (m.val y : ℂ)), complexL2Integrable L _ m.property⟩ k := by
    intro k
    rw [htr k, errorOne_transportCoeffs_smooth P L hρ hh ξ g hg k, hmf k, hψ0 k]
  have hcm : ψc.val = m.val :=
    continuous_eq_of_coeff_eq hψc hmc ψc.property m.property hcoef
  rw [hcm]
  exact hmv x

/-- Transport coefficients depend only on the Fourier coefficients. -/
lemma errorOne_transportCoeffs_congr (P : Parameters) (L : Length)
    (f g : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (h : ∀ k : ℤ, coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k =
      coeff L ⟨(fun x => (g.val x : ℂ)), complexL2Integrable L _ g.property⟩ k) (k : ℤ) :
    transportCoeffs P L f k = transportCoeffs P L g k := by
  unfold transportCoeffs
  rw [h k]

/-- The power bound for the near-mark envelope: `1 + Σ max(uⱼ, δ)^e ≤ (1 + n) δ^e` for a
nonpositive exponent `e` and `0 < δ ≤ 1`. -/
lemma errorOne_sum_rpow_le (n : ℕ) (δ e : ℝ) (u : Fin n → ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (he : e ≤ 0) :
    1 + ∑ j, max (u j) δ ^ e ≤ (1 + n) * δ ^ e := by
  have hterm : ∀ j, max (u j) δ ^ e ≤ δ ^ e := fun j =>
    Real.rpow_le_rpow_of_nonpos hδ (le_max_right _ _) he
  have hsum : ∑ j, max (u j) δ ^ e ≤ n * δ ^ e := by
    calc ∑ j, max (u j) δ ^ e ≤ ∑ _j : Fin n, δ ^ e := Finset.sum_le_sum fun j _ => hterm j
      _ = n * δ ^ e := by simp
  have h1 : 1 ≤ δ ^ e := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 he
  nlinarith

/-- The circle distance of `x` to `Lℤ` is the absolute value of its central representative. -/
lemma errorOne_circDist_centralRep {L : Length} (x : ℝ) :
    circDist L.val x = |centralRep L (x : Circle L)| := by
  obtain ⟨n, hn⟩ := centralRep_coe_eq L x
  have hc := centralRep_mem_Ico L (x : Circle L)
  set c := centralRep L (x : Circle L) with hcdef
  have hcabs : |c| ≤ L.val / 2 := by
    rw [abs_le]
    constructor
    · linarith [hc.1]
    · linarith [hc.2]
  have hx' : x = c + (n : ℝ) * L.val := by rw [hn]; ring
  calc circDist L.val x = circDist L.val (c + (n : ℝ) * L.val) := by rw [← hx']
    _ = circDist L.val c := circDist_add_int_mul L.property c n
    _ = |c| := circDist_eq_abs L.property hcabs

/-- A periodic profile vanishing on the far region of its period vanishes, with its first and
second derivatives, on a neighborhood of every point at distance larger than `c` from the
lattice. -/
lemma errorOne_zero_near_of_far {L : ℝ} (hL : 0 < L) {R : ℝ → ℝ}
    (hper : Function.Periodic R L) {c : ℝ}
    (hc : ∀ z : ℝ, c < |z| → |z| ≤ L / 2 → R z = 0) (x : ℝ) (hx : c < circDist L x) :
    deriv R x = 0 ∧ deriv (deriv R) x = 0 := by
  have hzero : ∀ y : ℝ, c < circDist L y → R y = 0 := by
    intro y hy
    have hz : |y - L * ((round (y / L) : ℤ) : ℝ)| = circDist L y := rfl
    have hzl : |y - L * ((round (y / L) : ℤ) : ℝ)| ≤ L / 2 := by
      have h1 := abs_sub_round (y / L)
      have h2 : |y - L * ((round (y / L) : ℤ) : ℝ)| =
          L * |y / L - ((round (y / L) : ℤ) : ℝ)| := by
        rw [show y - L * ((round (y / L) : ℤ) : ℝ) =
          L * (y / L - ((round (y / L) : ℤ) : ℝ)) by field_simp, abs_mul, abs_of_pos hL]
      rw [h2]
      nlinarith [h1, hL]
    have h3 : R (y - ((round (y / L) : ℤ) : ℝ) * L) = R y :=
      hper.sub_int_mul_eq (round (y / L))
    have h4 : y - ((round (y / L) : ℤ) : ℝ) * L = y - L * ((round (y / L) : ℤ) : ℝ) := by ring
    rw [← h3, h4, hc _ (by rw [hz]; exact hy) hzl]
  have hopen : ∀ y : ℝ, c < circDist L y → ∀ᶠ z in 𝓝 y, c < circDist L z := by
    intro y hy
    rw [Metric.eventually_nhds_iff]
    refine ⟨circDist L y - c, by linarith, fun z hz => ?_⟩
    have h1 := circDist_le_add_abs hL y z
    rw [Real.dist_eq, abs_sub_comm] at hz
    have h2 : |y - z| = |z - y| := abs_sub_comm y z
    linarith
  have hR : ∀ y : ℝ, c < circDist L y → R =ᶠ[𝓝 y] fun _ => (0 : ℝ) := fun y hy =>
    (hopen y hy).mono fun z hz => hzero z hz
  refine ⟨?_, ?_⟩
  · rw [(hR x hx).deriv_eq]
    exact deriv_const _ _
  · have hd : deriv R =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hopen x hx] with y hy
      rw [(hR y hy).deriv_eq]
      exact deriv_const _ _
    rw [hd.deriv_eq]
    exact deriv_const _ _

end Internal

end Riesz1
