/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockMoments
public import Riesz1.Variance.APrioriRotationJoint
public import Riesz1.Variance.APrioriRotationOriginMajorant

/-!
# The `L²` bound of the joint exterior sum

The claim in the proof of Lemma 5.2 that the joint exterior sum
`∑_{i ∉ I} f((N y_i - D)/K)` has `L²` norm at most a constant under the joint law of `(D, y)`.
The joint law is `1_{0<D<w(y)} dD dμ*(y)` with `w(y) = N y_1` (`sizeBiasWeight`), so the squared
`L²` norm is `∫ dμ*(y) ∫_{0<D<w(y)} S(D, y)² dD`, where `S` is `jointExteriorSum`.

The pointwise bound of `APrioriRotationOriginMajorant` gives `|S(D, y)| ≤ Q(X)` on the arc
`0 < D < w`, with `Q = originMajorant`. Then `w Q² ≤ (w² + Q⁴)/2` integrates to the bound, with
the second moment of the gap `w` (`blockLength_moments`) and the uniform `L⁴` bound of `Q`
(`originMajorant_L4`).

The main results are `jointExteriorSum_lintegral_sq_le` (the joint law form, uniform in `N`, `ℓ`
and `f`) and `lintegral_jointExteriorSum_sq_gibbs` (the same integral on the Gibbs measure).
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace Riesz1

/-- An arc integral of a squared function bounded by `Q` on `(0, w)` is at most `w Q²`. -/
theorem lintegral_arc_sq_le {g : ℝ → ℝ} {w Q : ℝ} (hw : 0 ≤ w)
    (hg : ∀ D ∈ Ioo (0 : ℝ) w, |g D| ≤ Q) :
    ∫⁻ D in Ioo (0 : ℝ) w, ENNReal.ofReal (g D ^ 2) ≤ ENNReal.ofReal (w * Q ^ 2) := by
  calc ∫⁻ D in Ioo (0 : ℝ) w, ENNReal.ofReal (g D ^ 2)
      ≤ ∫⁻ D in Ioo (0 : ℝ) w, ENNReal.ofReal (Q ^ 2) := by
        refine setLIntegral_mono' measurableSet_Ioo fun D hD => ENNReal.ofReal_le_ofReal ?_
        have h := abs_le.1 (hg D hD)
        exact sq_le_sq' h.1 h.2
    _ = ENNReal.ofReal (w * Q ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_mul hw, mul_comm]

/-- The arithmetic--geometric mean inequality for the pair `(w, Q²)`, in `ℝ≥0∞`:
`w Q² ≤ w²/2 + Q⁴/2`. -/
theorem ofReal_mul_sq_le_moments (w Q : ℝ) :
    ENNReal.ofReal (w * Q ^ 2) ≤
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal (w ^ 2) + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (|Q| ^ 4) := by
  have habs : |Q| ^ 4 = (Q ^ 2) ^ 2 := by
    rw [show |Q| ^ 4 = (|Q| ^ 2) ^ 2 by ring, sq_abs]
  have hAM : w * Q ^ 2 ≤ 1 / 2 * w ^ 2 + 1 / 2 * |Q| ^ 4 := by
    rw [habs]
    nlinarith [sq_nonneg (w - Q ^ 2)]
  calc ENNReal.ofReal (w * Q ^ 2) ≤ ENNReal.ofReal (1 / 2 * w ^ 2 + 1 / 2 * |Q| ^ 4) :=
        ENNReal.ofReal_le_ofReal hAM
    _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (w ^ 2) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (|Q| ^ 4) := by
        rw [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1 / 2 * w ^ 2)
          (by positivity : (0 : ℝ) ≤ 1 / 2 * |Q| ^ 4),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The joint exterior sum is continuous in the origin offset and the anchored positions. -/
theorem continuous_jointExteriorSum {N : ℕ+} (ℓ γ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × (Fin (N : ℕ) → ℝ) => jointExteriorSum N ℓ γ f p.1 p.2) := by
  unfold jointExteriorSum
  refine continuous_finsetSum _ fun (i : Fin (N : ℕ)) _ => ?_
  have hcoord : Continuous (fun p : ℝ × (Fin (N : ℕ) → ℝ) => p.2 i) :=
    (continuous_apply i).comp continuous_snd
  have harg : Continuous (fun p : ℝ × (Fin (N : ℕ) → ℝ) =>
      ((((N : ℕ) : ℝ) * p.2 i - p.1) / (((N : ℕ) : ℝ) * ℓ))) :=
    ((continuous_const.mul hcoord).sub continuous_fst).div_const _
  exact hf.comp harg

/-- The inner integral of a squared function on the arc `(0, N y_1)` is measurable in the anchored
positions, for a jointly measurable function `g` of the origin offset and the positions. -/
theorem measurable_lintegral_arc_sq {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    (g : ℝ → (Fin (N : ℕ) → ℝ) → ℝ)
    (hg : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) => ENNReal.ofReal (g p.1 p.2 ^ 2))) :
    Measurable (fun y : Fin (N : ℕ) → ℝ => ∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
      ENNReal.ofReal (g D y ^ 2)) := by
  have heq : ∀ y : Fin (N : ℕ) → ℝ, ∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
      ENNReal.ofReal (g D y ^ 2) =
      ∫⁻ D in Ioc (0 : ℝ) (sizeBiasWeight N hN y), ENNReal.ofReal (g D y ^ 2) := fun y => by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  simp_rw [heq]
  exact measurable_lintegral_Ioc_param (fun y => sizeBiasWeight N hN y)
    (measurable_sizeBiasWeight N hN) (fun q => ENNReal.ofReal (g q.2 q.1 ^ 2))
    (hg.comp measurable_swap)

/-- The inner integral of the joint law is measurable in the anchored positions. -/
theorem measurable_joint_inner {N : ℕ+} (hN : 2 ≤ (N : ℕ)) (ℓ γ : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    Measurable (fun y : Fin (N : ℕ) → ℝ => ∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
      ENNReal.ofReal (jointExteriorSum N ℓ γ f D y ^ 2)) :=
  measurable_lintegral_arc_sq hN (fun D y => jointExteriorSum N ℓ γ f D y)
    (ENNReal.measurable_ofReal.comp
      ((continuous_jointExteriorSum ℓ γ hf).measurable.pow_const 2))

/-- **Joint law form on the Gibbs measure.** The squared joint exterior sum, evaluated at the
origin offset and the origin positions of the configuration, integrates against the Gibbs
measure to the joint-law integral of `jointExteriorSum ^ 2`. This is the joint law
`joint_law_rotAnchoredLaw` for `φ = ofReal (S ^ 2)`. -/
theorem lintegral_jointExteriorSum_sq_gibbs (P : Parameters) {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    (ℓ γ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫⁻ X, ENNReal.ofReal (jointExteriorSum N ℓ γ f (originD X) (originPos X) ^ 2)
        ∂(gibbsMeasure P N) =
      ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
          ENNReal.ofReal (jointExteriorSum N ℓ γ f D y ^ 2)) ∂(rotAnchoredLaw P N) := by
  have hφ : Measurable (fun p : ℝ × (Fin (N : ℕ) → ℝ) =>
      ENNReal.ofReal (jointExteriorSum N ℓ γ f p.1 p.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((continuous_jointExteriorSum ℓ γ hf).measurable.pow_const 2)
  exact joint_law_rotAnchoredLaw P N hN
    (fun D y => ENNReal.ofReal (jointExteriorSum N ℓ γ f D y ^ 2)) hφ

/-- The second moment of the gap at the origin label, uniformly in `N`: the lintegral of
`ofReal (gap X 0 ^ 2)` is at most a constant `Cg` depending only on the model. -/
theorem exists_lintegral_gap_sq_le (P : Parameters) (hPL : External.PrekopaLeindler) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∫⁻ X : Configuration N, ENNReal.ofReal (gap X 0 ^ 2) ∂(gibbsMeasure P N) ≤
        ENNReal.ofReal Cg := by
  obtain ⟨Cg, hCg, hgm⟩ := blockLength_moments (2 : ℝ) (by norm_num)
  refine ⟨Cg, hCg, fun N hN => ?_⟩
  have h := (hgm hPL P N hN 0 1 one_pos).2
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
  refine (lintegral_congr fun X => ?_).trans_le h
  rw [Real.rpow_two]
  congr 1

/-- **`L²` bound of the joint exterior sum with explicit threshold** (part of the proof of
Lemma 5.2). Let `P` be the model parameters with exponent `s = P.val.2`, let
`λ ≥ 0` and `ε > 0`. For every `γ ≥ (2 - s)/(1 - s)`, there is `C ≥ 0` with the following property.
For every `N ≥ 2`, `0 < ℓ ≤ 1` with `K = Nℓ ≥ 1` and every `C¹` function `f` of period `1/ℓ` with
`f(1/(2ℓ)) = 0` satisfying the derivative bound of the kernel, the joint exterior sum has second
moment at most `C²` under the joint law of `(D, y)`. That is, its `L²` norm under the joint law is
at most `C`. The joint law is `∫ dμ*(y) ∫_{0<D<w(y)} dD` with `w(y) = N y_1`. The constant `C`
does not depend on `N`, `ℓ` or `f`. -/
theorem jointExteriorSum_lintegral_sq_le_of_ge (P : Parameters) (hPL : External.PrekopaLeindler)
    {lam ε : ℝ} (hlam : 0 ≤ lam) (hε : 0 < ε) (γ : ℝ) (hγ : (2 - P.val.2) / (1 - P.val.2) ≤ γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ+) (ℓ : ℝ) (hN : 2 ≤ (N : ℕ)), 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) → f (1 / ℓ / 2) = 0 →
        (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
          |deriv f u| ≤ (if |u| ≤ 2 then 1 / (max |u| (((N : ℕ) : ℝ) * ℓ)⁻¹) ^ (1 + lam) else 0) +
            (if 2 ≤ |u| then 1 / |u| ^ (3 - P.val.2) else 0)) →
        ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
            ENNReal.ofReal (jointExteriorSum N ℓ γ f D y ^ 2)) ∂(rotAnchoredLaw P N) ≤
          ENNReal.ofReal (C ^ 2) := by
  have hs0 : 0 < P.val.2 := P.property.2.1
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hs2 : P.val.2 < 2 := by linarith
  have hγ0 : 1 < (2 - P.val.2) / (1 - P.val.2) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  have hγ1 : 1 < γ := lt_of_lt_of_le hγ0 hγ
  have hγ0' : 0 ≤ γ := by linarith
  obtain ⟨M, hM0, hL4⟩ := originMajorant_L4 P hPL hlam hε hγ
  obtain ⟨Cg, hCg, hG2⟩ := exists_lintegral_gap_sq_le P hPL
  have hA0 : 0 ≤ (lam + ε + γ) / (γ - 1) + 2 := by
    have : 0 ≤ (lam + ε + γ) / (γ - 1) := div_nonneg (by linarith) (by linarith)
    linarith
  set A : ℝ := (lam + ε + γ) / (γ - 1) + 2 with hA_def
  have hCnn : 0 ≤ (Cg + M ^ 4) / 2 := div_nonneg (by have := pow_nonneg hM0 4; linarith)
    (by norm_num)
  refine ⟨Real.sqrt ((Cg + M ^ 4) / 2), Real.sqrt_nonneg _, fun N ℓ hN hℓ0 hℓ1 hK f hf hper
    hzero hder => ?_⟩
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hder' : ∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
      |deriv f u| ≤ cutoffMajorant P.val.2 lam (((N : ℕ) : ℝ) * ℓ) |u| :=
    fun u hu => hder u hu
  have hfc : Continuous f := hf.continuous
  -- The majorant at `D` is `Q X`, and its coefficients are nonnegative.
  have hα0 : 0 ≤ originAlpha P.val.2 lam ε ((lam + ε + γ) / (γ - 1) + 2)
      (((N : ℕ) : ℝ) * ℓ) := by
    unfold originAlpha
    exact mul_nonneg (mul_nonneg (kernelConst_nonneg hs2 hlam hε)
      (Real.rpow_nonneg hK0.le _)) (Real.rpow_nonneg (by linarith) _)
  have hβ0 : 0 ≤ originBeta P.val.2 (((N : ℕ) : ℝ) * ℓ) := by
    unfold originBeta
    exact div_nonneg (Real.rpow_nonneg hK0.le _) (by linarith)
  have hgap : ∀ X : Configuration N, gap X 0 = blockLength X 0 1 := fun X => by
    simp [gap, blockLength]
  have hgapm : Measurable (fun X : Configuration N => gap X 0) := by
    simp only [hgap]
    exact measurable_blockLength 0 1
  have hmeasG : Measurable (fun X : Configuration N => ENNReal.ofReal (gap X 0 ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hgapm.pow_const 2)
  have hQabs : Measurable (fun X : Configuration N =>
      |originMajorant N ℓ γ P.val.2 lam ε ((lam + ε + γ) / (γ - 1) + 2) X|) :=
    continuous_abs.measurable.comp
      (measurable_originMajorant N ℓ γ P.val.2 lam ε ((lam + ε + γ) / (γ - 1) + 2))
  have hmeasQ : Measurable (fun X : Configuration N =>
      ENNReal.ofReal (|originMajorant N ℓ γ P.val.2 lam ε ((lam + ε + γ) / (γ - 1) + 2) X| ^ 4)) :=
    ENNReal.measurable_ofReal.comp (hQabs.pow_const 4)
  -- The arc bound at each configuration, and the pointwise bound by the moments.
  have harc : ∀ X : Configuration N,
      (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN (rotAnchorVec N X)),
        ENNReal.ofReal (jointExteriorSum N ℓ γ f D (rotAnchorVec N X) ^ 2)) ≤
      ENNReal.ofReal (gap X 0 * originMajorant N ℓ γ P.val.2 lam ε A X ^ 2) := by
    intro X
    rw [sizeBiasWeight_anchorVec N hN X]
    exact lintegral_arc_sq_le (gap_pos X 0).le fun D hD =>
      abs_jointExteriorSum_le_originMajorant X hℓ0 hs2 hK hγ0' hlam hε hA0 hf hper hzero hder'
        hD.1 hD.2
  have hpt : ∀ X : Configuration N,
      (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN (rotAnchorVec N X)),
        ENNReal.ofReal (jointExteriorSum N ℓ γ f D (rotAnchorVec N X) ^ 2)) ≤
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X 0 ^ 2) +
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (|originMajorant N ℓ γ P.val.2 lam ε A X| ^ 4) :=
    fun X => (harc X).trans (ofReal_mul_sq_le_moments _ _)
  -- Integrate over the Gibbs measure and combine the two moments.
  have hint_bound : ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
      ENNReal.ofReal (jointExteriorSum N ℓ γ f D y ^ 2)) ∂(rotAnchoredLaw P N) ≤
      ENNReal.ofReal ((Cg + M ^ 4) / 2) := by
    unfold rotAnchoredLaw
    rw [lintegral_map (measurable_joint_inner hN ℓ γ hfc) (measurable_rotAnchorVec N)]
    have hm1 : Measurable (fun X : Configuration N =>
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X 0 ^ 2)) :=
      hmeasG.const_mul _
    calc ∫⁻ X, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN (rotAnchorVec N X)),
          ENNReal.ofReal (jointExteriorSum N ℓ γ f D (rotAnchorVec N X) ^ 2)) ∂(gibbsMeasure P N)
        ≤ ∫⁻ X, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (gap X 0 ^ 2) +
            ENNReal.ofReal (1 / 2) * ENNReal.ofReal
              (|originMajorant N ℓ γ P.val.2 lam ε A X| ^ 4)) ∂(gibbsMeasure P N) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (1 / 2) * ∫⁻ X, ENNReal.ofReal (gap X 0 ^ 2) ∂(gibbsMeasure P N) +
            ENNReal.ofReal (1 / 2) * ∫⁻ X, ENNReal.ofReal
              (|originMajorant N ℓ γ P.val.2 lam ε A X| ^ 4) ∂(gibbsMeasure P N) := by
          rw [lintegral_add_left hm1, lintegral_const_mul _ hmeasG, lintegral_const_mul _ hmeasQ]
      _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal Cg + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (M ^ 4) :=
          add_le_add (mul_le_mul_of_nonneg_left (hG2 N hN) zero_le) (mul_le_mul_of_nonneg_left (hL4 N ℓ hN hℓ0 hℓ1 hK) zero_le)
      _ = ENNReal.ofReal ((Cg + M ^ 4) / 2) := by
          have h1 : (0 : ℝ) ≤ 1 / 2 * Cg := mul_nonneg (by norm_num) hCg.le
          have h2 : (0 : ℝ) ≤ 1 / 2 * M ^ 4 := mul_nonneg (by norm_num) (pow_nonneg hM0 4)
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.ofReal_add h1 h2]
          congr 1
          ring
  rw [Real.sq_sqrt hCnn]
  exact hint_bound

/-- **`L²` bound of the joint exterior sum** (part of the proof of Lemma 5.2). Let `P` be the
model parameters with exponent `s = P.val.2`, let `λ ≥ 0` and `ε > 0`. There is `γ₀ > 1`
depending only on `s` such that, for every `γ ≥ γ₀`, there is `C ≥ 0` with the following property.
For every `N ≥ 2`, `0 < ℓ ≤ 1` with `K = Nℓ ≥ 1` and every `C¹` function `f` of period `1/ℓ` with
`f(1/(2ℓ)) = 0` satisfying the derivative bound of the kernel, the joint exterior sum has second
moment at most `C²` under the joint law of `(D, y)`. That is, its `L²` norm under the joint law is
at most `C`. The joint law is `∫ dμ*(y) ∫_{0<D<w(y)} dD` with `w(y) = N y_1`. The constant `C`
does not depend on `N`, `ℓ` or `f`. -/
theorem jointExteriorSum_lintegral_sq_le (P : Parameters) (hPL : External.PrekopaLeindler)
    {lam ε : ℝ} (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ γ₀ : ℝ, 1 < γ₀ ∧ ∀ γ : ℝ, γ₀ ≤ γ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ+) (ℓ : ℝ) (hN : 2 ≤ (N : ℕ)), 0 < ℓ → ℓ ≤ 1 → 1 ≤ ((N : ℕ) : ℝ) * ℓ →
        ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) → f (1 / ℓ / 2) = 0 →
        (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
          |deriv f u| ≤ (if |u| ≤ 2 then 1 / (max |u| (((N : ℕ) : ℝ) * ℓ)⁻¹) ^ (1 + lam) else 0) +
            (if 2 ≤ |u| then 1 / |u| ^ (3 - P.val.2) else 0)) →
        ∫⁻ y, (∫⁻ D in Ioo (0 : ℝ) (sizeBiasWeight N hN y),
            ENNReal.ofReal (jointExteriorSum N ℓ γ f D y ^ 2)) ∂(rotAnchoredLaw P N) ≤
          ENNReal.ofReal (C ^ 2) := by
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hγ0 : 1 < (2 - P.val.2) / (1 - P.val.2) := by
    rw [lt_div_iff₀ (by linarith)]
    linarith
  exact ⟨(2 - P.val.2) / (1 - P.val.2), hγ0,
    fun γ hγ => jointExteriorSum_lintegral_sq_le_of_ge P hPL hlam hε γ hγ⟩

end Riesz1

end

