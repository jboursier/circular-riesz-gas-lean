/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ReductionScalesMean
public import Riesz1.Rigidity.CurvatureTails
public import Riesz1.Rigidity.BlockMoments

/-!
# The block functional of the multiscale increment: moments and total variation

This is part of Lemma 4.4, the moment and total-variation assertions. The increment
`G_m` is the linear functional `y ↦ ⟪w, y⟫` of the block coordinates `y = x_{i0 + r} - ⌊x_{i0}⌋`,
where `w` has entries `scaleCoef`. This file

* defines this functional on `HsEuclidean (L + 1)` (`scaleFun`), shows that it represents `G_m` on
  the lifted block (`scaleFun_liftedBlock`), is invariant under real translation of the block
  (`scaleFun_translate`), and has derivative of norm `‖w‖ ≤ 2 N k^{-m/(2q)}` (`norm_fderiv_scaleFun`).
* proves the centered moment bound for `G_m` under its constrained law
  (`scale_centered_moment`), with the constant `2^{s+3}/(β a_s)`.
* proves the total-variation bound `TV(P, Q_m) ≤ 3 exp(-(log 2 / 4) k^{ε/(s+2)})`
  (`scale_totalVariation_le`), from the forcing comparison and the exponential block tail.

The Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler` are taken as explicit hypotheses.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

/-! ### The block functional -/

/-- The coefficient vector of `G_m` as an element of the block space `HsEuclidean (L + 1)`: its
`r`-th entry is `scaleCoef N i k q m r`. -/
noncomputable def scaleVec (N : ℕ+) (i : ℤ) (k q m : ℕ) (L : ℕ) : HsEuclidean (Nat.succPNat L) :=
  WithLp.toLp 2 (fun r : Fin (Nat.succPNat L : ℕ) => scaleCoef N i k q m (r : ℕ))

/-- The linear block functional `y ↦ ⟪w, y⟫` whose coefficients are those of `G_m`. -/
noncomputable def scaleFun (N : ℕ+) (i : ℤ) (k q m : ℕ) (L : ℕ) (y : HsEuclidean (Nat.succPNat L)) :
    ℝ :=
  inner ℝ (scaleVec N i k q m L) y

/-- The block functional is the continuous linear map `⟪w, ·⟫`. -/
theorem scaleFun_eq_innerSL (N : ℕ+) (i : ℤ) (k q m : ℕ) (L : ℕ) :
    scaleFun N i k q m L = ⇑(innerSL ℝ (scaleVec N i k q m L)) := by
  funext y
  rw [innerSL_apply_apply]
  rfl

/-- The block functional in coordinates: `∑_{r ≤ L} coef_r y_r`. -/
theorem scaleFun_apply (N : ℕ+) (i : ℤ) (k q m : ℕ) (L : ℕ) (y : HsEuclidean (Nat.succPNat L)) :
    scaleFun N i k q m L y = ∑ r : Fin (Nat.succPNat L : ℕ), scaleCoef N i k q m (r : ℕ) * y r := by
  unfold scaleFun scaleVec
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- The coefficients sum to zero, also in the `Fin` indexing of the block space. -/
theorem sum_scaleCoef_fin (N : ℕ+) (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) :
    ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
      scaleCoef N i k q m (r : ℕ) = 0 := by
  rw [Nat.succPNat_coe, Fin.sum_univ_eq_sum_range (fun r => scaleCoef N i k q m r)]
  exact sum_scaleCoef i hk hkN hm

/-- The block functional represents the increment `G_m` on the lifted block. -/
theorem scaleFun_liftedBlock (N : ℕ+) (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) (hL : cyclicRepSpan N (scaleIndex k q (m + 1)) < (N : ℕ)) (X : Configuration N) :
    scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)))
        (WithLp.toLp 2 (liftedBlock (cyclicRepStart N (scaleIndex k q (m + 1)) i) hL X).val) =
      scaleIncrement i k q m X := by
  have hsum := sum_scaleCoef_fin N i hk hkN hm
  rw [scaleFun_apply, scaleIncrement_eq_sum_coef i hk hkN hm X]
  have e : ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
      scaleCoef N i k q m (r : ℕ) *
        (WithLp.toLp 2 (liftedBlock (cyclicRepStart N (scaleIndex k q (m + 1)) i) hL X).val : HsEuclidean _) r =
      ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
        scaleCoef N i k q m (r : ℕ) *
          cyclicLift X (cyclicRepStart N (scaleIndex k q (m + 1)) i + (r : ℕ)) -
        ⌊cyclicLift X (cyclicRepStart N (scaleIndex k q (m + 1)) i)⌋ *
          ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
            scaleCoef N i k q m (r : ℕ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    show scaleCoef N i k q m (r : ℕ) *
        (cyclicLift X (cyclicRepStart N (scaleIndex k q (m + 1)) i + (r : ℕ)) -
          ⌊cyclicLift X (cyclicRepStart N (scaleIndex k q (m + 1)) i)⌋) = _
    ring
  rw [e, hsum, mul_zero, sub_zero]
  rw [Nat.succPNat_coe]
  exact Fin.sum_univ_eq_sum_range
    (fun r : ℕ => scaleCoef N i k q m r *
      cyclicLift X (cyclicRepStart N (scaleIndex k q (m + 1)) i + (r : ℤ))) _

/-- The block functional is invariant under a common real translation of the block coordinates. -/
theorem scaleFun_translate (N : ℕ+) (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) (x : HsEuclidean (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1)))))
    (t : ℝ) :
    scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1))) (hsTranslate t x) =
      scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1))) x := by
  have hsum := sum_scaleCoef_fin N i hk hkN hm
  rw [scaleFun_apply, scaleFun_apply]
  have e : ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
      scaleCoef N i k q m (r : ℕ) * hsTranslate t x r =
      ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
        scaleCoef N i k q m (r : ℕ) * x r +
      (∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
        scaleCoef N i k q m (r : ℕ)) * t := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hsTranslate_apply]
    ring
  rw [e, hsum, zero_mul, add_zero]

/-- The block functional is differentiable with derivative the continuous linear map `⟪w, ·⟫`. -/
theorem fderiv_scaleFun (N : ℕ+) (i : ℤ) (k q m L : ℕ)
    (x : HsEuclidean (Nat.succPNat L)) :
    fderiv ℝ (scaleFun N i k q m L) x = innerSL ℝ (scaleVec N i k q m L) := by
  rw [scaleFun_eq_innerSL]
  exact ContinuousLinearMap.fderiv _

/-- The squared norm of the coefficient vector is the sum of the squared coefficients. -/
theorem sq_norm_scaleVec (N : ℕ+) (i : ℤ) (k q m : ℕ) (L : ℕ) :
    ‖scaleVec N i k q m L‖ ^ 2 =
      ∑ r ∈ range (L + 1), scaleCoef N i k q m r ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold scaleVec
  simp only [Real.norm_eq_abs, sq_abs, Nat.succPNat_coe]
  exact Fin.sum_univ_eq_sum_range (fun r : ℕ => scaleCoef N i k q m r ^ 2) (L + 1)

/-- The norm of the derivative is bounded by the norm of the coefficient vector. -/
theorem norm_innerSL_le {M : ℕ+} (w : HsEuclidean M) : ‖innerSL ℝ w‖ ≤ ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
  rw [innerSL_apply_apply, Real.norm_eq_abs]
  exact abs_real_inner_le_norm w y

/-- The squared norm of the coefficient vector of `G_m` is at most `4 N² k^{-m/q}`. -/
theorem sq_norm_scaleVec_le {N : ℕ+} (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ))
    (hm : m < q) :
    ‖scaleVec N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)))‖ ^ 2 ≤
      4 * ((N : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ (-((m : ℝ) / q)) := by
  rw [sq_norm_scaleVec]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpow : (k : ℝ) ^ ((m : ℝ) / q) ≤
      ((cyclicRep N (lowScale k q m) i).card : ℝ) :=
    rpow_le_card_lowScale hk hkN hm.le i
  have hinv : ((cyclicRep N (lowScale k q m) i).card : ℝ)⁻¹ ≤ (k : ℝ) ^ (-((m : ℝ) / q)) := by
    rw [Real.rpow_neg hk0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hk0 _) hpow
  have hN2 : (0 : ℝ) ≤ 4 * ((N : ℕ) : ℝ) ^ 2 := by positivity
  calc ∑ r ∈ range (cyclicRepSpan N (scaleIndex k q (m + 1)) + 1), scaleCoef N i k q m r ^ 2
      ≤ 4 * ((N : ℕ) : ℝ) ^ 2 * ((cyclicRep N (lowScale k q m) i).card : ℝ)⁻¹ :=
        sum_scaleCoef_sq_le i hk hkN hm
    _ ≤ 4 * ((N : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ (-((m : ℝ) / q)) :=
        mul_le_mul_of_nonneg_left hinv hN2

/-! ### The moment constant -/

/-- The arithmetic of the moment bound: the curvature bound with
`R = 2 k^{(m+1)/q + ε/(s+2)}`, `B² = 4 N² k^{-m/q}` and `L + 1 ≥ k^{(m+1)/q}` is at most
`2^{s+3} t² k^{s(m+1)/q + 1/q + ε} / (β a)`. -/
theorem scale_moment_arith (s β a ε N L1 t m q k R B2 : ℝ) (hk : 1 ≤ k) (hq : 0 < q) (hs : 0 < s)
    (hβ : 0 < β) (ha : 0 < a) (hN : 0 < N) (hL1 : k ^ ((m + 1) / q) ≤ L1)
    (hR : R = 2 * k ^ ((m + 1) / q + ε / (s + 2))) (hB2 : B2 = 4 * N ^ 2 * k ^ (-(m / q))) :
    R ^ (s + 2) * B2 * t ^ 2 / (2 * β * a * N ^ 2 * L1) ≤
      2 ^ (s + 3) / (β * a) * t ^ 2 * k ^ (s * (m + 1) / q + 1 / q + ε) := by
  subst hR hB2
  have hk0 : 0 < k := by linarith
  have hkpos : 0 < k ^ ((m + 1) / q) := Real.rpow_pos_of_pos hk0 _
  have hs2 : (0 : ℝ) < s + 2 := by linarith
  have hpow : (2 * k ^ ((m + 1) / q + ε / (s + 2))) ^ (s + 2) =
      2 ^ (s + 2) * k ^ ((m + 1) / q * (s + 2) + ε) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hk0.le _), ← Real.rpow_mul hk0.le]
    congr 2
    rw [add_mul, div_mul_cancel₀ _ hs2.ne']
  have h3 : (2 : ℝ) ^ (s + 3) = 2 ^ (s + 2) * 2 := by
    rw [show s + 3 = (s + 2) + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  have key : k ^ ((m + 1) / q * (s + 2) + ε) * k ^ (-(m / q)) / k ^ ((m + 1) / q) =
      k ^ (s * (m + 1) / q + 1 / q + ε) := by
    rw [← Real.rpow_add hk0, ← Real.rpow_sub hk0]
    congr 1
    ring
  have hlhs : (2 * k ^ ((m + 1) / q + ε / (s + 2))) ^ (s + 2) * (4 * N ^ 2 * k ^ (-(m / q))) * t ^ 2 /
      (2 * β * a * N ^ 2 * L1) =
      2 ^ (s + 3) / (β * a) * t ^ 2 *
        (k ^ ((m + 1) / q * (s + 2) + ε) * k ^ (-(m / q)) / L1) := by
    rw [hpow, h3]
    field_simp
    ring
  rw [hlhs, ← key]
  have hnum : 0 ≤ k ^ ((m + 1) / q * (s + 2) + ε) * k ^ (-(m / q)) := by positivity
  have hC : 0 ≤ 2 ^ (s + 3) / (β * a) * t ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_left _ hC
  exact div_le_div_of_nonneg_left hnum hkpos hL1

/-- The total radius identity: `R_m = 2 k^{(m+1)/q + ε/(s+2)}` with the real exponent `m + 1`. -/
theorem scaleRadius_eq (P : Parameters) (ε : ℝ) (k q m : ℕ) :
    scaleRadius P ε k q m = 2 * (k : ℝ) ^ (((m : ℝ) + 1) / q + ε / (P.val.2 + 2)) := by
  unfold scaleRadius
  congr 3
  push_cast
  ring

/-! ### The centered moment bound -/

/-- **Centered moment bound** for the increment `G_m`: under its
constrained law the centered exponential moments of `G_m` are bounded by
`2^{s+3} t² k^{s(m+1)/q + 1/q + ε} / (β a_s)`. -/
theorem scale_centered_moment (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {ε : ℝ}
    (hε : 0 ≤ ε) (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ)) (hm : m < q) (t : ℝ) :
    Integrable (fun X => Real.exp (t * (scaleIncrement i k q m X -
        ∫ Y, scaleIncrement i k q m Y ∂scaleLaw P N θ ε i k q m)))
      (scaleLaw P N θ ε i k q m) ∧
    Real.log (∫ X, Real.exp (t * (scaleIncrement i k q m X -
        ∫ Y, scaleIncrement i k q m Y ∂scaleLaw P N θ ε i k q m)) ∂scaleLaw P N θ ε i k q m) ≤
      2 ^ (P.val.2 + 3) / (P.val.1 * rigidityCurvatureConstant (parametersExponent P).val) *
        t ^ 2 * (k : ℝ) ^ (P.val.2 * ((m : ℝ) + 1) / q + 1 / q + ε) := by
  have hK : 1 ≤ scaleIndex k q (m + 1) := one_le_scaleIndex hk
  have hKk : scaleIndex k q (m + 1) ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
  have hKN : 2 * scaleIndex k q (m + 1) ≤ (N : ℕ) := by omega
  have hL : cyclicRepSpan N (scaleIndex k q (m + 1)) < (N : ℕ) := cyclicRepSpan_lt hK hKN
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hs : 0 < P.val.2 := P.property.2.1
  have hβ : 0 < P.val.1 := P.property.1
  have ha : 0 < rigidityCurvatureConstant (parametersExponent P).val :=
    rigidityCurvatureConstant_pos (parametersExponent P)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast (show 0 < (N : ℕ) by omega)
  have hR1 : 1 ≤ scaleRadius P ε k q m := by
    rw [scaleRadius_eq]
    have hexp : (0 : ℝ) ≤ ε / (P.val.2 + 2) := div_nonneg hε (by linarith)
    have hm0 : (0 : ℝ) ≤ ((m : ℝ) + 1) / q := by positivity
    have h1 : (1 : ℝ) ≤ (k : ℝ) ^ (((m : ℝ) + 1) / q + ε / (P.val.2 + 2)) :=
      Real.one_le_rpow hk1 (by linarith)
    linarith
  -- the block functional and its derivative bound
  have hAeq := fun X => scaleFun_liftedBlock N i hk hkN hm hL X
  have hdiff : DifferentiableOn ℝ (scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1))))
      (hsChamber (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))))) := by
    intro x _
    rw [scaleFun_eq_innerSL]
    exact (ContinuousLinearMap.differentiableAt _).differentiableWithinAt
  have hrot : ∀ x ∈ hsChamber (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1)))), ∀ t : ℝ,
      scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1))) (hsTranslate t x) =
        scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1))) x := by
    intro x _ t
    exact scaleFun_translate N i hk hkN hm x t
  set Bsq : ℝ := 4 * ((N : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ (-((m : ℝ) / q)) with hBsq
  have hBsq0 : 0 ≤ Bsq := by positivity
  let B : NNReal := ⟨Real.sqrt Bsq, Real.sqrt_nonneg _⟩
  have hB2 : (B : ℝ) ^ 2 = Bsq := by
    show Real.sqrt Bsq ^ 2 = Bsq
    rw [Real.sq_sqrt hBsq0]
  have hBd : ∀ x ∈ hsChamber (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1)))),
      ‖fderiv ℝ (scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)))) x‖ ≤ (B : ℝ) := by
    intro x _
    rw [fderiv_scaleFun]
    refine (norm_innerSL_le _).trans ?_
    calc ‖scaleVec N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)))‖
        = Real.sqrt (‖scaleVec N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)))‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt Bsq := Real.sqrt_le_sqrt (sq_norm_scaleVec_le i hk hkN hm)
  have hcurv := curvature_centered_concentration hBE hPL P N
    (cyclicRepStart N (scaleIndex k q (m + 1)) i) hL hθ hR1 hdiff hrot hBd
  dsimp only at hcurv
  simp only [hAeq] at hcurv
  obtain ⟨-, hmgf, -⟩ := hcurv
  -- the arithmetic of the curvature bound
  have hLcard : ((cyclicRepSpan N (scaleIndex k q (m + 1)) : ℝ) + 1) =
      ((cyclicRep N (scaleIndex k q (m + 1)) i).card : ℝ) := by
    rw [card_cyclicRep]
    push_cast
    ring
  have hlowS : lowScale k q (m + 1) = scaleIndex k q (m + 1) := by
    unfold lowScale
    simp
  have hL1 : (k : ℝ) ^ (((m : ℝ) + 1) / q) ≤ (cyclicRepSpan N (scaleIndex k q (m + 1)) : ℝ) + 1 := by
    rw [hLcard]
    have h := rpow_le_card_lowScale (N := N) (k := k) (q := q) (m := m + 1) hk hkN (by omega) i
    rw [hlowS] at h
    have e : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [e] at h
    exact h
  have hbound := scale_moment_arith (P.val.2) (P.val.1)
    (rigidityCurvatureConstant (parametersExponent P).val) ε ((N : ℕ) : ℝ)
    ((cyclicRepSpan N (scaleIndex k q (m + 1)) : ℝ) + 1) t (m : ℝ) (q : ℝ) (k : ℝ)
    (scaleRadius P ε k q m) Bsq hk1 hq0 hs hβ ha hN0 hL1 (scaleRadius_eq P ε k q m) hBsq
  unfold scaleLaw
  refine ⟨(hmgf t).1, ?_⟩
  refine (hmgf t).2.trans ?_
  rw [hB2]
  exact hbound

/-! ### Derivatives of the block functional -/

/-- The partial derivatives of the block functional along the block coordinates sum to zero: the
derivative of `G_m` along the common translation of the block vanishes, `∑_{j ∈ B_m} ∂_j G_m = 0`. -/
theorem sum_fderiv_scaleFun_single (N : ℕ+) (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k)
    (hkN : 2 * k ≤ (N : ℕ)) (hm : m < q)
    (x : HsEuclidean (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))))) :
    ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
      fderiv ℝ (scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)))) x
        (EuclideanSpace.single r 1) = 0 := by
  have hsum := sum_scaleCoef_fin N i hk hkN hm
  calc ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
        fderiv ℝ (scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)))) x
          (EuclideanSpace.single r 1)
      = ∑ r : Fin (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))) : ℕ),
          scaleCoef N i k q m (r : ℕ) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [fderiv_scaleFun, innerSL_apply_apply, EuclideanSpace.inner_single_right]
        simp [scaleVec]
    _ = 0 := hsum

/-- The squared operator norm of the derivative of the block functional is at most `4 N² k^{-m/q}`. -/
theorem sq_norm_fderiv_scaleFun_le (N : ℕ+) (i : ℤ) {k q m : ℕ} (hk : 1 ≤ k)
    (hkN : 2 * k ≤ (N : ℕ)) (hm : m < q)
    (x : HsEuclidean (Nat.succPNat (cyclicRepSpan N (scaleIndex k q (m + 1))))) :
    ‖fderiv ℝ (scaleFun N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1)))) x‖ ^ 2 ≤
      4 * ((N : ℕ) : ℝ) ^ 2 * (k : ℝ) ^ (-((m : ℝ) / q)) := by
  rw [fderiv_scaleFun]
  have h1 := norm_innerSL_le (scaleVec N i k q m (cyclicRepSpan N (scaleIndex k q (m + 1))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (sq_norm_scaleVec_le i hk hkN hm)

/-! ### The total-variation bound -/

/-- **Total-variation bound** of Lemma 4.4: the constrained law `Q_m` of the
block is within `3 exp(-(log 2 / 4) k^{ε/(s+2)})` of the Gibbs law in total variation. -/
theorem scale_totalVariation_le (hPL : External.PrekopaLeindler) (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {ε : ℝ} (_hε : 0 ≤ ε) (i : ℤ)
    {k q m : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ (N : ℕ)) (hm : m < q) :
    totalVariation (gibbsMeasure P N) (scaleLaw P N θ ε i k q m) ≤
      3 * Real.exp (-(Real.log 2 / 4) * (k : ℝ) ^ (ε / (P.val.2 + 2))) := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hK : 1 ≤ scaleIndex k q (m + 1) := one_le_scaleIndex hk
  have hKk : scaleIndex k q (m + 1) ≤ k := (scaleIndex_mem hk (by omega) (by omega)).2
  have hKN : 2 * scaleIndex k q (m + 1) ≤ (N : ℕ) := by omega
  have hL : cyclicRepSpan N (scaleIndex k q (m + 1)) < (N : ℕ) := cyclicRepSpan_lt hK hKN
  have hLpos : 0 < cyclicRepSpan N (scaleIndex k q (m + 1)) := by
    unfold cyclicRepSpan
    split_ifs <;> omega
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hR : 0 < scaleRadius P ε k q m := scaleRadius_pos P ε hk q m
  have hLK : cyclicRepSpan N (scaleIndex k q (m + 1)) ≤ 2 * scaleIndex k q (m + 1) := by
    unfold cyclicRepSpan
    split_ifs <;> omega
  have hLKr : (cyclicRepSpan N (scaleIndex k q (m + 1)) : ℝ) ≤
      2 * (scaleIndex k q (m + 1) : ℝ) := by
    exact_mod_cast hLK
  have hKr : (scaleIndex k q (m + 1) : ℝ) ≤ (k : ℝ) ^ (((m : ℝ) + 1) / q) := by
    have h := scaleIndex_le_rpow (k := k) (q := q) (m := m + 1)
    push_cast at h
    exact h
  set u : ℝ := (k : ℝ) ^ (ε / (P.val.2 + 2)) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hk0.le _
  have hRL : (cyclicRepSpan N (scaleIndex k q (m + 1)) : ℝ) * u ≤ scaleRadius P ε k q m := by
    have hsplit : scaleRadius P ε k q m = 2 * (k : ℝ) ^ (((m : ℝ) + 1) / q) * u := by
      rw [scaleRadius_eq, hu, Real.rpow_add hk0]
      ring
    rw [hsplit]
    calc (cyclicRepSpan N (scaleIndex k q (m + 1)) : ℝ) * u
        ≤ 2 * (scaleIndex k q (m + 1) : ℝ) * u := mul_le_mul_of_nonneg_right hLKr hu0
      _ ≤ 2 * (k : ℝ) ^ (((m : ℝ) + 1) / q) * u :=
          mul_le_mul_of_nonneg_right (by linarith) hu0
  have hc := forcing_event_comparison P N θ hθ (cyclicRepStart N (scaleIndex k q (m + 1)) i)
    (cyclicRepSpan N (scaleIndex k q (m + 1))) hL (scaleRadius P ε k q m) hR
  unfold scaleLaw
  refine hc.1.trans (hc.2.1.trans ?_)
  have hmono : {X : Configuration N | scaleRadius P ε k q m < blockLength X
      (cyclicRepStart N (scaleIndex k q (m + 1)) i) (cyclicRepSpan N (scaleIndex k q (m + 1)))} ⊆
      {X : Configuration N | ((cyclicRepSpan N (scaleIndex k q (m + 1)) : ℕ) : ℝ) * u <
        blockLength X (cyclicRepStart N (scaleIndex k q (m + 1)) i)
          (cyclicRepSpan N (scaleIndex k q (m + 1)))} := by
    intro X hX
    exact lt_of_le_of_lt hRL hX
  refine (measureReal_mono hmono).trans ?_
  exact blockLength_upper_tail hPL P N hN _ _ hLpos u

end Riesz1

end
