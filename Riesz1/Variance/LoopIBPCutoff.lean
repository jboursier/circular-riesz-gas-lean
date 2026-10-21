/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingGeometry
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Riesz1.HelfferSjostrand.SettingTests

/-!
# Smooth gap cutoffs on the lifted chamber

The collision cutoffs in the proof of Proposition 5.5. For
`N ≥ 2` and `h > 0`, the product of smooth steps of the `N` cyclic gaps is a smooth periodic
function on the Euclidean lift. It vanishes when some gap is at most `h`, equals one when every gap
is at least `2h`, and has first and second partial derivatives of orders `h⁻¹` and `h⁻²`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The smooth step `loopStep t = 0` for `t ≤ 1` and `loopStep t = 1` for `2 ≤ t`. -/
def loopStep (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

theorem contDiff_loopStep : ContDiff ℝ ∞ loopStep :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem loopStep_nonneg (t : ℝ) : 0 ≤ loopStep t :=
  Real.smoothTransition.nonneg _

theorem loopStep_le_one (t : ℝ) : loopStep t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem loopStep_eq_zero_of_le {t : ℝ} (ht : t ≤ 1) : loopStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem loopStep_eq_one_of_le {t : ℝ} (ht : 2 ≤ t) : loopStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- The derivative of the smooth step vanishes outside `[1, 2]`. -/
theorem deriv_loopStep_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Icc (1 : ℝ) 2) :
    deriv loopStep t = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with h1 | h2
  · have hev : loopStep =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Iio_mem_nhds h1) (fun y (hy : y < 1) => loopStep_eq_zero_of_le hy.le)
    rw [hev.deriv_eq, deriv_const]
  · have hev : loopStep =ᶠ[𝓝 t] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds h2) (fun y (hy : 2 < y) => loopStep_eq_one_of_le hy.le)
    rw [hev.deriv_eq, deriv_const]

theorem tsupport_deriv_loopStep_subset : tsupport (deriv loopStep) ⊆ Icc (1 : ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra h
  exact Function.mem_support.mp ht (deriv_loopStep_eq_zero_of_notMem h)

/-- Both the first and second derivatives of the smooth step are bounded. -/
theorem exists_bound_deriv_loopStep :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv loopStep t| ≤ C ∧ |deriv (deriv loopStep) t| ≤ C := by
  have hd1 : ContDiff ℝ ∞ (deriv loopStep) := (contDiff_infty_iff_deriv.mp contDiff_loopStep).2
  have hc1 : Continuous (deriv loopStep) := hd1.continuous
  have hc2 : Continuous (deriv (deriv loopStep)) := hd1.continuous_deriv (by simp)
  have hs1 : HasCompactSupport (deriv loopStep) :=
    HasCompactSupport.intro (K := Icc (1 : ℝ) 2) isCompact_Icc
      (fun t ht => deriv_loopStep_eq_zero_of_notMem ht)
  have hs2 : HasCompactSupport (deriv (deriv loopStep)) := by
    refine HasCompactSupport.intro (K := Icc (1 : ℝ) 2) isCompact_Icc (fun t ht => ?_)
    have hev : deriv loopStep =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_Icc.isOpen_compl).mem_nhds ht] with y hy
      exact deriv_loopStep_eq_zero_of_notMem hy
    rw [hev.deriv_eq, deriv_const]
  obtain ⟨C1, hC1⟩ := hc1.bounded_above_of_compact_support hs1
  obtain ⟨C2, hC2⟩ := hc2.bounded_above_of_compact_support hs2
  refine ⟨max C1 C2, (norm_nonneg _).trans ((hC1 0).trans (le_max_left _ _)), fun t => ⟨?_, ?_⟩⟩
  · rw [← Real.norm_eq_abs]
    exact (hC1 t).trans (le_max_left _ _)
  · rw [← Real.norm_eq_abs]
    exact (hC2 t).trans (le_max_right _ _)

/-- The index `j + 1` modulo `N`, so that the last index is followed by the first one. -/
def hsNext (N : ℕ+) (j : Fin (N : ℕ)) : Fin (N : ℕ) :=
  ⟨((j : ℕ) + 1) % (N : ℕ), Nat.mod_lt _ N.pos⟩

/-- The `j`-th gap of the Euclidean lift: `x_{j+1} - x_j`, and `x_0 + 1 - x_{N-1}` for the last
index, so that the gaps sum to one. -/
def hsUnitGap (N : ℕ+) (j : Fin (N : ℕ)) (x : HsEuclidean N) : ℝ :=
  x (hsNext N j) - x j + if (j : ℕ) + 1 = (N : ℕ) then 1 else 0

/-- The linear part of `hsUnitGap N j`. -/
def hsUnitGapLinear (N : ℕ+) (j : Fin (N : ℕ)) : HsEuclidean N →L[ℝ] ℝ :=
  EuclideanSpace.proj (𝕜 := ℝ) (hsNext N j) - EuclideanSpace.proj (𝕜 := ℝ) j

theorem hsUnitGapLinear_apply (N : ℕ+) (j : Fin (N : ℕ)) (v : HsEuclidean N) :
    hsUnitGapLinear N j v = v (hsNext N j) - v j := by
  simp [hsUnitGapLinear]

theorem hsUnitGap_eq_add_const (N : ℕ+) (j : Fin (N : ℕ)) :
    hsUnitGap N j = fun y => hsUnitGapLinear N j y + (if (j : ℕ) + 1 = (N : ℕ) then 1 else 0) := by
  funext y
  rw [hsUnitGapLinear_apply]
  unfold hsUnitGap
  ring

theorem hasFDerivAt_hsUnitGap (N : ℕ+) (j : Fin (N : ℕ)) (x : HsEuclidean N) :
    HasFDerivAt (hsUnitGap N j) (hsUnitGapLinear N j) x := by
  rw [hsUnitGap_eq_add_const]
  exact (hsUnitGapLinear N j).hasFDerivAt.add_const _

theorem contDiff_hsUnitGap (N : ℕ+) (j : Fin (N : ℕ)) : ContDiff ℝ ∞ (hsUnitGap N j) := by
  rw [hsUnitGap_eq_add_const]
  exact (hsUnitGapLinear N j).contDiff.add contDiff_const

theorem hsUnitGap_translate (N : ℕ+) (j : Fin (N : ℕ)) (t : ℝ) (x : HsEuclidean N) :
    hsUnitGap N j (hsTranslate t x) = hsUnitGap N j x := by
  unfold hsUnitGap
  simp only [hsTranslate_apply]
  ring

/-- The product of smooth steps of all `N` gaps at collision scale `h`. -/
def hsUnitGapCutoff (N : ℕ+) (h : ℝ) (x : HsEuclidean N) : ℝ :=
  ∏ j : Fin (N : ℕ), loopStep (hsUnitGap N j x / h)

theorem hsUnitGapCutoff_translate (N : ℕ+) (h : ℝ) (t : ℝ) (x : HsEuclidean N) :
    hsUnitGapCutoff N h (hsTranslate t x) = hsUnitGapCutoff N h x := by
  unfold hsUnitGapCutoff
  simp only [hsUnitGap_translate]

theorem hsUnitGapCutoff_nonneg (N : ℕ+) (h : ℝ) (x : HsEuclidean N) : 0 ≤ hsUnitGapCutoff N h x :=
  Finset.prod_nonneg fun _ _ => loopStep_nonneg _

theorem hsUnitGapCutoff_le_one (N : ℕ+) (h : ℝ) (x : HsEuclidean N) : hsUnitGapCutoff N h x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => loopStep_nonneg _) fun _ _ => loopStep_le_one _

theorem hsUnitGapCutoff_eq_zero_of_le {N : ℕ+} {h : ℝ} (hh : 0 < h) {x : HsEuclidean N}
    {j : Fin (N : ℕ)} (hj : hsUnitGap N j x ≤ h) : hsUnitGapCutoff N h x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ j)
    (loopStep_eq_zero_of_le ((div_le_one hh).mpr hj))

theorem hsUnitGapCutoff_eq_one_of_le {N : ℕ+} {h : ℝ} (hh : 0 < h) {x : HsEuclidean N}
    (hx : ∀ j : Fin (N : ℕ), 2 * h ≤ hsUnitGap N j x) : hsUnitGapCutoff N h x = 1 :=
  Finset.prod_eq_one fun j _ =>
    loopStep_eq_one_of_le ((le_div_iff₀ hh).mpr (by linarith [hx j]))

/-- A nonvanishing cutoff has every gap strictly larger than the scale. -/
theorem lt_hsUnitGap_of_hsUnitGapCutoff_ne_zero {N : ℕ+} {h : ℝ} (hh : 0 < h) {x : HsEuclidean N}
    (hx : hsUnitGapCutoff N h x ≠ 0) (j : Fin (N : ℕ)) : h < hsUnitGap N j x := by
  have hj : loopStep (hsUnitGap N j x / h) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hx) j (Finset.mem_univ j)
  by_contra hle
  exact hj (loopStep_eq_zero_of_le ((div_le_one hh).mpr (not_lt.mp hle)))

/-- Consecutive increments of a function on `Fin n` make it strictly monotone. -/
theorem strictMono_fin_of_succ {n : ℕ} (x : Fin n → ℝ)
    (h : ∀ k : ℕ, ∀ hk : k + 1 < n, x ⟨k, by omega⟩ < x ⟨k + 1, hk⟩) : StrictMono x := by
  have key : ∀ d : ℕ, ∀ i j : Fin n, (j : ℕ) = i + d + 1 → x i < x j := by
    intro d
    induction d with
    | zero =>
      intro i j hij
      have hk : (i : ℕ) + 1 < n := by have := j.isLt; omega
      have hi : (⟨(i : ℕ), by omega⟩ : Fin n) = i := Fin.ext rfl
      have hj : (⟨(i : ℕ) + 1, hk⟩ : Fin n) = j := Fin.ext (by simp only; omega)
      have := h i hk
      rw [hi, hj] at this
      exact this
    | succ d ih =>
      intro i j hij
      have hk : (i : ℕ) + 1 < n := by have := j.isLt; omega
      let m : Fin n := ⟨(i : ℕ) + 1, hk⟩
      have h1 : x i < x m := by
        have hi : (⟨(i : ℕ), by omega⟩ : Fin n) = i := Fin.ext rfl
        have := h i hk
        rw [hi] at this
        exact this
      exact h1.trans (ih m j (by simp only [m]; omega))
  intro i j hij
  have hlt : (i : ℕ) < (j : ℕ) := hij
  exact key ((j : ℕ) - (i : ℕ) - 1) i j (by omega)

/-- Positive gaps place the lift in the open lifted chamber. -/
theorem mem_hsChamber_of_hsUnitGap_pos {N : ℕ+} {x : HsEuclidean N}
    (hx : ∀ j : Fin (N : ℕ), 0 < hsUnitGap N j x) : x ∈ hsChamber N := by
  have hNpos : 0 < (N : ℕ) := N.pos
  have hmono : StrictMono x := by
    apply strictMono_fin_of_succ (fun i : Fin (N : ℕ) => x i)
    intro k hk
    have hg := hx ⟨k, by omega⟩
    have hnext : hsNext N ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by
      apply Fin.ext
      simp only [hsNext]
      exact Nat.mod_eq_of_lt hk
    unfold hsUnitGap at hg
    rw [hnext] at hg
    have hne : ¬ (k + 1 = (N : ℕ)) := by omega
    simp only [hne, ite_false, add_zero] at hg
    linarith
  refine ⟨hmono, fun i => ?_⟩
  have hN1 : (N : ℕ) - 1 < (N : ℕ) := by omega
  have hlast := hx ⟨(N : ℕ) - 1, hN1⟩
  have hnext : hsNext N ⟨(N : ℕ) - 1, hN1⟩ = ⟨0, hNpos⟩ := by
    apply Fin.ext
    simp only [hsNext]
    have : ((N : ℕ) - 1 + 1) = (N : ℕ) := by omega
    rw [this, Nat.mod_self]
  unfold hsUnitGap at hlast
  rw [hnext] at hlast
  have hcond : (N : ℕ) - 1 + 1 = (N : ℕ) := by omega
  simp only [hcond, ite_true] at hlast
  have hi : x i ≤ x ⟨(N : ℕ) - 1, hN1⟩ := by
    apply hmono.monotone
    apply Fin.le_def.mpr
    have := i.isLt
    simp only
    omega
  linarith

/-- If every gap of `x` exceeds `h`, the Euclidean ball of radius `h / 2` lies in the chamber. -/
theorem ball_subset_hsChamber_of_hsUnitGap {N : ℕ+} {h : ℝ} {x : HsEuclidean N}
    (hx : ∀ j : Fin (N : ℕ), h < hsUnitGap N j x) :
    Metric.ball x (h / 2) ⊆ hsChamber N := by
  intro y hy
  rw [Metric.mem_ball] at hy
  apply mem_hsChamber_of_hsUnitGap_pos
  intro j
  have hcoord : ∀ i : Fin (N : ℕ), |y i - x i| < h / 2 := fun i => by
    rw [← Real.dist_eq]
    exact (PiLp.dist_apply_le y x i).trans_lt hy
  have h1 := hcoord (hsNext N j)
  have h2 := hcoord j
  have hg := hx j
  have hdiff : hsUnitGap N j y - hsUnitGap N j x =
      (y (hsNext N j) - x (hsNext N j)) - (y j - x j) := by
    unfold hsUnitGap; ring
  rw [abs_lt] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- The cutoff is smooth for every scale, since the gaps are affine. -/
theorem contDiff_hsUnitGapCutoff (N : ℕ+) (h : ℝ) : ContDiff ℝ ∞ (hsUnitGapCutoff N h) := by
  unfold hsUnitGapCutoff
  exact contDiff_prod fun j _ =>
    contDiff_loopStep.comp ((contDiff_hsUnitGap N j).div_const h)

/-- A nonvanishing cutoff keeps distance at least `h / 2` from the collision faces. -/
theorem ofReal_half_le_infEDist_of_hsUnitGapCutoff_ne_zero {N : ℕ+} {h : ℝ} (hh : 0 < h)
    {x : HsEuclidean N} (hx : hsUnitGapCutoff N h x ≠ 0) :
    ENNReal.ofReal (h / 2) ≤ Metric.infEDist x (hsChamber N)ᶜ := by
  refine Metric.le_infEDist.mpr fun y hy => ?_
  by_contra hlt
  have hd : dist x y < h / 2 := edist_lt_ofReal.mp (not_le.mp hlt)
  have hball : y ∈ Metric.ball x (h / 2) := by
    rw [Metric.mem_ball, dist_comm]
    exact hd
  exact hy (ball_subset_hsChamber_of_hsUnitGap (fun j => lt_hsUnitGap_of_hsUnitGapCutoff_ne_zero hh hx j)
    hball)

/-- The cutoff times a smooth periodic function is a test function on the lifted chamber. -/
def hsUnitGapCutoffTest {N : ℕ+} {h : ℝ} (hh : 0 < h) (Φ : HsEuclidean N → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hper : ∀ (k : ℤ) (x : HsEuclidean N), Φ (hsTranslate (k : ℝ) x) = Φ x) :
    HsTestFunction N where
  toFun := fun x => hsUnitGapCutoff N h x * Φ x
  smooth := (contDiff_hsUnitGapCutoff N h).mul hΦ
  periodic := fun k x => by
    simp only [hsUnitGapCutoff_translate, hper]
  boundarySupport := ⟨h / 2, by linarith, fun x hx => by
    have hχ : hsUnitGapCutoff N h x ≠ 0 := fun h0 => hx (by simp [h0])
    exact ofReal_half_le_infEDist_of_hsUnitGapCutoff_ne_zero hh hχ⟩

/-- The derivative of the smooth step is smooth. -/
theorem contDiff_deriv_loopStep : ContDiff ℝ ∞ (deriv loopStep) :=
  (contDiff_infty_iff_deriv.mp contDiff_loopStep).2

/-- The second derivative of the smooth step vanishes outside `[1, 2]`. -/
theorem deriv_deriv_loopStep_eq_zero_of_notMem {t : ℝ} (ht : t ∉ Icc (1 : ℝ) 2) :
    deriv (deriv loopStep) t = 0 := by
  have hev : deriv loopStep =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_Icc.isOpen_compl).mem_nhds ht] with y hy
    exact deriv_loopStep_eq_zero_of_notMem hy
  rw [hev.deriv_eq, deriv_const]

/-- The partial derivative of a function on the lift along the coordinate `k`. -/
def hsPartial {N : ℕ+} (F : HsEuclidean N → ℝ) (k : Fin (N : ℕ)) (x : HsEuclidean N) : ℝ :=
  fderiv ℝ F x (EuclideanSpace.single k 1)

theorem abs_single_apply_le {N : ℕ+} (k i : Fin (N : ℕ)) :
    |(EuclideanSpace.single k (1 : ℝ) : HsEuclidean N) i| ≤ 1 := by
  simp only [EuclideanSpace.single, PiLp.single_apply]
  split_ifs <;> simp

theorem abs_hsUnitGapLinear_single_le {N : ℕ+} (j k : Fin (N : ℕ)) :
    |hsUnitGapLinear N j (EuclideanSpace.single k (1 : ℝ))| ≤ 2 := by
  rw [hsUnitGapLinear_apply]
  have h1 := abs_single_apply_le (N := N) k (hsNext N j)
  have h2 := abs_single_apply_le (N := N) k j
  linarith [abs_sub ((EuclideanSpace.single k (1 : ℝ) : HsEuclidean N) (hsNext N j))
    ((EuclideanSpace.single k (1 : ℝ) : HsEuclidean N) j)]

/-- Each cutoff factor has derivative `(θ'(g/h) / h) • L`. -/
theorem hasFDerivAt_loopFactor (N : ℕ+) (h : ℝ) (j : Fin (N : ℕ)) (x : HsEuclidean N) :
    HasFDerivAt (fun y => loopStep (hsUnitGap N j y / h))
      ((deriv loopStep (hsUnitGap N j x / h) * h⁻¹) • hsUnitGapLinear N j) x := by
  have hg : HasFDerivAt (fun y => hsUnitGap N j y / h) (h⁻¹ • hsUnitGapLinear N j) x := by
    simpa only [div_eq_inv_mul] using (hasFDerivAt_hsUnitGap N j x).const_mul h⁻¹
  have hθ : HasDerivAt loopStep (deriv loopStep (hsUnitGap N j x / h)) (hsUnitGap N j x / h) :=
    ((contDiff_loopStep.differentiable (by simp)) _).hasDerivAt
  have := hθ.comp_hasFDerivAt x hg
  rw [← smul_smul]
  exact this

/-- The derivative of `θ'(g/h)` along the gap, with the scale factor. -/
theorem hasFDerivAt_loopDerivFactor (N : ℕ+) (h : ℝ) (j : Fin (N : ℕ)) (x : HsEuclidean N) :
    HasFDerivAt (fun y => deriv loopStep (hsUnitGap N j y / h))
      ((deriv (deriv loopStep) (hsUnitGap N j x / h) * h⁻¹) • hsUnitGapLinear N j) x := by
  have hg : HasFDerivAt (fun y => hsUnitGap N j y / h) (h⁻¹ • hsUnitGapLinear N j) x := by
    simpa only [div_eq_inv_mul] using (hasFDerivAt_hsUnitGap N j x).const_mul h⁻¹
  have hθ : HasDerivAt (deriv loopStep) (deriv (deriv loopStep) (hsUnitGap N j x / h))
      (hsUnitGap N j x / h) :=
    ((contDiff_deriv_loopStep.differentiable (by simp)) _).hasDerivAt
  have := hθ.comp_hasFDerivAt x hg
  rw [← smul_smul]
  exact this

/-- The cutoff is the product of its factors, with derivative the sum of the gap terms. -/
theorem hasFDerivAt_hsUnitGapCutoff (N : ℕ+) (h : ℝ) (x : HsEuclidean N) :
    HasFDerivAt (hsUnitGapCutoff N h) (∑ j : Fin (N : ℕ),
      (∏ i ∈ Finset.univ.erase j, loopStep (hsUnitGap N i x / h)) •
        ((deriv loopStep (hsUnitGap N j x / h) * h⁻¹) • hsUnitGapLinear N j)) x :=
  HasFDerivAt.finsetProd (fun j _ => hasFDerivAt_loopFactor N h j x)

/-- The partial derivative of the cutoff is a sum over the gaps. -/
theorem hsPartial_hsUnitGapCutoff (N : ℕ+) (h : ℝ) (k : Fin (N : ℕ)) (x : HsEuclidean N) :
    hsPartial (hsUnitGapCutoff N h) k x = ∑ j : Fin (N : ℕ),
      (∏ i ∈ Finset.univ.erase j, loopStep (hsUnitGap N i x / h)) *
        (deriv loopStep (hsUnitGap N j x / h) * h⁻¹ * hsUnitGapLinear N j (EuclideanSpace.single k 1)) := by
  unfold hsPartial
  rw [(hasFDerivAt_hsUnitGapCutoff N h x).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]

/-- The derivative of a finite product of factors bounded by one, evaluated at a vector. -/
theorem abs_finset_prod_deriv_le {ι : Type*} [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (S : Finset ι) (F : ι → E → ℝ) (D : ι → E →L[ℝ] ℝ) (x e : E) (A : ℝ)
    (hbound : ∀ i ∈ S, |F i x| ≤ 1) (hD : ∀ i ∈ S, |D i e| ≤ A) :
    |(∑ i ∈ S, (∏ j ∈ S.erase i, F j x) • D i) e| ≤ (S.card : ℝ) * A := by
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ S, |(∏ j ∈ S.erase i, F j x) * D i e| ≤ A := by
    intro i hi
    rw [abs_mul]
    have hP : |∏ j ∈ S.erase i, F j x| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
        fun j hj => hbound j (Finset.mem_of_mem_erase hj)
    calc |∏ j ∈ S.erase i, F j x| * |D i e| ≤ 1 * A :=
          mul_le_mul hP (hD i hi) (abs_nonneg _) zero_le_one
      _ = A := one_mul A
  calc ∑ i ∈ S, |(∏ j ∈ S.erase i, F j x) * D i e|
      ≤ ∑ _i ∈ S, A := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * A := by simp

/-- A coordinate derivative of one cutoff factor is bounded by `2 C / h`. -/
theorem abs_loopFactorDeriv_le (N : ℕ+) {C : ℝ} (hC : ∀ t, |deriv loopStep t| ≤ C)
    {h : ℝ} (hh : 0 < h) (k j : Fin (N : ℕ)) (x : HsEuclidean N) :
    |((deriv loopStep (hsUnitGap N j x / h) * h⁻¹) • hsUnitGapLinear N j) (EuclideanSpace.single k 1)|
      ≤ 2 * C / h := by
  rw [smul_apply, smul_eq_mul, abs_mul, abs_mul, abs_inv, abs_of_pos hh]
  have h1 := hC (hsUnitGap N j x / h)
  have h2 := abs_hsUnitGapLinear_single_le (N := N) j k
  have hinv : 0 ≤ h⁻¹ := (inv_pos.mpr hh).le
  have hC0 : 0 ≤ C := (abs_nonneg _).trans h1
  have : |deriv loopStep (hsUnitGap N j x / h)| * h⁻¹ * |hsUnitGapLinear N j (EuclideanSpace.single k 1)|
      ≤ C * h⁻¹ * 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_right h1 hinv) h2 (abs_nonneg _) (mul_nonneg hC0 hinv)
  calc _ ≤ C * h⁻¹ * 2 := this
    _ = 2 * C / h := by ring

/-- The first partial derivative of the cutoff is bounded by a constant times `h⁻¹`. -/
theorem abs_hsPartial_hsUnitGapCutoff_le (N : ℕ+) {C : ℝ} (hC : ∀ t, |deriv loopStep t| ≤ C)
    {h : ℝ} (hh : 0 < h) (k : Fin (N : ℕ)) (x : HsEuclidean N) :
    |hsPartial (hsUnitGapCutoff N h) k x| ≤ (N : ℝ) * (2 * C / h) := by
  have hF : ∀ i ∈ (Finset.univ : Finset (Fin (N : ℕ))), |loopStep (hsUnitGap N i x / h)| ≤ 1 := by
    intro i _
    rw [abs_of_nonneg (loopStep_nonneg _)]
    exact loopStep_le_one _
  have hsum := abs_finset_prod_deriv_le (Finset.univ : Finset (Fin (N : ℕ)))
    (fun i y => loopStep (hsUnitGap N i y / h))
    (fun j => (deriv loopStep (hsUnitGap N j x / h) * h⁻¹) • hsUnitGapLinear N j)
    x (EuclideanSpace.single k 1) (2 * C / h) hF
    (fun j _ => abs_loopFactorDeriv_le N hC hh k j x)
  have heq : hsPartial (hsUnitGapCutoff N h) k x = (∑ i : Fin (N : ℕ),
      (∏ j ∈ Finset.univ.erase i, loopStep (hsUnitGap N j x / h)) •
        ((deriv loopStep (hsUnitGap N i x / h) * h⁻¹) • hsUnitGapLinear N i)) (EuclideanSpace.single k 1) := by
    rw [hsPartial_hsUnitGapCutoff]
    simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [heq]
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  exact hsum.trans (le_of_eq (by simp))

/-- A gap term of the first partial derivative, split as a product of two factors. -/
def hsPartialTerm (N : ℕ+) (h : ℝ) (l j : Fin (N : ℕ)) (y : HsEuclidean N) : ℝ :=
  (∏ i ∈ Finset.univ.erase j, loopStep (hsUnitGap N i y / h)) *
    ((h⁻¹ * hsUnitGapLinear N j (EuclideanSpace.single l 1)) * deriv loopStep (hsUnitGap N j y / h))

theorem hsPartial_hsUnitGapCutoff_eq_sum (N : ℕ+) (h : ℝ) (l : Fin (N : ℕ)) :
    hsPartial (hsUnitGapCutoff N h) l = fun y => ∑ j : Fin (N : ℕ), hsPartialTerm N h l j y := by
  funext y
  rw [hsPartial_hsUnitGapCutoff]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold hsPartialTerm
  ring

/-- The derivative of one gap term, by the product rule for the product of factors and the
derivative of the scaled `θ'`. -/
theorem hasFDerivAt_hsPartialTerm (N : ℕ+) (h : ℝ) (l j : Fin (N : ℕ)) (x : HsEuclidean N) :
    HasFDerivAt (hsPartialTerm N h l j)
      ((∏ i ∈ Finset.univ.erase j, loopStep (hsUnitGap N i x / h)) •
          ((h⁻¹ * hsUnitGapLinear N j (EuclideanSpace.single l 1)) •
            ((deriv (deriv loopStep) (hsUnitGap N j x / h) * h⁻¹) • hsUnitGapLinear N j)) +
        ((h⁻¹ * hsUnitGapLinear N j (EuclideanSpace.single l 1)) * deriv loopStep (hsUnitGap N j x / h)) •
          (∑ i ∈ Finset.univ.erase j,
            (∏ m ∈ (Finset.univ.erase j).erase i, loopStep (hsUnitGap N m x / h)) •
              ((deriv loopStep (hsUnitGap N i x / h) * h⁻¹) • hsUnitGapLinear N i))) x := by
  have hP : HasFDerivAt (fun y => ∏ i ∈ Finset.univ.erase j, loopStep (hsUnitGap N i y / h))
      (∑ i ∈ Finset.univ.erase j,
        (∏ m ∈ (Finset.univ.erase j).erase i, loopStep (hsUnitGap N m x / h)) •
          ((deriv loopStep (hsUnitGap N i x / h) * h⁻¹) • hsUnitGapLinear N i)) x :=
    HasFDerivAt.finsetProd (fun i _ => hasFDerivAt_loopFactor N h i x)
  have hQ : HasFDerivAt
      (fun y => (h⁻¹ * hsUnitGapLinear N j (EuclideanSpace.single l 1)) *
        deriv loopStep (hsUnitGap N j y / h))
      ((h⁻¹ * hsUnitGapLinear N j (EuclideanSpace.single l 1)) •
        ((deriv (deriv loopStep) (hsUnitGap N j x / h) * h⁻¹) • hsUnitGapLinear N j)) x :=
    (hasFDerivAt_loopDerivFactor N h j x).const_mul _
  exact hP.mul hQ

theorem differentiableAt_hsPartialTerm (N : ℕ+) (h : ℝ) (l j : Fin (N : ℕ))
    (x : HsEuclidean N) : DifferentiableAt ℝ (hsPartialTerm N h l j) x :=
  (hasFDerivAt_hsPartialTerm N h l j x).differentiableAt

/-- The product-rule combination of the two terms, with all factors bounded. -/
theorem abs_productRule_le (P c hi C D1 D2 Le S K : ℝ) (hi0 : 0 ≤ hi) (hC0 : 0 ≤ C)
    (hP : |P| ≤ 1) (hc : |c| ≤ 2) (hD1 : |D1| ≤ C) (hD2 : |D2| ≤ C)
    (hLe : |Le| ≤ 2) (hS : |S| ≤ K * (2 * C * hi)) :
    |P * ((hi * c) * ((D2 * hi) * Le)) + ((hi * c) * D1) * S| ≤
      (4 * C + 4 * K * C ^ 2) * hi ^ 2 := by
  have hT1 : |P * ((hi * c) * ((D2 * hi) * Le))| ≤ 4 * C * hi ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hi0]
    calc |P| * (hi * |c| * (|D2| * hi * |Le|)) ≤ 1 * (hi * 2 * (C * hi * 2)) := by gcongr
      _ = 4 * C * hi ^ 2 := by ring
  have hT2 : |((hi * c) * D1) * S| ≤ 4 * K * C ^ 2 * hi ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hi0]
    calc hi * |c| * |D1| * |S| ≤ hi * 2 * C * (K * (2 * C * hi)) := by gcongr
      _ = 4 * K * C ^ 2 * hi ^ 2 := by ring
  calc _ ≤ |P * ((hi * c) * ((D2 * hi) * Le))| + |((hi * c) * D1) * S| := abs_add_le _ _
    _ ≤ 4 * C * hi ^ 2 + 4 * K * C ^ 2 * hi ^ 2 := add_le_add hT1 hT2
    _ = (4 * C + 4 * K * C ^ 2) * hi ^ 2 := by ring

/-- Each gap term of the second partial derivative is bounded by `(4 C + 4 N C²) / h²`. -/
theorem abs_fderiv_hsPartialTerm_le (N : ℕ+) {C : ℝ}
    (hC : ∀ t, |deriv loopStep t| ≤ C ∧ |deriv (deriv loopStep) t| ≤ C)
    {h : ℝ} (hh : 0 < h) (l k j : Fin (N : ℕ)) (x : HsEuclidean N) :
    |fderiv ℝ (hsPartialTerm N h l j) x (EuclideanSpace.single k 1)|
      ≤ (4 * C + 4 * (N : ℝ) * C ^ 2) / h ^ 2 := by
  have hC1 : ∀ t, |deriv loopStep t| ≤ C := fun t => (hC t).1
  have hC2 : ∀ t, |deriv (deriv loopStep) t| ≤ C := fun t => (hC t).2
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
  have hinv : 0 ≤ h⁻¹ := (inv_pos.mpr hh).le
  have hP : ∀ i ∈ (Finset.univ : Finset (Fin (N : ℕ))), |loopStep (hsUnitGap N i x / h)| ≤ 1 := by
    intro i _
    rw [abs_of_nonneg (loopStep_nonneg _)]
    exact loopStep_le_one _
  have hPprod : |∏ i ∈ Finset.univ.erase j, loopStep (hsUnitGap N i x / h)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
      fun i hi => hP i (Finset.mem_univ i)
  have hS := abs_finset_prod_deriv_le (Finset.univ.erase j)
    (fun i y => loopStep (hsUnitGap N i y / h))
    (fun i => (deriv loopStep (hsUnitGap N i x / h) * h⁻¹) • hsUnitGapLinear N i)
    x (EuclideanSpace.single k 1) (2 * C / h) (fun i _ => by
      rw [abs_of_nonneg (loopStep_nonneg _)]
      exact loopStep_le_one _)
    (fun i _ => abs_loopFactorDeriv_le N hC1 hh k i x)
  have hcard : ((Finset.univ.erase j).card : ℝ) ≤ (N : ℝ) := by
    have := (Finset.card_erase_le (s := (Finset.univ : Finset (Fin (N : ℕ)))) (a := j))
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hS' : |(∑ i ∈ Finset.univ.erase j,
      (∏ m ∈ (Finset.univ.erase j).erase i, loopStep (hsUnitGap N m x / h)) •
        ((deriv loopStep (hsUnitGap N i x / h) * h⁻¹) • hsUnitGapLinear N i))
      (EuclideanSpace.single k 1)| ≤ (N : ℝ) * (2 * C * h⁻¹) := by
    refine hS.trans ?_
    have hfac : 2 * C / h = 2 * C * h⁻¹ := by ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  rw [(hasFDerivAt_hsPartialTerm N h l j x).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  have key := abs_productRule_le _ _ h⁻¹ C _ _ _ _ (N : ℝ) hinv hC0
    hPprod (abs_hsUnitGapLinear_single_le j l) (hC1 (hsUnitGap N j x / h)) (hC2 (hsUnitGap N j x / h))
    (abs_hsUnitGapLinear_single_le j k) hS'
  have hfinal : (4 * C + 4 * (N : ℝ) * C ^ 2) * h⁻¹ ^ 2 = (4 * C + 4 * (N : ℝ) * C ^ 2) / h ^ 2 := by
    rw [inv_pow, div_eq_mul_inv]
  rw [← hfinal]
  exact key

/-- The second partial derivative of the cutoff is a sum of the gap terms. -/
theorem hsPartial_hsPartial_hsUnitGapCutoff_eq_sum (N : ℕ+) (h : ℝ) (l k : Fin (N : ℕ))
    (x : HsEuclidean N) :
    hsPartial (hsPartial (hsUnitGapCutoff N h) l) k x =
      ∑ j : Fin (N : ℕ), fderiv ℝ (hsPartialTerm N h l j) x (EuclideanSpace.single k 1) := by
  show fderiv ℝ (hsPartial (hsUnitGapCutoff N h) l) x (EuclideanSpace.single k 1) = _
  rw [hsPartial_hsUnitGapCutoff_eq_sum, ← Finset.sum_fn,
    fderiv_sum fun j _ => differentiableAt_hsPartialTerm N h l j x]
  simp only [sum_apply]

/-- The second partial derivative of the cutoff is bounded by a constant times `h⁻²`. -/
theorem abs_hsPartial_hsPartial_hsUnitGapCutoff_le (N : ℕ+) {C : ℝ}
    (hC : ∀ t, |deriv loopStep t| ≤ C ∧ |deriv (deriv loopStep) t| ≤ C)
    {h : ℝ} (hh : 0 < h) (l k : Fin (N : ℕ)) (x : HsEuclidean N) :
    |hsPartial (hsPartial (hsUnitGapCutoff N h) l) k x| ≤
      (N : ℝ) * ((4 * C + 4 * (N : ℝ) * C ^ 2) / h ^ 2) := by
  rw [hsPartial_hsPartial_hsUnitGapCutoff_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (N : ℕ))),
      |fderiv ℝ (hsPartialTerm N h l j) x (EuclideanSpace.single k 1)|
        ≤ (4 * C + 4 * (N : ℝ) * C ^ 2) / h ^ 2 :=
    fun j _ => abs_fderiv_hsPartialTerm_le N hC hh l k j x
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The first partial derivative vanishes where every gap exceeds `2h`. -/
theorem hsPartial_hsUnitGapCutoff_eq_zero {N : ℕ+} {h : ℝ} (hh : 0 < h) {x : HsEuclidean N}
    (hx : ∀ j : Fin (N : ℕ), 2 * h < hsUnitGap N j x) (k : Fin (N : ℕ)) :
    hsPartial (hsUnitGapCutoff N h) k x = 0 := by
  rw [hsPartial_hsUnitGapCutoff]
  refine Finset.sum_eq_zero fun j _ => ?_
  have ht : hsUnitGap N j x / h ∉ Icc (1 : ℝ) 2 := by
    intro hmem
    have h2 : hsUnitGap N j x / h ≤ 2 := hmem.2
    have hlt : 2 < hsUnitGap N j x / h := (lt_div_iff₀ hh).mpr (by linarith [hx j])
    linarith
  rw [deriv_loopStep_eq_zero_of_notMem ht]
  ring

/-- The second partial derivative vanishes where every gap exceeds `2h`. -/
theorem hsPartial_hsPartial_hsUnitGapCutoff_eq_zero {N : ℕ+} {h : ℝ} (hh : 0 < h) {x : HsEuclidean N}
    (hx : ∀ j : Fin (N : ℕ), 2 * h < hsUnitGap N j x) (l k : Fin (N : ℕ)) :
    hsPartial (hsPartial (hsUnitGapCutoff N h) l) k x = 0 := by
  rw [hsPartial_hsPartial_hsUnitGapCutoff_eq_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  have ht : hsUnitGap N j x / h ∉ Icc (1 : ℝ) 2 := by
    intro hmem
    have h2 : hsUnitGap N j x / h ≤ 2 := hmem.2
    have hlt : 2 < hsUnitGap N j x / h := (lt_div_iff₀ hh).mpr (by linarith [hx j])
    linarith
  have hd1 : deriv loopStep (hsUnitGap N j x / h) = 0 := deriv_loopStep_eq_zero_of_notMem ht
  have hd2 : deriv (deriv loopStep) (hsUnitGap N j x / h) = 0 :=
    deriv_deriv_loopStep_eq_zero_of_notMem ht
  rw [(hasFDerivAt_hsPartialTerm N h l j x).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, hd1, hd2, mul_zero, zero_mul, add_zero,
    sum_apply]

end Riesz1
