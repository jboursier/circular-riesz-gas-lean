/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopIBPLimit
public import Riesz1.Variance.LoopIBPTransfer
public import Riesz1.Variance.LoopIBPUniform
public import Riesz1.Variance.LoopIBPGibbs
public import Riesz1.Variance.LoopIBPCutoff
public import Riesz1.Variance.LoopIBPErrors
public import Riesz1.Variance.LoopIBPHessian
public import Riesz1.Variance.LoopIBPMoments
public import Riesz1.Variance.LoopIBPPairs
public import Riesz1.Variance.LoopIBPHS
import all Riesz1.Variance.LoopForceEnergy
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Variance identity for the diagonal field, `N ≥ 2`

Proposition 5.5, clause 3, for `N ≥ 2`. Write `𝓛F = ∑ₖ ∂ₖH ∂ₖF − ΔF`
for the Langevin operator of the Riesz Hamiltonian `H = β · energy`, and `Φ = Φ_{ψ,a}` for the
field potential.

The proof has four stages.

1. **Bochner identity for test functions.** For a smooth periodic `F` with compact support in the
   chamber, `∫ (𝓛F)² = ∫ ∑ₖₗ (∂ₖ∂ₗH) ∂ₖF ∂ₗF + ∑ₖₗ (∂ₖ∂ₗF)²`. It follows from the
   Helffer–Sjöstrand identity `rieszIBP` applied twice and the commutator
   `∂ₖ(𝓛F) = 𝓛(∂ₖF) + ∑ₗ ∂ₖ∂ₗH ∂ₗF`.
2. **Cutoff approximation.** The cutoffs `χ_h Φ` of `hsUnitGapCutoffTest` satisfy the identity of
   stage 1. As `h → 0` both sides converge, using the strip estimates of `LoopIBPGibbs`.
3. **Identification of the limit.** The limit of the right side is `a² ∫ (hessianQuadratic +
   frobeniusSqDiag)`, because `∂ₖΦ = a ℓ ψ(xₖ/ℓ)` and `∂ₖ∂ₗΦ = δₖₗ a ψ'(xₖ/ℓ)`.
4. **Mean zero.** `∫ 𝓛Φ = 0` by `loopLHS_integral_eq` with the constant test function, so the
   covariance is the second moment.

Section 1 below collects the calculus of `hsPartial` on the chamber and the class of test
functions. Its integrability lemma reduces all integrals to bounded or gap-integrable integrands.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-! ### Section 1: calculus of `hsPartial` and the test-function class -/

/-- The Langevin operator `𝓛F = ∑ₖ ∂ₖH ∂ₖF − ΔF` of the Riesz Hamiltonian, written in partial
derivatives on the lift. For `F = Φ_{ψ,a}` this is `loopLHS`. -/
def langOp (P : Parameters) (N : ℕ+) (F : HsEuclidean N → ℝ) (x : HsEuclidean N) : ℝ :=
  ∑ k : Fin (N : ℕ), hsPartial (rieszH P N) k x * hsPartial F k x -
    ∑ k : Fin (N : ℕ), hsPartial (hsPartial F k) k x

/-- The first Bochner term `∑ₖ 𝓛(∂ₖF) ∂ₖF`. -/
def bochA (P : Parameters) (N : ℕ+) (F : HsEuclidean N → ℝ) (x : HsEuclidean N) : ℝ :=
  ∑ k : Fin (N : ℕ), langOp P N (hsPartial F k) x * hsPartial F k x

/-- The second Bochner term `∑ₖₗ ∂ₖ∂ₗH ∂ₖF ∂ₗF`. -/
def bochB (P : Parameters) (N : ℕ+) (F : HsEuclidean N → ℝ) (x : HsEuclidean N) : ℝ :=
  ∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ),
    hsPartial (hsPartial (rieszH P N) k) l x * hsPartial F k x * hsPartial F l x

/-- The third Bochner term `∑ₖₗ (∂ₖ∂ₗF)²`. -/
def bochC (_P : Parameters) (N : ℕ+) (F : HsEuclidean N → ℝ) (x : HsEuclidean N) : ℝ :=
  ∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ), hsPartial (hsPartial F k) l x * hsPartial (hsPartial F k) l x

/-- The Bochner form `∑ₖₗ ∂ₖ∂ₗH ∂ₖF ∂ₗF + ∑ₖₗ (∂ₖ∂ₗF)²` of a smooth function `F`. -/
def bochnerForm (P : Parameters) (N : ℕ+) (F : HsEuclidean N → ℝ) (x : HsEuclidean N) : ℝ :=
  bochB P N F x + bochC P N F x

/-- The open neighbourhood `{x : dist(x, complement of the chamber) < δ}` of the chamber boundary. -/
def nearBoundary (N : ℕ+) (δ : ℝ) : Set (HsEuclidean N) :=
  {x | Metric.infEDist x (hsChamber N)ᶜ < ENNReal.ofReal δ}

theorem isOpen_nearBoundary (N : ℕ+) (δ : ℝ) : IsOpen (nearBoundary N δ) :=
  isOpen_lt Metric.continuous_infEDist continuous_const

theorem hsPartial_eq_zero_of_eventually {N : ℕ+} {F : HsEuclidean N → ℝ} {x : HsEuclidean N}
    (hF : ∀ᶠ y in 𝓝 x, F y = 0) (k : Fin (N : ℕ)) : hsPartial F k x = 0 := by
  unfold hsPartial
  have h0 : F =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := hF
  rw [h0.fderiv_eq]
  simp

/-- A test function vanishes on the boundary neighbourhood of its support radius. -/
theorem HsTestFunction.exists_nearBoundary_zero {N : ℕ+} (f : HsTestFunction N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ nearBoundary N δ, f.toFun y = 0 := by
  obtain ⟨δ, hδ, hs⟩ := f.boundarySupport
  refine ⟨δ, hδ, fun y hy => ?_⟩
  by_contra hf
  exact absurd (hs y hf) (not_le.mpr (show Metric.infEDist y (hsChamber N)ᶜ < ENNReal.ofReal δ from hy))

/-- Partial derivatives of a periodic function are periodic under diagonal integer shifts. -/
theorem hsPartial_hsTranslate {N : ℕ+} {F : HsEuclidean N → ℝ}
    (hper : ∀ (j : ℤ) (y : HsEuclidean N), F (hsTranslate (j : ℝ) y) = F y)
    (k : Fin (N : ℕ)) (j : ℤ) (x : HsEuclidean N) :
    hsPartial F k (hsTranslate (j : ℝ) x) = hsPartial F k x := by
  set c : HsEuclidean N := WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (j : ℝ)) with hc
  have hT : ∀ y : HsEuclidean N, hsTranslate (j : ℝ) y = y + c := by
    intro y
    ext i
    simp [hsTranslate_apply, hc]
  have hF : (fun y => F (y + c)) = F := by
    funext y
    rw [← hT]
    exact hper j y
  have h1 : fderiv ℝ F (x + c) = fderiv ℝ F x := by
    calc fderiv ℝ F (x + c) = fderiv ℝ (fun y => F (y + c)) x :=
          (by rw [fderiv_comp_add_right])
      _ = fderiv ℝ F x := by rw [hF]
  unfold hsPartial
  rw [hT, h1]

/-- The partial derivative of a smooth function on an open set is smooth on that set. -/
theorem contDiffOn_hsPartial_of_isOpen {N : ℕ+} {F : HsEuclidean N → ℝ}
    {U : Set (HsEuclidean N)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (k : Fin (N : ℕ)) :
    ContDiffOn ℝ ∞ (hsPartial F k) U := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  exact hfd.clm_apply contDiffOn_const

/-- Second partial derivatives of a function that is twice differentiable at a point commute. -/
theorem hsPartial_hsPartial_comm_at {N : ℕ+} {F : HsEuclidean N → ℝ} {x : HsEuclidean N}
    (hF : ContDiffAt ℝ ∞ F x) (k l : Fin (N : ℕ)) :
    hsPartial (hsPartial F k) l x = hsPartial (hsPartial F l) k x := by
  have hs : IsSymmSndFDerivAt ℝ F x := hF.isSymmSndFDerivAt (by simp)
  have hc : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have key : ∀ j m : Fin (N : ℕ), hsPartial (hsPartial F j) m x =
      fderiv ℝ (fderiv ℝ F) x (EuclideanSpace.single m 1) (EuclideanSpace.single j 1) := by
    intro j m
    unfold hsPartial
    rw [fderiv_clm_apply hc (differentiableAt_const _)]
    simp
  rw [key, key]
  exact hs _ _

/-- Second partial derivatives of a smooth function commute, as functions. -/
theorem hsPartial_hsPartial_comm_fun {N : ℕ+} {F : HsEuclidean N → ℝ} (hF : ContDiff ℝ ∞ F)
    (k l : Fin (N : ℕ)) :
    hsPartial (hsPartial F k) l = hsPartial (hsPartial F l) k := by
  funext x
  exact hsPartial_hsPartial_comm_at hF.contDiffAt k l

/-- The partial derivative of a finite sum. -/
theorem hsPartial_fun_sum {N : ℕ+} {ι : Type*} (s : Finset ι) (A : ι → HsEuclidean N → ℝ)
    {x : HsEuclidean N} (hA : ∀ i ∈ s, DifferentiableAt ℝ (A i) x) (k : Fin (N : ℕ)) :
    hsPartial (fun y => ∑ i ∈ s, A i y) k x = ∑ i ∈ s, hsPartial (A i) k x := by
  unfold hsPartial
  rw [fderiv_fun_sum hA, sum_apply]

/-- The partial derivative of a difference. -/
theorem hsPartial_fun_sub {N : ℕ+} {F G : HsEuclidean N → ℝ} {x : HsEuclidean N}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (k : Fin (N : ℕ)) :
    hsPartial (fun y => F y - G y) k x = hsPartial F k x - hsPartial G k x := by
  unfold hsPartial
  rw [fderiv_fun_sub hF hG]
  simp

/-- The energy `H = rieszH` is smooth on the open chamber, and so are its first partial
derivatives. -/
theorem contDiffOn_rieszH_partial (P : Parameters) (N : ℕ+) (k : Fin (N : ℕ)) :
    ContDiffOn ℝ ∞ (hsPartial (rieszH P N) k) (hsChamber N) :=
  contDiffOn_hsPartial_of_isOpen (isOpen_hsChamber N) (hsPairExpression_contDiffOn _) k

theorem contDiffAt_rieszH (P : Parameters) (N : ℕ+) {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    ContDiffAt ℝ ∞ (rieszH P N) x :=
  (hsPairExpression_contDiffOn _).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)

theorem contDiffAt_hsPartial_rieszH (P : Parameters) (N : ℕ+) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) (k : Fin (N : ℕ)) :
    ContDiffAt ℝ ∞ (hsPartial (rieszH P N) k) x :=
  (contDiffOn_rieszH_partial P N k).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)

/-- The Langevin operator is smooth on the open chamber. -/
theorem contDiffOn_langOp (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiffOn ℝ ∞ (langOp P N F) (hsChamber N) := by
  unfold langOp
  refine ContDiffOn.sub (ContDiffOn.sum fun k _ => ?_) (ContDiffOn.sum fun k _ => ?_)
  · exact (contDiffOn_rieszH_partial P N k).mul (contDiff_hsPartial hF k).contDiffOn
  · exact (contDiff_hsPartial (contDiff_hsPartial hF k) k).contDiffOn

/-- A function vanishing on an open set has vanishing partial derivatives there. -/
theorem hsPartial_eq_zero_of_open {N : ℕ+} {U : Set (HsEuclidean N)} (hU : IsOpen U)
    {F : HsEuclidean N → ℝ} (hF : ∀ y ∈ U, F y = 0) {x : HsEuclidean N} (hx : x ∈ U)
    (k : Fin (N : ℕ)) : hsPartial F k x = 0 :=
  hsPartial_eq_zero_of_eventually (Filter.eventually_of_mem (hU.mem_nhds hx) hF) k

/-- The Langevin operator of a test function vanishes near the chamber boundary, so it is smooth
on all of `HsEuclidean N`. -/
theorem contDiff_langOp_test (P : Parameters) (N : ℕ+) (f : HsTestFunction N) :
    ContDiff ℝ ∞ (langOp P N f.toFun) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ hsChamber N
  · exact (contDiffOn_langOp P N f.smooth).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)
  · obtain ⟨δ, hδ, hz⟩ := f.exists_nearBoundary_zero
    have hU := isOpen_nearBoundary N δ
    have hxU : x ∈ nearBoundary N δ := by
      show Metric.infEDist x (hsChamber N)ᶜ < ENNReal.ofReal δ
      rw [Metric.infEDist_zero_of_mem hx]
      exact ENNReal.ofReal_pos.mpr hδ
    have hd1 : ∀ y ∈ nearBoundary N δ, ∀ k : Fin (N : ℕ), hsPartial f.toFun k y = 0 :=
      fun y hy k => hsPartial_eq_zero_of_open hU hz hy k
    have hd2 : ∀ y ∈ nearBoundary N δ, ∀ k l : Fin (N : ℕ),
        hsPartial (hsPartial f.toFun k) l y = 0 :=
      fun y hy k l => hsPartial_eq_zero_of_open hU (fun z hz' => hd1 z hz' k) hy l
    have hzero : langOp P N f.toFun =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => by
        unfold langOp
        simp [hd1 y hy, hd2 y hy]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- The partial derivative of a test function is a test function with the same boundary radius. -/
def hsTestPartial {N : ℕ+} (f : HsTestFunction N) (k : Fin (N : ℕ)) : HsTestFunction N where
  toFun := hsPartial f.toFun k
  smooth := contDiff_hsPartial f.smooth k
  periodic := fun j y => hsPartial_hsTranslate f.periodic k j y
  boundarySupport := by
    obtain ⟨δ, hδ, hz⟩ := f.exists_nearBoundary_zero
    refine ⟨δ, hδ, fun y hy => ?_⟩
    by_contra hc
    have hyU : y ∈ nearBoundary N δ := show Metric.infEDist y (hsChamber N)ᶜ < ENNReal.ofReal δ from not_le.mp hc
    exact hy (hsPartial_eq_zero_of_open (isOpen_nearBoundary N δ) hz hyU k)

/-- A bounded function on the chamber whose support avoids a neighbourhood of the boundary is
integrable on the configurations. -/
theorem integrable_config_of_vanish (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hF : ContinuousOn F (hsChamber N)) {δ : ℝ} (hδ : 0 < δ)
    (hv : ∀ x ∈ nearBoundary N δ, F x = 0) :
    Integrable (fun X : Configuration N => F (WithLp.toLp 2 X.val)) (gibbsMeasure P N) := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  have hnorm : ∀ X : Configuration N,
      ‖(WithLp.toLp 2 X.val : HsEuclidean N)‖ ≤ 2 * ((N : ℕ) : ℝ) := by
    intro X
    have hX := X.property
    simp only [orderedDomain, Set.mem_ofPred_eq] at hX
    obtain ⟨hmono, h0, h1, hlt⟩ := hX
    have hmin : ∀ i : Fin (N : ℕ), X.val ⟨0, N.pos⟩ ≤ X.val i := fun i =>
      hmono.monotone (Fin.le_def.mpr (Nat.zero_le _))
    have hb : ∀ i : Fin (N : ℕ), |X.val i| ≤ 2 := fun i =>
      abs_le.mpr ⟨by linarith [hmin i], by linarith [hlt i]⟩
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hN1 : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
    calc ∑ i : Fin (N : ℕ), ‖(WithLp.toLp 2 X.val : HsEuclidean N) i‖ ^ 2
        ≤ ∑ _i : Fin (N : ℕ), (4 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := hb i
          simp only [Real.norm_eq_abs]
          nlinarith [abs_nonneg (X.val i)]
      _ = 4 * ((N : ℕ) : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ (2 * ((N : ℕ) : ℝ)) ^ 2 := by nlinarith [hN1]
  set K : Set (HsEuclidean N) := Metric.closedBall 0 (2 * ((N : ℕ) : ℝ)) ∩
    {x | ENNReal.ofReal δ ≤ Metric.infEDist x (hsChamber N)ᶜ} with hKdef
  have hK : IsCompact K :=
    (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const Metric.continuous_infEDist)
  have hKch : K ⊆ hsChamber N := by
    intro x hx
    by_contra hc
    have h0 : Metric.infEDist x (hsChamber N)ᶜ = 0 := Metric.infEDist_zero_of_mem hc
    have h2 : ENNReal.ofReal δ ≤ Metric.infEDist x (hsChamber N)ᶜ := hx.2
    rw [h0] at h2
    exact absurd h2 (not_le.mpr (ENNReal.ofReal_pos.mpr hδ))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF.mono hKch)
  have hcont : Continuous (fun X : Configuration N => F (WithLp.toLp 2 X.val)) :=
    hF.comp_continuous (continuous_toLp_config N) fun X => mem_hsChamber_configuration X
  refine Integrable.of_bound hcont.aestronglyMeasurable (max M 0)
    (Filter.Eventually.of_forall fun X => ?_)
  by_cases hX : (WithLp.toLp 2 X.val : HsEuclidean N) ∈ nearBoundary N δ
  · rw [hv _ hX, norm_zero]
    exact le_max_right _ _
  · have hXK : (WithLp.toLp 2 X.val : HsEuclidean N) ∈ K :=
      ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hnorm X,
        (show ENNReal.ofReal δ ≤ Metric.infEDist _ (hsChamber N)ᶜ from not_lt.mp hX)⟩
    exact (hM _ hXK).trans (le_max_left _ _)

/-! ### Section 2: the commutator and the Bochner identity for test functions -/

theorem hsTestPartial_toFun {N : ℕ+} (f : HsTestFunction N) (k : Fin (N : ℕ)) :
    (hsTestPartial f k).toFun = hsPartial f.toFun k :=
  rfl

/-- The Riesz energy is invariant under diagonal translations of the lift. -/
theorem rieszH_hsTranslate (P : Parameters) (N : ℕ+) (t : ℝ) (x : HsEuclidean N) :
    rieszH P N (hsTranslate t x) = rieszH P N x := by
  unfold rieszH hsPairExpression
  simp only [hsTranslate_apply, add_sub_add_right_eq_sub]

/-- The Langevin operator of a diagonally periodic function is diagonally periodic. -/
theorem langOp_hsTranslate (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hper : ∀ (j : ℤ) (y : HsEuclidean N), F (hsTranslate (j : ℝ) y) = F y) (j : ℤ)
    (x : HsEuclidean N) : langOp P N F (hsTranslate (j : ℝ) x) = langOp P N F x := by
  have hkk : ∀ (k l : Fin (N : ℕ)) (y : HsEuclidean N),
      hsPartial (hsPartial F k) l (hsTranslate (j : ℝ) y) = hsPartial (hsPartial F k) l y :=
    fun k l y => hsPartial_hsTranslate (fun j' z => hsPartial_hsTranslate hper k j' z) l j y
  have hH : ∀ (l : Fin (N : ℕ)) (y : HsEuclidean N),
      hsPartial (rieszH P N) l (hsTranslate (j : ℝ) y) = hsPartial (rieszH P N) l y :=
    fun l y => hsPartial_hsTranslate (fun j' z => rieszH_hsTranslate P N j' z) l j y
  unfold langOp
  simp only [hH, hsPartial_hsTranslate hper, hkk]

/-- The integrand of the Helffer–Sjöstrand identity is the Langevin operator in partial
derivatives. -/
theorem rieszIntegrand_eq (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hF : ContDiff ℝ ∞ F) (x : HsEuclidean N) :
    inner ℝ (gradient (hsPairExpression (rieszPairs P N)) x) (gradient F x) -
      Laplacian.laplacian F x = langOp P N F x := by
  rw [inner_gradient_eq_sum_hsPartial, laplacian_eq_sum_hsPartial_hsPartial hF]
  rfl

/-- The commutator identity on the chamber: `∂ₖ(𝓛F) = 𝓛(∂ₖF) + ∑ₗ ∂ₖ∂ₗH ∂ₗF`. -/
theorem hsPartial_langOp (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hF : ContDiff ℝ ∞ F) {x : HsEuclidean N} (hx : x ∈ hsChamber N) (k : Fin (N : ℕ)) :
    hsPartial (langOp P N F) k x = langOp P N (hsPartial F k) x +
      ∑ l : Fin (N : ℕ), hsPartial (hsPartial (rieszH P N) k) l x * hsPartial F l x := by
  have hHc : ContDiffAt ℝ ∞ (rieszH P N) x := contDiffAt_rieszH P N hx
  have hHd : ∀ l : Fin (N : ℕ), DifferentiableAt ℝ (hsPartial (rieszH P N) l) x := fun l =>
    (contDiffAt_hsPartial_rieszH P N hx l).differentiableAt (by simp)
  have hFd : ∀ l : Fin (N : ℕ), DifferentiableAt ℝ (hsPartial F l) x := fun l =>
    ((contDiff_hsPartial hF l).differentiable (by simp)) x
  have hFFd : ∀ l : Fin (N : ℕ), DifferentiableAt ℝ (hsPartial (hsPartial F l) l) x := fun l =>
    ((contDiff_hsPartial (contDiff_hsPartial hF l) l).differentiable (by simp)) x
  have hprod : ∀ l : Fin (N : ℕ),
      DifferentiableAt ℝ (fun y => hsPartial (rieszH P N) l y * hsPartial F l y) x :=
    fun l => (hHd l).mul (hFd l)
  have hsum1 : DifferentiableAt ℝ
      (fun y => ∑ l : Fin (N : ℕ), hsPartial (rieszH P N) l y * hsPartial F l y) x :=
    DifferentiableAt.fun_sum fun l _ => hprod l
  have hsum2 : DifferentiableAt ℝ
      (fun y => ∑ l : Fin (N : ℕ), hsPartial (hsPartial F l) l y) x :=
    DifferentiableAt.fun_sum fun l _ => hFFd l
  have hL : ∀ l : Fin (N : ℕ),
      hsPartial (fun y => hsPartial (rieszH P N) l y * hsPartial F l y) k x =
        hsPartial (hsPartial (rieszH P N) k) l x * hsPartial F l x +
          hsPartial (rieszH P N) l x * hsPartial (hsPartial F k) l x := by
    intro l
    rw [hsPartial_mul (hHd l) (hFd l) k, hsPartial_hsPartial_comm_at hHc l k,
      (congrFun (hsPartial_hsPartial_comm_fun hF k l) x).symm]
  have hR : ∀ l : Fin (N : ℕ), hsPartial (hsPartial (hsPartial F l) l) k x =
      hsPartial (hsPartial (hsPartial F k) l) l x := by
    intro l
    have e1 : hsPartial (hsPartial F l) k = hsPartial (hsPartial F k) l :=
      (hsPartial_hsPartial_comm_fun hF k l).symm
    calc hsPartial (hsPartial (hsPartial F l) l) k x
        = hsPartial (hsPartial (hsPartial F l) k) l x :=
          congrFun (hsPartial_hsPartial_comm_fun (contDiff_hsPartial hF l) l k) x
      _ = hsPartial (hsPartial (hsPartial F k) l) l x := by rw [e1]
  have hfun : langOp P N F = fun y =>
      (∑ l : Fin (N : ℕ), hsPartial (rieszH P N) l y * hsPartial F l y) -
        ∑ l : Fin (N : ℕ), hsPartial (hsPartial F l) l y := rfl
  have hS1 : hsPartial (fun y => ∑ l : Fin (N : ℕ), hsPartial (rieszH P N) l y * hsPartial F l y) k x
      = ∑ l : Fin (N : ℕ), hsPartial (fun y => hsPartial (rieszH P N) l y * hsPartial F l y) k x :=
    hsPartial_fun_sum Finset.univ _ (fun l _ => hprod l) k
  have hS2 : hsPartial (fun y => ∑ l : Fin (N : ℕ), hsPartial (hsPartial F l) l y) k x
      = ∑ l : Fin (N : ℕ), hsPartial (hsPartial (hsPartial F l) l) k x :=
    hsPartial_fun_sum Finset.univ _ (fun l _ => hFFd l) k
  rw [hfun, hsPartial_fun_sub hsum1 hsum2 k, hS1, hS2]
  simp only [hL, hR]
  unfold langOp
  rw [Finset.sum_add_distrib]
  ring

/-- `F ↦ 𝓛F` and the Bochner terms are smooth on the chamber for smooth `F`. -/
theorem contDiffOn_bochA (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiffOn ℝ ∞ (bochA P N F) (hsChamber N) := by
  unfold bochA
  exact ContDiffOn.sum fun k _ =>
    (contDiffOn_langOp P N (contDiff_hsPartial hF k)).mul (contDiff_hsPartial hF k).contDiffOn

theorem contDiffOn_bochB (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hF : ContDiff ℝ ∞ F) : ContDiffOn ℝ ∞ (bochB P N F) (hsChamber N) := by
  unfold bochB
  refine ContDiffOn.sum fun k _ => ContDiffOn.sum fun l _ => ?_
  exact ((contDiffOn_hsPartial_of_isOpen (isOpen_hsChamber N) (contDiffOn_rieszH_partial P N k) l).mul
    (contDiff_hsPartial hF k).contDiffOn).mul (contDiff_hsPartial hF l).contDiffOn

theorem continuous_bochC (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hF : ContDiff ℝ ∞ F) : Continuous (bochC P N F) := by
  unfold bochC
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    ((contDiff_hsPartial (contDiff_hsPartial hF k) l).continuous.mul
      (contDiff_hsPartial (contDiff_hsPartial hF k) l).continuous)

theorem hsPartial2_eq_zero_of_open {N : ℕ+} {U : Set (HsEuclidean N)} (hU : IsOpen U)
    {F : HsEuclidean N → ℝ} (hF : ∀ y ∈ U, F y = 0) {x : HsEuclidean N} (hx : x ∈ U)
    (k l : Fin (N : ℕ)) : hsPartial (hsPartial F k) l x = 0 :=
  hsPartial_eq_zero_of_open hU (fun _ hz => hsPartial_eq_zero_of_open hU hF hz k) hx l

theorem bochA_eq_zero_of_open (P : Parameters) (N : ℕ+) {U : Set (HsEuclidean N)}
    (hU : IsOpen U) {F : HsEuclidean N → ℝ} (hF : ∀ y ∈ U, F y = 0) {x : HsEuclidean N}
    (hx : x ∈ U) : bochA P N F x = 0 := by
  unfold bochA
  exact Finset.sum_eq_zero fun k _ => by rw [hsPartial_eq_zero_of_open hU hF hx k, mul_zero]

theorem bochB_eq_zero_of_open (P : Parameters) (N : ℕ+) {U : Set (HsEuclidean N)}
    (hU : IsOpen U) {F : HsEuclidean N → ℝ} (hF : ∀ y ∈ U, F y = 0) {x : HsEuclidean N}
    (hx : x ∈ U) : bochB P N F x = 0 := by
  unfold bochB
  exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => by
    rw [hsPartial_eq_zero_of_open hU hF hx k, mul_zero, zero_mul]

theorem bochC_eq_zero_of_open (P : Parameters) (N : ℕ+) {U : Set (HsEuclidean N)}
    (hU : IsOpen U) {F : HsEuclidean N → ℝ} (hF : ∀ y ∈ U, F y = 0) {x : HsEuclidean N}
    (hx : x ∈ U) : bochC P N F x = 0 := by
  unfold bochC
  exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => by
    rw [hsPartial2_eq_zero_of_open hU hF hx k l, mul_zero]

/-- The pointwise form of the commutator: `∑ₖ ∂ₖF ∂ₖ(𝓛F) = ∑ₖ 𝓛(∂ₖF) ∂ₖF + ∑ₖₗ ∂ₖ∂ₗH ∂ₖF ∂ₗF`
on the chamber. -/
theorem bochA_add_bochB_eq (P : Parameters) (N : ℕ+) {F : HsEuclidean N → ℝ}
    (hF : ContDiff ℝ ∞ F) {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    ∑ k : Fin (N : ℕ), hsPartial F k x * hsPartial (langOp P N F) k x =
      bochA P N F x + bochB P N F x := by
  simp only [hsPartial_langOp P N hF hx, bochA, bochB, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by ring
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The Bochner identity for a test function.** For a smooth periodic test function `f`
supported in the chamber, `∫ (𝓛f)² = ∫ (∑ₖₗ ∂ₖ∂ₗH ∂ₖf ∂ₗf + ∑ₖₗ (∂ₖ∂ₗf)²)`. -/
theorem bochner_identity_test (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (f : HsTestFunction N) :
    ∫ X : Configuration N, langOp P N f.toFun (WithLp.toLp 2 X.val) *
        langOp P N f.toFun (WithLp.toLp 2 X.val) ∂gibbsMeasure P N =
      ∫ X : Configuration N, bochnerForm P N f.toFun (WithLp.toLp 2 X.val)
        ∂gibbsMeasure P N := by
  obtain ⟨δ, hδ, hz⟩ := f.exists_nearBoundary_zero
  have hf : ContDiff ℝ ∞ f.toFun := f.smooth
  have hU := isOpen_nearBoundary N δ
  have hgper : ∀ (k : ℤ) (x : HsEuclidean N),
      langOp P N f.toFun (hsTranslate (k : ℝ) x) = langOp P N f.toFun x :=
    fun k x => langOp_hsTranslate P N f.periodic k x
  have h1 := rieszIBP P N hN f (langOp P N f.toFun) (contDiff_langOp_test P N f) hgper
  simp only [rieszIntegrand_eq P N hf] at h1
  simp only [inner_gradient_eq_sum_hsPartial] at h1
  have hpt : ∫ X : Configuration N, ∑ k : Fin (N : ℕ), hsPartial f.toFun k
        (WithLp.toLp 2 X.val) * hsPartial (langOp P N f.toFun) k (WithLp.toLp 2 X.val)
        ∂gibbsMeasure P N =
      ∫ X : Configuration N, (bochA P N f.toFun (WithLp.toLp 2 X.val) +
        bochB P N f.toFun (WithLp.toLp 2 X.val)) ∂gibbsMeasure P N :=
    integral_congr_ae (Filter.Eventually.of_forall fun X =>
      bochA_add_bochB_eq P N hf (mem_hsChamber_configuration X))
  rw [hpt] at h1
  have hintA := integrable_config_of_vanish P N (contDiffOn_bochA P N hf).continuousOn hδ
    (fun x hx => bochA_eq_zero_of_open P N hU hz hx)
  have hintB := integrable_config_of_vanish P N (contDiffOn_bochB P N hf).continuousOn hδ
    (fun x hx => bochB_eq_zero_of_open P N hU hz hx)
  have hintC := integrable_config_of_vanish P N (continuous_bochC P N hf).continuousOn hδ
    (fun x hx => bochC_eq_zero_of_open P N hU hz hx)
  -- the first Bochner term, one coordinate at a time
  have hk : ∀ k : Fin (N : ℕ), ∫ X : Configuration N,
      langOp P N (hsPartial f.toFun k) (WithLp.toLp 2 X.val) *
        hsPartial f.toFun k (WithLp.toLp 2 X.val) ∂gibbsMeasure P N =
      ∫ X : Configuration N, ∑ l : Fin (N : ℕ),
        hsPartial (hsPartial f.toFun k) l (WithLp.toLp 2 X.val) *
          hsPartial (hsPartial f.toFun k) l (WithLp.toLp 2 X.val) ∂gibbsMeasure P N := by
    intro k
    have h3 := rieszIBP P N hN (hsTestPartial f k) (hsPartial f.toFun k)
      (contDiff_hsPartial hf k) (fun j y => hsPartial_hsTranslate f.periodic k j y)
    simp only [hsTestPartial_toFun] at h3
    simp only [rieszIntegrand_eq P N (contDiff_hsPartial hf k)] at h3
    simp only [inner_gradient_eq_sum_hsPartial] at h3
    exact h3
  have hintAk : ∀ k : Fin (N : ℕ), Integrable (fun X : Configuration N =>
      langOp P N (hsPartial f.toFun k) (WithLp.toLp 2 X.val) *
        hsPartial f.toFun k (WithLp.toLp 2 X.val)) (gibbsMeasure P N) := by
    intro k
    refine integrable_config_of_vanish P N (F := fun x =>
      langOp P N (hsPartial f.toFun k) x * hsPartial f.toFun k x)
      ((contDiffOn_langOp P N (contDiff_hsPartial hf k)).continuousOn.mul
        (contDiff_hsPartial hf k).continuous.continuousOn) hδ ?_
    intro x hx
    simp only [hsPartial_eq_zero_of_open hU hz hx k, mul_zero]
  have hintCk : ∀ k : Fin (N : ℕ), Integrable (fun X : Configuration N =>
      ∑ l : Fin (N : ℕ), hsPartial (hsPartial f.toFun k) l (WithLp.toLp 2 X.val) *
        hsPartial (hsPartial f.toFun k) l (WithLp.toLp 2 X.val)) (gibbsMeasure P N) := by
    intro k
    refine integrable_config_of_vanish P N (F := fun x => ∑ l : Fin (N : ℕ),
      hsPartial (hsPartial f.toFun k) l x * hsPartial (hsPartial f.toFun k) l x)
      (continuous_finsetSum _ fun l _ =>
        ((contDiff_hsPartial (contDiff_hsPartial hf k) l).continuous.mul
          (contDiff_hsPartial (contDiff_hsPartial hf k) l).continuous)).continuousOn hδ ?_
    intro x hx
    exact Finset.sum_eq_zero fun l _ => by
      rw [hsPartial2_eq_zero_of_open hU hz hx k l, mul_zero]
  have hAC : ∫ X : Configuration N, bochA P N f.toFun (WithLp.toLp 2 X.val) ∂gibbsMeasure P N =
      ∫ X : Configuration N, bochC P N f.toFun (WithLp.toLp 2 X.val) ∂gibbsMeasure P N := by
    calc ∫ X : Configuration N, bochA P N f.toFun (WithLp.toLp 2 X.val) ∂gibbsMeasure P N
        = ∑ k : Fin (N : ℕ), ∫ X : Configuration N,
            langOp P N (hsPartial f.toFun k) (WithLp.toLp 2 X.val) *
              hsPartial f.toFun k (WithLp.toLp 2 X.val) ∂gibbsMeasure P N :=
          integral_finsetSum _ fun k _ => hintAk k
      _ = ∑ k : Fin (N : ℕ), ∫ X : Configuration N, ∑ l : Fin (N : ℕ),
            hsPartial (hsPartial f.toFun k) l (WithLp.toLp 2 X.val) *
              hsPartial (hsPartial f.toFun k) l (WithLp.toLp 2 X.val) ∂gibbsMeasure P N :=
          Finset.sum_congr rfl fun k _ => hk k
      _ = ∫ X : Configuration N, ∑ k : Fin (N : ℕ), ∑ l : Fin (N : ℕ),
            hsPartial (hsPartial f.toFun k) l (WithLp.toLp 2 X.val) *
              hsPartial (hsPartial f.toFun k) l (WithLp.toLp 2 X.val) ∂gibbsMeasure P N :=
          (integral_finsetSum _ fun k _ => hintCk k).symm
      _ = ∫ X : Configuration N, bochC P N f.toFun (WithLp.toLp 2 X.val) ∂gibbsMeasure P N := rfl
  rw [integral_add hintA hintB] at h1
  rw [h1]
  simp only [bochnerForm]
  rw [integral_add hintB hintC, hAC, add_comm]


/-! ### Section 3: integrability of gap power sums and the squared strip estimate -/

/-- The squared shifted power sum `(1 + ∑ gap^{-r})²` lies in `L²`, because its fourth power is
dominated by a power sum of gaps. -/
theorem memLp_sq_one_add_gapPowerSum (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    {r : ℝ} (hr : 0 < r) :
    MemLp (fun X : Configuration N => (1 + gapPowerSum r X) ^ 2) 2 (gibbsMeasure P N) := by
  have hm : Measurable (fun X : Configuration N => (1 + gapPowerSum r X) ^ 2) :=
    (measurable_const.add (measurable_gapPowerSum r)).pow_const 2
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have hG : Integrable (fun X : Configuration N => gapPowerSum (r * 4) X) (gibbsMeasure P N) :=
    integrable_gapPowerSum P hPL (mul_pos hr (by norm_num)) N
  refine Integrable.mono' (((integrable_const (1 : ℝ)).add (hG.const_mul (((N : ℕ) : ℝ) ^ 4))).const_mul 8)
    (hm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
  have hS := gapPowerSum_nonneg r X
  have h4 : gapPowerSum r X ^ 4 ≤ ((N : ℕ) : ℝ) ^ 4 * gapPowerSum (r * 4) X := by
    have := gapPowerSum_rpow_le X (r := r) (p := 4) (by norm_num)
    norm_num at this ⊢
    linarith
  have hpoly : ((1 + gapPowerSum r X) ^ 2) ^ 2 ≤ 8 * (1 + gapPowerSum r X ^ 4) := by
    nlinarith [mul_nonneg (sq_nonneg (gapPowerSum r X - 1))
      (by positivity : (0 : ℝ) ≤ 7 * gapPowerSum r X ^ 2 + 10 * gapPowerSum r X + 7)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show ((1 + gapPowerSum r X) ^ 2) ^ 2 ≤ 8 * (1 + ((N : ℕ) : ℝ) ^ 4 * gapPowerSum (r * 4) X)
  nlinarith [hpoly, h4]

/-- A real estimate for the strip constant: `(h⁻¹ + h⁻²)² ≤ 4 h⁻⁴` for `0 < h ≤ 1`. -/
theorem inv_add_sq_le {h : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) :
    (h⁻¹ + h⁻¹ ^ 2) ^ 2 ≤ 4 * (h ^ 4)⁻¹ := by
  have hD1 : 1 ≤ h⁻¹ := one_le_inv_iff₀.mpr ⟨hh0, hh1⟩
  have e : h⁻¹ ^ 2 = (h ^ 2)⁻¹ := by rw [inv_pow]
  have hle : h⁻¹ ≤ h⁻¹ ^ 2 := by nlinarith
  have hD0 : 0 ≤ h⁻¹ + h⁻¹ ^ 2 := by positivity
  have hDle : h⁻¹ + h⁻¹ ^ 2 ≤ 2 * (h ^ 2)⁻¹ := by linarith
  calc (h⁻¹ + h⁻¹ ^ 2) ^ 2 ≤ (2 * (h ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ hD0 hDle 2
    _ = 4 * (h ^ 4)⁻¹ := by field_simp; ring

theorem rpow_ten_eq (u : ℝ) : u ^ (10 : ℝ) = u ^ (10 : ℕ) := by
  exact_mod_cast Real.rpow_natCast u 10

/-- **Squared strip estimate.** If `|E_h| ≤ K (h⁻¹ + h⁻²)² 1_{strip(2h)} W` with `W ∈ L²`, then
`∫ |E_h| → 0`, because the strip has measure of order `h^{10}`. -/
theorem tendsto_integral_strip_sq (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    {W : Configuration N → ℝ} (hW0 : ∀ X, 0 ≤ W X) (hW : MemLp W 2 (gibbsMeasure P N))
    {E : ℝ → Configuration N → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      |E h X| ≤ K * (h⁻¹ + h⁻¹ ^ 2) ^ 2 *
        {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator W X) :
    Tendsto (fun h : ℝ => ∫ X, |E h X| ∂gibbsMeasure P N) (𝓝[>] 0) (𝓝 0) := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  obtain ⟨C, hC, hS⟩ := exists_gibbs_strip_le P hPL (p := 10) (by norm_num) N
  have hM0 : 0 ≤ (∫ X, W X ^ 2 ∂gibbsMeasure P N) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (integral_nonneg fun X => sq_nonneg _) _
  have hc0 : 0 ≤ C * (2 * ((N : ℕ) : ℝ)) ^ 10 := by
    have := (N.pos : 0 < (N : ℕ)); positivity
  have hbound : ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∫ X, |E h X| ∂gibbsMeasure P N ≤
        (4 * K * (∫ X, W X ^ 2 ∂gibbsMeasure P N) ^ (1 / 2 : ℝ) *
          (C * (2 * ((N : ℕ) : ℝ)) ^ 10) ^ (1 / 2 : ℝ)) * h := by
    intro h hh0 hh1
    have hSm : MeasurableSet {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} := measurableSet_strip (2 * h * N)
    -- the strip measure is of order `h^{10}`
    have hmu : (gibbsMeasure P N).real {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} ≤ C * (2 * ((N : ℕ) : ℝ)) ^ 10 * h ^ 10 := by
      have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity)
        (hS (u := 2 * h * N) (by positivity))
      rw [rpow_ten_eq] at hreal
      rw [measureReal_def]
      calc _ ≤ C * (2 * h * ((N : ℕ) : ℝ)) ^ 10 := hreal
        _ = C * (2 * ((N : ℕ) : ℝ)) ^ 10 * h ^ 10 := by ring
    have hsq : (gibbsMeasure P N).real {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N} ^ (1 / 2 : ℝ) ≤
          (C * (2 * ((N : ℕ) : ℝ)) ^ 10) ^ (1 / 2 : ℝ) * h ^ 5 := by
      have h1 := Real.rpow_le_rpow measureReal_nonneg hmu (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have h2 : (C * (2 * ((N : ℕ) : ℝ)) ^ 10 * h ^ 10) ^ (1 / 2 : ℝ) =
          (C * (2 * ((N : ℕ) : ℝ)) ^ 10) ^ (1 / 2 : ℝ) * h ^ 5 := by
        rw [Real.mul_rpow hc0 (by positivity)]
        congr 1
        rw [show (h : ℝ) ^ 10 = (h ^ 5) ^ (2 : ℕ) by ring, ← Real.rpow_natCast (h ^ 5) 2,
          ← Real.rpow_mul (by positivity)]
        norm_num
      linarith
    have hint : Integrable (fun X => K * (h⁻¹ + h⁻¹ ^ 2) ^ 2 *
        {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator W X)
        (gibbsMeasure P N) :=
      ((hW.integrable one_le_two).indicator hSm).const_mul _
    have hmono : ∫ X, |E h X| ∂gibbsMeasure P N ≤ ∫ X, K * (h⁻¹ + h⁻¹ ^ 2) ^ 2 *
        {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator W X
        ∂gibbsMeasure P N :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => abs_nonneg _) hint
        (Filter.Eventually.of_forall fun X => hE h hh0 hh1 X)
    have hstrip := integral_indicator_le_sqrt_mul (gibbsMeasure P N) hSm hW0 hW
    have hD := inv_add_sq_le hh0 hh1
    have hI0 : 0 ≤ ∫ X, {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N}.indicator W X ∂gibbsMeasure P N :=
      integral_nonneg fun X => Set.indicator_nonneg (fun X _ => hW0 X) X
    calc ∫ X, |E h X| ∂gibbsMeasure P N
        ≤ ∫ X, K * (h⁻¹ + h⁻¹ ^ 2) ^ 2 *
            {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N}.indicator W X
            ∂gibbsMeasure P N := hmono
      _ = K * (h⁻¹ + h⁻¹ ^ 2) ^ 2 * ∫ X, {X : Configuration N | ∃ j : Fin (N : ℕ),
            gap X (j : ℕ) ≤ 2 * h * N}.indicator W X ∂gibbsMeasure P N := integral_const_mul _ _
      _ ≤ K * (4 * (h ^ 4)⁻¹) * ((∫ X, W X ^ 2 ∂gibbsMeasure P N) ^ (1 / 2 : ℝ) *
            ((gibbsMeasure P N).real {X : Configuration N | ∃ j : Fin (N : ℕ),
              gap X (j : ℕ) ≤ 2 * h * N}) ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hD hK) hstrip hI0 ?_
          exact mul_nonneg hK (by positivity)
      _ ≤ K * (4 * (h ^ 4)⁻¹) * ((∫ X, W X ^ 2 ∂gibbsMeasure P N) ^ (1 / 2 : ℝ) *
            ((C * (2 * ((N : ℕ) : ℝ)) ^ 10) ^ (1 / 2 : ℝ) * h ^ 5)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hM0)
            (mul_nonneg hK (by positivity))
      _ = (4 * K * (∫ X, W X ^ 2 ∂gibbsMeasure P N) ^ (1 / 2 : ℝ) *
          (C * (2 * ((N : ℕ) : ℝ)) ^ 10) ^ (1 / 2 : ℝ)) * h := by
          have hh4 : h ^ 4 ≠ 0 := by positivity
          field_simp
  refine squeeze_zero' (g := fun h : ℝ => (4 * K * (∫ X, W X ^ 2 ∂gibbsMeasure P N) ^ (1 / 2 : ℝ) *
      (C * (2 * ((N : ℕ) : ℝ)) ^ 10) ^ (1 / 2 : ℝ)) * h)
    (Filter.Eventually.of_forall fun h => integral_nonneg fun X => abs_nonneg _) ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with h hh
    exact hbound h hh.1 hh.2.le
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp))


/-! ### Section 4: the left-hand limit `∫ (𝓛f_h)² → ∫ (𝓛Φ)²` -/

theorem langOp_eq_zero_of_nearBoundary {N : ℕ+} (P : Parameters) (f : HsTestFunction N) {δ : ℝ}
    (hz : ∀ y ∈ nearBoundary N δ, f.toFun y = 0) {y : HsEuclidean N}
    (hy : y ∈ nearBoundary N δ) : langOp P N f.toFun y = 0 := by
  have hU := isOpen_nearBoundary N δ
  have hd1 : ∀ z ∈ nearBoundary N δ, ∀ k : Fin (N : ℕ), hsPartial f.toFun k z = 0 :=
    fun z hz' k => hsPartial_eq_zero_of_open hU hz hz' k
  have hd2 : ∀ z ∈ nearBoundary N δ, ∀ k : Fin (N : ℕ),
      hsPartial (hsPartial f.toFun k) k z = 0 :=
    fun z hz' k => hsPartial_eq_zero_of_open hU (fun w hw => hd1 w hw k) hz' k
  unfold langOp
  simp [hd1 y hy, hd2 y hy]

/-- The square of the Langevin operator of a test function is integrable on the configurations. -/
theorem integrable_langOp_sq (P : Parameters) (N : ℕ+) (f : HsTestFunction N) :
    Integrable (fun X : Configuration N => langOp P N f.toFun (WithLp.toLp 2 X.val) *
      langOp P N f.toFun (WithLp.toLp 2 X.val)) (gibbsMeasure P N) := by
  obtain ⟨δ, hδ, hz⟩ := f.exists_nearBoundary_zero
  have hc := contDiff_langOp_test P N f
  exact integrable_config_of_vanish P N
    (F := fun x => langOp P N f.toFun x * langOp P N f.toFun x)
    (hc.continuous.mul hc.continuous).continuousOn hδ
    (fun x hx => by simp only [langOp_eq_zero_of_nearBoundary P f hz hx, mul_zero])

/-- The Langevin operator of the cutoff `χ_h Φ` splits into `χ_h 𝓛Φ` plus the error term. -/
theorem langOp_cutoff_eq (P : Parameters) (N : ℕ+) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) (h : ℝ) (x : HsEuclidean N) :
    langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) x =
      hsUnitGapCutoff N h x * loopLHS P N ℓ a ψ x + loopError P N ℓ a ψ h x := by
  rw [← langevin_cutoff_eq P N ℓ a ψ hψ h x]
  exact (rieszIntegrand_eq P N
    ((contDiff_hsUnitGapCutoff N h).mul (contDiff_loopHS ℓ a ψ hψ N)) x).symm

theorem lt_hsUnitGap_of_not_strip {N : ℕ+} {h : ℝ} (_hh : 0 < h) (X : Configuration N)
    (hX : ¬ ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N) (j : Fin (N : ℕ)) :
    2 * h < hsUnitGap N j (WithLp.toLp 2 X.val) := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  rw [hsUnitGap_liftConfiguration, lt_div_iff₀ hN]
  simp only [not_exists, not_le] at hX
  linarith [hX j]

theorem hsUnitGapCutoff_eq_one_of_not_strip {N : ℕ+} {h : ℝ} (hh : 0 < h) (X : Configuration N)
    (hX : ¬ ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N) :
    hsUnitGapCutoff N h (WithLp.toLp 2 X.val) = 1 :=
  hsUnitGapCutoff_eq_one_of_le hh fun j => (lt_hsUnitGap_of_not_strip hh X hX j).le

/-- Real algebra: if `|B| ≤ K₀ W` and `|e| ≤ C D W` with `D, W ≥ 1`, then `|(B+e)² − B²| ≤
(2K₀C + C²) D² W²`. -/
theorem abs_sq_add_sub_le (B e K0 C1 W D : ℝ) (hB : |B| ≤ K0 * W)
    (he : |e| ≤ C1 * D * W) (hK0 : 0 ≤ K0) (hC1 : 0 ≤ C1) (hW : 1 ≤ W) (hD : 1 ≤ D) :
    |(B + e) * (B + e) - B * B| ≤ (2 * K0 * C1 + C1 ^ 2) * D ^ 2 * W ^ 2 := by
  have hW0 : 0 ≤ W := by linarith
  have hD0 : 0 ≤ D := by linarith
  have key : (B + e) * (B + e) - B * B = 2 * B * e + e * e := by ring
  rw [key]
  have h2B : |2 * B * e| = 2 * (|B| * |e|) := by
    rw [abs_mul, abs_mul, abs_two]; ring
  have hBe : |B| * |e| ≤ (K0 * W) * (C1 * D * W) :=
    mul_le_mul hB he (abs_nonneg _) (mul_nonneg hK0 hW0)
  have hee : |e * e| ≤ (C1 * D * W) * (C1 * D * W) := by
    rw [abs_mul]; exact mul_le_mul he he (abs_nonneg _) (mul_nonneg (mul_nonneg hC1 hD0) hW0)
  have hDW : D * W ^ 2 ≤ D ^ 2 * W ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg W)
    nlinarith
  calc |2 * B * e + e * e| ≤ |2 * B * e| + |e * e| := abs_add_le _ _
    _ ≤ 2 * ((K0 * W) * (C1 * D * W)) + (C1 * D * W) * (C1 * D * W) := by
        rw [h2B]; linarith
    _ = 2 * K0 * C1 * (D * W ^ 2) + C1 ^ 2 * (D ^ 2 * W ^ 2) := by ring
    _ ≤ 2 * K0 * C1 * (D ^ 2 * W ^ 2) + C1 ^ 2 * (D ^ 2 * W ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hDW (mul_nonneg (mul_nonneg (by norm_num) hK0) hC1)) le_rfl
    _ = (2 * K0 * C1 + C1 ^ 2) * D ^ 2 * W ^ 2 := by ring

/-- **Pointwise cutoff bound.** The difference of the squares of `𝓛f_h` and `𝓛Φ` is bounded by
`K (h⁻¹ + h⁻²)²` times the squared shifted power sum on the strip. -/
theorem loopLHS_cutoff_sq_bound (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      |langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) *
          langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) -
        loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) * loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)| ≤
      K * (h⁻¹ + h⁻¹ ^ 2) ^ 2 * {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N}.indicator (fun X : Configuration N =>
          (1 + gapPowerSum ((parametersExponent P).val + 1) X) ^ 2) X := by
  obtain ⟨K0, hK0, hL⟩ := exists_abs_loopLHS_le P ℓ a ψ hψ N
  obtain ⟨Ke, hKe, hE⟩ := exists_loopError_bound P ℓ a ψ hψ hmean N
  refine ⟨2 * K0 * (K0 + Ke) + (K0 + Ke) ^ 2,
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) (add_nonneg hK0 hKe)) (sq_nonneg _), fun h hh0 hh1 X => ?_⟩
  have hD1 : 1 ≤ h⁻¹ + h⁻¹ ^ 2 := by
    have : 1 ≤ h⁻¹ := one_le_inv_iff₀.mpr ⟨hh0, hh1⟩
    nlinarith
  have hW1 : 1 ≤ 1 + gapPowerSum ((parametersExponent P).val + 1) X := by
    linarith [gapPowerSum_nonneg ((parametersExponent P).val + 1) X]
  by_cases hX : ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N
  · have hmem : X ∈ {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N} := hX
    rw [indicator_of_mem hmem]
    have hEX := hE h hh0 X
    rw [indicator_of_mem hmem] at hEX
    have hLX := hL X
    have hχ0 := hsUnitGapCutoff_nonneg N h (WithLp.toLp 2 X.val)
    have hχ1 := hsUnitGapCutoff_le_one N h (WithLp.toLp 2 X.val)
    have hχabs : |hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1| ≤ 1 :=
      abs_le.mpr ⟨by linarith only [hχ0], by linarith only [hχ1]⟩
    have hA : langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) =
        loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) +
          ((hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) * loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) +
            loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)) := by
      rw [langOp_cutoff_eq P N ℓ a ψ hψ h _]
      ring
    rw [hA]
    have hsplit := abs_add_le ((hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
      loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)) (loopError P N ℓ a ψ h (WithLp.toLp 2 X.val))
    rw [abs_mul] at hsplit
    have t1 : |hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1| * |loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)|
        ≤ K0 * (1 + gapPowerSum ((parametersExponent P).val + 1) X) :=
      (mul_le_mul_of_nonneg_right hχabs (abs_nonneg _)).trans (by rw [one_mul]; exact hLX)
    have hK0D : K0 * (1 + gapPowerSum ((parametersExponent P).val + 1) X) ≤
        K0 * (h⁻¹ + h⁻¹ ^ 2) * (1 + gapPowerSum ((parametersExponent P).val + 1) X) := by
      have := mul_le_mul_of_nonneg_left hD1 hK0
      nlinarith
    have he : |(hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) * loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) +
        loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)| ≤
        (K0 + Ke) * (h⁻¹ + h⁻¹ ^ 2) * (1 + gapPowerSum ((parametersExponent P).val + 1) X) := by
      have hs : |loopError P N ℓ a ψ h (WithLp.toLp 2 X.val)| ≤
          Ke * (h⁻¹ + h⁻¹ ^ 2) * (1 + gapPowerSum ((parametersExponent P).val + 1) X) := hEX
      nlinarith
    exact abs_sq_add_sub_le _ _ K0 (K0 + Ke) _ _ hLX he hK0 (by linarith) hW1 hD1
  · have hmem : X ∉ {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N} := hX
    rw [indicator_of_notMem hmem, mul_zero, abs_nonpos_iff]
    have hEX := hE h hh0 X
    rw [indicator_of_notMem hmem, mul_zero, abs_nonpos_iff] at hEX
    rw [langOp_cutoff_eq P N ℓ a ψ hψ h _, hsUnitGapCutoff_eq_one_of_not_strip hh0 X hX,
      hEX, one_mul, add_zero]
    ring

/-- **The left-hand limit.** `∫ (𝓛f_h)² → ∫ (𝓛Φ)²` as `h → 0⁺`. -/
theorem tendsto_langOp_sq (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    Tendsto (fun h : ℝ => ∫ X : Configuration N,
        langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) *
          langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val)
          ∂gibbsMeasure P N) (𝓝[>] 0)
      (𝓝 (∫ X : Configuration N, loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) *
        loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) ∂gibbsMeasure P N)) := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  obtain ⟨K, hK, hbd⟩ := loopLHS_cutoff_sq_bound P ℓ a ψ hψ hmean N
  obtain ⟨K0, hK0, hL⟩ := exists_abs_loopLHS_le P ℓ a ψ hψ N
  have hs : 0 < (parametersExponent P).val + 1 := by
    have := (parametersExponent P).property.1
    linarith
  have hW := memLp_sq_one_add_gapPowerSum P hPL N hs
  have hstrip := tendsto_integral_strip_sq P hPL N (fun X => sq_nonneg _) hW hK
    (fun h hh0 hh1 X => hbd h hh0 hh1 X)
  have hLint : Integrable (fun X : Configuration N => loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) *
      loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)) (gibbsMeasure P N) := by
    refine Integrable.mono' ((hW.integrable one_le_two).const_mul (K0 ^ 2))
      ((continuous_loopLHS_config P ℓ a ψ hψ).mul
        (continuous_loopLHS_config P ℓ a ψ hψ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    have h0 : 0 ≤ K0 * (1 + gapPowerSum ((parametersExponent P).val + 1) X) :=
      mul_nonneg hK0 (by linarith [gapPowerSum_nonneg ((parametersExponent P).val + 1) X])
    calc ‖loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) * loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)‖
        = |loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)| *
            |loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (K0 * (1 + gapPowerSum ((parametersExponent P).val + 1) X)) *
            (K0 * (1 + gapPowerSum ((parametersExponent P).val + 1) X)) :=
          mul_le_mul (hL X) (hL X) (abs_nonneg _) h0
      _ = K0 ^ 2 * (1 + gapPowerSum ((parametersExponent P).val + 1) X) ^ 2 := by ring
  have hAint : ∀ h : ℝ, 0 < h → Integrable (fun X : Configuration N =>
      langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) *
        langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val))
        (gibbsMeasure P N) := fun h hh =>
    integrable_langOp_sq P N (hsUnitGapCutoffTest hh (loopHS ℓ a ψ N)
      (contDiff_loopHS ℓ a ψ hψ N) (loopHS_periodic ℓ a ψ hψ hmean N))
  have hlim : Tendsto (fun h : ℝ => (∫ X : Configuration N,
        langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) *
          langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val)
          ∂gibbsMeasure P N) - ∫ X : Configuration N,
        loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) * loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)
          ∂gibbsMeasure P N) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hstrip
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [← integral_sub (hAint h hh) hLint, Real.norm_eq_abs]
    exact abs_integral_le_integral_abs
  have := hlim.add_const (∫ X : Configuration N,
    loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) * loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val)
      ∂gibbsMeasure P N)
  simp only [sub_add_cancel, zero_add] at this
  exact this


/-! ### Section 5: the right-hand limit `∫ bochnerForm(f_h) → ∫ bochnerForm Φ` -/

/-- Real algebra: `|F₁F₂ − p₁p₂| ≤ (2Mc + c²) D²` when `|Fᵢ − pᵢ| ≤ cD` and `|pᵢ| ≤ M`, `D ≥ 1`. -/
theorem abs_mul_sub_mul_le (F1 F2 p1 p2 M c D : ℝ) (hM : 0 ≤ M) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (h1 : |F1 - p1| ≤ c * D) (h2 : |F2 - p2| ≤ c * D) (hp1 : |p1| ≤ M) (hp2 : |p2| ≤ M) :
    |F1 * F2 - p1 * p2| ≤ (2 * M * c + c ^ 2) * D ^ 2 := by
  have key : F1 * F2 - p1 * p2 = p1 * (F2 - p2) + (F1 - p1) * p2 + (F1 - p1) * (F2 - p2) := by
    ring
  have hcD : 0 ≤ c * D := mul_nonneg hc (by linarith)
  have t1 : |p1 * (F2 - p2)| ≤ M * (c * D) := by
    rw [abs_mul]; exact mul_le_mul hp1 h2 (abs_nonneg _) hM
  have t2 : |(F1 - p1) * p2| ≤ (c * D) * M := by
    rw [abs_mul]; exact mul_le_mul h1 hp2 (abs_nonneg _) hcD
  have t3 : |(F1 - p1) * (F2 - p2)| ≤ (c * D) * (c * D) := by
    rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) hcD
  have s1 := abs_add_le (p1 * (F2 - p2)) ((F1 - p1) * p2)
  have s2 := abs_add_le (p1 * (F2 - p2) + (F1 - p1) * p2) ((F1 - p1) * (F2 - p2))
  have hD2 : D ≤ D ^ 2 := by nlinarith
  have hMc : 0 ≤ M * c := mul_nonneg hM hc
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_left hD2 hMc]

/-- The second partial of a product `χ Φ`, by the product rule twice. -/
theorem hsPartial_hsPartial_mul_eq {N : ℕ+} {χ Φ : HsEuclidean N → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hΦ : ContDiff ℝ ∞ Φ) (k l : Fin (N : ℕ)) (x : HsEuclidean N) :
    hsPartial (hsPartial (fun y => χ y * Φ y) k) l x =
      hsPartial (hsPartial χ k) l x * Φ x + hsPartial χ k x * hsPartial Φ l x +
        hsPartial χ l x * hsPartial Φ k x + χ x * hsPartial (hsPartial Φ k) l x := by
  have dχ : ∀ j : Fin (N : ℕ), Differentiable ℝ (hsPartial χ j) :=
    fun j => (contDiff_hsPartial hχ j).differentiable (by simp)
  have dΦ : ∀ j : Fin (N : ℕ), Differentiable ℝ (hsPartial Φ j) :=
    fun j => (contDiff_hsPartial hΦ j).differentiable (by simp)
  have e1 : hsPartial (fun y => χ y * Φ y) k =
      fun y => hsPartial χ k y * Φ y + χ y * hsPartial Φ k y := by
    funext y
    rw [hsPartial_mul (hχ.differentiable (by simp) y) (hΦ.differentiable (by simp) y) k]
  rw [e1, hsPartial_add
    (show DifferentiableAt ℝ (fun y => hsPartial χ k y * Φ y) x from
      ((dχ k) x).mul (hΦ.differentiable (by simp) x))
    (show DifferentiableAt ℝ (fun y => χ y * hsPartial Φ k y) x from
      (hχ.differentiable (by simp) x).mul ((dΦ k) x)) l,
    hsPartial_mul ((dχ k) x) (hΦ.differentiable (by simp) x) l,
    hsPartial_mul (hχ.differentiable (by simp) x) ((dΦ k) x) l]
  ring

/-- The Hessian of the Riesz Hamiltonian on a configuration is `β` times the Hessian sum. -/
theorem hsPartial_hsPartial_rieszH_config (P : Parameters) (N : ℕ+) (X : Configuration N)
    (k l : Fin (N : ℕ)) :
    hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val) =
      P.val.1 * hessianSum (parametersExponent P).val (N : ℕ) k l X.val := by
  unfold rieszH
  rw [hsPartial_hsPartial_hsPairExpression_of_mem_chamber N P.val.1 P.property.1
    (parametersExponent P) (mem_hsChamber_configuration X) k l]
  congr 1
  exact partialDeriv_partialDeriv_energyLift_eq' (parametersExponent P) X.val
    (fun i j hij => coe_sub_ne_zero X hij) k l

/-- Uniform bounds on the field potential and its first and second partial derivatives. -/
theorem loopHS_partial_bounds (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    ∃ M0 M1 M2 : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧ (∀ x : HsEuclidean N, |loopHS ℓ a ψ N x| ≤ M0) ∧
      (∀ (k : Fin (N : ℕ)) (x : HsEuclidean N), |hsPartial (loopHS ℓ a ψ N) k x| ≤ M1) ∧
      (∀ (k l : Fin (N : ℕ)) (x : HsEuclidean N),
        |hsPartial (hsPartial (loopHS ℓ a ψ N) k) l x| ≤ M2) := by
  obtain ⟨M0, hM0, hΦ⟩ := exists_abs_loopHS_le ℓ a ψ hψ hmean N
  obtain ⟨Mψ, hMψ0, hMψ⟩ := exists_abs_le_of_continuous_periodic (inv_pos.mpr ℓ.property.1)
    hψ.continuous ψ.property.1
  obtain ⟨Mq, hMq0, hMq⟩ := exists_abs_deriv_le_of_smooth_periodic (inv_pos.mpr ℓ.property.1)
    hψ ψ.property.1
  refine ⟨M0, |a| * ℓ.val * Mψ, |a| * Mq, hM0,
    mul_nonneg (mul_nonneg (abs_nonneg a) ℓ.property.1.le) hMψ0, mul_nonneg (abs_nonneg a) hMq0,
    hΦ, fun k x => ?_, fun k l x => ?_⟩
  · rw [hsPartial_loopHS ℓ a ψ hψ N k x]
    exact abs_partialDeriv_loopScalePotential_le ℓ a ψ hMψ k _
  · rw [hsPartial_hsPartial_loopHS ℓ a ψ hψ N k l x]
    exact abs_partialDeriv_partialDeriv_loopScalePotential_le ℓ a ψ hψ hMq k l _



/-- A difference of finite sums is bounded by the sum of termwise bounds. -/
theorem abs_sum_sub_sum_le {ι : Type*} (s : Finset ι) (A B b : ι → ℝ)
    (h : ∀ i ∈ s, |A i - B i| ≤ b i) : |∑ i ∈ s, A i - ∑ i ∈ s, B i| ≤ ∑ i ∈ s, b i := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)

/-- **Pointwise cutoff bound for the Bochner form.** On the strip the difference of the Bochner
forms of `χ_h Φ` and `Φ` is bounded by `K (h⁻¹ + h⁻²)²` times `1 + gapPowerSum(s+2)`. Off the
strip the two forms agree. -/
theorem bochnerForm_cutoff_bound (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ X : Configuration N,
      |bochnerForm P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) -
        bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)| ≤
      K * (h⁻¹ + h⁻¹ ^ 2) ^ 2 * {X : Configuration N | ∃ j : Fin (N : ℕ),
        gap X (j : ℕ) ≤ 2 * h * N}.indicator (fun X : Configuration N =>
          1 + gapPowerSum ((parametersExponent P).val + 2) X) X := by
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, hΦ0, hΦ1, hΦ2⟩ := loopHS_partial_bounds ℓ a ψ hψ hmean N
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_loopStep
  obtain ⟨CH, hCH0, hCH⟩ := exists_hessianSum_le (parametersExponent P) N
  have hβ : 0 ≤ P.val.1 := P.property.1.le
  have hNr : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hΦs : ContDiff ℝ ∞ (loopHS ℓ a ψ N) := contDiff_loopHS ℓ a ψ hψ N
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = 2 * N * C * M0 + M1 := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c : ℝ, c = N * (4 * C + 4 * N * C ^ 2) := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = c3 * M0 + 4 * N * C * M1 + M2 := ⟨_, rfl⟩
  obtain ⟨BH, hBH⟩ : ∃ c : ℝ, c = P.val.1 * CH := ⟨_, rfl⟩
  obtain ⟨KB, hKB⟩ : ∃ c : ℝ, c = BH * (2 * M1 * c1 + c1 ^ 2) := ⟨_, rfl⟩
  obtain ⟨KC, hKC⟩ : ∃ c : ℝ, c = 2 * M2 * c2 + c2 ^ 2 := ⟨_, rfl⟩
  have hc1_0 : 0 ≤ c1 := by
    rw [hc1]; exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hNr) hC0) hM0) hM1
  have hc3_0 : 0 ≤ c3 := by
    rw [hc3]; exact mul_nonneg hNr (add_nonneg (mul_nonneg (by norm_num) hC0)
      (mul_nonneg (mul_nonneg (by norm_num) hNr) (sq_nonneg C)))
  have hc2_0 : 0 ≤ c2 := by
    rw [hc2]; exact add_nonneg (add_nonneg (mul_nonneg hc3_0 hM0)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hNr) hC0) hM1)) hM2
  have hBH0 : 0 ≤ BH := by rw [hBH]; exact mul_nonneg hβ hCH0
  have hKB0 : 0 ≤ KB := by
    rw [hKB]; exact mul_nonneg hBH0
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1) hc1_0) (sq_nonneg _))
  have hKC0 : 0 ≤ KC := by
    rw [hKC]; exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM2) hc2_0) (sq_nonneg _)
  refine ⟨max ((N : ℝ) ^ 2 * (KB + KC)) 0, le_max_right _ _, fun h hh0 hh1 X => ?_⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = h⁻¹ + h⁻¹ ^ 2 := ⟨_, rfl⟩
  rw [← hD]
  have hinv0 : 0 ≤ h⁻¹ := inv_nonneg.mpr hh0.le
  have hD1 : 1 ≤ D := by
    have : 1 ≤ h⁻¹ := one_le_inv_iff₀.mpr ⟨hh0, hh1⟩
    rw [hD]; linarith only [this, sq_nonneg h⁻¹]
  have hinvD : h⁻¹ ≤ D := by rw [hD]; linarith only [sq_nonneg h⁻¹]
  have hinv2D : (h ^ 2)⁻¹ ≤ D := by
    rw [← inv_pow, hD]; linarith only [sq_nonneg h⁻¹, hinv0]
  have hC' : ∀ t : ℝ, |deriv loopStep t| ≤ C := fun t => (hC t).1
  have hχd : Differentiable ℝ (hsUnitGapCutoff N h) :=
    (contDiff_hsUnitGapCutoff N h).differentiable (by simp)
  have hΦd : Differentiable ℝ (loopHS ℓ a ψ N) := hΦs.differentiable (by simp)
  by_cases hX : ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N
  · -- the strip: the bound is the one of the Bochner terms
    have hmem : X ∈ {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N} := hX
    rw [indicator_of_mem hmem]
    dsimp only
    have hS := gapPowerSum_nonneg ((parametersExponent P).val + 2) X
    have hχk : ∀ k : Fin (N : ℕ),
        |hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val)| ≤ N * (2 * C) * D := by
      intro k
      refine (abs_hsPartial_hsUnitGapCutoff_le N hC' hh0 k _).trans ?_
      have e : (N : ℝ) * (2 * C / h) = N * (2 * C) * h⁻¹ := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hinvD (mul_nonneg hNr (mul_nonneg (by norm_num) hC0))
    have hχkl : ∀ k l : Fin (N : ℕ),
        |hsPartial (hsPartial (hsUnitGapCutoff N h) k) l (WithLp.toLp 2 X.val)| ≤ c3 * D := by
      intro k l
      refine (abs_hsPartial_hsPartial_hsUnitGapCutoff_le N hC hh0 k l _).trans ?_
      have e : (N : ℝ) * ((4 * C + 4 * (N : ℝ) * C ^ 2) / h ^ 2) = c3 * (h ^ 2)⁻¹ := by
        rw [hc3]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hinv2D hc3_0
    have hχ0 : 0 ≤ hsUnitGapCutoff N h (WithLp.toLp 2 X.val) :=
      hsUnitGapCutoff_nonneg N h _
    have hχ1' : hsUnitGapCutoff N h (WithLp.toLp 2 X.val) ≤ 1 := hsUnitGapCutoff_le_one N h _
    have hχ1 : |hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    -- the first partials of `χ Φ` minus those of `Φ`
    have hdk : ∀ k : Fin (N : ℕ),
        |hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k (WithLp.toLp 2 X.val) -
          hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val)| ≤ c1 * D := by
      intro k
      rw [hsPartial_mul (hχd (WithLp.toLp 2 X.val)) (hΦd (WithLp.toLp 2 X.val)) k]
      have e : hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
          loopHS ℓ a ψ N (WithLp.toLp 2 X.val) +
          hsUnitGapCutoff N h (WithLp.toLp 2 X.val) *
            hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) -
          hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) =
          hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) * loopHS ℓ a ψ N (WithLp.toLp 2 X.val) +
            (hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
              hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) := by ring
      rw [e]
      have s1 := abs_add_le (hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
        loopHS ℓ a ψ N (WithLp.toLp 2 X.val)) ((hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
        hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val))
      have b1 : |hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
          loopHS ℓ a ψ N (WithLp.toLp 2 X.val)| ≤ N * (2 * C) * D * M0 := by
        rw [abs_mul]
        exact mul_le_mul (hχk k) (hΦ0 _) (abs_nonneg _)
          (mul_nonneg (mul_nonneg hNr (mul_nonneg (by norm_num) hC0)) (by linarith only [hD1]))
      have b2 : |(hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
          hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val)| ≤ 1 * M1 := by
        rw [abs_mul]; exact mul_le_mul hχ1 (hΦ1 k _) (abs_nonneg _) zero_le_one
      have hM1D : M1 * 1 ≤ M1 * D := mul_le_mul_of_nonneg_left hD1 hM1
      have hfin : N * (2 * C) * D * M0 + 1 * M1 ≤ c1 * D := by
        rw [hc1]; linarith only [hM1D]
      linarith
    -- the second partials of `χ Φ` minus those of `Φ`
    have hdkl : ∀ k l : Fin (N : ℕ),
        |hsPartial (hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k)
            l (WithLp.toLp 2 X.val) -
          hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val)| ≤ c2 * D := by
      intro k l
      rw [hsPartial_hsPartial_mul_eq (contDiff_hsUnitGapCutoff N h) hΦs k l (WithLp.toLp 2 X.val)]
      have e : hsPartial (hsPartial (hsUnitGapCutoff N h) k) l (WithLp.toLp 2 X.val) *
          loopHS ℓ a ψ N (WithLp.toLp 2 X.val) +
          hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
            hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val) +
          hsPartial (hsUnitGapCutoff N h) l (WithLp.toLp 2 X.val) *
            hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) +
          hsUnitGapCutoff N h (WithLp.toLp 2 X.val) *
            hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val) -
          hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val) =
          hsPartial (hsPartial (hsUnitGapCutoff N h) k) l (WithLp.toLp 2 X.val) *
              loopHS ℓ a ψ N (WithLp.toLp 2 X.val) +
            hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
              hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val) +
            hsPartial (hsUnitGapCutoff N h) l (WithLp.toLp 2 X.val) *
              hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) +
            (hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
              hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val) := by ring
      rw [e]
      have s1 := abs_add_le (hsPartial (hsPartial (hsUnitGapCutoff N h) k) l (WithLp.toLp 2 X.val) *
        loopHS ℓ a ψ N (WithLp.toLp 2 X.val) + hsPartial (hsUnitGapCutoff N h) k
          (WithLp.toLp 2 X.val) * hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val) +
        hsPartial (hsUnitGapCutoff N h) l (WithLp.toLp 2 X.val) *
          hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val))
        ((hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
          hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val))
      have s2 := abs_add_le (hsPartial (hsPartial (hsUnitGapCutoff N h) k) l (WithLp.toLp 2 X.val) *
        loopHS ℓ a ψ N (WithLp.toLp 2 X.val) + hsPartial (hsUnitGapCutoff N h) k
          (WithLp.toLp 2 X.val) * hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val))
        (hsPartial (hsUnitGapCutoff N h) l (WithLp.toLp 2 X.val) *
          hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val))
      have s3 := abs_add_le (hsPartial (hsPartial (hsUnitGapCutoff N h) k) l (WithLp.toLp 2 X.val) *
        loopHS ℓ a ψ N (WithLp.toLp 2 X.val)) (hsPartial (hsUnitGapCutoff N h) k
          (WithLp.toLp 2 X.val) * hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val))
      have b1 : |hsPartial (hsPartial (hsUnitGapCutoff N h) k) l (WithLp.toLp 2 X.val) *
          loopHS ℓ a ψ N (WithLp.toLp 2 X.val)| ≤ c3 * D * M0 := by
        rw [abs_mul]; exact mul_le_mul (hχkl k l) (hΦ0 _) (abs_nonneg _) (by positivity)
      have b2 : |hsPartial (hsUnitGapCutoff N h) k (WithLp.toLp 2 X.val) *
          hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val)| ≤ N * (2 * C) * D * M1 := by
        rw [abs_mul]; exact mul_le_mul (hχk k) (hΦ1 l _) (abs_nonneg _)
          (mul_nonneg (mul_nonneg hNr (mul_nonneg (by norm_num) hC0)) (by linarith only [hD1]))
      have b3 : |hsPartial (hsUnitGapCutoff N h) l (WithLp.toLp 2 X.val) *
          hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val)| ≤ N * (2 * C) * D * M1 := by
        rw [abs_mul]; exact mul_le_mul (hχk l) (hΦ1 k _) (abs_nonneg _)
          (mul_nonneg (mul_nonneg hNr (mul_nonneg (by norm_num) hC0)) (by linarith only [hD1]))
      have b4 : |(hsUnitGapCutoff N h (WithLp.toLp 2 X.val) - 1) *
          hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val)| ≤ 1 * M2 := by
        rw [abs_mul]; exact mul_le_mul hχ1 (hΦ2 k l _) (abs_nonneg _) zero_le_one
      have hM2D : M2 * 1 ≤ M2 * D := mul_le_mul_of_nonneg_left hD1 hM2
      have hfin : c3 * D * M0 + N * (2 * C) * D * M1 + N * (2 * C) * D * M1 + 1 * M2 ≤ c2 * D := by
        rw [hc2]; linarith only [hM2D]
      linarith
    -- the Hessian of the Riesz Hamiltonian
    have hH : ∀ k l : Fin (N : ℕ),
        |hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val)| ≤
          BH * gapPowerSum ((parametersExponent P).val + 2) X := by
      intro k l
      rw [hsPartial_hsPartial_rieszH_config P N X k l, abs_mul, abs_of_nonneg hβ, hBH]
      calc P.val.1 * |hessianSum (parametersExponent P).val (N : ℕ) k l X.val|
          ≤ P.val.1 * (CH * gapPowerSum ((parametersExponent P).val + 2) X) :=
            mul_le_mul_of_nonneg_left (hCH X k l) hβ
        _ = P.val.1 * CH * gapPowerSum ((parametersExponent P).val + 2) X := by ring
    -- the Bochner terms
    have hBpair : ∀ k l : Fin (N : ℕ),
        |hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val) *
            hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k (WithLp.toLp 2 X.val) *
            hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) l (WithLp.toLp 2 X.val) -
          hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val) *
            hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) *
            hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val)| ≤
          KB * D ^ 2 * (1 + gapPowerSum ((parametersExponent P).val + 2) X) := by
      intro k l
      have e : hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val) *
            hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k (WithLp.toLp 2 X.val) *
            hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) l (WithLp.toLp 2 X.val) -
          hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val) *
            hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) *
            hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val) =
          hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val) *
            (hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k (WithLp.toLp 2 X.val) *
              hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) l (WithLp.toLp 2 X.val) -
            hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) *
              hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val)) := by ring
      rw [e, abs_mul]
      have hab := abs_mul_sub_mul_le _ _ _ _ M1 c1 D hM1 hc1_0 hD1 (hdk k) (hdk l) (hΦ1 k _)
        (hΦ1 l _)
      have hS := gapPowerSum_nonneg ((parametersExponent P).val + 2) X
      calc |hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val)| *
            |hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k (WithLp.toLp 2 X.val) *
              hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) l (WithLp.toLp 2 X.val) -
            hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) *
              hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val)|
          ≤ (BH * gapPowerSum ((parametersExponent P).val + 2) X) *
              ((2 * M1 * c1 + c1 ^ 2) * D ^ 2) :=
            mul_le_mul (hH k l) hab (abs_nonneg _) (mul_nonneg hBH0 hS)
        _ = KB * D ^ 2 * gapPowerSum ((parametersExponent P).val + 2) X := by rw [hKB]; ring
        _ ≤ KB * D ^ 2 * (1 + gapPowerSum ((parametersExponent P).val + 2) X) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (mul_nonneg hKB0 (sq_nonneg D))
    have hCpair : ∀ k l : Fin (N : ℕ),
        |hsPartial (hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k) l
            (WithLp.toLp 2 X.val) *
          hsPartial (hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k) l
            (WithLp.toLp 2 X.val) -
          hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val) *
          hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val)| ≤ KC * D ^ 2 := by
      intro k l
      rw [hKC]
      exact abs_mul_sub_mul_le _ _ _ _ M2 c2 D hM2 hc2_0 hD1 (hdkl k l) (hdkl k l)
        (hΦ2 k l _) (hΦ2 k l _)
    have hBsum : |bochB P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) -
        bochB P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)| ≤
        (N : ℝ) ^ 2 * (KB * D ^ 2 * (1 + gapPowerSum ((parametersExponent P).val + 2) X)) := by
      unfold bochB
      refine (abs_sum_sub_sum_le _ _ _ _ fun k _ =>
        abs_sum_sub_sum_le _ _ _ _ fun l _ => hBpair k l).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_of_eq (by ring)
    have hCsum : |bochC P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) -
        bochC P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)| ≤ (N : ℝ) ^ 2 * (KC * D ^ 2) := by
      unfold bochC
      refine (abs_sum_sub_sum_le _ _ _ _ fun k _ =>
        abs_sum_sub_sum_le _ _ _ _ fun l _ => hCpair k l).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact le_of_eq (by ring)
    have hsplit : bochnerForm P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y)
          (WithLp.toLp 2 X.val) - bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val) =
        (bochB P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) -
          bochB P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)) +
        (bochC P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) -
          bochC P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)) := by
      unfold bochnerForm; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ((add_le_add hBsum hCsum).trans ?_)
    have hW1 : 1 ≤ 1 + gapPowerSum ((parametersExponent P).val + 2) X :=
      le_add_of_nonneg_right hS
    have hD2 : 0 ≤ D ^ 2 := sq_nonneg D
    have hm : (N : ℝ) ^ 2 * (KB + KC) ≤ max ((N : ℝ) ^ 2 * (KB + KC)) 0 := le_max_left _ _
    have h1 : (N : ℝ) ^ 2 * (KC * D ^ 2) ≤
        (N : ℝ) ^ 2 * (KC * D ^ 2) * (1 + gapPowerSum ((parametersExponent P).val + 2) X) :=
      le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (mul_nonneg hKC0 hD2)) hW1
    have h2 := mul_le_mul_of_nonneg_right hm (mul_nonneg hD2
      (by linarith only [hW1] : (0 : ℝ) ≤ 1 + gapPowerSum ((parametersExponent P).val + 2) X))
    linarith only [h1, h2]
  · -- off the strip: the cutoff is `1` and its derivatives vanish, so the two forms agree
    have hmem : X ∉ {X : Configuration N | ∃ j : Fin (N : ℕ), gap X (j : ℕ) ≤ 2 * h * N} := hX
    rw [indicator_of_notMem hmem, mul_zero, abs_nonpos_iff]
    have hx' : ∀ j : Fin (N : ℕ), 2 * h < hsUnitGap N j (WithLp.toLp 2 X.val) :=
      lt_hsUnitGap_of_not_strip hh0 X hX
    have hχ1' := hsUnitGapCutoff_eq_one_of_not_strip hh0 X hX
    have hk : ∀ k : Fin (N : ℕ),
        hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k (WithLp.toLp 2 X.val) =
          hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) := by
      intro k
      rw [hsPartial_mul (hχd (WithLp.toLp 2 X.val)) (hΦd (WithLp.toLp 2 X.val)) k,
        hsPartial_hsUnitGapCutoff_eq_zero hh0 hx' k, hχ1']
      ring
    have hkl : ∀ k l : Fin (N : ℕ),
        hsPartial (hsPartial (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) k) l
            (WithLp.toLp 2 X.val) =
          hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val) := by
      intro k l
      rw [hsPartial_hsPartial_mul_eq (contDiff_hsUnitGapCutoff N h) hΦs k l (WithLp.toLp 2 X.val),
        hsPartial_hsPartial_hsUnitGapCutoff_eq_zero hh0 hx' k l,
        hsPartial_hsUnitGapCutoff_eq_zero hh0 hx' k, hsPartial_hsUnitGapCutoff_eq_zero hh0 hx' l, hχ1']
      ring
    have hfun : bochnerForm P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y)
          (WithLp.toLp 2 X.val) = bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val) := by
      unfold bochnerForm bochB bochC
      simp only [hk, hkl]
    rw [hfun, sub_self]



/-! ### Section 6: the right-hand limit and the identification of the limit -/

theorem hsPartial_const_one {N : ℕ+} (k : Fin (N : ℕ)) (x : HsEuclidean N) :
    hsPartial (fun _ : HsEuclidean N => (1 : ℝ)) k x = 0 := by
  unfold hsPartial; simp

theorem integrable_bochnerForm_test (P : Parameters) (N : ℕ+) (f : HsTestFunction N) :
    Integrable (fun X : Configuration N => bochnerForm P N f.toFun (WithLp.toLp 2 X.val))
      (gibbsMeasure P N) := by
  obtain ⟨δ, hδ, hz⟩ := f.exists_nearBoundary_zero
  have hU := isOpen_nearBoundary N δ
  exact integrable_config_of_vanish P N
    (F := fun x => bochB P N f.toFun x + bochC P N f.toFun x)
    ((contDiffOn_bochB P N f.smooth).continuousOn.add (continuous_bochC P N f.smooth).continuousOn)
    hδ (fun x hx => by
      simp only [bochB_eq_zero_of_open P N hU hz hx, bochC_eq_zero_of_open P N hU hz hx, zero_add])

/-- A sum over pairs of terms bounded by `c` is bounded by `N² c`. -/
theorem abs_sum_pair_le (N : ℕ+) (T : Fin (N : ℕ) → Fin (N : ℕ) → ℝ) (c : ℝ)
    (h : ∀ k l, |T k l| ≤ c) : |∑ k, ∑ l, T k l| ≤ (N : ℝ) ^ 2 * c := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => h k l)).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- The Bochner form of the field potential grows at most like `1 + gapPowerSum(s+2)`. -/
theorem abs_bochnerForm_loopHS_le (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : Configuration N,
      |bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)| ≤
        K * (1 + gapPowerSum ((parametersExponent P).val + 2) X) := by
  obtain ⟨M0, M1, M2, hM0, hM1, hM2, -, hΦ1, hΦ2⟩ := loopHS_partial_bounds ℓ a ψ hψ hmean N
  obtain ⟨CH, hCH0, hCH⟩ := exists_hessianSum_le (parametersExponent P) N
  have hβ : 0 ≤ P.val.1 := P.property.1.le
  obtain ⟨X0, hX0⟩ : ∃ c : ℝ, c = P.val.1 * CH * M1 ^ 2 := ⟨_, rfl⟩
  obtain ⟨Y0, hY0⟩ : ∃ c : ℝ, c = M2 ^ 2 := ⟨_, rfl⟩
  have hX00 : 0 ≤ X0 := by rw [hX0]; exact mul_nonneg (mul_nonneg hβ hCH0) (sq_nonneg _)
  have hY00 : 0 ≤ Y0 := by rw [hY0]; exact sq_nonneg _
  refine ⟨(N : ℝ) ^ 2 * (X0 + Y0), mul_nonneg (sq_nonneg _) (add_nonneg hX00 hY00),
    fun X => ?_⟩
  have hS := gapPowerSum_nonneg ((parametersExponent P).val + 2) X
  have hH : ∀ k l : Fin (N : ℕ), |hsPartial (hsPartial (rieszH P N) k) l
      (WithLp.toLp 2 X.val)| ≤ P.val.1 * CH * gapPowerSum ((parametersExponent P).val + 2) X := by
    intro k l
    rw [hsPartial_hsPartial_rieszH_config P N X k l, abs_mul, abs_of_nonneg hβ]
    calc P.val.1 * |hessianSum (parametersExponent P).val (N : ℕ) k l X.val|
        ≤ P.val.1 * (CH * gapPowerSum ((parametersExponent P).val + 2) X) :=
          mul_le_mul_of_nonneg_left (hCH X k l) hβ
      _ = P.val.1 * CH * gapPowerSum ((parametersExponent P).val + 2) X := by ring
  have hpair : ∀ k l : Fin (N : ℕ), |hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val) *
      hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) *
        hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val) +
      hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val) *
        hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val)| ≤
      X0 * gapPowerSum ((parametersExponent P).val + 2) X + Y0 := by
    intro k l
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, hX0]
      exact mul_le_mul (mul_le_mul (hH k l) (hΦ1 k _) (abs_nonneg _)
        (mul_nonneg (mul_nonneg hβ hCH0) hS)) (hΦ1 l _) (abs_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg hβ hCH0) hS) hM1)
        |>.trans (le_of_eq (by ring))
    · rw [abs_mul, hY0]
      exact (mul_le_mul (hΦ2 k l _) (hΦ2 k l _) (abs_nonneg _) hM2).trans (le_of_eq (by ring))
  have hfin := abs_sum_pair_le N _ _ hpair
  have hsum : bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val) =
      ∑ k, ∑ l, (hsPartial (hsPartial (rieszH P N) k) l (WithLp.toLp 2 X.val) *
        hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) *
          hsPartial (loopHS ℓ a ψ N) l (WithLp.toLp 2 X.val) +
        hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val) *
          hsPartial (hsPartial (loopHS ℓ a ψ N) k) l (WithLp.toLp 2 X.val)) := by
    simp only [bochnerForm, bochB, bochC, Finset.sum_add_distrib]
  rw [hsum]
  refine hfin.trans ?_
  have hY : 0 ≤ Y0 * gapPowerSum ((parametersExponent P).val + 2) X :=
    mul_nonneg hY00 hS
  have hXS : 0 ≤ X0 + Y0 * gapPowerSum ((parametersExponent P).val + 2) X := by linarith only [hX00, hY]
  have key : X0 * gapPowerSum ((parametersExponent P).val + 2) X + Y0 ≤
      (X0 + Y0) * (1 + gapPowerSum ((parametersExponent P).val + 2) X) := by
    linarith only [hXS]
  exact mul_le_mul_of_nonneg_left key (sq_nonneg _) |>.trans (le_of_eq (by ring))

/-- **The right-hand limit.** `∫ bochnerForm(χ_h Φ) → ∫ bochnerForm Φ` as `h → 0⁺`. -/
theorem tendsto_bochnerForm_cutoff (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    Tendsto (fun h : ℝ => ∫ X : Configuration N,
        bochnerForm P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y)
          (WithLp.toLp 2 X.val) ∂gibbsMeasure P N) (𝓝[>] 0)
      (𝓝 (∫ X : Configuration N, bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)
        ∂gibbsMeasure P N)) := by
  have : IsFiniteMeasure (gibbsMeasure P N) := by
    have := (modelWellDefined P N).2.2
    infer_instance
  obtain ⟨K, hK, hbd⟩ := bochnerForm_cutoff_bound P ℓ a ψ hψ hmean N
  obtain ⟨K', hK'0, hK'⟩ := abs_bochnerForm_loopHS_le P ℓ a ψ hψ hmean N
  have hs : 0 < (parametersExponent P).val + 2 := by
    have := (parametersExponent P).property.1
    linarith
  have hW : MemLp (fun X : Configuration N => 1 + gapPowerSum ((parametersExponent P).val + 2) X)
      2 (gibbsMeasure P N) := (memLp_const (1 : ℝ)).add (memLp_two_gapPowerSum P hPL N hs)
  have hstrip := tendsto_integral_strip_sq P hPL N
    (fun X => by linarith [gapPowerSum_nonneg ((parametersExponent P).val + 2) X]) hW hK
    (fun h hh0 hh1 X => hbd h hh0 hh1 X)
  have hΦint : Integrable (fun X : Configuration N =>
      bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)) (gibbsMeasure P N) := by
    have hg : Integrable (fun X : Configuration N =>
        K' * (1 + gapPowerSum ((parametersExponent P).val + 2) X)) (gibbsMeasure P N) :=
      ((integrable_const (1 : ℝ)).add (integrable_gapPowerSum P hPL hs N)).const_mul K'
    refine Integrable.mono' hg
      (ContinuousOn.comp_continuous ((contDiffOn_bochB P N (contDiff_loopHS ℓ a ψ hψ N)).continuousOn.add
        (continuous_bochC P N (contDiff_loopHS ℓ a ψ hψ N)).continuousOn)
        (continuous_toLp_config N) (fun X => mem_hsChamber_configuration X)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    exact hK' X
  have hlim : Tendsto (fun h : ℝ => (∫ X : Configuration N,
        bochnerForm P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val)
          ∂gibbsMeasure P N) - ∫ X : Configuration N,
        bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val) ∂gibbsMeasure P N) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hstrip
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with h hh hh1
    have hfi : Integrable (fun X : Configuration N =>
        bochnerForm P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val))
        (gibbsMeasure P N) :=
      integrable_bochnerForm_test P N (hsUnitGapCutoffTest hh (loopHS ℓ a ψ N)
        (contDiff_loopHS ℓ a ψ hψ N) (loopHS_periodic ℓ a ψ hψ hmean N))
    rw [← integral_sub hfi hΦint, Real.norm_eq_abs]
    exact abs_integral_le_integral_abs
  have := hlim.add_const (∫ X : Configuration N,
    bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val) ∂gibbsMeasure P N)
  simp only [sub_add_cancel, zero_add] at this
  exact this

/-- The second partial derivative of `Φ_{ψ,a}` on the lift is `a ψ'(xₖ/ℓ)` on the diagonal. -/
theorem partialDeriv_partialDeriv_loopScalePotential_eq (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) {N : ℕ} (k l : Fin N)
    (x : Fin N → ℝ) :
    partialDeriv (partialDeriv (loopScalePotential ℓ a ψ N) k) l x =
      if l = k then a * deriv ψ.val (x k / ℓ.val) else 0 := by
  have hfun : partialDeriv (loopScalePotential ℓ a ψ N) k =
      fun y => a * loopScaleField ℓ.val ψ.val (y k) := by
    funext y
    rw [partialDeriv_loopScalePotential ℓ a ψ k y]
    unfold loopScaleField
    ring
  rw [hfun]
  unfold partialDeriv
  by_cases hlk : l = k
  · subst hlk
    simp only [ite_true, Function.update_self]
    rw [deriv_const_mul_field']
    simp only [deriv_loopScaleField ℓ hψ]
  · have hc : (fun t : ℝ => a * loopScaleField ℓ.val ψ.val (Function.update x l t k)) =
        fun _ => a * loopScaleField ℓ.val ψ.val (x k) := by
      funext t
      rw [Function.update_of_ne (Ne.symm hlk)]
    rw [hc]
    simp [hlk]



/-- **Identification of the limit.** On a configuration, the Bochner form of `Φ_{ψ,a}` equals
`a² (hessianQuadratic + frobeniusSqDiag)`. -/
theorem bochnerForm_loopHS_eq (P : Parameters) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (_hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) (N : ℕ+) (X : Configuration N) :
    bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val) =
      a ^ 2 * (hessianQuadratic P N ℓ ψ X + frobeniusSqDiag ℓ ψ X) := by
  have h1 : ∀ k : Fin (N : ℕ), hsPartial (loopHS ℓ a ψ N) k (WithLp.toLp 2 X.val) =
      a * loopScaleField ℓ.val ψ.val (X.val k) := fun k =>
    (hsPartial_loopHS ℓ a ψ hψ N k _).trans ((partialDeriv_loopScalePotential ℓ a ψ k X.val).trans
      (by unfold loopScaleField; ring))
  have h2 : ∀ k l : Fin (N : ℕ), hsPartial (hsPartial (loopHS ℓ a ψ N) k) l
      (WithLp.toLp 2 X.val) = if l = k then a * deriv ψ.val (X.val k / ℓ.val) else 0 := fun k l =>
    (hsPartial_hsPartial_loopHS ℓ a ψ hψ N k l _).trans
      (partialDeriv_partialDeriv_loopScalePotential_eq ℓ a ψ hψ k l X.val)
  have hite : ∀ (p : Prop) [Decidable p] (c : ℝ),
      (if p then c else 0) * (if p then c else 0) = if p then c * c else 0 := by
    intro p _ c; split_ifs <;> ring
  unfold bochnerForm bochB bochC
  simp only [hsPartial_hsPartial_rieszH_config P N X, h1, h2, hite, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [hessianQuadratic_eq P N ℓ ψ X]
  unfold frobeniusSqDiag
  simp only [Finset.mul_sum, mul_add]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun k _ => by ring

/-- **Clauses 2 and 3 for `N ≥ 2`: the covariance of the loop operator.** The covariance of
`𝓛Φ_{ψ,a}` with itself is `a²` times the expectation of the Hessian term plus `‖DΨ‖²`, for
`N ≥ 2`. -/
theorem loop_variance_eq (P : Parameters) (hPL : External.PrekopaLeindler) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (ℓ : Ioc (0 : ℝ) 1) (a : ℝ) (ψ : LoopScaleProfile ℓ.val)
    (hψ : ContDiff ℝ ∞ ψ.val) (hmean : ∫ t in (0 : ℝ)..ℓ.val⁻¹, ψ.val t = 0) :
    gibbsCov (gibbsMeasure P N) (loopOperatorPotential P N ℓ a ψ)
        (loopOperatorPotential P N ℓ a ψ) =
      a ^ 2 * ∫ X : Configuration N,
        (hessianQuadratic P N ℓ ψ X + frobeniusSqDiag ℓ ψ X) ∂gibbsMeasure P N := by
  have hLO : ∀ X : Configuration N, loopOperatorPotential P N ℓ a ψ X =
      loopLHS P N ℓ a ψ (WithLp.toLp 2 X.val) := fun X =>
    (loopLHS_eq_loopOperatorPotential P N ℓ a ψ hψ X).symm
  have hmz : ∫ X : Configuration N, loopOperatorPotential P N ℓ a ψ X ∂gibbsMeasure P N = 0 := by
    have h0 := loopLHS_integral_eq P hPL N hN ℓ a ψ hψ hmean (fun _ => (1 : ℝ)) contDiff_const
      (fun _ _ => rfl) 1 (fun _ => by norm_num) (fun k x => by rw [hsPartial_const_one]; norm_num)
    simp only [hsPartial_const_one, mul_zero, Finset.sum_const_zero, mul_one, integral_zero] at h0
    simp only [hLO]
    exact h0
  unfold gibbsCov
  rw [hmz]
  simp only [sub_zero]
  have hL := tendsto_langOp_sq P hPL N ℓ a ψ hψ hmean
  have hB := tendsto_bochnerForm_cutoff P hPL N ℓ a ψ hψ hmean
  have heq : (fun h : ℝ => ∫ X : Configuration N,
        langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val) *
          langOp P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y) (WithLp.toLp 2 X.val)
          ∂gibbsMeasure P N) =ᶠ[𝓝[>] 0] fun h : ℝ => ∫ X : Configuration N,
        bochnerForm P N (fun y => hsUnitGapCutoff N h y * loopHS ℓ a ψ N y)
          (WithLp.toLp 2 X.val) ∂gibbsMeasure P N := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact bochner_identity_test P N hN (hsUnitGapCutoffTest hh (loopHS ℓ a ψ N)
      (contDiff_loopHS ℓ a ψ hψ N) (loopHS_periodic ℓ a ψ hψ hmean N))
  have key := tendsto_nhds_unique (hL.congr' heq) hB
  have hpt : ∫ X : Configuration N, loopOperatorPotential P N ℓ a ψ X *
      loopOperatorPotential P N ℓ a ψ X ∂gibbsMeasure P N =
      ∫ X : Configuration N, bochnerForm P N (loopHS ℓ a ψ N) (WithLp.toLp 2 X.val)
        ∂gibbsMeasure P N := by
    simp only [hLO]
    exact key
  rw [hpt]
  simp only [bochnerForm_loopHS_eq P ℓ a ψ hψ hmean N]
  rw [integral_const_mul]


end Riesz1

end

end
