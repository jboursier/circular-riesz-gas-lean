/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevLifts
public import Riesz1.HelfferSjostrand.GeometryHessian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Test functions and the pair Hessian energy

The vector space `𝒟_N` of smooth periodic functions whose
support has positive distance from the collision boundary. The file also records the pointwise
pair Hessian energy `(√(2 χ_ij''(y_j - y_i)) (v_j - v_i))_{i<j}`, whose squared norm is the
Hessian quadratic form `v · ∇²H v` of Lemma 3.6.

The separation lemma `hsBoundaryDistance_le_separation` converts the boundary distance into a
uniform lower and upper bound on every pair separation. It gives the pointwise boundedness of
the Hessian energy on test functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff

namespace Riesz1

/-- The test functions `𝒟_N`, as a real vector space: smooth periodic
functions on the Euclidean lift space whose support has positive distance from the collision
complement of the chamber. -/
def hsTestSubmodule (N : ℕ+) : Submodule ℝ (HsEuclidean N → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ (∀ (k : ℤ) (x : HsEuclidean N), f (hsTranslate (k : ℝ) x) = f x) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, f x ≠ 0 → ENNReal.ofReal δ ≤ infEDist x (hsChamber N)ᶜ}
  zero_mem' := ⟨contDiff_const, fun _ _ => rfl, 1, one_pos, fun x hx => absurd rfl hx⟩
  add_mem' := by
    rintro f g ⟨hf, hfp, δ, hδ, hfs⟩ ⟨hg, hgp, η, hη, hgs⟩
    refine ⟨hf.add hg, fun k x => by simp only [Pi.add_apply, hfp, hgp], min δ η, lt_min hδ hη,
      fun x hx => ?_⟩
    by_cases hfx : f x = 0
    · have hgx : g x ≠ 0 := by simpa [hfx] using hx
      exact (ENNReal.ofReal_le_ofReal (min_le_right δ η)).trans (hgs x hgx)
    · exact (ENNReal.ofReal_le_ofReal (min_le_left δ η)).trans (hfs x hfx)
  smul_mem' a f hf := by
    obtain ⟨hf, hfp, δ, hδ, hfs⟩ := hf
    refine ⟨hf.const_smul a, fun k x => by simp only [Pi.smul_apply, hfp], δ, hδ,
      fun x hx => hfs x fun h => hx (by simp [h])⟩

/-- A test function is in particular smooth on a neighborhood of the closed chamber. -/
theorem HsTestSubmodule.smoothOnClosure {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hf : f ∈ hsTestSubmodule N) : HsSmoothOnClosure N f := by
  obtain ⟨hs, hp, _⟩ := hf
  exact ⟨hp, univ, isOpen_univ, subset_univ _, hs.contDiffOn⟩

/-- The distance bound on the support of a test function, in the form of the infimum
distance `hsBoundaryDistance`. -/
theorem HsTestSubmodule.boundary_bound {N : ℕ+} (hN : 2 ≤ (N : ℕ)) {f : HsEuclidean N → ℝ}
    (hf : f ∈ hsTestSubmodule N) : ∃ δ : ℝ, 0 < δ ∧ ∀ x, f x ≠ 0 →
      δ ≤ hsBoundaryDistance N hN x := by
  obtain ⟨_, _, δ, hδ, hs⟩ := hf
  refine ⟨δ, hδ, fun x hx => ?_⟩
  change δ ≤ infDist x (hsChamber N)ᶜ
  unfold infDist
  exact (ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top (hsChamber_compl_nonempty hN))).mp
    (hs x hx)

/-- The boundary distance dominates the pair separation `x_j - x_i` and the complementary
separation `1 - (x_j - x_i)`, for every pair `i < j` in the chamber. -/
theorem hsBoundaryDistance_le_separation {N : ℕ+} (hN : 2 ≤ (N : ℕ)) {x : HsEuclidean N}
    (hx : x ∈ hsChamber N) {i j : Fin (N : ℕ)} (hij : i < j) :
    hsBoundaryDistance N hN x ≤ x j - x i ∧ hsBoundaryDistance N hN x ≤ 1 - (x j - x i) := by
  have hmono : Monotone x := hx.1.monotone
  constructor
  · -- Moving coordinate `j` down to `x i` leaves the chamber at distance `x j - x i`.
    set z : HsEuclidean N := x - (x j - x i) • EuclideanSpace.single j (1 : ℝ) with hzdef
    have hzi : z i = x i := by
      rw [hzdef, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, ite_eq_right hij.ne, smul_eq_mul,
        mul_zero, sub_zero]
    have hzj : z j = x i := by
      rw [hzdef, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, ite_eq_left rfl, smul_eq_mul,
        mul_one]
      ring
    have hz : z ∉ hsChamber N := by
      intro hzc
      have hlt := hzc.1 hij
      linarith
    have hd : dist x z = x j - x i := by
      rw [dist_eq_norm, hzdef, sub_sub_cancel, norm_smul, PiLp.norm_single, norm_one, mul_one,
        Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (hx.1 hij))]
    change infDist x (hsChamber N)ᶜ ≤ _
    rw [← hd]
    exact infDist_le_dist_of_mem hz
  · -- Moving the last coordinate up to `x 0 + 1` leaves the chamber at distance `1 + x 0 - x last`.
    let last : Fin (N : ℕ) := ⟨(N : ℕ) - 1, by omega⟩
    have hlast0 : (⟨0, N.pos⟩ : Fin (N : ℕ)) ≠ last := by
      intro h
      have := congrArg Fin.val h
      simp [last] at this
      omega
    set t : ℝ := 1 + x ⟨0, N.pos⟩ - x last with htdef
    have ht : 0 < t := by
      have := hx.2 last
      linarith
    set z : HsEuclidean N := x + t • EuclideanSpace.single last (1 : ℝ) with hzdef
    have hz : z ∉ hsChamber N := by
      intro hzc
      have hlt := hzc.2 last
      have hz0 : z ⟨0, N.pos⟩ = x ⟨0, N.pos⟩ := by
        rw [hzdef, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_eq_right hlast0, smul_eq_mul,
          mul_zero, add_zero]
      have hzl : z last = x ⟨0, N.pos⟩ + 1 := by
        rw [hzdef, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_eq_left rfl, smul_eq_mul,
          mul_one, htdef]
        ring
      linarith
    have hd : dist x z = t := by
      rw [dist_eq_norm, hzdef, sub_add_cancel_left, norm_neg, norm_smul, PiLp.norm_single,
        norm_one, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    have hsep : x j - x i ≤ x last - x ⟨0, N.pos⟩ :=
      sub_le_sub (hmono (Fin.le_def.mpr (by simp [last]; omega))) (hmono (Fin.zero_le _))
    change infDist x (hsChamber N)ᶜ ≤ 1 - (x j - x i)
    have hle : infDist x (hsChamber N)ᶜ ≤ t := by
      rw [← hd]
      exact infDist_le_dist_of_mem hz
    linarith

/-- The index set of the pair Hessian energy: the pairs `i < j`. -/
abbrev HsPairIndex (N : ℕ+) := {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2}

/-- The weight `√(2 χ_ij''(y_j - y_i))` of the pair `p = (i, j)` at the point `y`. -/
def hsEnergyWeight {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (p : HsPairIndex N)
    (y : HsEuclidean N) : ℝ :=
  Real.sqrt (2 * deriv (deriv (χ.potential p.1.1 p.1.2)) (y p.1.2 - y p.1.1))

/-- The pair Hessian energy at `y` of a vector `v`: the entries
`√(2 χ_ij''(y_j - y_i)) (v_j - v_i)` for the pairs `i < j`. -/
def hsHessianEnergy {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (y v : HsEuclidean N) :
    EuclideanSpace ℝ (HsPairIndex N) :=
  WithLp.toLp 2 (fun p => hsEnergyWeight χ p y * (v p.1.2 - v p.1.1))

/-- The vector `(u_1(x), …, u_N(x))` of an `N`-tuple of functions on the lift space. -/
def hsVectorAt {N : ℕ+} (u : Fin (N : ℕ) → HsEuclidean N → ℝ) (x : HsEuclidean N) :
    HsEuclidean N :=
  WithLp.toLp 2 (fun i => u i x)

theorem hsHessianEnergy_add {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (y v w : HsEuclidean N) :
    hsHessianEnergy χ y (v + w) = hsHessianEnergy χ y v + hsHessianEnergy χ y w := by
  ext p
  simp only [hsHessianEnergy, PiLp.add_apply, PiLp.toLp_apply]
  ring

theorem hsHessianEnergy_smul {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (y v : HsEuclidean N)
    (a : ℝ) : hsHessianEnergy χ y (a • v) = a • hsHessianEnergy χ y v := by
  ext p
  simp only [hsHessianEnergy, PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]
  ring

/-- The pair weights of the Hessian energy are bounded on every separation range `[δ, 1 - δ]`. -/
theorem hsHessianWeight_bounded {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C : HsPairIndex N → ℝ, ∀ p, ∀ r ∈ Icc δ (1 - δ),
      |deriv (deriv (χ.potential p.1.1 p.1.2)) r| ≤ |C p| := by
  have hsub : Icc δ (1 - δ) ⊆ Ioo (0 : ℝ) 1 := fun r hr => ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hex : ∀ p : HsPairIndex N, ∃ C : ℝ, ∀ r ∈ Icc δ (1 - δ),
      ‖deriv (deriv (χ.potential p.1.1 p.1.2)) r‖ ≤ C := by
    rintro ⟨⟨i, j⟩, hij⟩
    have h1 : ContDiffOn ℝ ∞ (deriv (χ.potential i j)) (Ioo 0 1) :=
      (χ.smooth i j hij).deriv_of_isOpen isOpen_Ioo (by simp)
    have h2 : ContinuousOn (deriv (deriv (χ.potential i j))) (Ioo 0 1) :=
      h1.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
    exact isCompact_Icc.exists_bound_of_continuousOn (h2.mono hsub)
  choose C hC using hex
  refine ⟨C, fun p r hr => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hC p r hr).trans (le_abs_self _)

/-- Every test tuple has bounded pair Hessian energy on the fundamental region of the lift
space. Only the separation bounds of test supports are used. -/
theorem hsHessianEnergy_bounded {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (hN : 2 ≤ (N : ℕ)) (u : Fin (N : ℕ) → HsEuclidean N → ℝ) (hu : ∀ i, u i ∈ hsTestSubmodule N) :
    ∃ B : ℝ, ∀ x ∈ hsFundamentalRegion N, ‖hsHessianEnergy χ x (hsVectorAt u x)‖ ≤ B := by
  -- One boundary margin serves every component.
  choose δ hδ hδs using fun i => HsTestSubmodule.boundary_bound hN (hu i)
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ δ Finset.univ_nonempty
  have hδ0 : 0 < δ i0 := hδ i0
  have hsupp : ∀ i x, u i x ≠ 0 → δ i0 ≤ hsBoundaryDistance N hN x := fun i x hx =>
    (hi0 i (Finset.mem_univ _)).trans (hδs i x hx)
  obtain ⟨C, hC⟩ := hsHessianWeight_bounded χ hδ0
  -- A uniform bound on the components over the closed fundamental region.
  have hV : ∀ i, ∃ V : ℝ, ∀ x ∈ closure (hsFundamentalRegion N), |u i x| ≤ V := fun i => by
    obtain ⟨V, hV⟩ := (isCompact_closure_hsFundamentalRegion N).exists_bound_of_continuousOn
      (hu i).1.continuous.continuousOn
    exact ⟨V, fun x hx => by simpa [Real.norm_eq_abs] using hV x hx⟩
  choose V hVb using hV
  set W : ℝ := ∑ i, |V i| with hW
  have hWb : ∀ i x, x ∈ hsFundamentalRegion N → |u i x| ≤ W := fun i x hx => by
    refine (hVb i x (subset_closure hx)).trans ((le_abs_self _).trans ?_)
    exact Finset.single_le_sum (f := fun i => |V i|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  refine ⟨Real.sqrt (∑ p, 8 * W ^ 2 * |C p|), fun x hx => ?_⟩
  have hxc : x ∈ hsChamber N := hx.1
  by_cases hzero : ∀ i, u i x = 0
  · have h0 : hsHessianEnergy χ x (hsVectorAt u x) = 0 := by
      ext p
      simp [hsHessianEnergy, hsVectorAt, hzero]
    rw [h0, norm_zero]
    exact Real.sqrt_nonneg _
  push Not at hzero
  obtain ⟨k, hk⟩ := hzero
  have hd : δ i0 ≤ hsBoundaryDistance N hN x := hsupp k x hk
  have hsq : ‖hsHessianEnergy χ x (hsVectorAt u x)‖ ^ 2 ≤ ∑ p, 8 * W ^ 2 * |C p| := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun p _ => ?_
    obtain ⟨⟨i, j⟩, hij⟩ := p
    have hsep := hsBoundaryDistance_le_separation hN hxc hij
    have hr : x j - x i ∈ Icc (δ i0) (1 - δ i0) := ⟨hd.trans hsep.1, by linarith [hsep.2]⟩
    have hbd := hC ⟨(i, j), hij⟩ (x j - x i) hr
    have hcurv := χ.curvature i j hij (x j - x i) (hsChamber_separation_mem hxc hij)
    have hnn : 0 ≤ 2 * deriv (deriv (χ.potential i j)) (x j - x i) := by
      have hc' : (0 : ℝ) ≤ c := hc.le
      linarith
    have hsq2 : hsEnergyWeight χ ⟨(i, j), hij⟩ x ^ 2 =
        2 * deriv (deriv (χ.potential i j)) (x j - x i) := Real.sq_sqrt hnn
    have hvj := abs_le.mp (hWb j x hx)
    have hvi := abs_le.mp (hWb i x hx)
    have hab : |hsVectorAt u x j - hsVectorAt u x i| ≤ 2 * W := by
      rw [abs_le]
      simp only [hsVectorAt, PiLp.toLp_apply]
      constructor <;> linarith [hvj.1, hvj.2, hvi.1, hvi.2]
    have hsq3 : (hsVectorAt u x j - hsVectorAt u x i) ^ 2 ≤ (2 * W) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    have hcoord : hsHessianEnergy χ x (hsVectorAt u x) ⟨(i, j), hij⟩ =
        hsEnergyWeight χ ⟨(i, j), hij⟩ x * (hsVectorAt u x j - hsVectorAt u x i) := by
      simp [hsHessianEnergy]
    have hCnn : 2 * deriv (deriv (χ.potential i j)) (x j - x i) ≤ 2 * |C ⟨(i, j), hij⟩| := by
      have := (le_abs_self _).trans hbd
      linarith
    calc ‖hsHessianEnergy χ x (hsVectorAt u x) ⟨(i, j), hij⟩‖ ^ 2
        = 2 * deriv (deriv (χ.potential i j)) (x j - x i) *
            (hsVectorAt u x j - hsVectorAt u x i) ^ 2 := by
          rw [hcoord, Real.norm_eq_abs, sq_abs, mul_pow, hsq2]
      _ ≤ (2 * |C ⟨(i, j), hij⟩|) * (2 * W) ^ 2 :=
          mul_le_mul hCnn hsq3 (sq_nonneg _) (by positivity)
      _ = 8 * W ^ 2 * |C ⟨(i, j), hij⟩| := by ring
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact Real.sqrt_le_sqrt hsq

end Riesz1

end
