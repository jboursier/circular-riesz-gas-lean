/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLaw
public import Riesz1.HelfferSjostrand.AnchoredHamiltonian
public import Riesz1.HelfferSjostrand.RieszAdmissiblePairs
public import Riesz1.Variance.Window
public import Riesz1.Rigidity.ForcingPotential
public import Riesz1.ToMathlib.Calculus.AffineHessian
public import Riesz1.ToMathlib.HurwitzKernel.CurvatureTerms
public import Riesz1.Gibbs.AnchoredCoordinates

/-!
# The anchored convexified potential and the form of its Hessian

Lemma 5.2, third claim. The anchored potential is
`β (H_N^* + F_{ε,γ}^*)`, a function on the anchored gap domain `anchoredDomain n`, with `N = n + 1`
particles. Its anchored Riesz part is `hsAnchoredHamiltonian` of the Riesz pair data, and its
forcing part is the sum of `θ (N (y_{i+1} - y_i) / K^ε)` over the nearest-neighbour pairs of the
window.

* `anchoredPotential` is `β (H_N^* + F^*)`. `anchoredForcing` is `F^*`.
* `anchorCoord`, `edgeForm` and `pairForm` are the anchored coordinates and the gap and pair
  separations as continuous linear forms. `anchoredGapAt_label` identifies the cyclic gap of
  `Riesz1.anchoredGapAt` with `N (edgeForm + wrapOffset)` at each label.
* `anchoredPotential_hessian` gives the Hessian quadratic form at a point of the domain as a sum over
  the ordered pairs `i < j` (Riesz terms) and over the nearest-neighbour edges (forcing terms).

The Hessian lower bound is proved in `Riesz1.Variance.ConvexificationHessian`.
-/

@[expose] public section

open Set Finset Filter Topology
open scoped ContDiff

namespace Riesz1

/-! ### Anchored coordinates as continuous linear forms -/

/-- The `k`-th entry of the anchor vector `(0, y_1, …, y_n)`, as a continuous linear form of `y`. -/
noncomputable def anchorCoord (n : ℕ) (k : Fin (n.succPNat : ℕ)) : (Fin n → ℝ) →L[ℝ] ℝ :=
  Fin.cases 0 (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) k

lemma anchorCoord_apply (n : ℕ) (y : Fin n → ℝ) (k : Fin (n.succPNat : ℕ)) :
    anchorCoord n k y = anchorVector y k := by
  induction k using Fin.cases with
  | zero => simp [anchorCoord]; exact (anchorVector_zero y).symm
  | succ j => simp [anchorCoord, anchorVector_succ]

/-- The separation `y_{j} - y_{i}` of the label pair `(i, j)` as a continuous linear form. -/
noncomputable def pairForm (n : ℕ) (p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  anchorCoord n p.2 - anchorCoord n p.1

lemma pairForm_apply (n : ℕ) (p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)) (y : Fin n → ℝ) :
    pairForm n p y = anchorVector y p.2 - anchorVector y p.1 := by
  simp [pairForm, anchorCoord_apply]

/-- The gap from label `i` to the next label `nextLabel i` in the cyclic order, as a continuous
linear form. -/
noncomputable def edgeForm (n : ℕ) (i : Fin (n.succPNat : ℕ)) : (Fin n → ℝ) →L[ℝ] ℝ :=
  anchorCoord n (nextLabel n.succPNat i) - anchorCoord n i

lemma edgeForm_apply (n : ℕ) (i : Fin (n.succPNat : ℕ)) (y : Fin n → ℝ) :
    edgeForm n i y = anchorVector y (nextLabel n.succPNat i) - anchorVector y i := by
  simp [edgeForm, anchorCoord_apply]

/-- The constant offset of the cyclic gap at label `i`: it is one at the wrap-around label `n`
(where the next label is label zero, shifted by the period one), and zero otherwise. -/
def wrapOffset (n : ℕ) (i : Fin (n.succPNat : ℕ)) : ℝ :=
  if (i : ℕ) = n then 1 else 0

/-- The label pairs `(i, j)` with `i < j`. -/
def pairSet (n : ℕ) : Finset (Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)) :=
  univ.filter fun p => p.1 < p.2

/-! ### The cyclic gap in anchored coordinates -/

/-- The cyclic gap `N (x_{i+1} - x_i)` at label `i` is `N (edgeForm + wrapOffset)` in the anchored
coordinates. This identifies `Riesz1.anchoredGapAt` with the affine form used below. -/
lemma anchoredGapAt_label (n : ℕ) (y : Fin n → ℝ) (i : Fin (n.succPNat : ℕ)) :
    anchoredGapAt n y (i : ℕ) = ((n : ℝ) + 1) * (edgeForm n i y + wrapOffset n i) := by
  unfold anchoredGapAt
  rw [edgeForm_apply]
  by_cases hi : (i : ℕ) = n
  · have hnext : nextLabel n.succPNat i = 0 := by
      apply Fin.ext
      simp [nextLabel, hi]
    have hoff : anchoredCyclicOffset n y (((i : ℕ) : ℤ) + 1) =
        anchoredCyclicOffset n y 0 + 1 := by
      have h := anchoredCyclicOffset_add_mul n y 0 1
      have hcast : (((i : ℕ) : ℤ) + 1) = 0 + ((n.succPNat : ℕ) : ℤ) * 1 := by
        rw [hi]
        simp
      rw [hcast, h, Int.cast_one]
    have h0 : anchoredCyclicOffset n y 0 = anchorVector y 0 := by
      have := anchoredCyclicOffset_natCast n y 0
      simpa using this
    have hi' : anchoredCyclicOffset n y ((i : ℕ) : ℤ) = anchorVector y i :=
      anchoredCyclicOffset_natCast n y i
    rw [hoff, h0, hi', hnext, anchorVector_zero]
    simp only [wrapOffset, hi, ite_true]
    ring
  · have hlt : (i : ℕ) + 1 < (n.succPNat : ℕ) := by
      have := i.isLt
      simp only [Nat.succPNat_coe] at this ⊢
      omega
    let i' : Fin (n.succPNat : ℕ) := ⟨(i : ℕ) + 1, hlt⟩
    have hnext : nextLabel n.succPNat i = i' := by
      apply Fin.ext
      simp only [nextLabel, i']
      exact Nat.mod_eq_of_lt hlt
    have hoff : anchoredCyclicOffset n y (((i : ℕ) : ℤ) + 1) = anchorVector y i' := by
      have := anchoredCyclicOffset_natCast n y i'
      simpa [i'] using this
    have hi' : anchoredCyclicOffset n y ((i : ℕ) : ℤ) = anchorVector y i :=
      anchoredCyclicOffset_natCast n y i
    rw [hoff, hi', hnext]
    simp [wrapOffset, hi]

/-! ### The anchored potential and its decomposition -/

/-- The anchored nearest-neighbour forcing `F^*(y) = ∑_{i,i+1 ∈ I_γ} θ (N (y_{i+1} - y_i) / K^ε)`
with the cyclic gaps of `Riesz1.anchoredGapAt`. -/
noncomputable def anchoredForcing (θ : ℝ → ℝ) (n : ℕ) (K γ ε : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i ∈ nearestPairs n.succPNat (window n.succPNat K γ),
    θ (anchoredGapAt n y ((i : ℕ) : ℤ) / K ^ ε)

/-- The anchored convexified potential `β (H_N^* + F^*)`, for the Riesz pair
data at inverse temperature `β` and exponent `s`, and the forcing cutoff `θ`. -/
noncomputable def anchoredPotential (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (θ : ℝ → ℝ)
    (n : ℕ) (K γ ε : ℝ) : (Fin n → ℝ) → ℝ :=
  fun y => hsAnchoredHamiltonian (hsRieszPairPotentials n.succPNat β hβ s) y +
    β * anchoredForcing θ n K γ ε y

/-- Summing over the first label and then the second is summing over the ordered pairs `i < j`. -/
lemma sum_filter_lt_eq {M : Type*} [AddCommMonoid M] (m : ℕ) (f : Fin m → Fin m → M) :
    ∑ i, ∑ j ∈ univ.filter (i < ·), f i j =
      ∑ p ∈ univ.filter (fun p : Fin m × Fin m => p.1 < p.2), f p.1 p.2 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter]

/-- The anchored Riesz energy is the sum over the pairs `i < j` of `2 χ_{ij} (y_j - y_i)`. -/
lemma hsAnchoredHamiltonian_eq_sum {n : ℕ} {c : ℝ} (χ : HsPairPotentials n.succPNat c) (y : Fin n → ℝ) :
    hsAnchoredHamiltonian χ y = ∑ p ∈ pairSet n, 2 * χ.potential p.1 p.2 (pairForm n p y) := by
  unfold hsAnchoredHamiltonian hsPairExpression pairSet
  rw [← Finset.mul_sum, sum_filter_lt_eq]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pairForm_apply]

/-- The anchored potential as a sum over the pairs `i < j` and over the nearest-neighbour edges. -/
lemma anchoredPotential_eq_sum (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (θ : ℝ → ℝ) (n : ℕ)
    (K γ ε : ℝ) (y : Fin n → ℝ) :
    anchoredPotential β hβ s θ n K γ ε y =
      ∑ p ∈ pairSet n, 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2
          (pairForm n p y) +
        ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
          β * θ (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
            ((n : ℝ) + 1) / K ^ ε * edgeForm n e y) := by
  unfold anchoredPotential anchoredForcing
  rw [hsAnchoredHamiltonian_eq_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [anchoredGapAt_label]
  congr 2
  ring

/-- The derivative of a constant multiple: `(c f)'' = c f''`. -/
lemma deriv_deriv_const_mul (c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    deriv (deriv (fun u => c * f u)) t = c * deriv (deriv f) t := by
  rw [deriv_const_mul_field', deriv_const_mul_field]

/-- The second derivative of the Riesz pair potential is that of the Hurwitz kernel, times the
coefficient `β N^{-s}`. -/
lemma deriv_deriv_riesz_pair (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (n : ℕ)
    (p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)) (r : ℝ) :
    deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2)) r =
      β * ((n.succPNat : ℕ) : ℝ) ^ (-s.val) * deriv (deriv (hurwitzKernel s.val)) r := by
  show deriv (deriv (fun u => β * ((n.succPNat : ℕ) : ℝ) ^ (-s.val) * hurwitzKernel s.val u)) r = _
  rw [deriv_deriv_const_mul]

/-! ### The Hessian of the anchored potential -/

/-- A function that is smooth on `(0, 1)` is `C²` at each point of `(0, 1)`. -/
lemma contDiffAt_two_of_contDiffOn_Ioo {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : ContDiffAt ℝ 2 f t :=
  (hf.contDiffAt (isOpen_Ioo.mem_nhds ht)).of_le (by simp)

/-- The pair potential of the Riesz data, as a function of one variable on `(0, 1)`. -/
lemma pairPot_contDiffOn (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (n : ℕ)
    (p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)) (hlt : p.1 < p.2) :
    ContDiffOn ℝ ∞ ((hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2) (Ioo (0 : ℝ) 1) :=
  (hsRieszPairPotentials n.succPNat β hβ s).smooth p.1 p.2 hlt

/-- Each pair term is `C²` near a point of the anchored domain: its separation stays in `(0, 1)`. -/
lemma pair_term_eventually_contDiffAt (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (n : ℕ)
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n) {p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)}
    (hp : p ∈ pairSet n) :
    ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2
      (fun z => 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2 (pairForm n p z)) z := by
  have hlt : p.1 < p.2 := (mem_filter.mp hp).2
  have h0 : pairForm n p y ∈ Ioo (0 : ℝ) 1 := by
    rw [pairForm_apply]
    exact anchorVector_sub_mem_Ioo hy hlt
  have hmem : ∀ᶠ z in 𝓝 y, pairForm n p z ∈ Ioo (0 : ℝ) 1 :=
    ((pairForm n p).continuous.tendsto y).eventually (isOpen_Ioo.mem_nhds h0)
  filter_upwards [hmem] with z hz
  have hpot := contDiffAt_two_of_contDiffOn_Ioo (pairPot_contDiffOn β hβ s n p hlt) hz
  exact contDiffAt_const.mul (hpot.comp z (pairForm n p).contDiff.contDiffAt)

/-- The Hessian of one pair term: `2 · (potential)'' (separation) · (separation of `U`)²`. -/
lemma hess_pair_term (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (n : ℕ) {y : Fin n → ℝ}
    (hy : y ∈ anchoredDomain n) {p : Fin (n.succPNat : ℕ) × Fin (n.succPNat : ℕ)}
    (hp : p ∈ pairSet n) (U : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2
      (pairForm n p z))) y U U =
      2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2))
        (pairForm n p y) * (pairForm n p U) ^ 2 := by
  have hlt : p.1 < p.2 := (mem_filter.mp hp).2
  have h0 : pairForm n p y ∈ Ioo (0 : ℝ) 1 := by
    rw [pairForm_apply]
    exact anchorVector_sub_mem_Ioo hy hlt
  have hpot0 := contDiffAt_two_of_contDiffOn_Ioo (pairPot_contDiffOn β hβ s n p hlt) h0
  have hpot : ContDiffAt ℝ 2 (fun t => 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential
      p.1 p.2 t) (0 + pairForm n p y) := by
    rw [zero_add]
    exact contDiffAt_const.mul hpot0
  have key := fderiv_fderiv_affine_comp (fun t => 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential
      p.1 p.2 t) (pairForm n p) 0 y U hpot
  simp only [zero_add] at key
  rw [key, deriv_deriv_const_mul]

/-- The smooth edge term `β θ(a + c · L z)` is `C²` at every point. -/
lemma edge_term_contDiff {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (β a c : ℝ) {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (z : Fin n → ℝ) :
    ContDiffAt ℝ 2 (fun z => β * θ (a + c * L z)) z :=
  ((contDiff_const.mul (hθ.1.comp (contDiff_const.add (contDiff_const.mul L.contDiff)))).contDiffAt).of_le
    (by simp)

/-- The Hessian of one forcing term `β θ(a + c · L z)` is `β θ''(a + c · L y) (c · L U)²`. -/
lemma hess_edge_term {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (β a c : ℝ) {n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] ℝ) (y U : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (fun z => β * θ (a + c * L z))) y U U =
      β * deriv (deriv θ) (a + c * L y) * (c * L U) ^ 2 := by
  have hφ : ContDiffAt ℝ 2 (fun t => β * θ t) (a + (c • L) y) :=
    (contDiffAt_const.mul hθ.1.contDiffAt).of_le (by simp)
  have key := fderiv_fderiv_affine_comp (fun t => β * θ t) (c • L) a y U hφ
  simp only [smul_apply, smul_eq_mul] at key
  rw [key, deriv_deriv_const_mul]

/-- **Hessian of the anchored potential.** At a point `y` of the anchored domain and for every
direction `U`, the Hessian quadratic form of `β (H_N^* + F^*)` is the sum of the Riesz pair terms
over the ordered pairs `i < j`, plus the forcing terms over the nearest-neighbour edges of the window.
-/
theorem anchoredPotential_hessian (β : ℝ) (hβ : 0 < β) (s : RieszExponent) (θ : ℝ → ℝ)
    (hθ : IsForcingCutoff θ) (n : ℕ) (K γ ε : ℝ) {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n)
    (U : Fin n → ℝ) :
    fderiv ℝ (fderiv ℝ (anchoredPotential β hβ s θ n K γ ε)) y U U =
      ∑ p ∈ pairSet n, 2 * deriv (deriv ((hsRieszPairPotentials n.succPNat β hβ s).potential
          p.1 p.2)) (pairForm n p y) * (pairForm n p U) ^ 2 +
        ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
          β * deriv (deriv θ) (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
            ((n : ℝ) + 1) / K ^ ε * edgeForm n e y) *
            (((n : ℝ) + 1) / K ^ ε * edgeForm n e U) ^ 2 := by
  have hfun : anchoredPotential β hβ s θ n K γ ε =
      fun z => (∑ p ∈ pairSet n, 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2
          (pairForm n p z)) +
        ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
          β * θ (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
            ((n : ℝ) + 1) / K ^ ε * edgeForm n e z) :=
    funext fun z => anchoredPotential_eq_sum β hβ s θ n K γ ε z
  have hP : ∀ᶠ z in 𝓝 y, ∀ p ∈ pairSet n, ContDiffAt ℝ 2
      (fun z => 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2 (pairForm n p z)) z :=
    (Filter.eventually_all_finset _).2 fun p hp => pair_term_eventually_contDiffAt β hβ s n hy hp
  have hE : ∀ᶠ z in 𝓝 y, ∀ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
      ContDiffAt ℝ 2 (fun z => β * θ (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
        ((n : ℝ) + 1) / K ^ ε * edgeForm n e z)) z :=
    Filter.Eventually.of_forall fun z e _ => edge_term_contDiff hθ β _ _ (edgeForm n e) z
  have hfP : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2
      (fun z => ∑ p ∈ pairSet n, 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2
        (pairForm n p z)) z := by
    filter_upwards [hP] with z hz
    exact ContDiffAt.sum fun p hp => hz p hp
  have hfE : ∀ᶠ z in 𝓝 y, ContDiffAt ℝ 2
      (fun z => ∑ e ∈ nearestPairs n.succPNat (window n.succPNat K γ),
        β * θ (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
          ((n : ℝ) + 1) / K ^ ε * edgeForm n e z)) z := by
    filter_upwards [hE] with z hz
    exact ContDiffAt.sum fun e he => hz e he
  rw [hfun, fderiv_fderiv_add_apply _ _ y U hfP hfE,
    fderiv_fderiv_sum_apply (pairSet n)
      (fun p z => 2 * (hsRieszPairPotentials n.succPNat β hβ s).potential p.1 p.2 (pairForm n p z))
      y U hP,
    fderiv_fderiv_sum_apply (nearestPairs n.succPNat (window n.succPNat K γ))
      (fun e z => β * θ (((n : ℝ) + 1) * wrapOffset n e / K ^ ε +
        ((n : ℝ) + 1) / K ^ ε * edgeForm n e z)) y U hE]
  congr 1
  · exact Finset.sum_congr rfl fun p hp => hess_pair_term β hβ s n hy hp U
  · refine Finset.sum_congr rfl fun e _ => ?_
    have h := hess_edge_term hθ β (((n : ℝ) + 1) * wrapOffset n e / K ^ ε)
      (((n : ℝ) + 1) / K ^ ε) (edgeForm n e) y U
    simpa using h

end Riesz1
