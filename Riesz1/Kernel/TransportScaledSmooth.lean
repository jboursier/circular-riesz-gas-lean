/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaledConvolution

/-!
# Smoothness of the transport convolution off the periodized support

Let `ζ` be integrable on `[-ρ, ρ]` with `ζ = 0` a.e. outside `[-ρ, ρ]`, where `0 < ρ < 1/2`. The
transport convolution `Ψ = transportConv` is `C^∞` at every point at distance more than `ρ` from the
periodized support `[-ρ, ρ] + L ℤ`, and its derivatives satisfy `|Ψ^{(m)}(x)| ≤ C ‖ζ‖₁ |x|^{s-1-m}`
for `m ≥ 1` and `1 ≤ |x| ≤ L/2`.

The argument differentiates under the integral sign on the window `[-ρ, ρ]`, where the derivative
bounds of `TransportScaledLattice` apply uniformly near each point off the periodized support.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- **Smoothness from a family of derivatives.** If `G m` has derivative `G (m+1)` on an open set
`U`, then every `G m` is `C^∞` on `U`. -/
lemma contDiffOn_of_hasDerivAt_family {U : Set ℝ} (hU : IsOpen U) (G : ℕ → ℝ → ℝ)
    (hG : ∀ m : ℕ, ∀ x ∈ U, HasDerivAt (G m) (G (m + 1) x) x) :
    ∀ m : ℕ, ContDiffOn ℝ ∞ (G m) U := by
  have hcont : ∀ n : ℕ, ∀ m : ℕ, ContDiffOn ℝ n (G m) U := by
    intro n
    induction n with
    | zero =>
      intro m
      exact contDiffOn_zero.2 fun x hx => (hG m x hx).continuousAt.continuousWithinAt
    | succ n ih =>
      intro m
      have hn : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
      rw [hn, contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun x hx => (hG m x hx).differentiableAt.differentiableWithinAt,
        fun h => absurd h WithTop.coe_ne_top, ?_⟩
      have heq : Set.EqOn (deriv (G m)) (G (m + 1)) U := fun x hx => (hG m x hx).deriv
      exact (ih (m + 1)).congr heq
  intro m
  exact contDiffOn_infty.2 fun n => hcont n m

/-- The distance to the lattice is `1`-Lipschitz. -/
lemma latticeDist_sub_le (L z w : ℝ) (hL : 0 < L) :
    latticeDist L w ≤ latticeDist L z + |z - w| := by
  have h := latticeDist_le_abs_sub L w hL (round (z / L))
  have h2 : |w - (round (z / L) : ℝ) * L| ≤ |w - z| + |z - (round (z / L) : ℝ) * L| := by
    calc |w - (round (z / L) : ℝ) * L| = |(w - z) + (z - (round (z / L) : ℝ) * L)| := by ring_nf
      _ ≤ |w - z| + |z - (round (z / L) : ℝ) * L| := abs_add_le _ _
  have h3 : latticeDist L z = |z - (round (z / L) : ℝ) * L| := by
    unfold latticeDist
    rw [mul_comm]
  rw [abs_sub_comm w z] at h2
  linarith

/-- A lower bound for the lattice distance from lower bounds on all lattice distances. -/
lemma le_latticeDist {L z c : ℝ} (h : ∀ k : ℤ, c ≤ |z - k * L|) :
    c ≤ latticeDist L z := by
  have := h (round (z / L))
  unfold latticeDist
  rw [mul_comm] at this
  exact this

/-- The Lipschitz bound of the lattice distance, in both directions. -/
lemma latticeDist_lipschitz (L z w : ℝ) (hL : 0 < L) :
    latticeDist L z ≥ latticeDist L w - |z - w| := by
  have := latticeDist_sub_le L z w hL
  linarith

/-- The unit window derivative: the `m`-th derivative of the scaled kernel is differentiable off
the lattice, with derivative the `(m+1)`-st derivative. -/
lemma hasDerivAt_iteratedDeriv_scaledKernel {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    {r : ℝ} (hr : ∀ k : ℤ, r ≠ k * L) (m : ℕ) :
    HasDerivAt (iteratedDeriv m (scaledKernel s L)) (iteratedDeriv (m + 1) (scaledKernel s L) r) r := by
  have hU := isOpen_lattice_compl hL
  have hC := contDiffOn_iteratedDeriv_of_isOpen hU m (scaledKernel s L)
    (scaledKernel_contDiffOn hs0 hs1 hL)
  have hdiff : DifferentiableAt ℝ (iteratedDeriv m (scaledKernel s L)) r :=
    ((hC r hr).contDiffAt (hU.mem_nhds hr)).differentiableAt (by simp)
  have h := hdiff.hasDerivAt
  rwa [← iteratedDeriv_succ] at h

/-- The unit-scale distance `|x - kL|` exceeds `|x|/2` for every lattice point, when `1 ≤ |x| ≤ L/2`
and `|y| ≤ 1/2`. -/
lemma le_abs_sub_mul_of_mem_window {L x y : ℝ} (hx1 : 1 ≤ |x|) (hxL : |x| ≤ L / 2)
    (hy : |y| ≤ 1 / 2) (k : ℤ) : |x| / 2 ≤ |x - y - k * L| := by
  have hL2 : 2 ≤ L := by linarith
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    have : |x| ≤ |x - y| + |y| := by
      have := abs_sub_abs_le_abs_sub x y
      linarith [abs_sub_comm x y]
    simp only [Int.cast_zero, zero_mul, sub_zero]
    linarith
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast this
    have hkL : L ≤ |(k : ℝ) * L| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < L)]
      nlinarith
    have hxy : |x - y| ≤ |x| + |y| := abs_sub x y
    have hdiff : |(k : ℝ) * L| - |x - y| ≤ |x - y - k * L| := by
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * L) (x - y)
      rw [abs_sub_comm ((k : ℝ) * L) (x - y)] at h
      exact h
    linarith

/-- The window convolution `∫_{(-ρ,ρ]} ζ(y) ∂^m K_{s,L}(x - y) dy`. -/
@[expose] noncomputable def windowConv (s L ρ : ℝ) (ζ : ℝ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∫ y in Ioc (-ρ) ρ, ζ y * iteratedDeriv m (scaledKernel s L) (x - y)

/-- Continuity of `y ↦ ∂^m K_{s,L}(x - y)` on the window, when `x` is off the periodized window. -/
lemma continuousOn_iteratedDeriv_window {s L ρ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    {x : ℝ} (hx : ∀ y ∈ Icc (-ρ) ρ, ∀ k : ℤ, x - y ≠ k * L) (m : ℕ) :
    ContinuousOn (fun y => iteratedDeriv m (scaledKernel s L) (x - y)) (Icc (-ρ) ρ) := by
  have hC := contDiffOn_iteratedDeriv_of_isOpen (isOpen_lattice_compl hL) m (scaledKernel s L)
    (scaledKernel_contDiffOn hs0 hs1 hL)
  refine (hC.continuousOn).comp (continuous_const.sub continuous_id).continuousOn ?_
  intro y hy
  exact hx y hy

/-- A uniform bound for `∂^m K_{s,L}(x - ·)` on the window. -/
lemma exists_bound_iteratedDeriv_window {s L ρ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    {x : ℝ} (hx : ∀ y ∈ Icc (-ρ) ρ, ∀ k : ℤ, x - y ≠ k * L) (m : ℕ) :
    ∃ M : ℝ, ∀ y ∈ Icc (-ρ) ρ, ‖iteratedDeriv m (scaledKernel s L) (x - y)‖ ≤ M :=
  isCompact_Icc.exists_bound_of_continuousOn (continuousOn_iteratedDeriv_window hs0 hs1 hL hx m)

/-- **Differentiation under the integral.** If `x` has a neighbourhood `U` on which the window
points stay at distance `η` from the lattice, then `∂^m` of the window convolution is differentiable
with derivative `∂^{m+1}`. -/
lemma hasDerivAt_windowConv {s L ρ η : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    {ζ : ℝ → ℝ} (hζ : IntegrableOn ζ (Ioc (-ρ) ρ)) (hη : 0 < η) {U : Set ℝ} (hU : IsOpen U)
    (hsep : ∀ x ∈ U, ∀ y ∈ Icc (-ρ) ρ, ∀ k : ℤ, η ≤ |x - y - k * L|) (m : ℕ) {x : ℝ}
    (hx : x ∈ U) :
    HasDerivAt (windowConv s L ρ ζ m) (windowConv s L ρ ζ (m + 1) x) x := by
  have hnot : ∀ z ∈ U, ∀ y ∈ Icc (-ρ) ρ, ∀ k : ℤ, z - y ≠ k * L := by
    intro z hz y hy k h
    have := hsep z hz y hy k
    rw [h, sub_self, abs_zero] at this
    linarith
  obtain ⟨C, hC0, hCb⟩ := norm_iteratedDeriv_scaledKernel_le hs0 hs1 (m := m + 1) (by omega)
  have hexp : s - 1 - ((m + 1 : ℕ) : ℝ) < 0 := by push_cast; linarith
  have hbound : ∀ z ∈ U, ∀ y ∈ Ioc (-ρ) ρ,
      ‖iteratedDeriv (m + 1) (scaledKernel s L) (z - y)‖ ≤ C * η ^ (s - 1 - ((m + 1 : ℕ) : ℝ)) := by
    intro z hz y hy
    have hy' : y ∈ Icc (-ρ) ρ := Ioc_subset_Icc_self hy
    have hd : η ≤ latticeDist L (z - y) := le_latticeDist (fun k => hsep z hz y hy' k)
    have h1 := hCb L (z - y) hL (hnot z hz y hy')
    have h2 : latticeDist L (z - y) ^ (s - 1 - ((m + 1 : ℕ) : ℝ)) ≤
        η ^ (s - 1 - ((m + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hη hd hexp.le
    calc ‖iteratedDeriv (m + 1) (scaledKernel s L) (z - y)‖
        ≤ C * latticeDist L (z - y) ^ (s - 1 - ((m + 1 : ℕ) : ℝ)) := h1
      _ ≤ C * η ^ (s - 1 - ((m + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h2 hC0.le
  have hsx : U ∈ 𝓝 x := hU.mem_nhds hx
  obtain ⟨M, hM⟩ := exists_bound_iteratedDeriv_window hs0 hs1 hL (hnot x hx) m
  have hcontF : ∀ z ∈ U, AEStronglyMeasurable
      (fun y => ζ y * iteratedDeriv m (scaledKernel s L) (z - y))
      (volume.restrict (Ioc (-ρ) ρ)) := by
    intro z hz
    exact hζ.aestronglyMeasurable.mul
      (((continuousOn_iteratedDeriv_window hs0 hs1 hL (hnot z hz) m).mono
        Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
  have hcontF' : AEStronglyMeasurable
      (fun y => ζ y * iteratedDeriv (m + 1) (scaledKernel s L) (x - y))
      (volume.restrict (Ioc (-ρ) ρ)) :=
    hζ.aestronglyMeasurable.mul
      (((continuousOn_iteratedDeriv_window hs0 hs1 hL (hnot x hx) (m + 1)).mono
        Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
  have hint : Integrable (fun y => ζ y * iteratedDeriv m (scaledKernel s L) (x - y))
      (volume.restrict (Ioc (-ρ) ρ)) := by
    refine Integrable.mono' (hζ.abs.const_mul M) (hcontF x hx) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    calc ‖ζ y * iteratedDeriv m (scaledKernel s L) (x - y)‖
        = |ζ y| * ‖iteratedDeriv m (scaledKernel s L) (x - y)‖ := by
          rw [norm_mul, Real.norm_eq_abs]
      _ ≤ |ζ y| * M := mul_le_mul_of_nonneg_left (hM y (Ioc_subset_Icc_self hy)) (abs_nonneg _)
      _ = M * |ζ y| := mul_comm _ _
  have hdiff := _root_.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (-ρ) ρ))
    (F := fun z y => ζ y * iteratedDeriv m (scaledKernel s L) (z - y))
    (F' := fun z y => ζ y * iteratedDeriv (m + 1) (scaledKernel s L) (z - y))
    (x₀ := x) (s := U) hsx
    (Filter.eventually_of_mem hsx fun z hz => hcontF z hz) hint hcontF'
    (bound := fun y => |ζ y| * (C * η ^ (s - 1 - ((m + 1 : ℕ) : ℝ))))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy z hz
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound z hz y hy) (abs_nonneg _))
    (hζ.abs.mul_const _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy z hz
      have hr : ∀ k : ℤ, z - y ≠ k * L := hnot z hz y (Ioc_subset_Icc_self hy)
      have h1 := hasDerivAt_iteratedDeriv_scaledKernel hs0 hs1 hL (r := z - y) hr m
      exact (h1.comp_sub_const z y).const_mul (ζ y))
  exact hdiff.2

/-- The transport constant `A_s = -1/(4πβ tan(πs/2))` is nonzero for `β > 0` and `0 < s < 1`. -/
lemma transportConst_ne_zero {β s : ℝ} (hβ : 0 < β) (hs0 : 0 < s) (hs1 : s < 1) :
    transportConst β s ≠ 0 := by
  have htan : 0 < Real.tan (π * s / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by positivity) (by nlinarith [Real.pi_pos])
  unfold transportConst
  have : (4 * π * β * Real.tan (π * s / 2)) ≠ 0 := by positivity
  exact neg_ne_zero.2 (one_div_ne_zero this)

/-- The transport convolution equals `A_s` times the window convolution of order zero, since the
profile vanishes almost everywhere outside `[-ρ, ρ]`. -/
lemma transportConv_eq_window {β s L ρ : ℝ} (hρL : ρ ≤ L / 2) {ζ : ℝ → ℝ}
    (hsupp : ∀ᵐ y : ℝ, ρ ≤ |y| → ζ y = 0) (x : ℝ) :
    transportConv β s L ζ x = transportConst β s * windowConv s L ρ ζ 0 x := by
  unfold transportConv windowConv
  congr 1
  simp only [iteratedDeriv_zero]
  have hsub : Ioc (-ρ) ρ ⊆ Ioc (-(L / 2)) (L / 2) := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsupp' : ∀ y ∈ Ioc (-(L / 2)) (L / 2) \ Ioc (-ρ) ρ, ρ ≤ |y| := by
    rintro y ⟨-, hy⟩
    rcases le_or_gt y (-ρ) with h1 | h1
    · exact le_abs.2 (Or.inr (by linarith))
    · have h2 : ρ < y := by
        by_contra h2
        exact hy ⟨h1, not_lt.1 h2⟩
      exact le_abs.2 (Or.inl h2.le)
  refine MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioc.nullMeasurableSet hsub ?_
  filter_upwards [hsupp] with y hy hyd
  rw [hy (hsupp' y hyd), zero_mul]

/-- **Separation.** If `x0` avoids the periodized window, then a ball around `x0` keeps every window
point at a uniform distance from the lattice. -/
lemma exists_separation {L ρ : ℝ} (hL : 0 < L) {x0 : ℝ}
    (hx0 : ∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x0 ≠ y + k * L) :
    ∃ η > 0, ∀ x ∈ Metric.ball x0 η, ∀ y ∈ Icc (-ρ) ρ, ∀ k : ℤ, η ≤ |x - y - k * L| := by
  have hd0 : ρ < latticeDist L x0 := by
    by_contra h
    have h' : latticeDist L x0 ≤ ρ := not_lt.1 h
    have hdef : latticeDist L x0 = |x0 - L * round (x0 / L)| := by unfold latticeDist; rfl
    rw [hdef] at h'
    have hy := abs_le.1 h'
    exact hx0 (round (x0 / L)) (x0 - L * round (x0 / L)) ⟨by linarith [hy.1], by linarith [hy.2]⟩
      (by ring)
  refine ⟨(latticeDist L x0 - ρ) / 2, by linarith, fun x hx y hy k => ?_⟩
  have hxd : |x - x0| < (latticeDist L x0 - ρ) / 2 := by
    rw [Metric.mem_ball, Real.dist_eq] at hx
    exact hx
  have h1 := latticeDist_lipschitz L (x - y) x0 hL
  have h2 := latticeDist_le_abs_sub L (x - y) hL k
  have h3 : |x - y - x0| ≤ |x - x0| + |y| := by
    calc |x - y - x0| = |(x - x0) - y| := by ring_nf
      _ ≤ |x - x0| + |y| := abs_sub _ _
  have hy' : |y| ≤ ρ := abs_le.2 ⟨by linarith [hy.1], hy.2⟩
  linarith

/-- **Derivatives of the transport on the separated ball.** On a ball where the window stays
separated from the lattice, `∂^m Ψ = A_s ∂^m-window convolution`, for every `m`. -/
lemma iteratedDeriv_transportConv_of_mem {s β L ρ η : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hρL : ρ ≤ L / 2) {ζ : ℝ → ℝ} (hsupp : ∀ᵐ y : ℝ, ρ ≤ |y| → ζ y = 0)
    (hζ : IntegrableOn ζ (Ioc (-ρ) ρ)) (hη : 0 < η) {U : Set ℝ} (hU : IsOpen U)
    (hsep : ∀ x ∈ U, ∀ y ∈ Icc (-ρ) ρ, ∀ k : ℤ, η ≤ |x - y - k * L|) (m : ℕ) :
    ∀ x ∈ U, iteratedDeriv m (transportConv β s L ζ) x =
      transportConst β s * windowConv s L ρ ζ m x := by
  have hfun : transportConv β s L ζ = fun x => transportConst β s * windowConv s L ρ ζ 0 x :=
    funext (transportConv_eq_window hρL hsupp)
  have hG : ∀ m : ℕ, ∀ x ∈ U, HasDerivAt (windowConv s L ρ ζ m) (windowConv s L ρ ζ (m + 1) x) x :=
    fun m x hx => hasDerivAt_windowConv hs0 hs1 hL hζ hη hU hsep m hx
  rw [hfun]
  induction m with
  | zero =>
    intro x _
    simp only [iteratedDeriv_zero]
  | succ m ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv m (fun t => transportConst β s * windowConv s L ρ ζ 0 t) =ᶠ[𝓝 x]
        fun t => transportConst β s * windowConv s L ρ ζ m t :=
      Filter.eventually_of_mem (hU.mem_nhds hx) fun t ht => ih t ht
    rw [heq.deriv_eq, ((hG m x hx).const_mul (transportConst β s)).deriv]

/-- **Smoothness off the periodized support.** The
transport convolution is `C^∞` at every point at distance more than `ρ` from `[-ρ, ρ] + Lℤ`. -/
theorem contDiffAt_transportConv {s β L ρ : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hρL : ρ ≤ L / 2) {ζ : ℝ → ℝ} (hsupp : ∀ᵐ y : ℝ, ρ ≤ |y| → ζ y = 0)
    (hζ : IntegrableOn ζ (Ioc (-ρ) ρ)) {x0 : ℝ} (hx0 : ∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x0 ≠ y + k * L) :
    ContDiffAt ℝ ∞ (transportConv β s L ζ) x0 := by
  obtain ⟨η, hη, hsep⟩ := exists_separation hL hx0
  have hfun : transportConv β s L ζ = fun x => transportConst β s * windowConv s L ρ ζ 0 x :=
    funext (transportConv_eq_window hρL hsupp)
  have hG : ∀ m : ℕ, ∀ x ∈ Metric.ball x0 η,
      HasDerivAt (windowConv s L ρ ζ m) (windowConv s L ρ ζ (m + 1) x) x :=
    fun m x hx => hasDerivAt_windowConv hs0 hs1 hL hζ hη Metric.isOpen_ball hsep m hx
  have hcd := contDiffOn_of_hasDerivAt_family Metric.isOpen_ball (windowConv s L ρ ζ) hG 0
  rw [hfun]
  exact contDiffAt_const.mul (hcd.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hη)))

/-- **Derivative bounds off the periodized support.** For `m ≥ 1`,
`|Ψ^{(m)}(x)| ≤ C_{s,m,β} ‖ζ‖₁ |x|^{s-1-m}` for `1 ≤ |x| ≤ L/2`, with
`C_{s,m,β}` independent of `L` and of the profile. -/
theorem norm_iteratedDeriv_transportConv_le {s β : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hβ : 0 < β)
    {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (ζ : ℝ → ℝ) (ρ x0 : ℝ), 0 < ρ → ρ < 1 / 2 →
      1 ≤ |x0| → |x0| ≤ L / 2 → IntegrableOn ζ (Ioc (-ρ) ρ) →
      (∀ᵐ y : ℝ, ρ ≤ |y| → ζ y = 0) →
      ‖iteratedDeriv m (transportConv β s L ζ) x0‖ ≤
        C * (∫ y in Ioc (-ρ) ρ, |ζ y|) * |x0| ^ (s - 1 - (m : ℝ)) := by
  obtain ⟨Cm, hCm, hCb⟩ := norm_iteratedDeriv_scaledKernel_le hs0 hs1 hm
  have hexp : s - 1 - (m : ℝ) < 0 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  refine ⟨|transportConst β s| * Cm * (1 / 2) ^ (s - 1 - (m : ℝ)), by
      have hA : 0 < |transportConst β s| := abs_pos.2 (transportConst_ne_zero hβ hs0 hs1)
      positivity,
    fun L ζ ρ x0 hρ0 hρ1 hx1 hxL hζ hsupp => ?_⟩
  have hL2 : 2 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hρL : ρ ≤ L / 2 := by linarith
  have hx0 : ∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x0 ≠ y + k * L := by
    intro k y hy h
    have hyb : |y| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have := le_abs_sub_mul_of_mem_window hx1 hxL hyb k
    have h0 : x0 - y - k * L = 0 := by linarith
    rw [h0, abs_zero] at this
    linarith
  obtain ⟨η, hη, hsep⟩ := exists_separation hL hx0
  have hid := iteratedDeriv_transportConv_of_mem (β := β) hs0 hs1 hL hρL hsupp hζ hη Metric.isOpen_ball
    hsep m x0 (Metric.mem_ball_self hη)
  rw [hid, norm_mul, Real.norm_eq_abs]
  have hW : ‖windowConv s L ρ ζ m x0‖ ≤
      Cm * (|x0| / 2) ^ (s - 1 - (m : ℝ)) * ∫ y in Ioc (-ρ) ρ, |ζ y| := by
    unfold windowConv
    have hgint : Integrable (fun y : ℝ => Cm * (|x0| / 2) ^ (s - 1 - (m : ℝ)) * |ζ y|)
        (volume.restrict (Ioc (-ρ) ρ)) := hζ.abs.const_mul _
    calc ‖∫ y in Ioc (-ρ) ρ, ζ y * iteratedDeriv m (scaledKernel s L) (x0 - y)‖
        ≤ ∫ y in Ioc (-ρ) ρ, Cm * (|x0| / 2) ^ (s - 1 - (m : ℝ)) * |ζ y| := by
          refine MeasureTheory.norm_integral_le_of_norm_le hgint ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
          have hy' : y ∈ Icc (-ρ) ρ := Ioc_subset_Icc_self hy
          have hyb : |y| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hy'.1], by linarith [hy'.2]⟩
          have hd : |x0| / 2 ≤ latticeDist L (x0 - y) :=
            le_latticeDist (fun k => le_abs_sub_mul_of_mem_window hx1 hxL hyb k)
          have hnot : ∀ k : ℤ, x0 - y ≠ k * L := fun k h => by
            have := le_abs_sub_mul_of_mem_window hx1 hxL hyb k
            rw [show x0 - y - k * L = 0 by linarith, abs_zero] at this
            linarith
          have hK := hCb L (x0 - y) hL hnot
          have hpow : latticeDist L (x0 - y) ^ (s - 1 - (m : ℝ)) ≤ (|x0| / 2) ^ (s - 1 - (m : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hd hexp.le
          rw [norm_mul, Real.norm_eq_abs]
          calc |ζ y| * ‖iteratedDeriv m (scaledKernel s L) (x0 - y)‖
              ≤ |ζ y| * (Cm * latticeDist L (x0 - y) ^ (s - 1 - (m : ℝ))) :=
                mul_le_mul_of_nonneg_left hK (abs_nonneg _)
            _ ≤ |ζ y| * (Cm * (|x0| / 2) ^ (s - 1 - (m : ℝ))) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hCm.le) (abs_nonneg _)
            _ = Cm * (|x0| / 2) ^ (s - 1 - (m : ℝ)) * |ζ y| := by ring
      _ = Cm * (|x0| / 2) ^ (s - 1 - (m : ℝ)) * ∫ y in Ioc (-ρ) ρ, |ζ y| :=
          MeasureTheory.integral_const_mul _ _
  have hsplit : (|x0| / 2) ^ (s - 1 - (m : ℝ)) = |x0| ^ (s - 1 - (m : ℝ)) * (1 / 2) ^ (s - 1 - (m : ℝ)) := by
    rw [← Real.mul_rpow (abs_nonneg x0) (by norm_num)]
    congr 1
    ring
  calc |transportConst β s| * ‖windowConv s L ρ ζ m x0‖
      ≤ |transportConst β s| * (Cm * (|x0| / 2) ^ (s - 1 - (m : ℝ)) * ∫ y in Ioc (-ρ) ρ, |ζ y|) :=
        mul_le_mul_of_nonneg_left hW (abs_nonneg _)
    _ = |transportConst β s| * Cm * (1 / 2) ^ (s - 1 - (m : ℝ)) * (∫ y in Ioc (-ρ) ρ, |ζ y|) *
        |x0| ^ (s - 1 - (m : ℝ)) := by
        rw [hsplit]
        ring

end Riesz1
