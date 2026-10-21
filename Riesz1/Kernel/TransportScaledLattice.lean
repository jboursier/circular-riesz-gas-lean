/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaled
public import Riesz1.Kernel.TransportKernelBounds

/-!
# Smoothness and derivative bounds of the scaled transport kernel

For `L > 0` the scaled kernel `K_{s,L}(r) = L^{s-1} K_s(r/L)` of `TransportScaled` is `C^∞` off the
lattice `L ℤ`, and its `m`-th derivative is bounded by `C_{s,m} dist(r, L ℤ)^{s-1-m}` with `C_{s,m}`
independent of `L`. Here `dist(r, L ℤ) = |r - L · round(r/L)|`, the distance to the nearest lattice
point (`latticeDist`). This is the derivative part of `Riesz1.transport_kernel_scaled`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The distance from `r` to the lattice `L ℤ`, written `|r - L · round(r/L)|` (the nearest
lattice point is `L · round(r/L)`). -/
@[expose] noncomputable def latticeDist (L r : ℝ) : ℝ := |r - L * round (r / L)|

/-- Every integer `k` satisfies `|t - k| ≥ min(fract t, 1 - fract t)`. -/
lemma min_fract_le_abs_sub_int (t : ℝ) (k : ℤ) :
    min (Int.fract t) (1 - Int.fract t) ≤ |t - k| := by
  have hfl : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have hfr : Int.fract t = t - ⌊t⌋ := rfl
  rcases le_or_gt k ⌊t⌋ with hk | hk
  · have hk' : (k : ℝ) ≤ ⌊t⌋ := by exact_mod_cast hk
    calc min (Int.fract t) (1 - Int.fract t) ≤ Int.fract t := min_le_left _ _
      _ ≤ t - k := by rw [hfr]; linarith
      _ ≤ |t - k| := le_abs_self _
  · have hk' : (⌊t⌋ : ℝ) + 1 ≤ k := by exact_mod_cast (show ⌊t⌋ + 1 ≤ k by omega)
    have hlt : t < ⌊t⌋ + 1 := Int.lt_floor_add_one t
    calc min (Int.fract t) (1 - Int.fract t) ≤ 1 - Int.fract t := min_le_right _ _
      _ ≤ k - t := by rw [hfr]; linarith
      _ ≤ |k - t| := le_abs_self _
      _ = |t - k| := abs_sub_comm _ _

/-- The distance from `t` to `ℤ` is `min(fract t, 1 - fract t)`, attained at the nearest integer. -/
lemma abs_sub_round_eq_min (t : ℝ) :
    |t - round t| = min (Int.fract t) (1 - Int.fract t) := by
  have hfr : Int.fract t = t - ⌊t⌋ := rfl
  have hfl : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
  have hlt : t < ⌊t⌋ + 1 := Int.lt_floor_add_one t
  apply le_antisymm
  · have h1 := round_le t ⌊t⌋
    have h2 := round_le t (⌊t⌋ + 1)
    have e1 : |t - (⌊t⌋ : ℝ)| = Int.fract t := by
      rw [hfr, abs_of_nonneg (by linarith)]
    have e2 : |t - ((⌊t⌋ + 1 : ℤ) : ℝ)| = 1 - Int.fract t := by
      rw [hfr, abs_of_neg (by push_cast; linarith)]
      push_cast
      ring
    exact le_min (by linarith) (by linarith)
  · exact min_fract_le_abs_sub_int t (round t)

/-- The lattice distance in terms of the fractional part. -/
lemma latticeDist_eq (L r : ℝ) (hL : 0 < L) :
    latticeDist L r = L * min (Int.fract (r / L)) (1 - Int.fract (r / L)) := by
  unfold latticeDist
  have hL' : L ≠ 0 := hL.ne'
  have e : r - L * round (r / L) = L * (r / L - round (r / L)) := by field_simp
  rw [e, abs_mul, abs_of_pos hL, abs_sub_round_eq_min]

/-- The lattice distance is at most the distance to any lattice point. -/
lemma latticeDist_le_abs_sub (L r : ℝ) (hL : 0 < L) (k : ℤ) :
    latticeDist L r ≤ |r - k * L| := by
  unfold latticeDist
  have h := round_le (r / L) k
  have e1 : r - L * round (r / L) = L * (r / L - round (r / L)) := by field_simp
  have e2 : r - k * L = L * (r / L - k) := by field_simp
  rw [e1, e2, abs_mul, abs_mul, abs_of_pos hL]
  exact mul_le_mul_of_nonneg_left h hL.le

/-- The lattice distance is positive off the lattice. -/
lemma latticeDist_pos {L r : ℝ} (hr : ∀ k : ℤ, r ≠ k * L) : 0 < latticeDist L r := by
  unfold latticeDist
  refine abs_pos.2 (sub_ne_zero.2 fun h => hr (round (r / L)) ?_)
  linarith

/-- The lattice distance is the distance from `r` to the lattice `L ℤ` (as `Metric.infDist`): the
nearest lattice point is `L · round(r/L)`. -/
lemma latticeDist_eq_infDist {L : ℝ} (hL : 0 < L) (r : ℝ) :
    latticeDist L r = Metric.infDist r (Set.range fun k : ℤ => (k : ℝ) * L) := by
  have : Nonempty (Set.range fun k : ℤ => (k : ℝ) * L) := ⟨⟨0, 0, by simp⟩⟩
  apply le_antisymm
  · rw [Metric.infDist_eq_iInf]
    refine le_ciInf fun y => ?_
    obtain ⟨k, hk⟩ := y.2
    rw [← hk, Real.dist_eq]
    exact latticeDist_le_abs_sub L r hL k
  · have h := Metric.infDist_le_dist_of_mem (x := r)
      (show (round (r / L) : ℝ) * L ∈ Set.range fun k : ℤ => (k : ℝ) * L from ⟨round (r / L), rfl⟩)
    rw [Real.dist_eq] at h
    have e : latticeDist L r = |r - (round (r / L) : ℝ) * L| := by
      unfold latticeDist
      rw [mul_comm]
    rw [e]
    exact h

/-- The points off the integers form an open set. -/
lemma isOpen_not_int : IsOpen {t : ℝ | ∀ k : ℤ, t ≠ k} := by
  rw [Metric.isOpen_iff]
  intro t ht
  have ht' : ∀ k : ℤ, t ≠ k := ht
  refine ⟨|t - round t|, ?_, ?_⟩
  · refine abs_pos.2 (sub_ne_zero.2 fun h => ht' (round t) ?_)
    exact_mod_cast h
  · intro s hs
    show ∀ k : ℤ, s ≠ k
    intro k hsk
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have h1 := round_le t k
    have h2 : |t - k| ≤ |s - t| := by
      calc |t - k| = |(t - s) + (s - k)| := by ring_nf
        _ ≤ |t - s| + |s - k| := abs_add_le _ _
        _ = |s - t| := by rw [abs_sub_comm t s, hsk, sub_self, abs_zero, add_zero]
    linarith

/-- Scaling of the iterated derivative of a function that is smooth on an open set `U`: for
`c ≠ 0`, the derivative of `t ↦ f(c t)` is `c^m` times the derivative of `f` at `c x`. -/
lemma iteratedDeriv_comp_mul_of_contDiffOn {U : Set ℝ} (hU : IsOpen U) (c : ℝ) (m : ℕ) :
    ∀ f : ℝ → ℝ, ContDiffOn ℝ ∞ f U → ∀ x : ℝ, c * x ∈ U →
      iteratedDeriv m (fun t => f (c * t)) x = c ^ m * iteratedDeriv m f (c * x) := by
  induction m with
  | zero => intro f _ x _; simp
  | succ m ih =>
    intro f hf x hx
    have hdf : ContDiffOn ℝ ∞ (deriv f) U := ((contDiffOn_infty_iff_deriv_of_isOpen hU).1 hf).2
    have hderiv : deriv (fun t => f (c * t)) = fun t => c • deriv f (c * t) := by
      funext t
      exact deriv_comp_mul_left (f := f) (c := c) (x := t)
    have hcd : ContDiffAt ℝ m (fun t => deriv f (c * t)) x := by
      have h1 : ContDiffAt ℝ ∞ (deriv f) (c * x) :=
        (hdf (c * x) hx).contDiffAt (hU.mem_nhds hx)
      have h2 : ContDiffAt ℝ ∞ (fun t : ℝ => c * t) x :=
        (contDiff_const.mul contDiff_id).contDiffAt
      exact (ContDiffAt.comp (f := fun t : ℝ => c * t) (g := deriv f) x h1 h2).of_le (by simp)
    have hsm : iteratedDeriv m (fun t => c • deriv f (c * t)) x =
        c • iteratedDeriv m (fun t => deriv f (c * t)) x := iteratedDeriv_const_smul hcd c
    rw [iteratedDeriv_succ', hderiv, hsm, ih (deriv f) hdf x hx, iteratedDeriv_succ', smul_eq_mul,
      pow_succ]
    ring

/-- The complement of the lattice `L ℤ` is open. -/
lemma isOpen_lattice_compl {L : ℝ} (hL : 0 < L) : IsOpen {r : ℝ | ∀ k : ℤ, r ≠ k * L} := by
  have h : {r : ℝ | ∀ k : ℤ, r ≠ k * L} = (fun r : ℝ => r / L) ⁻¹' {t : ℝ | ∀ k : ℤ, t ≠ k} := by
    ext r
    refine forall_congr' fun k => ?_
    show r ≠ k * L ↔ r / L ≠ k
    rw [Ne, Ne, div_eq_iff hL.ne']
  rw [h]
  exact isOpen_not_int.preimage (continuous_id.div_const L)

/-- Off the lattice the scaled kernel is the unit kernel rescaled: `K_{s,L}(r) = L^{s-1} K_s(r/L)`.
The identity follows from uniqueness of limits, since the scaled symmetric sums are `L^{s-1}` times
the unit symmetric sums. -/
lemma scaledKernel_eq_periodic {s L r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hr : ∀ k : ℤ, r ≠ k * L) :
    scaledKernel s L r = L ^ (s - 1) * periodicKernel s (r / L) := by
  have hu : ∀ k : ℤ, r / L ≠ k := fun k h => hr k (by rw [div_eq_iff hL.ne'] at h; linarith)
  have h1 := tendsto_scaled_signPow hs0 hs1 hL hr
  have h2 := ((tendsto_symmetric_signPow hs0 hs1 hu).const_mul (L ^ (s - 1)))
  refine tendsto_nhds_unique h1 (h2.congr fun M => ?_)
  rw [signPow_scaled_sum hL M]

/-- Near a point off the lattice, the scaled kernel agrees with `L^{s-1} K_s(· / L)`. -/
lemma scaledKernel_eventuallyEq {s L r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hr : ∀ k : ℤ, r ≠ k * L) :
    scaledKernel s L =ᶠ[𝓝 r] fun y => L ^ (s - 1) * periodicKernel s (y / L) := by
  filter_upwards [isOpen_lattice_compl hL |>.mem_nhds hr] with y hy
  exact scaledKernel_eq_periodic hs0 hs1 hL hy

/-- The scaled kernel is `C^∞` at every point off the lattice `L ℤ`. -/
lemma scaledKernel_contDiffAt {s L r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hr : ∀ k : ℤ, r ≠ k * L) : ContDiffAt ℝ ∞ (scaledKernel s L) r := by
  have hu : ∀ k : ℤ, r / L ≠ k := fun k h => hr k (by rw [div_eq_iff hL.ne'] at h; linarith)
  have hK := contDiffAt_periodicKernel_of_not_int hs0 hs1 hu
  have h2 : ContDiffAt ℝ ∞ (fun y : ℝ => y / L) r := contDiffAt_id.div_const L
  have h3 : ContDiffAt ℝ ∞ (fun y : ℝ => periodicKernel s (y / L)) r :=
    ContDiffAt.comp (f := fun y : ℝ => y / L) (g := periodicKernel s) r hK h2
  exact ((contDiffAt_const (c := L ^ (s - 1))).mul h3).congr_of_eventuallyEq
    (scaledKernel_eventuallyEq hs0 hs1 hL hr)

/-- The scaled kernel is `C^∞` on the complement of the lattice. -/
lemma scaledKernel_contDiffOn {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L) :
    ContDiffOn ℝ ∞ (scaledKernel s L) {r : ℝ | ∀ k : ℤ, r ≠ k * L} :=
  fun _ hr => (scaledKernel_contDiffAt hs0 hs1 hL hr).contDiffWithinAt

/-- The `m`-th derivative of the scaled kernel off the lattice: `L^{s-1-m}` times the `m`-th
derivative of the unit kernel at `r / L`. -/
lemma iteratedDeriv_scaledKernel_eq {s L r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hr : ∀ k : ℤ, r ≠ k * L) (m : ℕ) :
    iteratedDeriv m (scaledKernel s L) r =
      (L⁻¹) ^ m * (L ^ (s - 1) * iteratedDeriv m (periodicKernel s) (r / L)) := by
  have hU : ∀ k : ℤ, r / L ≠ k := fun k h => hr k (by rw [div_eq_iff hL.ne'] at h; linarith)
  have hK : ContDiffOn ℝ ∞ (fun t : ℝ => L ^ (s - 1) * periodicKernel s t) {t : ℝ | ∀ k : ℤ, t ≠ k} :=
    fun t ht => ((contDiffAt_const (c := L ^ (s - 1))).mul
      (contDiffAt_periodicKernel_of_not_int hs0 hs1 ht)).contDiffWithinAt
  have hscale := iteratedDeriv_comp_mul_of_contDiffOn isOpen_not_int (L⁻¹) m
    (fun t => L ^ (s - 1) * periodicKernel s t) hK r (by
      show ∀ k : ℤ, L⁻¹ * r ≠ k
      intro k h
      exact hU k (by rw [div_eq_inv_mul]; exact h))
  have hfun : (fun t : ℝ => L ^ (s - 1) * periodicKernel s (L⁻¹ * t)) =ᶠ[𝓝 r]
      scaledKernel s L := by
    filter_upwards [isOpen_lattice_compl hL |>.mem_nhds hr] with y hy
    rw [scaledKernel_eq_periodic hs0 hs1 hL hy, div_eq_inv_mul]
  have hsm : iteratedDeriv m (fun t : ℝ => L ^ (s - 1) * periodicKernel s t) (L⁻¹ * r) =
      L ^ (s - 1) * iteratedDeriv m (periodicKernel s) (L⁻¹ * r) := by
    have hK' : ContDiffAt ℝ ∞ (periodicKernel s) (L⁻¹ * r) :=
      contDiffAt_periodicKernel_of_not_int hs0 hs1 (fun k h => hU k (by
        rw [div_eq_inv_mul]; exact h))
    exact iteratedDeriv_const_smul (hK'.of_le (by simp)) (L ^ (s - 1))
  rw [← hfun.iteratedDeriv_eq m, hscale, hsm, div_eq_inv_mul]

/-- The `m`-th derivative of the scaled kernel is bounded by `C_{s,m} · dist(r, L ℤ)^{s-1-m}`, with
`C_{s,m}` independent of `L`. -/
theorem norm_iteratedDeriv_scaledKernel_le {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {m : ℕ}
    (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ L r : ℝ, 0 < L → (∀ k : ℤ, r ≠ k * L) →
      ‖iteratedDeriv m (scaledKernel s L) r‖ ≤ C * (latticeDist L r) ^ (s - 1 - (m : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := norm_iteratedDeriv_periodicKernel_le hs0 hs1 hm
  refine ⟨C, hC, fun L r hL hr => ?_⟩
  have hu : ∀ k : ℤ, r / L ≠ k := fun k h => hr k (by rw [div_eq_iff hL.ne'] at h; linarith)
  rw [iteratedDeriv_scaledKernel_eq hs0 hs1 hL hr m, latticeDist_eq L r hL]
  set μ := min (Int.fract (r / L)) (1 - Int.fract (r / L)) with hμ
  have hμ0 : 0 ≤ μ := le_min (Int.fract_nonneg _) (by linarith [Int.fract_lt_one (r / L)])
  have hKb := hb (r / L) hu
  rw [← hμ] at hKb
  have hpow : L ^ (s - 1 - (m : ℝ)) = L ^ (s - 1) * (L⁻¹) ^ m := by
    rw [Real.rpow_sub hL, Real.rpow_natCast, inv_pow, div_eq_mul_inv]
  have hLpos : 0 < L⁻¹ ^ m := pow_pos (inv_pos.2 hL) m
  have hLs : 0 < L ^ (s - 1) := Real.rpow_pos_of_pos hL _
  calc ‖(L⁻¹) ^ m * (L ^ (s - 1) * iteratedDeriv m (periodicKernel s) (r / L))‖
      = L⁻¹ ^ m * L ^ (s - 1) * ‖iteratedDeriv m (periodicKernel s) (r / L)‖ := by
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hLpos, abs_of_pos hLs]
        ring
    _ ≤ L⁻¹ ^ m * L ^ (s - 1) * (C * μ ^ (s - 1 - (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hKb (by positivity)
    _ = C * (L * μ) ^ (s - 1 - (m : ℝ)) := by
        rw [Real.mul_rpow hL.le hμ0, hpow]
        ring

end Riesz1
