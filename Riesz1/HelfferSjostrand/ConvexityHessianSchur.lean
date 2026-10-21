/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.ConvexLineHessian
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Schur complement as a variational energy (part of the proof of Lemma 3.7)

Let `K` be convex and `C²` on the open convex set `Q ⊆ ℝ^m × ℝ^n`. For a point `(z, y) ∈ Q` and a
direction `b ∈ ℝ^m`, put `B = D²K(z, y)` and define the Schur energy

`schurEnergy K z b y = inf_{a ∈ ℝⁿ} B((b, a), (b, a))`.

The Brascamp–Lieb energy of the fiber function `y ↦ DK(z,y)(b,0)`, with weak gradient `G`, is
`sup_h (2 ⟪G, h⟫ - D²_yy K(z,y)(h, h))`. Substituting `h = -a` shows that it equals
`B((b,0),(b,0)) - schurEnergy K z b y`, and `schurEnergy` is nonnegative by convexity. The
ingredients proved here are:

* the Hessian of the fiber function `y ↦ K(z, y)` is the `yy`-block of `D²K`
  (`fderiv_fderiv_fiber`).
* the gradient of `y ↦ DK(z,y)(b,0)` is `D²K(z,y)((0, ·), (b, 0))` (`fderiv_fiber_apply`).
* the supremum of `c - g(-h)` over `h` is `c - inf g` for a nonnegative `g` (`sSup_range_neg_eq`).
* the identity `sSup_fiber_energy_eq` and the nonnegativity `schurEnergy_nonneg`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace

namespace Riesz1.ConvexityHessian

variable {m n : ℕ}

/-- The Schur energy `inf_a D²K(z, y)((b, a), (b, a))` of the Hessian of `K` at `(z, y)`. -/
def schurEnergy (K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) (b : EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨅ a : EuclideanSpace ℝ (Fin n),
    fderiv ℝ (fderiv ℝ K) (z, y) (b, a) (b, a)

/-- The Hessian of `y ↦ K(z, y)` at `x` is the `yy`-block of the Hessian of `K` at `(z, x)`. -/
theorem fderiv_fderiv_fiber {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q) {z : EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hx : (z, x) ∈ Q) (h : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun y => K (z, y))) x h h =
      fderiv ℝ (fderiv ℝ K) (z, x) (0, h) (0, h) := by
  have hKa : ContDiffAt ℝ 2 K (z, x) := hK.contDiffAt (hQo.mem_nhds hx)
  have hVa : ContDiffAt ℝ 2 (fun y => K (z, y)) x :=
    hKa.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hdV : DifferentiableAt ℝ (fderiv ℝ (fun y => K (z, y))) x :=
    (hVa.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdK : DifferentiableAt ℝ (fderiv ℝ K) (z, x) :=
    (hKa.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := hasDerivAt_fderiv_comp_line (f := fun y => K (z, y)) (p := x) (v := h) hdV
  have hB := hasDerivAt_fderiv_comp_line (f := K) (p := (z, x))
    (v := ((0, h) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) hdK
  have hfun : (fun s : ℝ => K (z, x + s • h)) =
      fun s : ℝ => K ((z, x) + s • ((0, h) : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin n))) :=
    funext fun s => by simp
  -- Near `0` the two directional derivatives describe the same function `s ↦ K(z, x + s h)`.
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), (z, x + t • h) ∈ Q := by
    have hc : Continuous fun t : ℝ => (z, x + t • h) := by fun_prop
    filter_upwards [(hQo.preimage hc).mem_nhds (by simpa using hx)] with t ht
    exact ht
  have key : ∀ᶠ t in 𝓝 (0 : ℝ),
      fderiv ℝ K ((z, x) + t • ((0, h) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
          (0, h) =
        fderiv ℝ (fun y => K (z, y)) (x + t • h) h := by
    filter_upwards [hmem] with t ht
    have hpt : (z, x + t • h) = (z, x) + t • ((0, h) : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin n)) := by
      ext <;> simp
    have hKt : DifferentiableAt ℝ K (z, x + t • h) :=
      (hK.differentiableOn (by norm_num)).differentiableAt (hQo.mem_nhds ht)
    have hVt : DifferentiableAt ℝ (fun y => K (z, y)) (x + t • h) :=
      hKt.comp (x + t • h) ((differentiableAt_const z).prodMk differentiableAt_id)
    have d1 := hasDerivAt_comp_line (f := fun y => K (z, y)) (p := x) (v := h) (s := t) hVt
    have d2 := hasDerivAt_comp_line (f := K) (p := (z, x))
      (v := ((0, h) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) (s := t)
      (by rw [← hpt]; exact hKt)
    have d2' : HasDerivAt (fun s : ℝ => K (z, x + s • h))
        (fderiv ℝ K ((z, x) + t • ((0, h) : EuclideanSpace ℝ (Fin m) ×
          EuclideanSpace ℝ (Fin n))) (0, h)) t := by
      rw [hfun]
      exact d2
    exact d2'.unique d1
  have key' : (fun t : ℝ => fderiv ℝ (fun y => K (z, y)) (x + t • h) h) =ᶠ[𝓝 (0 : ℝ)]
      fun t : ℝ => fderiv ℝ K ((z, x) + t • ((0, h) : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin n))) (0, h) :=
    key.mono fun t ht => ht.symm
  have hB' := hB.congr_of_eventuallyEq key'
  exact hA.unique hB'

/-- The gradient of `y ↦ DK(z, y)(b, 0)` at `y` in direction `h` is `D²K(z, y)((0, h), (b, 0))`. -/
theorem fderiv_fiber_apply {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q) {z : EuclideanSpace ℝ (Fin m)}
    {y : EuclideanSpace ℝ (Fin n)} (hy : (z, y) ∈ Q) (b : EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y' => fderiv ℝ K (z, y') (b, 0)) y h =
      fderiv ℝ (fderiv ℝ K) (z, y) (0, h) (b, 0) := by
  have hK1 : ContDiffAt ℝ 1 (fderiv ℝ K) (z, y) :=
    (hK.contDiffAt (hQo.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)
  have hφ : DifferentiableAt ℝ (fun y' : EuclideanSpace ℝ (Fin n) => (z, y')) y :=
    (differentiableAt_const z).prodMk differentiableAt_id
  have hdK1 : DifferentiableAt ℝ (fun y' : EuclideanSpace ℝ (Fin n) => fderiv ℝ K (z, y')) y :=
    (hK1.differentiableAt (by norm_num)).comp y hφ
  have hF : DifferentiableAt ℝ (fun y' => fderiv ℝ K (z, y') (b, 0)) y :=
    hdK1.clm_apply (differentiableAt_const _)
  have hA := hasDerivAt_comp_line (f := fun y' => fderiv ℝ K (z, y') (b, 0)) (p := y) (v := h)
    (s := 0) (by simpa using hF)
  simp only [zero_smul, add_zero] at hA
  have hdK : DifferentiableAt ℝ (fderiv ℝ K) (z, y) :=
    (hK1.differentiableAt (by norm_num))
  have hB := hasDerivAt_fderiv_apply_comp_line (f := K) (p := (z, y))
    (v := ((0, h) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))
    (w := ((b, 0) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) hdK
  have hfun : (fun t : ℝ => fderiv ℝ K (z, y + t • h) (b, 0)) =
      fun t : ℝ => fderiv ℝ K ((z, y) + t • ((0, h) : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin n))) (b, 0) :=
    funext fun t => by
      rw [show (z, y + t • h) = (z, y) + t • ((0, h) : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin n)) from by ext <;> simp]
  have hB' : HasDerivAt (fun t : ℝ => fderiv ℝ K (z, y + t • h) (b, 0))
      (fderiv ℝ (fderiv ℝ K) (z, y) (0, h) (b, 0)) 0 := by
    rw [hfun]
    exact hB
  exact hA.unique hB'

/-- The Hessian of a convex `C²` function is symmetric. -/
theorem hessian_symm_of_mem {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hK : ContDiffOn ℝ 2 K Q) {p : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin n)} (hp : p ∈ Q) (u w : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ K) p u w = fderiv ℝ (fderiv ℝ K) p w u :=
  (hK.contDiffAt (hQo.mem_nhds hp)).isSymmSndFDerivAt (by simp) u w

/-- For a symmetric bilinear form `B`, `B(u - w, u - w) = B(u, u) - 2 B(w, u) + B(w, w)`. -/
theorem bilin_sub_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u w, B u w = B w u) (u w : E) :
    B (u - w) (u - w) = B u u - 2 * B w u + B w w := by
  simp only [map_sub, sub_apply]
  rw [hB u w]
  ring

/-- The supremum of `c - g(-h)` over `h` is `c - inf g`, for a nonnegative `g`. -/
theorem sSup_range_neg_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    {g : E → ℝ} (hg : ∀ a, 0 ≤ g a) :
    sSup (Set.range fun h : E => c - g (-h)) = c - ⨅ a, g a := by
  have hbdd : BddAbove (Set.range fun h : E => c - g (-h)) :=
    ⟨c, by rintro _ ⟨h, rfl⟩; linarith [hg (-h)]⟩
  have hbddg : BddBelow (Set.range g) := ⟨0, by rintro _ ⟨a, rfl⟩; exact hg a⟩
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨h, rfl⟩
    linarith [ciInf_le hbddg (-h)]
  · have hinf : c - sSup (Set.range fun h : E => c - g (-h)) ≤ ⨅ a, g a := by
      refine le_ciInf fun a => ?_
      have := le_csSup hbdd (Set.mem_range_self (-a))
      simp only [neg_neg] at this
      linarith
    linarith

/-- The Schur energy is nonnegative when the Hessian of `K` is positive semidefinite. -/
theorem schurEnergy_nonneg {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hQc : Convex ℝ Q) (hKc : ConvexOn ℝ Q K) (hK : ContDiffOn ℝ 2 K Q)
    {z : EuclideanSpace ℝ (Fin m)} {y : EuclideanSpace ℝ (Fin n)} (hy : (z, y) ∈ Q)
    (b : EuclideanSpace ℝ (Fin m)) :
    0 ≤ schurEnergy K z b y :=
  le_ciInf fun a => fderiv_fderiv_nonneg_of_convexOn hQo hQc hKc hK hy (b, a)

/-- The Brascamp–Lieb energy of the fiber function is the Schur complement: if `G` represents the
gradient of `y ↦ DK(z, y)(b, 0)` at `y`, then `sup_h (2⟪G, h⟫ - D²_yy K(h, h))` equals
`D²K((b,0),(b,0)) - schurEnergy K z b y`. -/
theorem sSup_fiber_energy_eq {Q : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hQc : Convex ℝ Q) (hKc : ConvexOn ℝ Q K) (hK : ContDiffOn ℝ 2 K Q)
    {z : EuclideanSpace ℝ (Fin m)} {y : EuclideanSpace ℝ (Fin n)} (hy : (z, y) ∈ Q)
    (b : EuclideanSpace ℝ (Fin m)) (G : EuclideanSpace ℝ (Fin n))
    (hG : ∀ h, ⟪G, h⟫_ℝ = fderiv ℝ (fun y' => fderiv ℝ K (z, y') (b, 0)) y h) :
    sSup (Set.range fun h : EuclideanSpace ℝ (Fin n) =>
        2 * ⟪G, h⟫_ℝ - fderiv ℝ (fderiv ℝ (fun y' => K (z, y'))) y h h) =
      fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) - schurEnergy K z b y := by
  have hsym := hessian_symm_of_mem hQo hK hy
  have hfun : (fun h : EuclideanSpace ℝ (Fin n) =>
        2 * ⟪G, h⟫_ℝ - fderiv ℝ (fderiv ℝ (fun y' => K (z, y'))) y h h) =
      fun h => fderiv ℝ (fderiv ℝ K) (z, y) (b, 0) (b, 0) -
        (fun a : EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ (fderiv ℝ K) (z, y) (b, a) (b, a)) (-h) := by
    funext h
    rw [hG h, fderiv_fiber_apply hQo hK hy b h, fderiv_fderiv_fiber hQo hK hy h]
    have hsplit : ((b, -h) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) =
        (b, 0) - (0, h) := by
      ext <;> simp
    simp only [hsplit]
    rw [bilin_sub_sq (fderiv ℝ (fderiv ℝ K) (z, y)) hsym (b, 0) (0, h)]
    ring
  rw [hfun, sSup_range_neg_eq _ (g := fun a : EuclideanSpace ℝ (Fin n) =>
    fderiv ℝ (fderiv ℝ K) (z, y) (b, a) (b, a))]
  · rfl
  · intro a
    exact fderiv_fderiv_nonneg_of_convexOn hQo hQc hKc hK hy (b, a)

end Riesz1.ConvexityHessian

end

end
