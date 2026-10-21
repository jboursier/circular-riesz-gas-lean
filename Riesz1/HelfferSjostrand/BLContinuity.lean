/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLEnergy
public import Mathlib.Topology.Order.Compact

/-!
# Continuity of the inverse-Hessian energy

Uniform coercivity restricts quadratic optimization to one compact ball.
Continuity of its maximum follows without making any choice of inverses.
-/

public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace Riesz1

/-- The variational energy of continuous uniformly positive forms is continuous
on a compact finite-dimensional parameter set. -/
theorem bl_variational_energy_continuousOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK : IsCompact K) (g : E → E →L[ℝ] ℝ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (hg : ContinuousOn g K) (hB : ContinuousOn B K)
    {κ : ℝ} (hκ : 0 < κ) (hb : ∀ x ∈ K, ∀ h, κ * ‖h‖ ^ 2 ≤ B x h h) :
    ContinuousOn (fun x => sSup (Set.range (fun h : E => 2 * g x h - B x h h))) K := by
  obtain ⟨M, hM⟩ := (hK.image_of_continuousOn hg).isBounded.exists_norm_le
  let L : ℝ := max M 0
  have hL : 0 ≤ L := le_max_right _ _
  have hgL (x) (hx : x ∈ K) : ‖g x‖ ≤ L :=
    (hM _ (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  let R : ℝ := 2 * L / κ
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRκ : κ * R = 2 * L := by dsimp [R]; field_simp
  let obj (x h : E) : ℝ := 2 * g x h - B x h h
  have hbd (x) (hx : x ∈ K) : BddAbove (Set.range (obj x)) := by
    refine ⟨‖(InnerProductSpace.toDual ℝ E).symm (g x)‖ ^ 2 / κ, ?_⟩
    rintro _ ⟨h, rfl⟩
    simpa only [obj, InnerProductSpace.toDual_symm_apply] using
      bl_quadratic_le_norm_sq_div hκ (hb x hx)
        ((InnerProductSpace.toDual ℝ E).symm (g x)) h
  have hzero : (0 : E) ∈ Metric.closedBall 0 R := by simpa using hR
  have heq (x) (hx : x ∈ K) :
      sSup (Set.range (obj x)) = sSup (obj x '' Metric.closedBall 0 R) := by
    have hsub : obj x '' Metric.closedBall 0 R ⊆ Set.range (obj x) := image_subset_range _ _
    have hbd' := (hbd x hx).mono hsub
    have hz : (0 : ℝ) ≤ sSup (obj x '' Metric.closedBall 0 R) := by
      have hi := le_csSup hbd' (mem_image_of_mem (obj x) hzero)
      simpa [obj] using hi
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨h, rfl⟩
      by_cases hh : h ∈ Metric.closedBall 0 R
      · exact le_csSup hbd' (mem_image_of_mem _ hh)
      · have hr : R < ‖h‖ := by simpa using hh
        have hv : g x h ≤ L * ‖h‖ :=
          (le_abs_self _).trans ((g x).le_opNorm h |>.trans
            (mul_le_mul_of_nonneg_right (hgL x hx) (norm_nonneg h)))
        have hp := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr.le hκ.le) (norm_nonneg h)
        have hn : obj x h ≤ 0 := by dsimp [obj]; nlinarith [hb x hx h]
        exact hn.trans hz
    · exact csSup_le_csSup (hbd x hx) ⟨_, mem_image_of_mem _ hzero⟩ hsub
  have hgc : Continuous (fun x : K => g x) := continuousOn_iff_continuous_domRestrict.mp hg
  have hBc : Continuous (fun x : K => B x) := continuousOn_iff_continuous_domRestrict.mp hB
  have hc : Continuous (Function.uncurry (fun (x : K) (h : E) => obj x h)) := by
    change Continuous (fun p : K × E => 2 * g p.1 p.2 - B p.1 p.2 p.2)
    exact (continuous_const.mul ((hgc.comp continuous_fst).clm_apply continuous_snd)).sub
      (((hBc.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd)
  rw [continuousOn_iff_continuous_domRestrict]
  convert (isCompact_closedBall (0 : E) R).continuous_sSup
    (f := fun (x : K) (h : E) => obj x h) hc using 1
  ext x
  exact heq x x.property

/-- The actual Hessian energy is continuous up to the boundary. Coercivity at
boundary points follows by continuity from the assumed interior lower bound. -/
theorem bl_hessian_energy_continuousOn
    {d : ℕ} {U W : Set (EuclideanSpace ℝ (Fin d))}
    {V F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : Bornology.IsBounded U) (hW : IsOpen W) (hUW : closure U ⊆ W)
    (hV : ContDiffOn ℝ 2 V W) (hF : ContDiffOn ℝ 2 F W)
    {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h) :
    ContinuousOn (fun x => sSup (Set.range (fun h : EuclideanSpace ℝ (Fin d) =>
      2 * fderiv ℝ F x h - fderiv ℝ (fderiv ℝ V) x h h))) (closure U) := by
  have hg := (hF.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hUW
  have hV1 : ContDiffOn ℝ 1 (fderiv ℝ V) W := hV.fderiv_of_isOpen hW (by norm_num)
  have hB := (hV1.continuousOn_fderiv_of_isOpen hW (by norm_num)).mono hUW
  apply bl_variational_energy_continuousOn hU.isCompact_closure _ _ hg hB hκ
  intro x hx h
  exact le_on_closure (fun y hy => hb y hy h) continuousOn_const
    ((hB.clm_apply continuousOn_const).clm_apply continuousOn_const) hx

end Riesz1

end
