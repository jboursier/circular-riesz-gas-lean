/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLQuadratic
public import Riesz1.HelfferSjostrand.BLEnergy
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Bases

/-!
# The variational Brascamp–Lieb energy: continuity in the gradient and measurability

For a coercive symmetric form `B`, the energy `g ↦ sup_h (2⟪g, h⟫ - B h h)` is the inverse
quadratic form of `g` (`bl_quadratic_sSup_eq_inverse`). Three facts are used by the density
argument of Lemma 3.6:

* the energy is Lipschitz in the gradient, with an explicit constant depending on `κ` only.
* the supremum over all directions is the supremum over a dense sequence of directions, so the
  energy of an arbitrary measurable field is an almost everywhere limit of measurable functions.
* the Hessian of a `C²` potential is measurable in the base point, without any continuity.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace

namespace Riesz1

/-- The gradient of a function is the Riesz representative of its derivative, paired with any
direction, so the energy written with `fderiv` and with `gradient` agree. -/
theorem inner_gradient_eq_fderiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (F : E → ℝ) (x h : E) :
    ⟪gradient F x, h⟫_ℝ = fderiv ℝ F x h := by
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {B : E →L[ℝ] E →L[ℝ] ℝ}

/-- The variational energy is Lipschitz in the gradient on the set where the form is coercive:
`Q(g) - Q(g') ≤ 4 ‖g - g'‖ ‖g‖ / κ`. -/
theorem bl_sSup_sub_le (hs : ∀ v w, B v w = B w v) {κ : ℝ} (hκ : 0 < κ)
    (hb : ∀ h, κ * ‖h‖ ^ 2 ≤ B h h) (g g' : E) :
    sSup (Set.range fun h : E => 2 * ⟪g, h⟫_ℝ - B h h) -
        sSup (Set.range fun h : E => 2 * ⟪g', h⟫_ℝ - B h h) ≤
      4 * ‖g - g'‖ * ‖g‖ / κ := by
  have hC : IsCoercive B := ⟨κ, hκ, fun h => by simpa only [pow_two, mul_assoc] using hb h⟩
  have hbdd (u : E) : BddAbove (Set.range fun h : E => 2 * ⟪u, h⟫_ℝ - B h h) :=
    ⟨‖u‖ ^ 2 / κ, by
      rintro _ ⟨h, rfl⟩
      exact bl_quadratic_le_norm_sq_div hκ hb u h⟩
  -- A maximizer `h₀` for the energy at `g`, with value `Q(g) ≥ 0`.
  obtain ⟨h₀, hh₀⟩ := (bl_quadratic_isGreatest hC hs g).1
  dsimp only at hh₀
  have hsup_g : sSup (Set.range fun h : E => 2 * ⟪g, h⟫_ℝ - B h h) = 2 * ⟪g, h₀⟫_ℝ - B h₀ h₀ := by
    rw [hh₀]
    exact (bl_quadratic_isGreatest hC hs g).csSup_eq
  have hQnonneg : 0 ≤ 2 * ⟪g, h₀⟫_ℝ - B h₀ h₀ := by
    rw [← hsup_g]
    exact (bl_variational_energy_bounds B g hκ hb).1
  have hQ'_ge : 2 * ⟪g', h₀⟫_ℝ - B h₀ h₀ ≤
      sSup (Set.range fun h : E => 2 * ⟪g', h⟫_ℝ - B h h) :=
    le_csSup (hbdd g') ⟨h₀, rfl⟩
  -- Bound on the maximizer: `κ ‖h₀‖² ≤ B h₀ h₀ ≤ 2 ‖g‖ ‖h₀‖`.
  have hmax : κ * ‖h₀‖ ^ 2 ≤ 2 * ‖g‖ * ‖h₀‖ := by
    have h1 : B h₀ h₀ ≤ 2 * ⟪g, h₀⟫_ℝ := by linarith
    have h2 : ⟪g, h₀⟫_ℝ ≤ ‖g‖ * ‖h₀‖ := real_inner_le_norm g h₀
    nlinarith [hb h₀]
  have hnorm : κ * ‖h₀‖ ≤ 2 * ‖g‖ := by
    rcases eq_or_lt_of_le (norm_nonneg h₀) with h0 | hpos
    · rw [← h0, mul_zero]
      exact mul_nonneg (by norm_num) (norm_nonneg g)
    · refine le_of_mul_le_mul_right ?_ hpos
      nlinarith [hmax]
  have hh₀_bound : ‖h₀‖ ≤ 2 * ‖g‖ / κ := by
    rw [le_div_iff₀ hκ]
    linarith
  -- Compare the two energies at the common direction `h₀`.
  have hdiff : 2 * ⟪g, h₀⟫_ℝ - B h₀ h₀ - (2 * ⟪g', h₀⟫_ℝ - B h₀ h₀) =
      2 * ⟪g - g', h₀⟫_ℝ := by
    rw [inner_sub_left]
    ring
  have hcs : ⟪g - g', h₀⟫_ℝ ≤ ‖g - g'‖ * ‖h₀‖ := real_inner_le_norm _ _
  have hfinal : sSup (Set.range fun h : E => 2 * ⟪g, h⟫_ℝ - B h h) -
      sSup (Set.range fun h : E => 2 * ⟪g', h⟫_ℝ - B h h) ≤
      2 * ‖g - g'‖ * (2 * ‖g‖ / κ) := by
    have hle : 2 * ⟪g, h₀⟫_ℝ - B h₀ h₀ - sSup (Set.range fun h : E => 2 * ⟪g', h⟫_ℝ - B h h) ≤
        2 * ‖g - g'‖ * ‖h₀‖ := by
      linarith
    rw [hsup_g]
    have hmul : 2 * ‖g - g'‖ * ‖h₀‖ ≤ 2 * ‖g - g'‖ * (2 * ‖g‖ / κ) :=
      mul_le_mul_of_nonneg_left hh₀_bound (by positivity)
    linarith
  have hrw : 2 * ‖g - g'‖ * (2 * ‖g‖ / κ) = 4 * ‖g - g'‖ * ‖g‖ / κ := by ring
  linarith

end Lipschitz

section Density

variable {E : Type*} [NormedAddCommGroup E]

/-- A supremum of a bounded above family of continuous functions over a dense set of parameters
equals the supremum over all parameters. -/
theorem sSup_range_eq_iSup_dense {f : E → ℝ} (hf : Continuous f)
    (hbdd : BddAbove (Set.range f)) {D : ℕ → E} (hD : DenseRange D) :
    sSup (Set.range f) = ⨆ n, f (D n) := by
  have hbddD : BddAbove (Set.range fun n => f (D n)) :=
    hbdd.mono (Set.range_comp_subset_range D f)
  apply le_antisymm
  · refine csSup_le (Set.range_nonempty _) ?_
    rintro _ ⟨h, rfl⟩
    have hmem : h ∈ closure (Set.range D) := by
      rw [hD.closure_range]
      trivial
    obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
    have hle : ∀ n, f (s n) ≤ ⨆ m, f (D m) := by
      intro n
      obtain ⟨m, hm⟩ := hs n
      rw [← hm]
      exact le_ciSup hbddD m
    exact le_of_tendsto ((hf.tendsto h).comp hlim) (Eventually.of_forall hle)
  · exact ciSup_le fun n => le_csSup hbdd ⟨D n, rfl⟩

end Density

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
/-- The Hessian of any function, evaluated on a fixed pair of directions, is measurable in the
base point. No regularity of the function is needed. -/
theorem measurable_fderiv_fderiv_apply (V : E → ℝ) (d : E) :
    Measurable (fun x => fderiv ℝ (fderiv ℝ V) x d d) := by
  have hev : Continuous fun L : E →L[ℝ] E →L[ℝ] ℝ => L d d := by fun_prop
  exact hev.measurable.comp (measurable_fderiv ℝ (fderiv ℝ V))

omit [CompleteSpace E] in
/-- The variational energy of a measurable gradient field is almost everywhere measurable,
on a set where the Hessian of `V` is uniformly coercive. -/
theorem aemeasurable_sSup_hessian [TopologicalSpace.SeparableSpace E] {U : Set E} {V : E → ℝ} {μ : Measure E}
    {g : E → E} (hg : Measurable g) (hμU : ∀ᵐ x ∂μ, x ∈ U) {κ : ℝ}
    (hb : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (hκ : 0 < κ) :
    AEMeasurable (fun x => sSup (Set.range fun h : E =>
      2 * ⟪g x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)) μ := by
  have : Nonempty E := ⟨0⟩
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq E
  have hinner (d : E) : Measurable fun x => ⟪g x, d⟫_ℝ :=
    (continuous_id.inner continuous_const).measurable.comp hg
  have hmeas : Measurable fun x => ⨆ n, (2 * ⟪g x, D n⟫_ℝ - fderiv ℝ (fderiv ℝ V) x (D n) (D n)) :=
    Measurable.iSup fun n => ((hinner (D n)).const_mul 2).sub (measurable_fderiv_fderiv_apply V (D n))
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hμU] with x hx
  have hcont : Continuous fun h : E => 2 * ⟪g x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h := by
    fun_prop
  have hbdd : BddAbove (Set.range fun h : E =>
      2 * ⟪g x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) :=
    ⟨‖g x‖ ^ 2 / κ, by
      rintro _ ⟨h, rfl⟩
      exact bl_quadratic_le_norm_sq_div hκ (hb x hx) (g x) h⟩
  exact (sSup_range_eq_iSup_dense hcont hbdd hD).symm

end Measurability

end Riesz1

end

end
