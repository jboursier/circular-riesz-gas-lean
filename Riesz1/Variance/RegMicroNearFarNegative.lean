/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroNearFarLocal
public import Riesz1.CLT.IdentityDefs

/-!
# Applying the negative-exponent kernel bound to the actual near error

The continuous representative is the unique representative supplied by the
`MicroKernelBounds`. The mollification is the existing `cltRegCircle`,
and the near function is the actual `microNearError` product. The resulting
variance bound is `D C² K^(2α)`, with `D` chosen before all analytic data.
-/

public section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The negative-exponent near step of Lemma 5.3, including `N=1`.
The only analytic input is the already proved kernel conclusion. -/
theorem micro_near_negative_of_kernel (P : Parameters) (n : ℕ+) :
    ∃ D : ℝ, 0 < D ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (ℓ : Scale),
      1 ≤ (N : ℝ)*ℓ.val →
      let L := observationLength ℓ
      let K := (N : ℝ)*ℓ.val
      ∀ (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (α C H : ℝ),
        α < 0 → 0 ≤ C → K⁻¹ ≤ H →
      ∀ (a : Fin (n : ℕ) → ℝ),
        (∀ i j, i ≠ j → 8*K⁻¹ ≤ dist (a i : Circle L) (a j : Circle L)) →
      ∀ f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
        MicroKernelBounds P ρ α C H n a L f →
      ∃ g : C(Circle L, ℝ),
        ((g : Circle L → ℝ) =ᵐ[arclength L] f.val) ∧
      ∃ hF : Integrable (fun X : Configuration N => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a
            (fun z => g z - cltRegCircle hρ L (show 0<K⁻¹ from inv_pos.mpr (mul_pos
              (by exact_mod_cast N.pos) ℓ.property.1)) f z)
            ((X.val i/ℓ.val : ℝ) : Circle L)) (gibbsMeasure P N),
        variance (gibbsMeasure P N) (fun X => ∑ i : Fin (N : ℕ),
          microNearError L.val K⁻¹ a
            (fun z => g z - cltRegCircle hρ L (show 0<K⁻¹ from inv_pos.mpr (mul_pos
              (by exact_mod_cast N.pos) ℓ.property.1)) f z)
            ((X.val i/ℓ.val : ℝ) : Circle L)) hF ≤ ENNReal.ofReal (D*C^2*K^(2*α)) := by
  obtain ⟨D, hD, hb⟩ := micro_near_rate_of_bound P n
  refine ⟨D, hD, fun hPL N ℓ hK => ?_⟩
  dsimp only
  intro ρ hρ α C H hα hC hH a hsep f hkernel
  let L := observationLength ℓ
  let K := (N : ℝ)*ℓ.val
  have hh : 0 < K⁻¹ := inv_pos.mpr (mul_pos (by exact_mod_cast N.pos) ℓ.property.1)
  rcases hkernel with ⟨ψ, _hc, _hcoef, _hrep, _hmoll, _hder, _herr,
    hnegative, _hpositive, _hloc, _htrans, _haway⟩
  obtain ⟨g, hg, _huniq⟩ := hnegative hα
  let e : Circle L → ℝ := fun z => g z - cltRegCircle hρ L hh f z
  have hregc : Continuous (cltRegCircle hρ L hh f) :=
    (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
      (cltRegCircle_contDiff hρ L hh f).continuous
  have he : Measurable e := (g.continuous.sub hregc).measurable
  have hbound (z : Circle L) : |e z| ≤ C*K⁻¹^(-α) := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    dsimp only [e]
    rw [cltRegCircle_coe]
    exact hg.2.2 K⁻¹ hh hH x
  obtain ⟨hF, hv⟩ := hb hPL N ℓ hK a hsep α C hC e he hbound
  exact ⟨g, hg.1, hF, hv⟩

end Riesz1.Internal
