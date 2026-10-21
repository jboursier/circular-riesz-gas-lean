/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartDerivatives
public import Riesz1.ToMathlib.Chamber.PeriodizationIntegrable
public import Riesz1.ToMathlib.EllipticRegularity.LipschitzMultipliers

/-!
# Compact interior strip localizations and quotient L²

Closed interior supports intersected with closed rotation strips are
compact in the Euclidean chamber. This proves integrability on the actual
quotient of locally L² representatives supported away from collisions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff NNReal

namespace Riesz1

/-- A closed interior set in a bounded rotation slab is compact. There
is no assumption on where the slab lies relative to the integer seam. -/
theorem isCompact_hsChamber_slab {N : ℕ+} {K : Set (HsEuclidean N)}
    (hK : IsClosed K) (hKC : K ⊆ hsChamber N) {a d : ℝ}
    (hslab : ∀ x ∈ K, a ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ ≤ d) : IsCompact K := by
  have hbox : IsCompact (WithLp.toLp 2 ''
      Icc (fun _ : Fin (N : ℕ) => a) (fun _ => d + 1)) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  apply hbox.of_isClosed_subset hK
  intro x hx
  refine ⟨WithLp.ofLp x, ⟨?_, ?_⟩, WithLp.toLp_ofLp 2 x⟩
  · intro i
    exact (hslab x hx).1.trans ((hKC hx).1.monotone (Fin.zero_le i))
  · intro i
    have hi := (hKC hx).2 i
    have hd := (hslab x hx).2
    change x i ≤ d + 1
    linarith

/-- A closed interior support has compact intersection with every closed
rotation strip, including the two endpoints of the fundamental region. -/
theorem isCompact_tsupport_inter_hsSlab {N : ℕ+} {b : HsEuclidean N → ℝ}
    (hbU : tsupport b ⊆ hsChamber N) (a d : ℝ) :
    IsCompact (tsupport b ∩ {x | a ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ ≤ d}) := by
  apply isCompact_hsChamber_slab
    ((isClosed_tsupport b).inter (isClosed_Icc.preimage
      (EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))).continuous))
    (inter_subset_left.trans hbU)
  exact fun _ hx => hx.2

/-- Multiplying an interior lift by a compact rotation cutoff gives a
compact cover cutoff, even when the original lift crosses the seam. -/
theorem hasCompactSupport_hsStrip_mul {N : ℕ+} {b : HsEuclidean N → ℝ}
    (hbU : tsupport b ⊆ hsChamber N) {r : ℝ → ℝ} (hr : HasCompactSupport r) :
    HasCompactSupport (fun x => r (x ⟨0, N.pos⟩) * b x) := by
  obtain ⟨C, hC⟩ := hr.isBounded.exists_norm_le
  apply (isCompact_tsupport_inter_hsSlab hbU (-C) C).of_isClosed_subset
    (isClosed_tsupport _)
  intro x hx
  refine ⟨tsupport_mul_subset_right hx, ?_⟩
  have hx' : x ⟨0, N.pos⟩ ∈ tsupport r :=
    tsupport_comp_subset_preimage r
      (EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))).continuous
      (tsupport_mul_subset_left hx)
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hC _ hx')

/-- An arbitrary locally L² representative supported in a closed
interior set is L² on the fundamental region. No continuity is required. -/
theorem memLp_hsFundamentalRegion_of_support {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] {f : HsEuclidean N → F}
    (hf : LocallySquareIntegrableOn (hsChamber N) f) {b : HsEuclidean N → ℝ}
    (hbU : tsupport b ⊆ hsChamber N) (hfb : Function.support f ⊆ tsupport b) :
    MemLp f 2 (volume.restrict (hsFundamentalRegion N)) := by
  classical
  let K := tsupport b ∩ {x : HsEuclidean N | 0 ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ ≤ 1}
  have hK : IsCompact K := isCompact_tsupport_inter_hsSlab hbU 0 1
  have hKI : MemLp (K.indicator f) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).mpr
      (hf K hK (inter_subset_left.trans hbU))
  apply (hKI.restrict (hsFundamentalRegion N)).ae_eq
  filter_upwards [ae_restrict_mem (measurableSet_hsFundamentalRegion N)] with x hx
  by_cases hxf : f x = 0
  · rw [indicator_apply]
    split_ifs <;> simp only [hxf]
  · exact indicator_of_mem (s := K) ⟨hfb hxf, hx.2.1, hx.2.2.le⟩ f

/-- Local L² supported away from collisions descends to L² of the
quotient volume by the existing representative map. -/
theorem memLp_quotient_of_local_support {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] {f : HsEuclidean N → F}
    (hf : LocallySquareIntegrableOn (hsChamber N) f) {b : HsEuclidean N → ℝ}
    (hbU : tsupport b ⊆ hsChamber N) (hfb : Function.support f ⊆ tsupport b) :
    MemLp (f ∘ hsLiftPoint N) 2 (hsConfigurationVolume N) :=
  memLp_hsLiftPoint_volume_iff.mpr (memLp_hsFundamentalRegion_of_support hf hbU hfb)

/-- An interior periodic continuous cutoff is bounded on the whole
cover, by reducing its support to one compact closed strip. -/
theorem bounded_hsPeriodic_cutoff {N : ℕ+} {b : HsEuclidean N → ℝ}
    (hb : Continuous b) (hp : ∀ (k : ℤ) x, b (hsTranslate (k : ℝ) x) = b x)
    (hbU : tsupport b ⊆ hsChamber N) : ∃ M : ℝ≥0, ∀ x, ‖b x‖ ≤ M := by
  let K := tsupport b ∩ {x : HsEuclidean N | 0 ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ ≤ 1}
  have hK : IsCompact K := isCompact_tsupport_inter_hsSlab hbU 0 1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hb.continuousOn
  refine ⟨⟨|M|, abs_nonneg M⟩, fun x => ?_⟩
  by_cases hxb : b x = 0
  · simp only [hxb, norm_zero]
    exact abs_nonneg M
  · let y := hsTranslate (-((⌊x ⟨0, N.pos⟩⌋ : ℤ) : ℝ)) x
    have hyb : b y = b x := by simpa only [y, Int.cast_neg] using hp (-⌊x ⟨0, N.pos⟩⌋) x
    have hy : y ∈ K := by
      refine ⟨subset_tsupport b (by change b y ≠ 0; rwa [hyb]), ?_, ?_⟩
      · change 0 ≤ x ⟨0, N.pos⟩ + -((⌊x ⟨0, N.pos⟩⌋ : ℤ) : ℝ)
        linarith [Int.floor_le (x ⟨0, N.pos⟩)]
      · change x ⟨0, N.pos⟩ + -((⌊x ⟨0, N.pos⟩⌋ : ℤ) : ℝ) ≤ 1
        linarith [Int.lt_floor_add_one (x ⟨0, N.pos⟩)]
    exact hyb ▸ (hM y hy).trans (le_abs_self M)

/-- The lift convention used for interior cutoffs gives actual compact
support in the configuration quotient. -/
theorem hasCompactSupport_quotient_cutoff {N : ℕ+} {b : HsEuclidean N → ℝ}
    (hbU : tsupport b ⊆ hsChamber N) : HasCompactSupport (b ∘ hsLiftPoint N) := by
  let K := tsupport b ∩ {x : HsEuclidean N | 0 ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ ≤ 1}
  have hK : IsCompact K := isCompact_tsupport_inter_hsSlab hbU 0 1
  have hKC : K ⊆ hsChamber N := inter_subset_left.trans hbU
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set (hsChamber N)) := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rwa [image_preimage_eq_of_subset (by simpa using hKC)]
  have hQ := hK'.image (continuous_hsChamberProjection N)
  apply hQ.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hQ.isClosed
  intro x hx
  refine ⟨⟨hsLiftPoint N x, hsLiftPoint_mem_chamber N x⟩, ?_, hsChamberProjection_liftPoint x⟩
  refine ⟨subset_tsupport b hx, ?_, ?_⟩
  · exact ((hsConfigurationEquiv N).symm x).property.2.1
  · exact ((hsConfigurationEquiv N).symm x).property.2.2.1.le

end Riesz1
