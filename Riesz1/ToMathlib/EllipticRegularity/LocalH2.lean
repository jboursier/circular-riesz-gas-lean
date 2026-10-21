/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.SecondLocalization
public import Riesz1.ToMathlib.EllipticRegularity.Exhaustion
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Interior H² regularity for distributional Schrödinger solutions

The Euclidean interior H² assertion, in the existing
weak-derivative encoding. The potential need only be smooth locally.
No lower bound is needed for this assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

namespace Internal

omit [MeasurableSpace E] [BorelSpace E] in
/-- A compact interior set has a smooth compact interior cutoff equal
to one on an open neighborhood of that set. -/
theorem exists_smooth_interior_cutoff {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (V : Set E) (b : E → ℝ), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ U ∧
      ∀ x ∈ V, b x = 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨S, hSo, hLS, hSU, hSc⟩ :=
    exists_open_between_and_isCompact_closure hLc hU hLU
  obtain ⟨b, hb, _, hbs, hb1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hSo hLc.isClosed hLS
  refine ⟨interior L, b, isOpen_interior, hKL, interior_subset.trans hLU,
    hb, ?_, ?_, fun x hx => (hb1 x).mp (interior_subset hx)⟩
  · change IsCompact (closure (Function.support b))
    rwa [hbs]
  · change closure (Function.support b) ⊆ U
    rwa [hbs]

end Internal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The local H² regularity conclusion on a Euclidean
open set, for complex Hilbert valued solutions. Global L² on the domain
is the only Sobolev hypothesis. -/
theorem isLocalH2_of_distributional_schrodinger {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → F}
    (huL : MemLp u 2 (volume.restrict U))
    (hu : IsDistributionalSchrodingerSolution U W lam u) : IsLocalH2 U u := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let C := CompactExhaustion.choice U
  have hC (n : ℕ) : IsCompact (Subtype.val '' C n : Set E) :=
    (C.isCompact n).image continuous_subtype_val
  have hCU (n : ℕ) : (Subtype.val '' C n : Set E) ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  choose V b hVo hCV hVU hb hbc hbU hb1 using
    fun n => Internal.exists_smooth_interior_cutoff hU (hC n) (hCU n)
  have hcover : ∀ K : Set E, IsCompact K → K ⊆ U → ∃ n, K ⊆ V n := by
    intro K hK hKU
    have hK' : IsCompact (Subtype.val ⁻¹' K : Set U) := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rw [image_preimage_eq_of_subset (by simpa using hKU)]
      exact hK
    obtain ⟨n, hn⟩ := C.exists_superset_of_isCompact hK'
    refine ⟨n, fun x hx => hCV n ?_⟩
    exact ⟨⟨x, hKU hx⟩, hn hx, rfl⟩
  apply Internal.isLocalH2_of_exhaustion hU hVo hcover
  intro n
  have h := Internal.schrodinger_cutoff_isLocalH2 hU hW lam huL hu (hb n) (hbc n) (hbU n)
  apply (h.mono (subset_univ (V n))).congr (hVo n)
  filter_upwards [ae_restrict_mem (hVo n).measurableSet] with x hx
  simp only [hb1 n x hx, one_smul]

/-- Interior regularity only needs locally L² data. In particular this
form does not require a periodic lift to be globally square integrable. -/
theorem isLocalH2_of_locallySquareIntegrable_schrodinger {U : Set E} (hU : IsOpen U)
    {W : E → ℝ} (hW : ContDiffOn ℝ ∞ W U) (lam : ℝ) {u : E → F}
    (huL : LocallySquareIntegrableOn U u)
    (hu : IsDistributionalSchrodingerSolution U W lam u) : IsLocalH2 U u := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let C := CompactExhaustion.choice U
  have hC (n : ℕ) : IsCompact (Subtype.val '' C n : Set E) :=
    (C.isCompact n).image continuous_subtype_val
  have hCU (n : ℕ) : (Subtype.val '' C n : Set E) ⊆ U := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  choose V b hVo hCV hVU hb hbc hbU hb1 using
    fun n => Internal.exists_smooth_interior_cutoff hU (hC n) (hCU n)
  have hcover : ∀ K : Set E, IsCompact K → K ⊆ U → ∃ n, K ⊆ V n := by
    intro K hK hKU
    have hK' : IsCompact (Subtype.val ⁻¹' K : Set U) := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rw [image_preimage_eq_of_subset (by simpa using hKU)]
      exact hK
    obtain ⟨n, hn⟩ := C.exists_superset_of_isCompact hK'
    refine ⟨n, fun x hx => hCV n ?_⟩
    exact ⟨⟨x, hKU hx⟩, hn hx, rfl⟩
  apply Internal.isLocalH2_of_exhaustion hU hVo hcover
  intro n
  have hVs : V n ⊆ tsupport (b n) := by
    intro x hx
    apply subset_tsupport (b n)
    simp only [Function.mem_support, hb1 n x hx, ne_eq, one_ne_zero, not_false_eq_true]
  have hLn : MemLp u 2 (volume.restrict (V n)) :=
    (huL _ (hbc n) (hbU n)).mono_measure (Measure.restrict_mono hVs le_rfl)
  exact isLocalH2_of_distributional_schrodinger (hVo n) (hW.mono (hVU n)) lam hLn
    (hu.mono (hVU n))

end Riesz1
