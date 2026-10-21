/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingTests
public import Riesz1.ToMathlib.WeightedSobolev.Graph

/-!
# Finite-norm smooth periodic lifts

The smooth core of the periodic weighted Sobolev completion. Compactness of the closed
fundamental region ensures that the values and gradients of a function
smooth on the closed chamber belong to `L²` for every finite measure on
the quotient. This step does not assert closability of the gradient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ENNReal ContDiff

namespace Riesz1

theorem HsSmoothOnClosure.zero (N : ℕ+) :
    HsSmoothOnClosure N (0 : HsEuclidean N → ℝ) :=
  ⟨fun _ _ => rfl, univ, isOpen_univ, subset_univ _, contDiffOn_const⟩

theorem HsSmoothOnClosure.add {N : ℕ+} {f g : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (hg : HsSmoothOnClosure N g) :
    HsSmoothOnClosure N (f + g) := by
  obtain ⟨hfp, U, hU, hsU, hfU⟩ := hf
  obtain ⟨hgp, V, hV, hsV, hgV⟩ := hg
  exact ⟨fun k x => by simp only [Pi.add_apply, hfp, hgp], U ∩ V, hU.inter hV,
    fun x hx => ⟨hsU hx, hsV hx⟩,
    (hfU.mono inter_subset_left).add (hgV.mono inter_subset_right)⟩

theorem HsSmoothOnClosure.smul {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (a : ℝ) : HsSmoothOnClosure N (a • f) := by
  obtain ⟨hp, U, hU, hs, hfU⟩ := hf
  exact ⟨fun k x => by simp only [Pi.smul_apply, hp], U, hU, hs, hfU.const_smul a⟩

/-- The vector space of smooth periodic lifts on the closed chamber. -/
def hsSmoothCore (N : ℕ+) : Submodule ℝ (HsEuclidean N → ℝ) where
  carrier := {f | HsSmoothOnClosure N f}
  zero_mem' := HsSmoothOnClosure.zero N
  add_mem' := HsSmoothOnClosure.add
  smul_mem' a _ hf := hf.smul a


/-- The Euclidean point in the unique half-open fundamental representative. -/
def hsLiftPoint (N : ℕ+) (x : HsConfiguration N) : HsEuclidean N :=
  WithLp.toLp 2 ((hsConfigurationEquiv N).symm x).val

theorem hsLiftPoint_mem_fundamentalRegion (N : ℕ+) (x : HsConfiguration N) :
    hsLiftPoint N x ∈ hsFundamentalRegion N := by
  rw [hsFundamentalRegion_eq_preimage]
  exact ((hsConfigurationEquiv N).symm x).property

theorem hsLiftPoint_mem_chamber (N : ℕ+) (x : HsConfiguration N) :
    hsLiftPoint N x ∈ hsChamber N :=
  (hsLiftPoint_mem_fundamentalRegion N x).1

theorem measurable_hsLiftPoint (N : ℕ+) : Measurable (hsLiftPoint N) :=
  (PiLp.homeomorph 2 (fun _ : Fin (N : ℕ) => ℝ)).symm.continuous.measurable.comp
    (measurable_subtype_coe.comp (measurable_hsConfigurationEquiv_symm N))

/-- Including the two periodic ends makes the fundamental region compact. -/
theorem isCompact_closure_hsFundamentalRegion (N : ℕ+) :
    IsCompact (closure (hsFundamentalRegion N)) := by
  let e := PiLp.homeomorph 2 (fun _ : Fin (N : ℕ) => ℝ)
  have hc : IsCompact (e.symm '' Icc (fun _ => (0 : ℝ)) (fun _ => (2 : ℝ))) :=
    isCompact_Icc.image e.symm.continuous
  apply hc.of_isClosed_subset isClosed_closure
  apply hc.isClosed.closure_subset_iff.mpr
  intro x hx
  refine ⟨WithLp.ofLp x, ⟨?_, ?_⟩, rfl⟩
  · intro i
    exact hx.2.1.trans (hx.1.1.monotone (Fin.zero_le i))
  · intro i
    have hi := hx.1.2 i
    linarith [hx.2.2]

/-- Continuous functions on the closed chamber have finite norm after
evaluation at fundamental representatives. -/
theorem memLp_hsLiftPoint {N : ℕ+} {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (p : ℝ≥0∞)
    {f : HsEuclidean N → F} (hf : ContinuousOn f (closure (hsChamber N))) :
    MemLp (fun x => f (hsLiftPoint N x)) p μ := by
  have hsub : closure (hsFundamentalRegion N) ⊆ closure (hsChamber N) :=
    closure_mono (fun _ hx => hx.1)
  obtain ⟨C, hC⟩ := (isCompact_closure_hsFundamentalRegion N).exists_bound_of_continuousOn
    (hf.mono hsub)
  have hm : Measurable (fun x => f (hsLiftPoint N x)) :=
    hf.domRestrict.measurable.comp ((measurable_hsLiftPoint N).subtype_mk
      (h := fun x => subset_closure (hsLiftPoint_mem_chamber N x)))
  exact MemLp.of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall fun x =>
    hC _ (subset_closure (hsLiftPoint_mem_fundamentalRegion N x)))

/-- The value of a smooth lift on the cyclic quotient. -/
def hsSmoothValue {N : ℕ+} (f : HsEuclidean N → ℝ) (x : HsConfiguration N) : ℝ :=
  f (hsLiftPoint N x)

/-- Its Euclidean gradient in the fundamental representative. -/
def hsSmoothGradient {N : ℕ+} (f : hsSmoothCore N)
    (x : HsConfiguration N) : HsEuclidean N :=
  gradient f.val (hsLiftPoint N x)

theorem HsSmoothOnClosure.memLp_value {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    MemLp (hsSmoothValue f) 2 μ := by
  obtain ⟨_, W, hW, hsub, hfW⟩ := hf
  exact memLp_hsLiftPoint μ 2 (hfW.continuousOn.mono hsub)

theorem HsSmoothOnClosure.memLp_gradient {N : ℕ+} {f : HsEuclidean N → ℝ}
    (hf : HsSmoothOnClosure N f) (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    MemLp (hsSmoothGradient ⟨f, hf⟩) 2 μ := by
  obtain ⟨_, W, hW, hsub, hfW⟩ := hf
  apply memLp_hsLiftPoint μ 2
  exact ((InnerProductSpace.toDual ℝ (HsEuclidean N)).symm.continuous.comp_continuousOn
    (hfW.continuousOn_fderiv_of_isOpen hW (by norm_num))).mono hsub

theorem hsSmoothValue_test {N : ℕ+} (f : HsTestFunction N) :
    hsSmoothValue f.toFun = hsTestOnQuotient f := rfl

end Riesz1

end
