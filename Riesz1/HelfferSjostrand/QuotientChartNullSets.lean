/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartDerivatives

/-!
# Null sets and weak derivative uniqueness on the quotient

Restriction to the fundamental region and the measure preserving
representative map transfer almost everywhere identities to quotient volume.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Local almost everywhere equality on the chamber passes to the
representatives used in quotient integration. -/
theorem ae_eq_comp_hsLiftPoint_volume {N : ℕ+} {F : Type*}
    {f g : HsEuclidean N → F} (hfg : f =ᵐ[volume.restrict (hsChamber N)] g) :
    f ∘ hsLiftPoint N =ᵐ[hsConfigurationVolume N] g ∘ hsLiftPoint N := by
  have hfund : f =ᵐ[volume.restrict (hsFundamentalRegion N)] g :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hfg
  exact (measurePreserving_hsLiftPoint_volume N).quasiMeasurePreserving.ae hfund

/-- Chart uniqueness implies uniqueness of the descended L² gradient
representatives with respect to quotient volume. -/
theorem quotient_weak_derivative_unique {N : ℕ+} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {u f g : HsEuclidean N → F} {v : HsEuclidean N}
    (hf : HasWeakDirectionalDerivativeOn (hsChamber N) u f v)
    (hg : HasWeakDirectionalDerivativeOn (hsChamber N) u g v) :
    f ∘ hsLiftPoint N =ᵐ[hsConfigurationVolume N] g ∘ hsLiftPoint N :=
  ae_eq_comp_hsLiftPoint_volume (hf.unique (isOpen_hsChamber N) hg)

end Riesz1
