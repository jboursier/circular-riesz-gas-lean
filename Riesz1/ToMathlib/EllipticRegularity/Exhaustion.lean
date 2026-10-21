/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.WeakOperations
public import Riesz1.ToMathlib.EllipticRegularity.Representatives

/-!
# Gluing local weak derivatives along an exhaustion

Supporting locality results for the interior H² regularity assertion.
The derivative predicates and local L² spaces are those of `WeakDerivatives`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Restrict a weak derivative to a smaller domain. -/
theorem HasWeakDirectionalDerivativeOn.mono {U V : Set E} {u g : E → F} {v : E}
    (hu : HasWeakDirectionalDerivativeOn U u g v) (hVU : V ⊆ U) :
    HasWeakDirectionalDerivativeOn V u g v :=
  ⟨hu.1.mono_set hVU, hu.2.1.mono_set hVU,
    fun φ hφ hφc hφV => hu.2.2 φ hφ hφc (hφV.trans hVU)⟩

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Restrict local square integrability to a smaller domain. -/
theorem LocallySquareIntegrableOn.mono {U V : Set E} {u : E → F}
    (hu : LocallySquareIntegrableOn U u) (hVU : V ⊆ U) :
    LocallySquareIntegrableOn V u := fun K hK hKV => hu K hK (hKV.trans hVU)

omit [CompleteSpace F] in
/-- Restrict the same first and second weak representatives. -/
theorem IsLocalH2.mono {U V : Set E} {u : E → F}
    (hu : IsLocalH2 U u) (hVU : V ⊆ U) : IsLocalH2 V u := by
  obtain ⟨hu, g, h, hd⟩ := hu
  refine ⟨hu.mono hVU, g, h, fun i => ?_⟩
  exact ⟨(hd i).1.mono hVU, (hd i).2.1.mono hVU,
    fun j => ⟨((hd i).2.2 j).1.mono hVU, ((hd i).2.2 j).2.mono hVU⟩⟩

omit [CompleteSpace F] in
/-- Restrict the distributional equation to a smaller domain. -/
theorem IsDistributionalSchrodingerSolution.mono {U V : Set E} {W : E → ℝ} {lam : ℝ}
    {u : E → F} (hu : IsDistributionalSchrodingerSolution U W lam u) (hVU : V ⊆ U) :
    IsDistributionalSchrodingerSolution V W lam u :=
  ⟨hu.1.mono_set hVU, hu.2.1.mono_set hVU,
    fun φ hφ hφc hφV => hu.2.2 φ hφ hφc (hφV.trans hVU)⟩

namespace Internal

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- Local L² can be checked on a sequence covering every compact interior set. -/
theorem locallySquareIntegrableOn_of_exhaustion {U : Set E} {V : ℕ → Set E}
    (hcover : ∀ K : Set E, IsCompact K → K ⊆ U → ∃ n, K ⊆ V n)
    {u : E → F} (hu : ∀ n, LocallySquareIntegrableOn (V n) u) :
    LocallySquareIntegrableOn U u := by
  intro K hK hKU
  obtain ⟨n, hn⟩ := hcover K hK hKU
  exact hu n K hK hn

omit [CompleteSpace F] in
/-- Weak test identities pass from a compact exhaustion to its union. -/
theorem weakDerivative_of_exhaustion {U : Set E} (hU : IsOpen U) {V : ℕ → Set E}
    (hcover : ∀ K : Set E, IsCompact K → K ⊆ U → ∃ n, K ⊆ V n)
    {u g : E → F} {v : E} (hu : LocallySquareIntegrableOn U u)
    (hg : LocallySquareIntegrableOn U g)
    (hd : ∀ n, HasWeakDirectionalDerivativeOn (V n) u g v) :
    HasWeakDirectionalDerivativeOn U u g v := by
  refine ⟨hu.locallyIntegrableOn hU, hg.locallyIntegrableOn hU, ?_⟩
  intro φ hφ hφc hφU
  obtain ⟨n, hn⟩ := hcover (tsupport φ) hφc hφU
  exact (hd n).2.2 φ hφ hφc hn

/-- Coherent local H² representatives glue on a countable open exhaustion.
Coherence is derived from uniqueness of weak derivatives, not assumed. -/
theorem isLocalH2_of_exhaustion {U : Set E} (hU : IsOpen U) {V : ℕ → Set E}
    (hV : ∀ n, IsOpen (V n))
    (hcover : ∀ K : Set E, IsCompact K → K ⊆ U → ∃ n, K ⊆ V n)
    {u : E → F} (hu : ∀ n, IsLocalH2 (V n) u) : IsLocalH2 U u := by
  classical
  choose hul gn hn hd using hu
  have hgpair (n m : ℕ) (i : Fin (Module.finrank ℝ E)) :
      gn n i =ᵐ[volume.restrict (V n ∩ V m)] gn m i :=
    ((hd n i).2.1.mono inter_subset_left).unique ((hV n).inter (hV m))
      ((hd m i).2.1.mono inter_subset_right)
  have hhpair (n m : ℕ) (i j : Fin (Module.finrank ℝ E)) :
      hn n i j =ᵐ[volume.restrict (V n ∩ V m)] hn m i j := by
    have hd1 := ((hd n i).2.2 j).2.mono (V := V n ∩ V m) inter_subset_left
    have hd2 := ((hd m i).2.2 j).2.mono (V := V n ∩ V m) inter_subset_right
    exact (hd1.congr ((hV n).inter (hV m)) (hgpair n m i)
      Filter.EventuallyEq.rfl).unique ((hV n).inter (hV m)) hd2
  let g : Fin (Module.finrank ℝ E) → E → F := fun i x =>
    if hx : ∃ n, x ∈ V n then gn (Nat.find hx) i x else 0
  let h : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → F := fun i j x =>
    if hx : ∃ n, x ∈ V n then hn (Nat.find hx) i j x else 0
  have hge (n : ℕ) (i : Fin (Module.finrank ℝ E)) :
      gn n i =ᵐ[volume.restrict (V n)] g i := by
    have hall : ∀ᵐ x ∂volume, ∀ m, x ∈ V n ∩ V m → gn n i x = gn m i x := by
      apply ae_all_iff.mpr
      intro m
      exact (ae_restrict_iff' ((hV n).inter (hV m)).measurableSet).mp (hgpair n m i)
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem (hV n).measurableSet] with x hx hxV
    have hex : ∃ m, x ∈ V m := ⟨n, hxV⟩
    change gn n i x = if hy : ∃ m, x ∈ V m then gn (Nat.find hy) i x else 0
    rw [dite_eq_left hex]
    exact hx _ ⟨hxV, Nat.find_spec hex⟩
  have hhe (n : ℕ) (i j : Fin (Module.finrank ℝ E)) :
      hn n i j =ᵐ[volume.restrict (V n)] h i j := by
    have hall : ∀ᵐ x ∂volume, ∀ m, x ∈ V n ∩ V m → hn n i j x = hn m i j x := by
      apply ae_all_iff.mpr
      intro m
      exact (ae_restrict_iff' ((hV n).inter (hV m)).measurableSet).mp (hhpair n m i j)
    filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem (hV n).measurableSet] with x hx hxV
    have hex : ∃ m, x ∈ V m := ⟨n, hxV⟩
    change hn n i j x = if hy : ∃ m, x ∈ V m then hn (Nat.find hy) i j x else 0
    rw [dite_eq_left hex]
    exact hx _ ⟨hxV, Nat.find_spec hex⟩
  have huL := locallySquareIntegrableOn_of_exhaustion hcover hul
  have hgL (i) : LocallySquareIntegrableOn U (g i) :=
    locallySquareIntegrableOn_of_exhaustion hcover
      (fun n => ((hd n i).1).congr (hge n i))
  have hhL (i j) : LocallySquareIntegrableOn U (h i j) :=
    locallySquareIntegrableOn_of_exhaustion hcover
      (fun n => (((hd n i).2.2 j).1).congr (hhe n i j))
  refine ⟨huL, g, h, fun i => ⟨hgL i, ?_, fun j => ⟨hhL i j, ?_⟩⟩⟩
  · exact weakDerivative_of_exhaustion hU hcover huL (hgL i)
      (fun n => (hd n i).2.1.congr (hV n) Filter.EventuallyEq.rfl (hge n i))
  · exact weakDerivative_of_exhaustion hU hcover (hgL i) (hhL i j)
      (fun n => ((hd n i).2.2 j).2.congr (hV n) (hge n i) (hhe n i j))

end Internal
end Riesz1
