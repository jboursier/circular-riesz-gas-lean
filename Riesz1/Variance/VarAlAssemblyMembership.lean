/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblyCutoff
public import Riesz1.Variance.VarAlAssemblyLocal
public import Riesz1.Variance.VarAlAssemblySeparation

/-!
# The cutoff-loop product belongs to the anchored Sobolev space

Proposition 5.9: the relative cutoff support lies in the open
set of selected noncollisions. Smooth extension of the loop there and
the completed-graph product rule discharge the domain condition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace Riesz1

/-- The actual cutoff-loop product, with its actual product weak gradient,
belongs to the anchored completion. No hypothesis asserts membership or
an approximation of the product. -/
theorem varAlAssembly_loopCutoffF_product_h1 {n : ℕ} {c s ℓ γ ε : ℝ}
    (Q : HsPairPotentials n.succPNat c) (hc : 0 < c) (hn : 1 ≤ n)
    (hs0 : 0 < s) (hs1 : s < 1) (hγ : 1 ≤ γ)
    (hε : 0 ≤ ε) (hεs : ε ≤ 1 - s / 2) (hℓ : 0 < ℓ)
    (hK : 1 ≤ (n.succPNat : ℝ) * ℓ) {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ ℓ⁻¹) :
    let η := fun y : AnchoredEuclidean n =>
      loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y))
    let H := fun y : AnchoredEuclidean n =>
      gradLoop s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ (anchorVector (WithLp.ofLp y))
    IsAnchoredH1 Q
      (fun y => loopCutoffF χ s γ ε n.succPNat ℓ ψ (anchorVector (WithLp.ofLp y)))
      (fun y => η y • gradient H y + H y • gradient η y) := by
  let N := n.succPNat
  let φ := loopTransport χ N ℓ γ ψ
  let T : AnchoredEuclidean n →L[ℝ] (Fin (N : ℕ) → ℝ) :=
    (ContinuousLinearMap.pi (anchorCoord n)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap
  have hT (y : AnchoredEuclidean n) : T y = anchorVector (WithLp.ofLp y) := by
    ext k
    exact anchorCoord_apply n (WithLp.ofLp y) k
  let S : Set (Fin (N : ℕ) → ℝ) := {X | ∀ i ∈ gradLabels N ℓ γ,
    ∀ j ∈ gradLabels N ℓ γ, i ≠ j →
      ((gradLift N X j - gradLift N X i : ℝ) : UnitAddCircle) ≠ 0}
  let O := T ⁻¹' S
  have hO : IsOpen O := (isOpen_gradNonInt N ℓ γ).preimage T.continuous
  have hSO : closure {y : AnchoredEuclidean n | y ∈ anchoredSimplex n ∧
      loopCutoff s γ ε N ℓ (anchorVector (WithLp.ofLp y)) ≠ 0} ⊆ O := by
    intro y hy
    have hev := Internal.varAlAssembly_relative_support_good hℓ hy
    change ∀ i ∈ gradLabels N ℓ γ, ∀ j ∈ gradLabels N ℓ γ, i ≠ j → _
    rw [hT]
    intro i hi j hj hij
    exact Internal.varAlAssembly_good_pair_noncollision hs0 hs1 hγ hεs hℓ hK hev hi hj hij
  have hφ : ContDiff ℝ ∞ φ := contDiff_loopTransport hχ hψ hχs N hℓ γ
  have hpφ : Function.Periodic φ (1 / ℓ) := by
    simpa only [one_div] using loopTransport_periodic (N := N) (γ := γ) hℓ χ hp
  have hH : ContDiffOn ℝ ∞
      (fun y : AnchoredEuclidean n => gradLoop s φ N ℓ γ (anchorVector (WithLp.ofLp y))) O := by
    have hFun : (fun y : AnchoredEuclidean n => gradLoop s φ N ℓ γ (anchorVector (WithLp.ofLp y))) =
        gradLoop s φ N ℓ γ ∘ T := funext fun y => congrArg (gradLoop s φ N ℓ γ) (hT y).symm
    rw [hFun]
    have hm := (contDiffOn_gradLoop_nonInt hφ hℓ hpφ hs0 hs1
      (fun hP t ht => varAlGap_transport_support hχs hℓ hP t ht)).comp
        T.contDiff.contDiffOn (fun _ hy => hy)
    exact hm
  have hη := varAlAssembly_loopCutoff_h1 Q hc hn s γ ε ℓ hK hε
  have hbη : ∀ᵐ y ∂anchoredMeasureE Q,
      |loopCutoff s γ ε N ℓ (anchorVector (WithLp.ofLp y))| ≤ 1 := by
    exact Eventually.of_forall fun y => by
      rw [abs_of_nonneg (loopCutoff_mem_Icc s γ ε ℓ _).1]
      exact (loopCutoff_mem_Icc s γ ε ℓ _).2
  exact Internal.varAlAssembly_mul_local Q hc hη zero_le_one hbη hO hSO hH

end Riesz1

end
