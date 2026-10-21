/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlAssemblyMembership
public import Riesz1.ToMathlib.EuclideanGradientPi

/-!
# The three-field weak gradient of the cutoff loop

Proposition 5.9: the Sobolev pair has precisely the singular,
gap, and cutoff fields used by the inverse-energy estimates.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ContDiff

namespace Riesz1

theorem varAlAssembly_loopCutoffF_h1 {n : ℕ} {c s ℓ γ ε : ℝ}
    (Q : HsPairPotentials n.succPNat c) (hc : 0 < c) (hn : 1 ≤ n)
    (hs0 : 0 < s) (hs1 : s < 1) (hγ : 1 ≤ γ)
    (hε : 0 ≤ ε) (hεs : ε ≤ 1 - s / 2) (hℓ : 0 < ℓ)
    (hK : 1 ≤ (n.succPNat : ℝ) * ℓ) {χ ψ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ ℓ⁻¹) :
    let v := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
      loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
        gradVfield s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
          (anchorVector (WithLp.ofLp y)) i.succ
    let w := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
      loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
        gradWfield s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
          (anchorVector (WithLp.ofLp y)) i.succ
    let d := fun y : AnchoredEuclidean n => WithLp.toLp 2 fun i : Fin n =>
      gradLoop s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
          (anchorVector (WithLp.ofLp y)) *
        fderiv ℝ (fun z => loopCutoff s γ ε n.succPNat ℓ (anchorVector z))
          (WithLp.ofLp y) (Pi.single i 1)
    IsAnchoredH1 Q
      (fun y => loopCutoffF χ s γ ε n.succPNat ℓ ψ (anchorVector (WithLp.ofLp y)))
      (fun y => v y + w y + d y) := by
  have hmem := varAlAssembly_loopCutoffF_product_h1 Q hc hn hs0 hs1 hγ hε hεs hℓ hK hχ hχs hψ hp
  apply hmem.congr EventuallyEq.rfl
  let N := n.succPNat
  let φ := loopTransport χ N ℓ γ ψ
  have hφ : ContDiff ℝ ∞ φ := contDiff_loopTransport hχ hψ hχs N hℓ γ
  have hpφ : Function.Periodic φ (1 / ℓ) := by
    simpa only [one_div] using loopTransport_periodic (N := N) (γ := γ) hℓ χ hp
  have hsupp := fun hP t ht => varAlGap_transport_support (N := N) (γ := γ) (ψ := ψ) hχs hℓ hP t ht
  have hsplit := (gradient_splitting_identity hφ hℓ hpφ hs0 hs1 hsupp).2.1
  filter_upwards [ae_mem_anchoredSimplex Q,
    anchoredMeasureE_cutoff_chain_ae hn Q s ((N : ℝ) * ℓ) (2 * γ) ε hK
      (by linarith) hs0.le hε] with y hy hcut
  have hphys := varAl_anchorVector_mem hy
  have hdLoop : DifferentiableAt ℝ (gradLoop s φ N ℓ γ) (anchorVector (WithLp.ofLp y)) :=
    (contDiffAt_gradLoop hφ hℓ hpφ hs0 hs1 hsupp
      (nonInt_of_mem_orderedDomain hℓ.le hphys)).differentiableAt (by simp)
  let A := ContinuousLinearMap.pi (anchorCoord n)
  have hA : (A : (Fin n → ℝ) → (Fin (N : ℕ) → ℝ)) = anchorVector :=
    funext fun z => funext fun k => anchorCoord_apply n z k
  have hdH : DifferentiableAt ℝ (fun z : Fin n → ℝ => gradLoop s φ N ℓ γ (anchorVector z))
      (WithLp.ofLp y) := by
    have hdA : DifferentiableAt ℝ anchorVector (WithLp.ofLp y) := by
      simpa only [hA] using A.differentiableAt (x := WithLp.ofLp y)
    exact hdLoop.comp _ hdA
  have hdCut : DifferentiableAt ℝ (anchoredCutoff N s ((N : ℝ) * ℓ) (2 * γ) ε)
      (WithLp.ofLp y) := by
    rw [anchoredCutoff_eq_comp_gapVector]
    exact hcut.1.comp _ (anchoredGapVector_hasFDerivAt n _).differentiableAt
  have hev : (fun z => loopCutoff s γ ε N ℓ (anchorVector z)) =ᶠ[𝓝 (WithLp.ofLp y)]
      anchoredCutoff N s ((N : ℝ) * ℓ) (2 * γ) ε := by
    filter_upwards [(isOpen_anchoredDomain n).mem_nhds hy] with z hz
    exact varAlGap_loopCutoff_eq_anchoredCutoff hn hK s ε hz
  have hdη := hdCut.congr_of_eventuallyEq hev
  ext i
  change loopCutoff s γ ε N ℓ (anchorVector (WithLp.ofLp y)) *
      gradient (fun z : AnchoredEuclidean n => gradLoop s φ N ℓ γ
        (anchorVector (WithLp.ofLp z))) y i +
    gradLoop s φ N ℓ γ (anchorVector (WithLp.ofLp y)) *
      gradient (fun z : AnchoredEuclidean n => loopCutoff s γ ε N ℓ
        (anchorVector (WithLp.ofLp z))) y i = _
  rw [gradient_comp_ofLp_apply hdH, gradient_comp_ofLp_apply hdη,
    varAlLoop_fderiv_anchor hdLoop, hsplit _ hphys i.succ]
  simp only [mul_add]
  rfl

end Riesz1

end
