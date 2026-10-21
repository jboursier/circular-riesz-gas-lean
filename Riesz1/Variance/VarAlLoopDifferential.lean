/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlGapCutoffBridge
public import Riesz1.Variance.VarAlGapCutoffEnergy

/-!
# Anchored differentiation of the cutoff loop

The pointwise product rule in the proof of Proposition 5.9.
The anchor stays fixed, so only the coordinates of the next labels occur.
This file does not assert Sobolev membership from differentiability.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- Restricting a differentiable function to the anchored chart restricts
its differential to the unpinned coordinates. -/
theorem varAlLoop_fderiv_anchor {n : ℕ} {f : (Fin (n.succPNat : ℕ) → ℝ) → ℝ}
    {y : Fin n → ℝ} (hf : DifferentiableAt ℝ f (anchorVector y)) (i : Fin n) :
    fderiv ℝ (fun z => f (anchorVector z)) y (Pi.single i 1) =
      fderiv ℝ f (anchorVector y) (Pi.single i.succ 1) := by
  let A := ContinuousLinearMap.pi (anchorCoord n)
  have hA : ∀ z : Fin n → ℝ, A z = anchorVector z := by
    intro z
    ext k
    exact anchorCoord_apply n z k
  have hsingle : A (Pi.single i 1) = Pi.single i.succ 1 := by
    rw [hA]
    ext k
    induction k using Fin.cases with
    | zero => simp [anchorVector]
    | succ j => simp [anchorVector, Pi.single_apply]
  have hAd : HasFDerivAt anchorVector A y := by
    rw [show anchorVector = (A : (Fin n → ℝ) → (Fin (n.succPNat : ℕ) → ℝ)) from
      (funext hA).symm]
    exact A.hasFDerivAt
  have hd := (hf.hasFDerivAt.comp y hAd).fderiv
  simp only [Function.comp_def] at hd
  change fderiv ℝ (fun z => f (anchorVector z)) y _ = _
  rw [hd, ContinuousLinearMap.comp_apply, hsingle]
  rfl

/-- The exact three-term derivative of `loopCutoffF` at
every differentiability point of its cutoff in the anchored domain.
Proposition 5.9, product-rule display. -/
theorem varAlLoop_cutoff_product_rule {n : ℕ} {s ℓ γ ε : ℝ} {χ ψ : ℝ → ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hℓ : 0 < ℓ)
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ ℓ⁻¹)
    {y : Fin n → ℝ} (hy : y ∈ anchoredDomain n)
    (hη : DifferentiableAt ℝ
      (fun z => loopCutoff s γ ε n.succPNat ℓ (anchorVector z)) y) (i : Fin n) :
    fderiv ℝ (fun z => loopCutoffF χ s γ ε n.succPNat ℓ ψ (anchorVector z)) y
        (Pi.single i 1) =
      loopCutoff s γ ε n.succPNat ℓ (anchorVector y) *
        gradVfield s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ (anchorVector y) i.succ +
      loopCutoff s γ ε n.succPNat ℓ (anchorVector y) *
        gradWfield s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ (anchorVector y) i.succ +
      gradLoop s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ (anchorVector y) *
        fderiv ℝ (fun z => loopCutoff s γ ε n.succPNat ℓ (anchorVector z)) y
          (Pi.single i 1) := by
  let φ := loopTransport χ n.succPNat ℓ γ ψ
  have hφ : ContDiff ℝ ∞ φ := contDiff_loopTransport hχ hψ hχs n.succPNat hℓ γ
  have hpφ : Function.Periodic φ (1 / ℓ) := by
    simpa only [one_div] using loopTransport_periodic (N := n.succPNat) (γ := γ) hℓ χ hp
  have hid := gradient_splitting_identity hφ hℓ hpφ hs0 hs1
    (fun hpart t ht => varAlGap_transport_support hχs hℓ hpart t ht)
  have hphys := varAl_anchorVector_mem hy
  have hH := contDiffAt_gradLoop hφ hℓ hpφ hs0 hs1
    (fun hpart t ht => varAlGap_transport_support hχs hℓ hpart t ht)
    (X := anchorVector y)
    (fun i hi j hj hij => coe_ne_zero_of_forall_ne_int
      (gradLift_sub_not_int hℓ.le hphys hi hj hij))
  have hd : DifferentiableAt ℝ (gradLoop s φ n.succPNat ℓ γ) (anchorVector y) :=
    hH.differentiableAt (by simp)
  have hA : DifferentiableAt ℝ (fun z : Fin n → ℝ => anchorVector z) y := by
    apply differentiableAt_pi.mpr
    intro k
    convert (anchorCoord n k).differentiableAt (x := y) using 1
    exact (funext fun z => anchorCoord_apply n z k).symm
  have hprod := (hη.hasFDerivAt.mul (hd.comp y hA).hasFDerivAt).fderiv
  calc
    _ = loopCutoff s γ ε n.succPNat ℓ (anchorVector y) *
          fderiv ℝ (fun z => gradLoop s φ n.succPNat ℓ γ (anchorVector z)) y (Pi.single i 1) +
        gradLoop s φ n.succPNat ℓ γ (anchorVector y) *
          fderiv ℝ (fun z => loopCutoff s γ ε n.succPNat ℓ (anchorVector z)) y (Pi.single i 1) :=
      congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hprod
    _ = _ := by
      rw [varAlLoop_fderiv_anchor hd, hid.2.1 _ hphys i.succ]
      ring

/-- The cutoff product rule holds almost everywhere under every anchored
pair law. The kink sets are null by the cutoff calculus. This is
an identity of classical derivatives. Sobolev membership is separate. -/
theorem varAlLoop_cutoff_product_rule_ae {n : ℕ} (hn : 1 ≤ n) {c s ℓ γ ε : ℝ}
    (Q : HsPairPotentials n.succPNat c)
    {χ ψ : ℝ → ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hℓ : 0 < ℓ)
    (hK : 1 ≤ (n.succPNat : ℝ) * ℓ) (hγ : 0 ≤ γ) (hε : 0 ≤ ε)
    (hχ : ContDiff ℝ ∞ χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ ℓ⁻¹) :
    ∀ᵐ y ∂anchoredMeasureE Q, ∀ i : Fin n,
      fderiv ℝ (fun z => loopCutoffF χ s γ ε n.succPNat ℓ ψ (anchorVector z)) (WithLp.ofLp y)
          (Pi.single i 1) =
        loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
          gradVfield s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
            (anchorVector (WithLp.ofLp y)) i.succ +
        loopCutoff s γ ε n.succPNat ℓ (anchorVector (WithLp.ofLp y)) *
          gradWfield s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
            (anchorVector (WithLp.ofLp y)) i.succ +
        gradLoop s (loopTransport χ n.succPNat ℓ γ ψ) n.succPNat ℓ γ
            (anchorVector (WithLp.ofLp y)) *
          fderiv ℝ (fun z => loopCutoff s γ ε n.succPNat ℓ (anchorVector z)) (WithLp.ofLp y)
            (Pi.single i 1) := by
  filter_upwards [ae_mem_anchoredSimplex Q,
    anchoredMeasureE_cutoff_chain_ae hn Q s ((n.succPNat : ℝ) * ℓ) (2 * γ) ε hK
      (by linarith) hs0.le hε] with y hy hd
  have hcut : DifferentiableAt ℝ
      (anchoredCutoff n.succPNat s ((n.succPNat : ℝ) * ℓ) (2 * γ) ε) (WithLp.ofLp y) := by
    rw [anchoredCutoff_eq_comp_gapVector]
    exact hd.1.comp _ (anchoredGapVector_hasFDerivAt n _).differentiableAt
  have hEq : (fun z => loopCutoff s γ ε n.succPNat ℓ (anchorVector z)) =ᶠ[nhds (WithLp.ofLp y)]
      anchoredCutoff n.succPNat s ((n.succPNat : ℝ) * ℓ) (2 * γ) ε := by
    filter_upwards [(isOpen_anchoredDomain n).mem_nhds hy] with z hz
    exact varAlGap_loopCutoff_eq_anchoredCutoff hn hK s ε hz
  exact fun i => varAlLoop_cutoff_product_rule hs0 hs1 hℓ hχ hχs hψ hp hy
    (hcut.congr_of_eventuallyEq hEq) i

end Riesz1

end
