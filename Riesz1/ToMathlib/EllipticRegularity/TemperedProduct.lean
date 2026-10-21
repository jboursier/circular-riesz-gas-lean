/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.EllipticRegularity.NegativeOrder

/-!
# Cutoff product rules for tempered distributions

Distributional product rules used in the localization of the interior
H² regularity argument. The Laplacian formula is in divergence form, so its
right hand side can be estimated before a weak gradient is known.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv

namespace Riesz1

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- Multiplication by a Schwartz cutoff obeys the distributional
directional derivative product rule. -/
theorem tempered_lineDeriv_smul (b : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) (v : E) :
    ∂_{v} (smulLeftCLM F b u) =
      smulLeftCLM F b (∂_{v} u) + smulLeftCLM F (∂_{v} b : 𝓢(E, ℂ)) u := by
  ext ψ
  change u (SchwartzMap.smulLeftCLM ℂ b (-∂_{v} ψ)) =
    u (-∂_{v} (SchwartzMap.smulLeftCLM ℂ b ψ)) +
      u (SchwartzMap.smulLeftCLM ℂ (∂_{v} b : 𝓢(E, ℂ)) ψ)
  rw [← map_add]
  congr 1
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply b.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (∂_{v} b).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, neg_apply, add_apply]
  rw [SchwartzMap.smulLeftCLM_apply b.hasTemperateGrowth]
  change b x * -(fderiv ℝ (ψ : E → ℂ) x v) =
    -(fderiv ℝ (fun y => b y * ψ y) x v) + (fderiv ℝ (b : E → ℂ) x v) * ψ x
  rw [fderiv_fun_mul (b.differentiableAt) (ψ.differentiableAt)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The second derivative product rule in divergence form. -/
theorem tempered_lineDeriv_two_smul (b : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) (v : E) :
    ∂_{v} (∂_{v} (smulLeftCLM F b u)) =
      smulLeftCLM F b (∂_{v} (∂_{v} u)) +
        (∂_{v} (smulLeftCLM F (∂_{v} b : 𝓢(E, ℂ)) u) +
          ∂_{v} (smulLeftCLM F (∂_{v} b : 𝓢(E, ℂ)) u)) -
        smulLeftCLM F (∂_{v} (∂_{v} b) : 𝓢(E, ℂ)) u := by
  rw [tempered_lineDeriv_smul, LineDeriv.lineDerivOp_add]
  simp_rw [tempered_lineDeriv_smul]
  abel

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
/-- The cutoff Laplacian formula before any first derivative of `u`
has been constructed: `Δ(bu) = bΔu + 2 div(u∇b) - (Δb)u`. -/
theorem tempered_laplacian_smul_divergence (b : 𝓢(E, ℂ)) (u : 𝓢'(E, F)) :
    Δ (smulLeftCLM F b u) = smulLeftCLM F b (Δ u) +
      (∑ i, (∂_{stdOrthonormalBasis ℝ E i}
        (smulLeftCLM F (∂_{stdOrthonormalBasis ℝ E i} b : 𝓢(E, ℂ)) u) +
        ∂_{stdOrthonormalBasis ℝ E i}
        (smulLeftCLM F (∂_{stdOrthonormalBasis ℝ E i} b : 𝓢(E, ℂ)) u))) -
      smulLeftCLM F (Δ b : 𝓢(E, ℂ)) u := by
  classical
  let e := stdOrthonormalBasis ℝ E
  rw [TemperedDistribution.laplacian_eq_sum e,
    TemperedDistribution.laplacian_eq_sum e,
    SchwartzMap.laplacian_eq_sum e]
  simp_rw [tempered_lineDeriv_two_smul]
  rw [map_sum]
  have hb : smulLeftCLM F (∑ i, ∂_{e i} (∂_{e i} b) : 𝓢(E, ℂ)) u =
      ∑ i, smulLeftCLM F (∂_{e i} (∂_{e i} b) : 𝓢(E, ℂ)) u := by
    have hc : (⇑(∑ i, ∂_{e i} (∂_{e i} b) : 𝓢(E, ℂ))) =
        (fun x => ∑ i, (∂_{e i} (∂_{e i} b) : 𝓢(E, ℂ)) x) := by
      ext x
      simp
    rw [hc, TemperedDistribution.smulLeftCLM_sum
      (fun i _ => (∂_{e i} (∂_{e i} b) : 𝓢(E, ℂ)).hasTemperateGrowth)]
    simp
  rw [hb, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- A Schwartz multiplier maps an L² distribution to an L² distribution. -/
theorem memSobolev_zero_smul_schwartz (b : 𝓢(E, ℂ))
    (u : Lp F 2 (volume : Measure E)) :
    MemSobolev 0 2 (smulLeftCLM F b (u : 𝓢'(E, F))) := by
  have hb : MemLp (b : E → ℂ) ⊤ volume := b.memLp_top volume
  apply memSobolev_zero_iff.mpr
  refine ⟨(hb.toLp b) • u, ?_⟩
  exact (Lp.toTemperedDistribution_smul_eq b.hasTemperateGrowth hb u).symm

namespace Internal

/-- The first cutoff step: the localized forcing gives H¹ without an
initial gradient assumption. The forcing hypothesis is for this internal
Fourier helper. It must be derived from the distributional equation. -/
theorem tempered_cutoff_memSobolev_one (u : Lp F 2 (volume : Measure E))
    (b : 𝓢(E, ℂ))
    (hforce : MemSobolev 0 2 (smulLeftCLM F b (Δ (u : 𝓢'(E, F))))) :
    MemSobolev 1 2 (smulLeftCLM F b (u : 𝓢'(E, F))) := by
  have hz := memSobolev_zero_smul_schwartz b u
  have hsum : MemSobolev (-1) 2
      (∑ i, (∂_{stdOrthonormalBasis ℝ E i}
        (smulLeftCLM F (∂_{stdOrthonormalBasis ℝ E i} b : 𝓢(E, ℂ)) u) +
        ∂_{stdOrthonormalBasis ℝ E i}
        (smulLeftCLM F (∂_{stdOrthonormalBasis ℝ E i} b : 𝓢(E, ℂ)) u))) := by
    classical
    apply Finset.sum_induction
    · intro a b ha hb
      exact ha.add hb
    · exact memSobolev_fun_zero E F (-1) 2
    · intro i _
      have hd : MemSobolev (-1) 2 (∂_{stdOrthonormalBasis ℝ E i}
          (smulLeftCLM F (∂_{stdOrthonormalBasis ℝ E i} b : 𝓢(E, ℂ)) u)) := by
        simpa using (memSobolev_zero_smul_schwartz
          (∂_{stdOrthonormalBasis ℝ E i} b) u).lineDerivOp
      exact hd.add hd
  have hΔ : MemSobolev (-1) 2 (Δ (smulLeftCLM F b (u : 𝓢'(E, F)))) := by
    rw [tempered_laplacian_smul_divergence]
    exact ((hforce.mono (by norm_num)).add hsum).sub
      ((memSobolev_zero_smul_schwartz (Δ b) u).mono (by norm_num))
  convert memSobolev_add_two_of_laplacian (hz.mono (by norm_num)) hΔ using 1
  norm_num

end Internal

end Riesz1
