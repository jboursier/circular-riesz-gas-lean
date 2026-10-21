/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlPiecesEnvelopeMacro
public import Riesz1.Variance.RegUniformTails
public import Riesz1.Variance.RegUniformFirstTransport
public import Riesz1.Variance.RegUniformSecondTransport

/-!
# Decomposition and envelopes of the regularized transport, shrinking scales

Proposition 5.9, compact case: the circle of length `L_N = ℓ_N⁻¹` varies with `N`.
This file contains the length-generic decomposition, the separation of the marks uniform in `N`,
and the uniform bounds of the remainder by the tails of the transport.
-/

public section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace Riesz1

/-- The decomposition of the regularized transport on a circle of length `L ≥ 1`, with the
envelopes of the singular pieces and uniform bounds of the remainder. -/
theorem pieces_envelope_general {r δ M1 M2 S A b K h₀ L : ℝ} {p : ℕ}
    (hL : 1 ≤ L) (hr : 0 < r) (hr16 : r ≤ 1 / 16) (hδr : 6 * r ≤ δ)
    (hM1 : ∀ s, |deriv (cutoffBump r) s| ≤ M1)
    (hM2 : ∀ s, |deriv (deriv (cutoffBump r)) s| ≤ M2)
    (marks : Fin p → ℝ) (hsep : ∀ i k, i ≠ k → δ ≤ circDist L (marks i - marks k))
    {F : ℝ → ℝ} (hFC : ContDiff ℝ ∞ F) (hFP : Function.Periodic F L)
    (hFS : ∀ x, |F x| ≤ S) (hA : 0 ≤ A) (hb : 0 < b) (hK : 1 ≤ K) (hh : K⁻¹ ≤ h₀)
    (hD1 : ∀ x, |deriv F x| ≤ A * (1 + ∑ k, max (circDist L (x - marks k)) h₀ ^ (-b)))
    (hD2 : ∀ x, |deriv (deriv F) x| ≤ A * (1 + ∑ k, max (circDist L (x - marks k)) h₀ ^ (-1 - b))) :
    (∀ j, ContDiff ℝ ∞ (varAlPiece (cutoffBump r) L marks F j) ∧
      Function.Periodic (varAlPiece (cutoffBump r) L marks F j) L) ∧
    (∀ x, F x = ∑ j, varAlPiece (cutoffBump r) L marks F j x) ∧
    (∀ i : Fin p, ∀ x : ℝ,
      |deriv (varAlPiece (cutoffBump r) L marks F (Fin.castSucc i)) (x + marks i)| ≤
          varAlConst M1 M2 S A r p b *
            (if circDist L x < 1 then max (circDist L x) K⁻¹ ^ (-b) else 0) ∧
      |deriv (deriv (varAlPiece (cutoffBump r) L marks F (Fin.castSucc i))) (x + marks i)| ≤
          varAlConst M1 M2 S A r p b *
            (if circDist L x < 1 then max (circDist L x) K⁻¹ ^ (-1 - b) else 0)) ∧
    (∀ x : ℝ,
      |deriv (varAlPiece (cutoffBump r) L marks F (Fin.last p)) x| ≤
          p * M1 * S + (1 + p) * (A * (1 + p * r ^ (-b))) ∧
      |deriv (deriv (varAlPiece (cutoffBump r) L marks F (Fin.last p))) x| ≤
          p * M2 * S + 2 * (p * M1) * (A * (1 + p * r ^ (-b))) +
            (1 + p) * (A * (1 + p * r ^ (-1 - b)))) := by
  have hL0 : 0 < L := by linarith
  have hLr : 4 * r < L := by
    have : (4 : ℝ) * r < 1 := by linarith
    linarith
  have hS : 0 ≤ S := (abs_nonneg _).trans (hFS 0)
  have hM1nn : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2nn : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  obtain ⟨c1, c2, c3, c4, hC1⟩ := varAlConst_bounds (p := p) hM1nn hM2nn hS hA hr b
  have hζ := contDiff_cutoffBump r
  have hζ0 : ∀ s, 2 * r ≤ |s| → cutoffBump r s = 0 := fun s hs => cutoffBump_eq_zero hr hs
  have hK0 : 0 ≤ K := by linarith
  have hWnn : ∀ (x e : ℝ), 0 ≤ (if circDist L x < 1 then max (circDist L x) K⁻¹ ^ e else 0) := by
    intro x e
    split_ifs
    · exact Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.mpr hK0)) _
    · exact le_rfl
  refine ⟨fun j => ⟨contDiff_varAlPiece (ζ := cutoffBump r) hζ hζ0 hL0 hLr marks hFC j,
    periodic_varAlPiece (ζ := cutoffBump r) hL0 marks hFP j⟩,
    fun x => (sum_varAlPiece (cutoffBump r) L marks F x).symm, fun i x => ⟨?_, ?_⟩, fun x => ⟨?_, ?_⟩⟩
  · have hs := (sing_envelope hζ hζ0 (fun s => cutoffBump_mem_Icc r s) hM1 hM2 hL marks hsep
      hr hr16 hδr hFC hFS hA hb hK hh hD1 hD2 i x).1
    refine hs.trans (mul_le_mul_of_nonneg_right c1 ?_)
    exact hWnn x _
  · have hs := (sing_envelope hζ hζ0 (fun s => cutoffBump_mem_Icc r s) hM1 hM2 hL marks hsep
      hr hr16 hδr hFC hFS hA hb hK hh hD1 hD2 i x).2
    refine hs.trans (mul_le_mul_of_nonneg_right c2 ?_)
    exact hWnn x _
  · exact (remainder_envelope hζ hζ0 (fun s hs => cutoffBump_eq_one hs)
      (fun s => cutoffBump_mem_Icc r s) hM1 hM2 hL marks hsep hr hr16 hδr hFC hFS hA hb
      hD1 hD2 x).1
  · exact (remainder_envelope hζ hζ0 (fun s hs => cutoffBump_eq_one hs)
      (fun s => cutoffBump_mem_Icc r s) hM1 hM2 hL marks hsep hr hr16 hδr hFC hFS hA hb
      hD1 hD2 x).2

/-- The circular distance is at most the absolute value. -/
lemma circDist_le_abs' {L : ℝ} (hL : 0 < L) (t : ℝ) : circDist L t ≤ |t| := by
  have h : |cutRep L t| ≤ |t - ((0 : ℤ) : ℝ) * L| := abs_cutRep_le_abs_sub_int_mul hL t 0
  rw [Int.cast_zero, zero_mul, sub_zero] at h
  exact h

/-- Far from the marks, the first and second derivatives of the remainder equal those of `F`. -/
lemma remainder_eq_near {r L : ℝ} (hL0 : 0 < L) (hζ0 : ∀ s, 2 * r ≤ |s| → cutoffBump r s = 0)
    {p : ℕ} (marks : Fin p → ℝ) (F : ℝ → ℝ) {x : ℝ}
    (hx : ∀ i, 2 * r < circDist L (x - marks i)) :
    deriv (varAlPiece (cutoffBump r) L marks F (Fin.last p)) x = deriv F x ∧
      deriv (deriv (varAlPiece (cutoffBump r) L marks F (Fin.last p))) x = deriv (deriv F) x := by
  have hall : ∀ᶠ y in 𝓝 x, ∀ i, markCut (cutoffBump r) L (marks i) y = 0 := by
    rw [Filter.eventually_all]
    intro i
    exact eventually_markCut_eq_zero hL0 hζ0 (marks i) x (hx i)
  have hev : varAlPiece (cutoffBump r) L marks F (Fin.last p) =ᶠ[𝓝 x] F := by
    filter_upwards [hall] with y hy
    rw [varAlPiece_last]
    simp [hy]
  exact ⟨hev.deriv_eq, hev.deriv.deriv_eq⟩

/-- The tail bounds of a periodic function, for points at distance at least two from `0`, follow
from the tail bounds for the central representative. -/
lemma tail_of_central {L : ℝ} (hL : 0 < L) {F : ℝ → ℝ} (hFP : Function.Periodic F L) {C s : ℝ}
    (hcen : ∀ y : ℝ, 2 ≤ |y| → |y| ≤ L / 2 →
      |deriv F y| ≤ C * |y| ^ (s - 2) ∧ |deriv (deriv F) y| ≤ C * |y| ^ (s - 3))
    (x : ℝ) (hx : 2 ≤ circDist L x) :
    |deriv F x| ≤ C * circDist L x ^ (s - 2) ∧
      |deriv (deriv F) x| ≤ C * circDist L x ^ (s - 3) := by
  set m : ℤ := round (x / L) with hm
  set xc : ℝ := x - L * round (x / L) with hxc
  have hxm : xc + (m : ℝ) * L = x := by
    rw [hxc, hm]
    ring
  have hd1 : Function.Periodic (deriv F) L := varAlPieces_periodic_deriv_of hFP
  have hd2 : Function.Periodic (deriv (deriv F)) L := varAlPieces_periodic_deriv_of hd1
  have e1 : deriv F x = deriv F xc := by
    rw [← hxm]
    exact hd1.int_mul m xc
  have e2 : deriv (deriv F) x = deriv (deriv F) xc := by
    rw [← hxm]
    exact hd2.int_mul m xc
  have hcd : circDist L x = |xc| := rfl
  have hxc2 : 2 ≤ |xc| := by rw [← hcd]; exact hx
  have hxcL : |xc| ≤ L / 2 := abs_cutRep_le_half hL x
  obtain ⟨h1, h2⟩ := hcen xc hxc2 hxcL
  rw [hcd, e1, e2]
  exact ⟨h1, h2⟩

/-- The weighted envelope of a remainder bounded by `A0` near the marks, and by the tails away
from the marks. -/
lemma weighted_remainder_bound {d v A0 Ct R s k W K : ℝ} (hd0 : 0 ≤ d) (hR : 2 ≤ R)
    (hk : s < k) (hW : d < 1 → 1 ≤ W) (hv : |v| ≤ A0)
    (hRd : R ≤ d → |v| ≤ Ct * d ^ (s - k))
    (hK1 : A0 * R ^ (k - s) ≤ K) (hK2 : A0 ≤ K) (hK3 : Ct ≤ K) (hK0 : 0 ≤ K) :
    |v| ≤ K * (if d < 1 then W else d ^ (s - k)) := by
  have hA0 : 0 ≤ A0 := (abs_nonneg v).trans hv
  split_ifs with hd1
  · exact hv.trans (hK2.trans (le_mul_of_one_le_right hK0 (hW hd1)))
  · have hd1' : 1 ≤ d := not_lt.mp hd1
    by_cases hdR : d < R
    · have hpos : 0 < d := lt_of_lt_of_le zero_lt_one hd1'
      have hRpos : 0 < R := by linarith
      have hmono : R ^ (s - k) ≤ d ^ (s - k) :=
        Real.rpow_le_rpow_of_nonpos hpos hdR.le (by linarith)
      have hprod : 1 ≤ R ^ (k - s) * d ^ (s - k) := by
        have hsplit : R ^ (k - s) * R ^ (s - k) = 1 := by
          rw [← Real.rpow_add hRpos, show k - s + (s - k) = 0 by ring, Real.rpow_zero]
        have hdpos : 0 ≤ d ^ (s - k) := Real.rpow_nonneg hd0 _
        have hRk : 0 ≤ R ^ (k - s) := Real.rpow_nonneg hRpos.le _
        nlinarith [mul_le_mul_of_nonneg_left hmono hRk]
      calc |v| ≤ A0 := hv
        _ ≤ A0 * (R ^ (k - s) * d ^ (s - k)) := le_mul_of_one_le_right hA0 hprod
        _ = (A0 * R ^ (k - s)) * d ^ (s - k) := by ring
        _ ≤ K * d ^ (s - k) := mul_le_mul_of_nonneg_right hK1 (Real.rpow_nonneg hd0 _)
    · have hdR' : R ≤ d := not_lt.mp hdR
      have hRd' := hRd hdR'
      exact hRd'.trans (mul_le_mul_of_nonneg_right hK3 (Real.rpow_nonneg hd0 _))

/-- The weight `max(d, K⁻¹)^e` is at least one for `d < 1`, `K ≥ 1` and `e ≤ 0`. -/
lemma one_le_weight_of_lt {L x K e : ℝ} (hd : circDist L x < 1) (hK : 1 ≤ K) (he : e ≤ 0) :
    1 ≤ max (circDist L x) K⁻¹ ^ e := by
  have hKinv : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
  have hpos : 0 < max (circDist L x) K⁻¹ :=
    lt_max_of_lt_right (inv_pos.mpr (by linarith))
  have hle : max (circDist L x) K⁻¹ ≤ 1 := max_le hd.le hKinv
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpos hle he

/-- A finite family of positive numbers has a common positive lower bound. -/
lemma exists_pos_le_finset {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a s ha ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    refine ⟨min δ (f a), lt_min hδ (hf a), fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h i hi)

/-- The marks stay uniformly separated on the circles of all scales of a sequence tending to
zero in the scale, that is, of lengths tending to infinity. -/
theorem compact_mark_separation {n : ℕ} (marks : Fin n → ℝ) (ell : Scales)
    (hell : Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0))
    (hinj : ∀ N : ℕ+, Function.Injective
      (fun j : Fin n => ((marks j : ℝ) : Circle (observationLength (ell N))))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (N : ℕ+) (i k : Fin n), i ≠ k →
      δ ≤ circDist (observationLength (ell N)).val (marks i - marks k) := by
  classical
  have hmarks : Function.Injective marks := by
    intro i k hik
    apply hinj 1
    simp only [hik]
  obtain ⟨δ0, hδ0, hδ0sep⟩ := exists_pos_le_dist_of_injective hmarks
  have hδ0' : ∀ i k : Fin n, i ≠ k → δ0 ≤ |marks i - marks k| := fun i k hik => by
    have := hδ0sep i k hik
    rwa [Real.dist_eq] at this
  set D : ℝ := ∑ i, ∑ k, |marks i - marks k| with hD
  have hDle : ∀ i k : Fin n, |marks i - marks k| ≤ D := by
    intro i k
    have h1 : |marks i - marks k| ≤ ∑ k', |marks i - marks k'| :=
      Finset.single_le_sum (f := fun k' => |marks i - marks k'|)
        (fun k' _ => abs_nonneg _) (Finset.mem_univ k)
    have h2 : ∑ k', |marks i - marks k'| ≤ D :=
      Finset.single_le_sum (f := fun i' => ∑ k', |marks i' - marks k'|)
        (fun i' _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  have hT : 0 < 2 * D + 2 := by linarith
  have hε : (0 : ℝ) < 1 / (2 * D + 2) := by positivity
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.1 (hell.eventually (Iio_mem_nhds hε))
  -- The finitely many circles of small length.
  have hfin : ∀ k : ℕ, ∃ d : ℝ, 0 < d ∧ ∀ i k' : Fin n, i ≠ k' →
      d ≤ circDist (observationLength (ell ⟨k + 1, Nat.succ_pos k⟩)).val
        (marks i - marks k') := by
    intro k
    obtain ⟨d, hd, hdsep⟩ := exists_pos_le_dist_of_injective (hinj ⟨k + 1, Nat.succ_pos k⟩)
    refine ⟨d, hd, fun i k' hik => ?_⟩
    have h1 := hdsep i k' hik
    rwa [dist_coe_eq_circDist_sub (observationLength _).property] at h1
  choose G hGpos hGsep using hfin
  obtain ⟨δf, hδf, hδfle⟩ := exists_pos_le_finset (Finset.range K0) G hGpos
  refine ⟨min δ0 δf, lt_min hδ0 hδf, fun N i k hik => ?_⟩
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (N : ℕ) = k₀ + 1 := ⟨(N : ℕ) - 1, by have := N.pos; omega⟩
  have hN : N = ⟨k₀ + 1, Nat.succ_pos k₀⟩ := PNat.eq hk₀
  subst hN
  by_cases hsmall : k₀ < K0
  · exact (min_le_right _ _).trans
      ((hδfle k₀ (Finset.mem_range.mpr hsmall)).trans (hGsep k₀ i k hik))
  · have hsmall' : K0 ≤ k₀ := not_lt.mp hsmall
    have hℓ := hK0 k₀ hsmall'
    have hℓpos : 0 < (ell ⟨k₀ + 1, Nat.succ_pos k₀⟩).val := (ell _).property.1
    have hLD : 2 * D + 2 < (ell ⟨k₀ + 1, Nat.succ_pos k₀⟩).val⁻¹ := by
      have h1 : (ell ⟨k₀ + 1, Nat.succ_pos k₀⟩).val * (2 * D + 2) < 1 :=
        (lt_div_iff₀ hT).1 hℓ
      have hinv : (ell ⟨k₀ + 1, Nat.succ_pos k₀⟩).val *
          (ell ⟨k₀ + 1, Nat.succ_pos k₀⟩).val⁻¹ = 1 := mul_inv_cancel₀ hℓpos.ne'
      nlinarith [mul_pos (sub_pos.2 h1) (inv_pos.2 hℓpos)]
    show min δ0 δf ≤ circDist (ell ⟨k₀ + 1, Nat.succ_pos k₀⟩).val⁻¹ (marks i - marks k)
    have hle : |marks i - marks k| ≤ (ell ⟨k₀ + 1, Nat.succ_pos k₀⟩).val⁻¹ / 2 := by
      linarith [hDle i k]
    rw [circDist_eq_abs (inv_pos.mpr hℓpos) hle]
    exact (min_le_left _ _).trans (hδ0' i k hik)

/-- The compact decomposition: on the circles of the shrinking scales, the regularized transport
is a sum of `n + 1` smooth periodic pieces with envelopes, with constants independent of `N`,
`h` and the transport. -/
theorem varAl_envelope_compact (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B C₀ : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α : ℝ)
    (hη : 0 < η) (hB : 0 < B) (hC₀ : 0 < C₀) (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2)
    (ell : Scales)
    (hell : Filter.Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) Filter.atTop
      (nhds 0))
    (hreg : ∀ N : ℕ+,
      PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ (m : ℕ) (C : ℝ), 0 < C ∧ ∀ (N : ℕ+) (h : ℝ),
      1 ≤ (N : ℝ) * (ell N).val → ((N : ℝ) * (ell N).val)⁻¹ ≤ h → h ≤ 1 →
      ∀ ψ : {g : Circle (observationLength (ell N)) → ℝ //
          MemLp (fun x => (g x : ℂ)) 2 (arclength (observationLength (ell N)))},
        (∀ k : ℤ, coeff (observationLength (ell N)) ⟨(fun x => (ψ.val x : ℂ)),
            complexL2Integrable _ _ ψ.property⟩ k
            = transportCoeffs P (observationLength (ell N))
                ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ k) →
        Continuous ψ.val →
        ∃ φ : Fin m → ℝ → ℝ,
          (∀ j, ContDiff ℝ ∞ (φ j) ∧ Function.Periodic (φ j) (observationLength (ell N)).val ∧
              ∃ C' : NNReal, LipschitzWith C' (φ j)) ∧
          (∀ x : ℝ, circleMollify ρ (observationLength (ell N)).val h
              (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) x = ∑ j, φ j x) ∧
          (∀ j, ∃ a : ℝ,
              (∀ x : ℝ, |deriv (fun t => φ j (t + a)) x| ≤
                  C * (if circDist (observationLength (ell N)).val x < 1 then
                    max (circDist (observationLength (ell N)).val x)
                      ((N : ℝ) * (ell N).val)⁻¹ ^ (-(1 - P.val.2 + α))
                    else circDist (observationLength (ell N)).val x ^ (P.val.2 - 2))) ∧
              (∀ x : ℝ, |deriv (deriv (fun t => φ j (t + a))) x| ≤
                  C * (if circDist (observationLength (ell N)).val x < 1 then
                    max (circDist (observationLength (ell N)).val x)
                      ((N : ℝ) * (ell N).val)⁻¹ ^ (-(1 + (1 - P.val.2 + α)))
                    else circDist (observationLength (ell N)).val x ^ (P.val.2 - 3)))) := by
  classical
  -- Separation of the marks, uniform in `N`, and the cutoff radius.
  obtain ⟨δ, hδ0, hδsep⟩ := compact_mark_separation marks ell hell (fun N => (hreg N).2.1)
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = min (δ / 6) (1 / 16) := ⟨_, rfl⟩
  have hr : 0 < r := by
    rw [hr_def]
    exact lt_min (by linarith) (by norm_num)
  have hr16 : r ≤ 1 / 16 := by
    rw [hr_def]
    exact min_le_right _ _
  have hδr : 6 * r ≤ δ := by
    have h1 := min_le_left (δ / 6) (1 / 16)
    rw [← hr_def] at h1
    linarith
  have hζ0 : ∀ s, 2 * r ≤ |s| → cutoffBump r s = 0 := fun s hs => cutoffBump_eq_zero hr hs
  obtain ⟨M1, M2, hM1, hM2⟩ := exists_bounds_deriv_bump (contDiff_cutoffBump r) hζ0
  -- The transports and the sup bound, with constants before the scales.
  have hα0' : P.val.2 - 1 ≤ α := hα0.le
  obtain ⟨C₁, hC₁, hT1⟩ := regUniform_firstTransport_compact P p hp η B n marks α α C₀ hη
    hB.le hC₀.le hα0' hα1 le_rfl hα0 hα1 ρ hρ
  obtain ⟨C₂, hC₂, hT2⟩ := regUniform_secondTransport_compact P p hp η B n marks α α C₀ hη
    hB.le hC₀.le hα0' hα1 le_rfl hα0 hα1 ρ hρ
  obtain ⟨Ct, hCt, hTails⟩ := regUniform_transportTails_compact P p hp η B n marks α α C₀ hη
    hB.le hC₀.le hα0' hα1 le_rfl hα0 hα1 ρ hρ
  obtain ⟨Cs, hCs, hsup⟩ := regUniform_transport_sup P η B hη hB.le
  have hb : 0 < 1 - P.val.2 + α := by linarith
  have hs1 : P.val.2 < 1 := P.property.2.2
  have hA : 0 ≤ max C₁ C₂ := le_trans hC₁.le (le_max_left _ _)
  have hM1nn : 0 ≤ M1 := (abs_nonneg _).trans (hM1 0)
  have hM2nn : 0 ≤ M2 := (abs_nonneg _).trans (hM2 0)
  -- The radius beyond which the tails apply.
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 + ∑ j, |marks j| := ⟨_, rfl⟩
  have hR2 : 2 ≤ R := by
    have : 0 ≤ ∑ j, |marks j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  have hRa : ∀ i, |marks i| ≤ R - 2 := by
    intro i
    have h1 : |marks i| ≤ ∑ j, |marks j| :=
      Finset.single_le_sum (f := fun j => |marks j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    linarith
  -- The constant of the envelopes, independent of `N`, `h` and the transport.
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, R1 = ((n : ℕ) : ℝ) * M1 * Cs +
      (1 + ((n : ℕ) : ℝ)) * (max C₁ C₂ * (1 + ((n : ℕ) : ℝ) *
        r ^ (-(1 - P.val.2 + α)))) := ⟨_, rfl⟩
  obtain ⟨R2, hR2def⟩ : ∃ R2 : ℝ, R2 = ((n : ℕ) : ℝ) * M2 * Cs +
      2 * (((n : ℕ) : ℝ) * M1) * (max C₁ C₂ * (1 + ((n : ℕ) : ℝ) *
        r ^ (-(1 - P.val.2 + α)))) +
      (1 + ((n : ℕ) : ℝ)) * (max C₁ C₂ * (1 + ((n : ℕ) : ℝ) *
        r ^ (-1 - (1 - P.val.2 + α)))) := ⟨_, rfl⟩
  have hvc := varAlConst_bounds (p := (n : ℕ)) hM1nn hM2nn hCs.le hA hr (1 - P.val.2 + α)
  obtain ⟨Kc, hKc⟩ : ∃ K : ℝ, K = varAlConst M1 M2 Cs (max C₁ C₂) r (n : ℕ)
      (1 - P.val.2 + α) + Ct + |R1| * R ^ (2 - P.val.2) + |R2| * R ^ (3 - P.val.2) :=
    ⟨_, rfl⟩
  have hR1le : R1 ≤ varAlConst M1 M2 Cs (max C₁ C₂) r (n : ℕ) (1 - P.val.2 + α) := by
    have := hvc.2.2.1
    rw [hR1]
    exact this
  have hR2le : R2 ≤ varAlConst M1 M2 Cs (max C₁ C₂) r (n : ℕ) (1 - P.val.2 + α) := by
    have := hvc.2.2.2.1
    rw [hR2def]
    exact this
  have hRpow1 : 0 ≤ R ^ (2 - P.val.2) := Real.rpow_nonneg (by linarith) _
  have hRpow2 : 0 ≤ R ^ (3 - P.val.2) := Real.rpow_nonneg (by linarith) _
  have hvc1 : 1 ≤ varAlConst M1 M2 Cs (max C₁ C₂) r (n : ℕ) (1 - P.val.2 + α) := hvc.2.2.2.2
  have hK0 : 0 ≤ Kc := by
    rw [hKc]
    have := mul_nonneg (abs_nonneg R1) hRpow1
    have := mul_nonneg (abs_nonneg R2) hRpow2
    linarith
  have hKgeV : varAlConst M1 M2 Cs (max C₁ C₂) r (n : ℕ) (1 - P.val.2 + α) ≤ Kc := by
    rw [hKc]
    have := mul_nonneg (abs_nonneg R1) hRpow1
    have := mul_nonneg (abs_nonneg R2) hRpow2
    linarith
  have hKgeT : Ct ≤ Kc := by
    rw [hKc]
    have := mul_nonneg (abs_nonneg R1) hRpow1
    have := mul_nonneg (abs_nonneg R2) hRpow2
    have := hvc1
    linarith
  have hK1a : R1 * R ^ (2 - P.val.2) ≤ Kc := by
    rw [hKc]
    have h1 : R1 * R ^ (2 - P.val.2) ≤ |R1| * R ^ (2 - P.val.2) :=
      mul_le_mul_of_nonneg_right (le_abs_self R1) hRpow1
    have := mul_nonneg (abs_nonneg R2) hRpow2
    linarith [hvc.1, hvc1]
  have hK1b : R2 * R ^ (3 - P.val.2) ≤ Kc := by
    rw [hKc]
    have h1 : R2 * R ^ (3 - P.val.2) ≤ |R2| * R ^ (3 - P.val.2) :=
      mul_le_mul_of_nonneg_right (le_abs_self R2) hRpow2
    have := mul_nonneg (abs_nonneg R1) hRpow1
    linarith
  have hK2a : R1 ≤ Kc := le_trans hR1le hKgeV
  have hK2b : R2 ≤ Kc := le_trans hR2le hKgeV
  have hKcpos : 0 < Kc := lt_of_lt_of_le one_pos (le_trans hvc1 hKgeV)
  refine ⟨(n : ℕ) + 1, Kc, hKcpos, ?_⟩
  intro N h hN hNh hh1 ψ hψcoeff hψcont
  -- The circle of this scale.
  have hℓpos : 0 < (ell N).val := (ell N).property.1
  have hℓle : (ell N).val ≤ 1 := (ell N).property.2
  have hLpos : 0 < (observationLength (ell N)).val := (observationLength (ell N)).property
  have hL1 : (1 : ℝ) ≤ (observationLength (ell N)).val := by
    show (1 : ℝ) ≤ (ell N).val⁻¹
    exact (one_le_inv₀ hℓpos).2 hℓle
  have hK0pos : 0 < (N : ℝ) * (ell N).val := lt_of_lt_of_le one_pos hN
  have hh0 : 0 < h := lt_of_lt_of_le (inv_pos.mpr hK0pos) hNh
  have hK1 : (1 : ℝ) ≤ (N : ℝ) * (ell N).val := hN
  -- The transports and the sup bound on this circle, identified with `ψ` by uniqueness.
  obtain ⟨ψ₁, hψ₁c, hψ₁m, hψ₁coeff, hD1raw⟩ :=
    hT1 ell hell hreg (ell N) (hreg N).1 (hreg N).2
  obtain ⟨ψ₂, hψ₂c, hψ₂m, hψ₂coeff, hD2raw⟩ :=
    hT2 ell hell hreg (ell N) (hreg N).1 (hreg N).2
  obtain ⟨ψt, hψtc, hψtm, hψtcoeff, htail⟩ :=
    hTails ell hell hreg (ell N) (hreg N).1 (hreg N).2
  obtain ⟨ψs, hψsc, hψsm, hψscoeff, -, hψsmoll⟩ :=
    hsup (observationLength (ell N))
      ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
      (hreg N).1
  have hψ1 : ψ.val = ψ₁ :=
    continuous_eq_of_coeff_eq hψcont hψ₁c ψ.property hψ₁m
      (fun k => (hψcoeff k).trans (hψ₁coeff k).symm)
  have hψ2 : ψ.val = ψ₂ :=
    continuous_eq_of_coeff_eq hψcont hψ₂c ψ.property hψ₂m
      (fun k => (hψcoeff k).trans (hψ₂coeff k).symm)
  have hψt : ψ.val = ψt :=
    continuous_eq_of_coeff_eq hψcont hψtc ψ.property hψtm
      (fun k => (hψcoeff k).trans (hψtcoeff k).symm)
  have hψs : ψ.val = ψs :=
    continuous_eq_of_coeff_eq hψcont hψsc ψ.property hψsm
      (fun k => (hψcoeff k).trans (hψscoeff k).symm)
  -- The regularization of `ψ` on this circle.
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = circleMollify ρ (observationLength (ell N)).val h
      (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) := ⟨_, rfl⟩
  have hlocI : LocallyIntegrable
      (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N)))) volume :=
    (hψcont.comp (AddCircle.continuous_mk' (observationLength (ell N)).val)).locallyIntegrable
  have hperψ : Function.Periodic
      (fun t : ℝ => ψ.val (t : Circle (observationLength (ell N))))
      (observationLength (ell N)).val := by
    intro t
    simp only [AddCircle.coe_add_period]
  have hFC : ContDiff ℝ ∞ F := by
    rw [hF]
    exact contDiff_circleMollify hρ hLpos hh0 hlocI hperψ
  have hFP : Function.Periodic F (observationLength (ell N)).val := by
    rw [hF]
    exact Riesz1.Internal.circleMollify_periodic hρ hLpos hh0 hlocI hperψ
  have hFS : ∀ x, |F x| ≤ Cs := by
    intro x
    have h1 := hψsmoll ρ hρ h hh0 x
    rw [← hψs] at h1
    rw [hF]
    exact h1
  have hD1 : ∀ x, |deriv F x| ≤ max C₁ C₂ * (1 + ∑ k, max
      (circDist (observationLength (ell N)).val (x - marks k)) h ^ (-(1 - P.val.2 + α))) := by
    intro x
    have h1 := hD1raw h hh0 hh1 x
    rw [← hψ1] at h1
    simp only [dist_coe_eq_circDist_sub hLpos] at h1
    have e : -1 + P.val.2 - α = -(1 - P.val.2 + α) := by ring
    rw [e] at h1
    rw [hF]
    have hsum0 : 0 ≤ ∑ k, max (circDist (observationLength (ell N)).val (x - marks k)) h ^
        (-(1 - P.val.2 + α)) :=
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg (le_max_of_le_right hh0.le) _
    calc _ ≤ C₁ * (1 + ∑ k, max (circDist (observationLength (ell N)).val (x - marks k)) h ^
          (-(1 - P.val.2 + α))) := h1
      _ ≤ max C₁ C₂ * (1 + ∑ k, max (circDist (observationLength (ell N)).val (x - marks k)) h ^
          (-(1 - P.val.2 + α))) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  have hD2 : ∀ x, |deriv (deriv F) x| ≤ max C₁ C₂ * (1 + ∑ k, max
      (circDist (observationLength (ell N)).val (x - marks k)) h ^
        (-1 - (1 - P.val.2 + α))) := by
    intro x
    have h1 := hD2raw h hh0 hh1 x
    rw [← hψ2] at h1
    simp only [dist_coe_eq_circDist_sub hLpos] at h1
    have e : -2 + P.val.2 - α = -1 - (1 - P.val.2 + α) := by ring
    rw [e] at h1
    rw [hF]
    have hsum0 : 0 ≤ ∑ k, max (circDist (observationLength (ell N)).val (x - marks k)) h ^
        (-1 - (1 - P.val.2 + α)) :=
      Finset.sum_nonneg fun k _ => Real.rpow_nonneg (le_max_of_le_right hh0.le) _
    calc _ ≤ C₂ * (1 + ∑ k, max (circDist (observationLength (ell N)).val (x - marks k)) h ^
          (-1 - (1 - P.val.2 + α))) := h1
      _ ≤ max C₁ C₂ * (1 + ∑ k, max (circDist (observationLength (ell N)).val (x - marks k)) h ^
          (-1 - (1 - P.val.2 + α))) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  -- The pieces and their envelopes on this circle.
  obtain ⟨hpc, hsum, hsing, hrem⟩ := pieces_envelope_general hL1 hr hr16 hδr hM1 hM2 marks
    (fun i k hik => hδsep N i k hik) hFC hFP hFS hA hb hN hNh hD1 hD2
  -- The central tail bound for `F`, and the far-field equality of the remainder.
  have hcen : ∀ y : ℝ, 2 ≤ |y| → |y| ≤ (observationLength (ell N)).val / 2 →
      |deriv F y| ≤ Ct * |y| ^ (P.val.2 - 2) ∧ |deriv (deriv F) y| ≤ Ct * |y| ^ (P.val.2 - 3) := by
    intro y hy1 hy2
    have h1 := htail h hh0 hh1 y hy1 hy2
    rw [← hψt, ← hF] at h1
    exact h1
  have hfar : ∀ y : ℝ, R ≤ circDist (observationLength (ell N)).val y →
      ∀ i, 2 * r < circDist (observationLength (ell N)).val (y - marks i) := by
    intro y hy i
    have h1 := circDist_add_le hLpos (y - marks i) (marks i)
    rw [sub_add_cancel] at h1
    have h2 := circDist_le_abs' hLpos (marks i)
    have h3 := hRa i
    linarith
  refine ⟨varAlPiece (cutoffBump r) (observationLength (ell N)).val marks F,
    fun j => ⟨(hpc j).1, (hpc j).2,
      lipschitz_of_periodic_contDiff hLpos (hpc j).1 (hpc j).2⟩,
    fun x => by rw [← hF]; exact hsum x, ?_⟩
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · -- The remainder piece, translated by `0`.
    refine ⟨0, fun x => ?_, fun x => ?_⟩
    · simp only [add_zero]
      have hW : circDist (observationLength (ell N)).val x < 1 →
          1 ≤ max (circDist (observationLength (ell N)).val x) ((N : ℝ) * (ell N).val)⁻¹ ^
            (-(1 - P.val.2 + α)) := fun hd =>
        one_le_weight_of_lt hd hK1 (by linarith)
      have hv : |deriv (varAlPiece (cutoffBump r) (observationLength (ell N)).val marks F
          (Fin.last (n : ℕ))) x| ≤ R1 := by
        rw [hR1]
        exact (hrem x).1
      exact weighted_remainder_bound (k := 2) (s := P.val.2) (A0 := R1) (Ct := Ct) (R := R)
        (K := Kc) (circDist_nonneg _ _) hR2 (by linarith) hW hv
        (fun hRd => by
          obtain ⟨e1, -⟩ := remainder_eq_near hLpos hζ0 marks F
            (hfar x hRd)
          rw [e1]
          exact (tail_of_central hLpos hFP hcen x (by linarith)).1)
        hK1a hK2a hKgeT hK0
    · simp only [add_zero]
      rw [show -(1 + (1 - P.val.2 + α)) = -1 - (1 - P.val.2 + α) by ring]
      have hW : circDist (observationLength (ell N)).val x < 1 →
          1 ≤ max (circDist (observationLength (ell N)).val x) ((N : ℝ) * (ell N).val)⁻¹ ^
            (-1 - (1 - P.val.2 + α)) := fun hd =>
        one_le_weight_of_lt hd hK1 (by linarith)
      have hv : |deriv (deriv (varAlPiece (cutoffBump r) (observationLength (ell N)).val marks F
          (Fin.last (n : ℕ)))) x| ≤ R2 := by
        rw [hR2def]
        exact (hrem x).2
      exact weighted_remainder_bound (k := 3) (s := P.val.2) (A0 := R2) (Ct := Ct) (R := R)
        (K := Kc) (circDist_nonneg _ _) hR2 (by linarith) hW hv
        (fun hRd => by
          obtain ⟨-, e2⟩ := remainder_eq_near hLpos hζ0 marks F
            (hfar x hRd)
          rw [e2]
          exact (tail_of_central hLpos hFP hcen x (by linarith)).2)
        hK1b hK2b hKgeT hK0
  · -- A singular piece, translated to its mark.
    refine ⟨marks i, fun x => ?_, fun x => ?_⟩
    · rw [deriv_comp_add_const]
      have hs := (hsing i x).1
      split_ifs at hs ⊢ with hd
      · exact hs.trans (mul_le_mul_of_nonneg_right hKgeV
          (Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.mpr hK0pos.le)) _))
      · rw [mul_zero] at hs
        exact hs.trans (mul_nonneg hK0 (Real.rpow_nonneg (circDist_nonneg _ _) _))
    · have hfun : deriv (fun t => varAlPiece (cutoffBump r) (observationLength (ell N)).val
          marks F (Fin.castSucc i) (t + marks i)) =
          fun t => deriv (varAlPiece (cutoffBump r) (observationLength (ell N)).val marks F
            (Fin.castSucc i)) (t + marks i) :=
        funext fun t => deriv_comp_add_const _ _ _
      rw [hfun, deriv_comp_add_const,
        show -(1 + (1 - P.val.2 + α)) = -1 - (1 - P.val.2 + α) by ring]
      have hs := (hsing i x).2
      split_ifs at hs ⊢ with hd
      · exact hs.trans (mul_le_mul_of_nonneg_right hKgeV
          (Real.rpow_nonneg (le_max_of_le_right (inv_nonneg.mpr hK0pos.le)) _))
      · rw [mul_zero] at hs
        exact hs.trans (mul_nonneg hK0 (Real.rpow_nonneg (circDist_nonneg _ _) _))

end Riesz1
