/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsLpLattice
public import Riesz1.Auxiliary.LoopArcsLambda

/-!
# Measurability of the arc discrepancies and of `Λ`

Preparation for the `L^p` bound of the arcs part of Lemma 5.8.
The `L^p` norm of a function of the configuration is defined only for strongly measurable
functions, so the cell estimate needs the joint measurability of `Λ` in the configuration and
the time. This file proves

* `measurable_loopCount_of`: the count `loopCount (a b) (r b) (c b)` is measurable in a parameter
  `b` and a configuration `c b`, for measurable `a`, `r`, `c`.
* `loopDiscrepancy_eq_sub`: for `0 ≤ r ≤ N`, the discrepancy is the count minus `r`, so the
  volume term, which is not measurable in its arguments a priori, is replaced by `r`.
* `loopArcLambda_eq_replace`: `Λ` is unchanged when its discrepancies are replaced by the
  measurable expression `loopCount - r`, on the integration domain.
* `stronglyMeasurable_loopArcLambda`: `(X, t) ↦ Λ(t)` is strongly measurable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set

namespace Riesz1

/-- The `i`-th coordinate of the microscopic lift `N x_i` is measurable in the configuration. -/
theorem measurable_lift_coord (N : ℕ+) (i : Fin (N : ℕ)) :
    Measurable (fun X : Configuration N => (N : ℝ) * X.val i) :=
  measurable_const.mul ((measurable_pi_apply i).comp measurable_subtype_coe)

/-- **Joint measurability of counts.** For measurable arc endpoints and lengths and a
measurable configuration map, the count in the arc `microArc N (a b) (r b)` of the configuration
`c b` is measurable in `b`. -/
theorem measurable_loopCount_of {β : Type*} [MeasurableSpace β] {N : ℕ+} {a r : β → ℝ}
    {c : β → Configuration N} (ha : Measurable a) (hr : Measurable r)
    (hc : Measurable c) :
    Measurable (fun b => loopCount (a b) (r b) (c b)) := by
  unfold loopCount
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have hlift : Measurable (fun b => (N : ℝ) * (c b).val i) :=
    (measurable_lift_coord N i).comp hc
  have hset : MeasurableSet {b | loopPos (c b) i ∈ microArc N (a b) (r b)} := by
    have heq : {b | loopPos (c b) i ∈ microArc N (a b) (r b)} =
        ⋃ n : ℤ, ({b | a b < (N : ℝ) * (c b).val i + n * N} ∩
          {b | (N : ℝ) * (c b).val i + n * N < a b + r b}) := by
      ext b
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, loopPos_mem_microArc_iff]
    rw [heq]
    refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt ha (hlift.add_const ((n : ℝ) * N))
    · exact measurableSet_lt (hlift.add_const ((n : ℝ) * N)) (ha.add hr)
  exact Measurable.ite hset measurable_const measurable_const

/-- **Discrepancy without volume term.** For `0 ≤ r ≤ N` the discrepancy of the arc
`microArc N a r` is the count minus the arclength `r`. -/
theorem loopDiscrepancy_eq_sub {N : ℕ+} (a r : ℝ) (X : Configuration N) (hr0 : 0 ≤ r)
    (hrN : r ≤ N) :
    loopDiscrepancy a r X = loopCount a r X - r := by
  rcases hr0.eq_or_lt with rfl | hr
  · have hempty : microArc N a 0 = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      obtain ⟨σ, hσ, _⟩ := hz
      linarith [hσ.1, hσ.2]
    have hcount : loopCount a 0 X = 0 := by
      simp [loopCount, hempty]
    unfold loopDiscrepancy
    rw [hempty, hcount, measure_empty, ENNReal.toReal_zero]
  · unfold loopDiscrepancy
    rw [volume_microArc hr hrN, ENNReal.toReal_ofReal hr.le]

/-- The third derivative of the kernel `g_N` is measurable: it is the derivative of a function. -/
theorem measurable_iteratedDeriv_three (s : ℝ) (N : ℕ+) :
    Measurable (iteratedDeriv 3 (loopArcG s N)) := by
  have h : iteratedDeriv 3 (loopArcG s N) = deriv (iteratedDeriv 2 (loopArcG s N)) :=
    iteratedDeriv_succ
  rw [h]
  exact measurable_deriv _

/-- **Replacement of the discrepancies.** On the integration domain, the arc
discrepancies in `Λ(t)` are the counts minus the arclength `u` or `v`, as `0 ≤ u, v ≤ N/2`. -/
theorem loopArcLambda_eq_replace (s : ℝ) (N : ℕ+) (X : Configuration N) (t : ℝ) :
    loopArcLambda s N X t
      = (∫ u in (0 : ℝ)..((N : ℝ) / 2), ∫ v in (0 : ℝ)..((N : ℝ) / 2 - u),
          -iteratedDeriv 3 (loopArcG s N) (u + v) * (loopCount (t - u) u X - u)
            * (loopCount t v X - v))
        + iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
          * ∫ u in (0 : ℝ)..((N : ℝ) / 2),
              (loopCount (t - u) u X - u)
                * (loopCount t ((N : ℝ) / 2 - u) X - ((N : ℝ) / 2 - u)) := by
  have hN : (0 : ℝ) ≤ N := by positivity
  have hR0 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have hRN : (N : ℝ) / 2 ≤ N := by linarith
  unfold loopArcLambda
  congr 1
  · refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hR0] at hu
    obtain ⟨hu0, huR⟩ := hu
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by linarith)] at hv
    obtain ⟨hv0, hvR⟩ := hv
    rw [loopDiscrepancy_eq_sub (t - u) u X hu0 (by linarith),
      loopDiscrepancy_eq_sub t v X hv0 (by linarith)]
  · congr 1
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hR0] at hu
    obtain ⟨hu0, huR⟩ := hu
    rw [loopDiscrepancy_eq_sub (t - u) u X hu0 (by linarith),
      loopDiscrepancy_eq_sub t ((N : ℝ) / 2 - u) X (by linarith) (by linarith)]

/-- **Parametric interval integrals.** For a measurable integrand `F` of a parameter and a
variable, and measurable endpoints depending on the parameter, the integral over the interval is
strongly measurable in the parameter. -/
theorem stronglyMeasurable_param_interval {P : Type*} [MeasurableSpace P]
    {F : P × ℝ → ℝ} (hF : Measurable F) {a b : P → ℝ} (ha : Measurable a)
    (hb : Measurable b) :
    StronglyMeasurable (fun p => ∫ v in a p..b p, F (p, v)) := by
  have hI : ∀ c d : P → ℝ, Measurable c → Measurable d →
      StronglyMeasurable (fun p => ∫ v in Ioc (c p) (d p), F (p, v)) := by
    intro c d hc hd
    have hset : MeasurableSet {q : P × ℝ | q.2 ∈ Ioc (c q.1) (d q.1)} := by
      have heq : {q : P × ℝ | q.2 ∈ Ioc (c q.1) (d q.1)} =
          {q | c q.1 < q.2} ∩ {q | q.2 ≤ d q.1} := by
        ext q
        simp [Set.mem_Ioc]
      rw [heq]
      exact (measurableSet_lt (hc.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hd.comp measurable_fst))
    have hG : Measurable (fun q : P × ℝ => if q.2 ∈ Ioc (c q.1) (d q.1) then F q else 0) :=
      Measurable.ite hset hF measurable_const
    have hint := StronglyMeasurable.integral_prod_right' (ν := volume)
      (f := fun q : P × ℝ => if q.2 ∈ Ioc (c q.1) (d q.1) then F q else 0)
      hG.stronglyMeasurable
    have e2 : (fun p : P => ∫ v in Ioc (c p) (d p), F (p, v)) =
        fun p => ∫ v, (if v ∈ Ioc (c p) (d p) then F (p, v) else 0) := by
      funext p
      rw [← integral_indicator measurableSet_Ioc]
      congr 1
      ext v
      simp only [Set.indicator_apply]
    rw [e2]
    exact hint
  have e : (fun p => ∫ v in a p..b p, F (p, v)) =
      fun p => (∫ v in Ioc (a p) (b p), F (p, v)) - ∫ v in Ioc (b p) (a p), F (p, v) := rfl
  rw [e]
  exact (hI a b ha hb).sub (hI b a hb ha)

/-- **Strong measurability of `Λ`.** The map `(X, t) ↦ Λ(t)` is strongly measurable, so its
`L^p` norms over the configuration are defined. -/
theorem stronglyMeasurable_loopArcLambda (s : ℝ) (N : ℕ+) :
    StronglyMeasurable (fun q : Configuration N × ℝ => loopArcLambda s N q.1 q.2) := by
  have hg3 := measurable_iteratedDeriv_three s N
  -- The first double integral, with the inner variable `v` last: `b = ((X, t), u), v`.
  have hF1 : Measurable (fun b : ((Configuration N × ℝ) × ℝ) × ℝ =>
      -iteratedDeriv 3 (loopArcG s N) (b.1.2 + b.2)
        * (loopCount (b.1.1.2 - b.1.2) b.1.2 b.1.1.1 - b.1.2)
        * (loopCount b.1.1.2 b.2 b.1.1.1 - b.2)) := by
    have hX : Measurable (fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.1.1.1) := by fun_prop
    have ht : Measurable (fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.1.1.2) := by fun_prop
    have hu : Measurable (fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.1.2) := by fun_prop
    have hv : Measurable (fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.2) := by fun_prop
    have hc1 := measurable_loopCount_of (N := N) (c := fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.1.1.1)
      (a := fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.1.1.2 - b.1.2) (r := fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.1.2) (ht.sub hu) hu hX
    have hc2 := measurable_loopCount_of (N := N) (c := fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.1.1.1)
      (a := fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.1.1.2) (r := fun b : ((Configuration N × ℝ) × ℝ) × ℝ => b.2) ht hv hX
    exact ((((hg3.comp (hu.add hv)).neg).mul (hc1.sub hu))).mul (hc2.sub hv)
  -- The inner integral over `v ∈ (0, N/2 - u)`, as a function of `((X, t), u)`.
  have hin : StronglyMeasurable (fun p : (Configuration N × ℝ) × ℝ =>
      ∫ v in (0 : ℝ)..((N : ℝ) / 2 - p.2),
        -iteratedDeriv 3 (loopArcG s N) (p.2 + v)
          * (loopCount (p.1.2 - p.2) p.2 p.1.1 - p.2) * (loopCount p.1.2 v p.1.1 - v)) :=
    stronglyMeasurable_param_interval (a := fun _ => (0 : ℝ))
      (b := fun p => (N : ℝ) / 2 - p.2) hF1 measurable_const (measurable_const.sub measurable_snd)
  -- The outer integral over `u ∈ (0, N/2)`.
  have hout : StronglyMeasurable (fun q : Configuration N × ℝ =>
      ∫ u in (0 : ℝ)..((N : ℝ) / 2), ∫ v in (0 : ℝ)..((N : ℝ) / 2 - u),
        -iteratedDeriv 3 (loopArcG s N) (u + v) * (loopCount (q.2 - u) u q.1 - u)
          * (loopCount q.2 v q.1 - v)) :=
    stronglyMeasurable_param_interval hin.measurable (a := fun _ => (0 : ℝ))
      (b := fun _ => (N : ℝ) / 2) measurable_const measurable_const
  -- The atom integral over `u ∈ (0, N/2)`.
  have hF2 : Measurable (fun w : (Configuration N × ℝ) × ℝ =>
      (loopCount (w.1.2 - w.2) w.2 w.1.1 - w.2)
        * (loopCount w.1.2 ((N : ℝ) / 2 - w.2) w.1.1 - ((N : ℝ) / 2 - w.2))) := by
    have hX : Measurable (fun w : (Configuration N × ℝ) × ℝ => w.1.1) := by fun_prop
    have ht : Measurable (fun w : (Configuration N × ℝ) × ℝ => w.1.2) := by fun_prop
    have hu : Measurable (fun w : (Configuration N × ℝ) × ℝ => w.2) := by fun_prop
    have hR : Measurable (fun w : (Configuration N × ℝ) × ℝ => (N : ℝ) / 2 - w.2) :=
      measurable_const.sub hu
    have hc1 := measurable_loopCount_of (N := N) (c := fun w : (Configuration N × ℝ) × ℝ => w.1.1)
      (a := fun w : (Configuration N × ℝ) × ℝ => w.1.2 - w.2) (r := fun w : (Configuration N × ℝ) × ℝ => w.2) (ht.sub hu) hu hX
    have hc2 := measurable_loopCount_of (N := N) (c := fun w : (Configuration N × ℝ) × ℝ => w.1.1)
      (a := fun w : (Configuration N × ℝ) × ℝ => w.1.2) (r := fun w : (Configuration N × ℝ) × ℝ => (N : ℝ) / 2 - w.2) ht hR hX
    exact (hc1.sub hu).mul (hc2.sub hR)
  have hatom : StronglyMeasurable (fun q : Configuration N × ℝ =>
      ∫ u in (0 : ℝ)..((N : ℝ) / 2),
        (loopCount (q.2 - u) u q.1 - u)
          * (loopCount q.2 ((N : ℝ) / 2 - u) q.1 - ((N : ℝ) / 2 - u))) :=
    stronglyMeasurable_param_interval hF2 (a := fun _ => (0 : ℝ)) (b := fun _ => (N : ℝ) / 2)
      measurable_const measurable_const
  have hfun : (fun q : Configuration N × ℝ => loopArcLambda s N q.1 q.2) =
      fun q => (∫ u in (0 : ℝ)..((N : ℝ) / 2), ∫ v in (0 : ℝ)..((N : ℝ) / 2 - u),
          -iteratedDeriv 3 (loopArcG s N) (u + v) * (loopCount (q.2 - u) u q.1 - u)
            * (loopCount q.2 v q.1 - v))
        + iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
          * ∫ u in (0 : ℝ)..((N : ℝ) / 2),
              (loopCount (q.2 - u) u q.1 - u)
                * (loopCount q.2 ((N : ℝ) / 2 - u) q.1 - ((N : ℝ) / 2 - u)) :=
    funext fun q => loopArcLambda_eq_replace s N q.1 q.2
  rw [hfun]
  exact hout.add (hatom.const_mul _)

end Riesz1

end
end
