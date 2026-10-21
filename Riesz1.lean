/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.AlmostOptimalRigidity
public import Riesz1.Frozen.QuantitativeVariance
public import Riesz1.Frozen.CentralLimitTheorem
public import Riesz1.Frozen.FluctuationsGapsDiscrepancy
public import Riesz1.Frozen.PowerLawObservable

/-!
# Optimal local laws and central limit theorem for the circular Riesz gas

Lean formalization of J. Boursier, *Optimal local laws and central limit theorem for the
circular Riesz gas* (arXiv:2112.05881). Importing this module gives the five main results:

* `Riesz1.almost_optimal_rigidity`: Theorem 1, near-optimal rigidity of gaps and arc counts.
* `Riesz1.quantitative_variance`: Theorem 2, variance of singular linear statistics.
* `Riesz1.central_limit_theorem`: Theorem 3, CLT for singular linear statistics.
* `Riesz1.fluctuations_gaps_discrepancy`: Corollary 1, CLT for interval counts and gaps.
* `Riesz1.power_law_observable`: Corollary 2, CLT for power-law observables.

Each statement lives in its own file under `Riesz1/Frozen/`, together with the definitions it
uses.
-/
