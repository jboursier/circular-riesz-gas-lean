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
# Axiom report of the main results

Prints the axioms on which each of the five main results depends. `scripts/check_axioms.py`
checks that each report lists exactly `propext`, `Classical.choice` and `Quot.sound`:

```bash
lake env lean Riesz1/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

The root module `Riesz1` does not import this file, because its `#print axioms` commands run
again whenever the module is rebuilt.
-/

#print axioms Riesz1.almost_optimal_rigidity
#print axioms Riesz1.quantitative_variance
#print axioms Riesz1.central_limit_theorem
#print axioms Riesz1.fluctuations_gaps_discrepancy
#print axioms Riesz1.power_law_observable
