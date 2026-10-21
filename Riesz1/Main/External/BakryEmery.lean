/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.BakryEmery
public import Riesz1.Externals.BakryEmeryProof

/-!
# Proof of `Riesz1.External.bakry_emery`

The Bakry–Émery criterion `Riesz1.External.BakryEmery` is proved in
`Riesz1.Externals.BakryEmeryProof`. Intermediate results take it as an explicit hypothesis.
The main theorems supply this proof, so they are unconditional. Only
`Riesz1/Frozen/External/BakryEmeryProof.lean` imports this module.
-/

public section

namespace Riesz1.Main.External

theorem bakry_emery : Riesz1.External.BakryEmery := Riesz1.Externals.bakry_emery_proof

end Riesz1.Main.External
