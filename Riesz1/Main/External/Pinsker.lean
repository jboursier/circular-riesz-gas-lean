/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.Pinsker
public import Riesz1.Externals.Pinsker

/-!
# Proof of `Riesz1.External.pinsker`

Pinsker's inequality `Riesz1.External.Pinsker` is proved in `Riesz1.Externals.Pinsker`.
Intermediate results take it as an explicit hypothesis. The main theorems supply this proof,
so they are unconditional. Only `Riesz1/Frozen/External/PinskerProof.lean` imports this module.
-/

public section

namespace Riesz1.Main.External

theorem pinsker : Riesz1.External.Pinsker := Riesz1.Externals.pinsker_proof

end Riesz1.Main.External
