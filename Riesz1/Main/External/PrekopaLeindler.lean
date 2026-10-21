/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.PrekopaLeindler
public import Riesz1.Externals.PrekopaLeindlerProof

/-!
# Proof of `Riesz1.External.prekopa_leindler`

The Prékopa–Leindler inequality `Riesz1.External.PrekopaLeindler` is proved in
`Riesz1.Externals.PrekopaLeindlerProof`. Intermediate results take it as an explicit hypothesis.
The main theorems supply this proof, so they are unconditional. Only
`Riesz1/Frozen/External/PrekopaLeindlerProof.lean` imports this module.
-/

public section

namespace Riesz1.Main.External

theorem prekopa_leindler : Riesz1.External.PrekopaLeindler := Riesz1.Externals.prekopa_leindler_proof

end Riesz1.Main.External
