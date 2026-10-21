/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.PrekopaLeindler
import Riesz1.Main.External.PrekopaLeindler

/-!
# Prékopa–Leindler inequality: `Riesz1.External.prekopa_leindler`

Proof of the Prékopa–Leindler inequality `Riesz1.External.PrekopaLeindler`. The proof is
`Riesz1.Main.External.prekopa_leindler`. Intermediate results take
`Riesz1.External.PrekopaLeindler` as an explicit hypothesis. The main theorems supply this proof.
-/

@[expose] public section

namespace Riesz1.External

theorem prekopa_leindler : Riesz1.External.PrekopaLeindler :=
  by exact Riesz1.Main.External.prekopa_leindler

end Riesz1.External

end
