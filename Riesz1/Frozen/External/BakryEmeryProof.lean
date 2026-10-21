/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.BakryEmery
import Riesz1.Main.External.BakryEmery

/-!
# Bakry–Émery criterion: `Riesz1.External.bakry_emery`

The Bakry–Émery criterion `Riesz1.External.BakryEmery` is proved in `Riesz1/Externals/`.
Intermediate results take it as an explicit hypothesis. The main theorems supply this proof,
so they are unconditional.
-/

@[expose] public section

namespace Riesz1.External

theorem bakry_emery : Riesz1.External.BakryEmery :=
  by exact Riesz1.Main.External.bakry_emery

end Riesz1.External

end
