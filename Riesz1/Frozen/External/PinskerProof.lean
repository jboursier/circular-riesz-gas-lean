/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.External.Pinsker
import Riesz1.Main.External.Pinsker

/-!
# Pinsker's inequality: `Riesz1.External.pinsker`

Proof of Pinsker's inequality `Riesz1.External.Pinsker`, from `Riesz1.Main.External.pinsker`.
Downstream proofs take `Riesz1.External.Pinsker` as an explicit hypothesis.
The main theorems supply this proof, so they are unconditional.
-/

@[expose] public section

namespace Riesz1.External

theorem pinsker : Riesz1.External.Pinsker :=
  by exact Riesz1.Main.External.pinsker

end Riesz1.External

end
