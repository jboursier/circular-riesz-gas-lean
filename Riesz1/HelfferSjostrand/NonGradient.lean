/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.NonGradientEnergy
public import Riesz1.HelfferSjostrand.NonGradientSum

/-!
# The normalized quotient vector inverse

Import interface for existence, uniqueness, minimization, preservation of the
pointwise zero coordinate sum, the linear inverse `T`,
and the quotient inverse energy. The gap-factorization assertion
of Proposition 3.2 is not supplied by this interface.
-/

public section
