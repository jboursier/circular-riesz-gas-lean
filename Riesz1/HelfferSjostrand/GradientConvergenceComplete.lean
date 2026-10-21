/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GradientConvergenceVector
public import Riesz1.HelfferSjostrand.GradientConvergenceAnchoredVector

/-!
# Commutator and gradient convergence: complete statements

The gradient part of Proposition 3.1, in full, is the
conjunction of the following results:

* `hsGradient_commutator` and `anchoredGradient_commutator`: every coordinate.
* `hsGradient_scalar_energy` and `anchoredGradient_scalar_energy`: scalar energy.
* `hsGradient_vector_energy` and `anchoredGradient_vector_energy`: vector energy.
* `hsGradient_graph_convergence` and `anchoredGradient_graph_convergence`:
  scalar domain, limiting operator value, gradient membership in the existing
  vector completion, and convergence in its norm.

The statements are generalized to every positively curved pair family, without
the boundary-growth bound. The input sequences already belong to the
operator, and the variational resolvents identify their scalar limits.
-/

public section
