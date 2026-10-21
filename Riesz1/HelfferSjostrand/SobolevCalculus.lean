/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevC1Composition
public import Riesz1.HelfferSjostrand.SobolevPiecewiseComposition
public import Riesz1.HelfferSjostrand.SobolevTruncation
public import Riesz1.HelfferSjostrand.AnchoredSobolevPiecewiseComposition
public import Riesz1.HelfferSjostrand.AnchoredSobolevTruncation

/-!
# Scalar calculus for the periodic and anchored Gibbs Sobolev completions

The chain rules, level-set locality, and truncation claims for the periodic
Sobolev completion, with their anchored counterparts.
This module collects the scalar calculus API. The literal transport of
weak gradients to all Euclidean charts is a separate remaining task.
-/

public section
