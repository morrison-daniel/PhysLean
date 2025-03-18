/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.TODO.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Basic
/-!
# Space time

This file introduce 4d Minkowski spacetime.

-/

/-- The type `Space d` representes `d` dimensional Euclidean space.
  The default value of `d` is `3`. Thus `Space = Space 3`. -/
abbrev Space (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

noncomputable section

TODO "SpaceTime should be refactored into a structure, or similar, to prevent casting."

/-- The space-time -/
abbrev SpaceTime (d : ℕ := 3) := Lorentz.Vector d

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The space part of spacetime. -/
@[simp]
def space (x : SpaceTime d) : EuclideanSpace ℝ (Fin d) :=
  fun i => x (Sum.inr i)

end SpaceTime

end
