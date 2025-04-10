/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.Informal.Basic
/-!
# Space

This file contains `d`-dimensional Euclidean space.

-/

/-- The type `Space d` representes `d` dimensional Euclidean space.
  The default value of `d` is `3`. Thus `Space = Space 3`. -/
abbrev Space (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

namespace Space

/-- The standard basis of Space based on `Fin d`. -/
noncomputable
def basis (μ : Fin d) : Space d :=
  EuclideanSpace.single μ 1

/-- The standard coordinate functions of Space based on `Fin d`.

The notation `𝔁 μ p` can be used for this. -/
noncomputable
def coord (μ : Fin d) (p : Space d): ℝ :=
  inner p (basis μ)

@[inherit_doc coord]
scoped notation "𝔁" => coord

/-!

## Calculus

-/

/-- Given a function `f : Space d → M` the derivative of `f` in direction `μ`. -/
informal_definition deriv where
  deps := []
  tag := "7MTGT"

/-- The theorem that derivatives on space commute with one another. -/
informal_lemma deriv_comm where
  deps := []
  tag := "7MTIX"

/-- The vector calculus operator `grad`. -/
informal_definition grad where
  deps := []
  tag := "7MTI6"

/-- The vector calculus operator `curl`. -/
informal_definition curl where
  deps := []
  tag := "7MTJ4"

/-- The vector calculus operator `div`. -/
informal_definition div where
  deps := []
  tag := "7MTKF"

end Space
