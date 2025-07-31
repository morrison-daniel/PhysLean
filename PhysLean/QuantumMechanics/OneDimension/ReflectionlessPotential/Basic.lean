/-
Copyright (c) 2025 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
import PhysLean.QuantumMechanics.OneDimension.Operators.Parity
import PhysLean.SpaceAndTime.Space.VectorIdentities
import PhysLean.SpaceAndTime.Time.Basic
import Mathlib.Data.Complex.Trigonometric
/-!

# 1d Reflectionless Potential

The quantum reflectionless potential in 1d.
This file contains
- the definition of the reflectionless potential as defined https://arxiv.org/pdf/2411.14941
- properties of reflectionless potentials

## TODO
- Define creation and annihilation operators for reflectionless potentials
- Write the proof of the general solution of the reflectionless potential using the creation and annihilation operators
- Show reflectionless properties
-/

namespace QuantumMechanics
open Real
open Space
namespace OneDimension


structure ReflectionlessPotential where
  /-- The potential function V(x) -/
  m : ℝ
  κ : ℝ
  ℏ : ℝ
  N : ℕ
  m_pos : 0 < m
  κ_pos : 0 < κ

namespace ReflectionlessPotential

variable (Q : ReflectionlessPotential)

/-!

## Theorems
TODO: Add theorems about reflectionless potential - the main result is the actual 1d solution
-/

noncomputable def reflectionlessPotential (x : ℝ) : ℝ :=
  -( (Q.ℏ^2 * Q.κ^2 * Q.N * (Q.N + 1)) / ((2 : ℝ) * Q.m * (Real.cosh (Q.κ * x)) ^ 2))

end ReflectionlessPotential
end OneDimension
end QuantumMechanics
