/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Electromagnetism.Basic
import PhysLean.Relativity.SpaceTime.Basic
/-!

# Maxwell's equations

-/

namespace Electromagnetism

/-- An electromagnetic system consists of charge density, a current density,
  the speed ofl light and the electric permittivity. -/
structure EMSystem where
  /-- The charge density. -/
  ρ : SpaceTime → ℝ
  /-- The current density. -/
  J : SpaceTime → EuclideanSpace ℝ (Fin 3)
  /-- The speed of light. -/
  c : ℝ
  /-- The permittivity. -/
  ε₀ : ℝ

namespace EMSystem
variable (𝓔 : EMSystem)
open SpaceTime

/-- The permeability. -/
noncomputable def μ₀ : ℝ := 1/(𝓔.c^2 * 𝓔.ε₀)

/-- Coulomb's constant. -/
noncomputable def coulombConstant : ℝ := 1/(4 * Real.pi * 𝓔.ε₀)

local notation "ε₀" => 𝓔.ε₀
local notation "μ₀" => 𝓔.μ₀
local notation "J" => 𝓔.J
local notation "ρ" => 𝓔.ρ

/-- Gauss's law for the Electric field. -/
def GaussLawElectric (E : ElectricField) : Prop :=
  ∀ x : SpaceTime, ε₀ * (∇⬝ E) x = ρ x

/-- Gauss's law for the Magnetic field. -/
def GaussLawMagnetic (B : MagneticField) : Prop :=
  ∀ x : SpaceTime, (∇⬝ B) x = 0

/-- Ampère's law. -/
def AmpereLaw (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ x : SpaceTime, ∇× B x = μ₀ • (J x + ε₀ • ∂ₜ E x)

/-- Faraday's law. -/
def FaradayLaw (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ x : SpaceTime, ∇× E x = - ∂ₜ B x

/-- Maxwell's equations. -/
def MaxwellEquations (E : ElectricField) (B : MagneticField) : Prop :=
  𝓔.GaussLawElectric E ∧ GaussLawMagnetic B ∧
  FaradayLaw E B ∧ 𝓔.AmpereLaw E B

end EMSystem
end Electromagnetism
