/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.ClassicalMechanics.VectorFields
import PhysLean.Electromagnetism.MaxwellEquations
/-!
# Electromagnetism in Homogeneous medium

Basic properties for homogeneous medium and free space.

Variables are bundled in structure, for unbundled version use
PhysLean.Electromagnetism.MaxwellEquations.

-/

namespace Electromagnetism

namespace Homogeneous
/-- Optical Medium has scalar electric permittivity as a function of space. -/
structure OpticalMedium extends EMSystem where
  /-- The electric permittivity of the material. -/
  ε : Space → ℝ

/-- Charged Medium is defined as Optical Medium with charge and current. -/
structure ChargedMedium extends OpticalMedium where
  /-- The charge density. -/
  ρ : ChargeDensity
  /-- The current density. -/
  J : CurrentDensity

open Space
open Time

/-- Gauss's law for the Electric field in homogeneous medium. -/
def GaussLawElectricHomogeneous (CM : ChargedMedium) (E : ElectricField) : Prop :=
  ∀ t : Time, ∀ x : Space, CM.ε₀ * (∇ ⬝ E t) x = CM.ρ t x

/-- Gauss's law for the Magnetic field in homogeneous medium. -/
def GaussLawMagneticHomogeneous (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ ⬝ B t) x = 0

/-- Ampère's law in homogeneous medium. -/
def AmpereLawHomogeneous (CM : ChargedMedium)
    (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ × B t) x =
  CM.μ₀ • (CM.J t x + CM.ε₀ • ∂ₜ (fun t => E t x) t)

/-- Faraday's law in homogeneous medium. -/
def FaradayLawHomogeneous (E : ElectricField) (B : MagneticField) : Prop :=
  ∀ t : Time, ∀ x : Space, (∇ × E t) x = - ∂ₜ (fun t => B t x) t

/-!
## Equivalence of bundled and unbundled versions of Maxwell's Equations.
-/
def ChargedMedium.𝓔 (CM : ChargedMedium) : EMSystem where
  μ₀ := CM.μ₀
  ε₀ := CM.ε₀

variable (CM : ChargedMedium)

lemma GaussLawElectricHomogeneousEquiv :
    GaussLawElectricHomogeneous CM = GaussLawElectric CM.𝓔 CM.ρ := by
  rfl

lemma GaussLawMagneticHomogeneousEquiv :
    GaussLawMagneticHomogeneous = GaussLawMagnetic := by
  rfl

lemma AmpereLawHomogeneousEquiv :
    AmpereLawHomogeneous CM = AmpereLaw CM.𝓔 CM.J := by
  rfl

lemma FaradayLawHomogeneousEquiv :
    FaradayLawHomogeneous = FaradayLaw := by
  rfl

/-!
## Maxwell's equations for optical medium
-/
/-- Optical medium defined as charge and current free charged medium. -/
def OpticalMedium.free (OM : OpticalMedium) : ChargedMedium where
  μ₀ := OM.μ₀
  ε₀ := OM.ε₀
  ε := OM.ε
  ρ := fun _ _ => 0
  J := fun _ _ => 0

variable (OM : OpticalMedium)

local notation "ε₀" => OM.free.ε₀
local notation "μ₀" => OM.free.μ₀

/-- Maxwell's equations for free space. -/
theorem GaussLawElectricFree (E : ElectricField)
    (h : GaussLawElectricHomogeneous OM.free E) :
    ε₀ * (∇ ⬝ E t) x = 0 := by
  rw [h]
  rfl

theorem GaussLawMagneticFree (B : MagneticField)
    (h : GaussLawMagneticHomogeneous B) :
    (∇ ⬝ B t) x = 0 := by
  rw [h]

theorem AmpereLawFree (E : ElectricField) (B : MagneticField)
    (h : AmpereLawHomogeneous OM.free E B) :
    (∇ × B t) x = μ₀ • ε₀ • ∂ₜ (fun t => E t x) t := by
  rw [h]
  simp only [smul_add, add_eq_right, smul_eq_zero]
  right
  rfl

theorem FaradayLawFree (E : ElectricField) (B : MagneticField)
    (h : FaradayLawHomogeneous E B) :
    (∇ × E t) x = - ∂ₜ (fun t => B t x) t := by
  rw [h]
