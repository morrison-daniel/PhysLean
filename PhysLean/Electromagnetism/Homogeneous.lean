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

/-- Charged Medium is defined as Optical Medium with charge and current. -/
structure ChargedMedium extends OpticalMedium where
  /-- The charge density. -/
  ρ : ChargeDensity
  /-- The current density. -/
  J : CurrentDensity

open Space
open Time

variable (CM : ChargedMedium)

/-- Gauss's law for the Electric field in homogeneous medium. -/
abbrev ChargedMedium.GaussLawElectric (E : ElectricField) : Prop :=
  Electromagnetism.GaussLawElectric CM.toOpticalMedium CM.ρ E

/-- Gauss's law for the Magnetic field in homogeneous medium. -/
abbrev ChargedMedium.GaussLawMagnetic (CM : ChargedMedium)
    (B : MagneticField) : Prop :=
  Electromagnetism.GaussLawMagnetic B

/-- Ampère's law in homogeneous medium. -/
abbrev ChargedMedium.AmpereLaw (CM : ChargedMedium)
    (E : ElectricField) (B : MagneticField) : Prop :=
  Electromagnetism.AmpereLaw CM.toOpticalMedium CM.J E B

/-- Faraday's law in homogeneous medium. -/
abbrev ChargedMedium.FaradayLaw (CM : ChargedMedium)
    (E : ElectricField) (B : MagneticField) : Prop :=
  Electromagnetism.FaradayLaw E B

/-!
## Maxwell's equations for charge and current free medium
-/
/-- Optical medium defined as charge and current free charged medium. -/
def OpticalMedium.free (OM : OpticalMedium) : ChargedMedium where
  μ := OM.μ
  ε := OM.ε
  ρ := fun _ _ => 0
  J := fun _ _ => 0

variable (OM : OpticalMedium)

local notation "ε" => OM.free.ε
local notation "μ" => OM.free.μ

/-- Maxwell's equations for free space. -/
theorem ChargedMedium.gaussLawElectric_of_free (E : ElectricField)
    (h : OM.free.GaussLawElectric E) :
    ε x * (∇ ⬝ E t) x = 0 := by
  rw [h]
  rfl

theorem ChargedMedium.gaussLawMagnetic_of_free (B : MagneticField)
    (h : OM.free.GaussLawMagnetic B) :
    (∇ ⬝ B t) x = 0 := by
  rw [h]

theorem ChargedMedium.ampereLaw_of_free (E : ElectricField) (B : MagneticField)
    (h : OM.free.AmpereLaw E B) :
    (∇ × B t) x = μ x • ε x • ∂ₜ (fun t => E t x) t := by
  rw [h]
  simp only [smul_add, add_eq_right, smul_eq_zero]
  right
  rfl

theorem ChargedMedium.faradayLaw_of_free (E : ElectricField) (B : MagneticField)
    (h : OM.free.FaradayLaw E B) :
    (∇ × E t) x = - ∂ₜ (fun t => B t x) t := by
  rw [h]

def IsFree (OM : OpticalMedium) (E : ElectricField) (B : MagneticField) : Prop :=
    OM.free.GaussLawElectric E ∧ OM.free.GaussLawMagnetic B ∧
    OM.free.AmpereLaw E B ∧ OM.free.FaradayLaw E B
