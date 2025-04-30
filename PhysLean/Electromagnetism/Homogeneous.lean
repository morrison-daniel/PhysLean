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
abbrev ChargedMedium.GaussLawMagnetic
    (B : MagneticField) : Prop :=
  Electromagnetism.GaussLawMagnetic B

/-- Ampère's law in homogeneous medium. -/
abbrev ChargedMedium.AmpereLaw (CM : ChargedMedium)
    (E : ElectricField) (B : MagneticField) : Prop :=
  Electromagnetism.AmpereLaw CM.toOpticalMedium CM.J E B

/-- Faraday's law in homogeneous medium. -/
abbrev ChargedMedium.FaradayLaw
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

local notation "ε" => OM.ε
local notation "μ" => OM.μ

/-- An optical medium which is charge and current free. -/
def IsFree (OM : OpticalMedium)
    (E : ElectricField) (B : MagneticField) : Prop :=
    OM.free.ρ = 0 ∧ OM.free.J = 0 ∧
    MaxwellEquations OM OM.free.ρ OM.free.J E B

/-- Maxwell's equations for charge and current free medium. -/
theorem OpticalMedium.gaussLawElectric_of_free (E : ElectricField) (B : MagneticField)
    (h : IsFree OM E B) :
    ε * (∇ ⬝ E t) x = 0 := by
  have h' := h.2.2.1
  unfold GaussLawElectric at h'
  rw [h.1] at h'
  simp_all

theorem OpticalMedium.gaussLawMagnetic_of_isfree (E : ElectricField) (B : MagneticField)
    (h : IsFree OM E B) :
    (∇ ⬝ B t) x = 0 := by
  have h' := h.2.2.2.1
  unfold GaussLawMagnetic at h'
  rw [h']

theorem OpticalMedium.ampereLaw_of_isfree (E : ElectricField) (B : MagneticField)
    (h : IsFree OM E B) :
    (∇ × B t) x = μ • ε • ∂ₜ (fun t => E t x) t := by
  have h' := h.2.2.2.2.1
  unfold AmpereLaw at h'
  rw [h.2.1] at h'
  simp_all

theorem OpticalMedium.faradayLaw_of_isfree (E : ElectricField) (B : MagneticField)
    (h : IsFree OM E B) :
    (∇ × E t) x = - ∂ₜ (fun t => B t x) t := by
  have h' := h.2.2.2.2.2
  unfold FaradayLaw at h'
  rw [h']
