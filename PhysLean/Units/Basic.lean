/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Time.TimeUnit
import PhysLean.SpaceAndTime.Space.LengthUnit
import PhysLean.ClassicalMechanics.Mass.MassUnit
import PhysLean.Electromagnetism.Charge.ChargeUnit
import PhysLean.Thermodynamics.Temperature.TemperatureUnits
/-!

# Dimensions and unit

A unit in physics arises from choice of something in physics which is non-canonical.
An example is the choice of translationally-invariant metric on the time manifold `TimeMan`.

A dimension is a property of a quantity related to how it changes with respect to a
change in the unit.

The fundamental choices one has in physics are related to:
- Time
- Length
- Mass
- Charge
- Temperature

(In fact temperature is not really a fundamental choice, however we leave this as a `TODO`.)

From these fundamental choices one can construct all other units and dimensions.

## Implementation details

Units within PhysLean are implemented with the following convention:
- The fundamental units, and the choices they correspond to, are defined within the
  appropriate physics directory, in particular:
  - `PhysLean/SpaceAndTime/Time/TimeUnit.lean`
  - `PhysLean/SpaceAndTime/Space/LengthUnit.lean`
  - `PhysLean/ClassicalMechanics/Mass/MassUnit.lean`
  - `PhysLean/Electromagnetism/Charge/ChargeUnit.lean`
  - `PhysLean/Thermodynamics/Temperature/TemperatureUnit.lean`
- In this `Units` directory, we define the necessary structures and properties
  to work derived units and dimensions.

## References

Zulip chats discussing units:
- https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units
- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Dimensional.20Analysis.20Revisited/with/530238303

## Note

A lot of the results around units is still experimental and should be adapted based on needs.

-/

open NNReal

/-!

## Defining dimensions

-/

/-- The foundational dimensions.
  Defined in the order ⟨length, time, mass, charge, temperature⟩ -/
structure Dimension where
  /-- The length dimension. -/
  length : ℚ
  /-- The time dimension. -/
  time : ℚ
  /-- The mass dimension. -/
  mass : ℚ
  /-- The charge dimension. -/
  charge : ℚ
  /-- The temperature dimension. -/
  temperature : ℚ

namespace Dimension

instance : Zero Dimension where
  zero := ⟨0, 0, 0, 0, 0⟩

lemma zero_eq : (0 : Dimension) = ⟨0, 0, 0, 0, 0⟩ := rfl

instance : Mul Dimension where
  mul d1 d2 := ⟨d1.length + d2.length,
    d1.time + d2.time,
    d1.mass + d2.mass,
    d1.charge + d2.charge,
    d1.temperature + d2.temperature⟩

@[simp]
lemma time_mul (d1 d2 : Dimension) :
    (d1 * d2).time = d1.time + d2.time := rfl

@[simp]
lemma length_mul (d1 d2 : Dimension) :
    (d1 * d2).length = d1.length + d2.length := rfl

@[simp]
lemma mass_mul (d1 d2 : Dimension) :
    (d1 * d2).mass = d1.mass + d2.mass := rfl

@[simp]
lemma charge_mul (d1 d2 : Dimension) :
    (d1 * d2).charge = d1.charge + d2.charge := rfl

@[simp]
lemma temperature_mul (d1 d2 : Dimension) :
    (d1 * d2).temperature = d1.temperature + d2.temperature := rfl

instance : Div Dimension where
  div d1 d2 := ⟨d1.length - d2.length,
    d1.time - d2.time,
    d1.mass - d2.mass,
    d1.charge - d2.charge,
    d1.temperature - d2.temperature⟩

@[simp]
lemma time_div (d1 d2 : Dimension) :
    (d1 / d2).time = d1.time - d2.time := rfl

@[simp]
lemma length_div (d1 d2 : Dimension) :
    (d1 / d2).length = d1.length - d2.length := rfl

@[simp]
lemma mass_div (d1 d2 : Dimension) :
    (d1 / d2).mass = d1.mass - d2.mass := rfl

@[simp]
lemma charge_div (d1 d2 : Dimension) :
    (d1 / d2).charge = d1.charge - d2.charge := rfl

@[simp]
lemma temperature_div (d1 d2 : Dimension) :
    (d1 / d2).temperature = d1.temperature - d2.temperature := rfl

instance : Inv Dimension where
  inv d := ⟨-d.length, -d.time, -d.mass, -d.charge, -d.temperature⟩

@[simp]
lemma inv_length (d : Dimension) : d⁻¹.length = -d.length := rfl

@[simp]
lemma inv_time (d : Dimension) : d⁻¹.time = -d.time := rfl

@[simp]
lemma inv_mass (d : Dimension) : d⁻¹.mass = -d.mass := rfl

@[simp]
lemma inv_charge (d : Dimension) : d⁻¹.charge = -d.charge := rfl

@[simp]
lemma inv_temperature (d : Dimension) : d⁻¹.temperature = -d.temperature := rfl

instance : Pow Dimension ℚ where
  pow d n := ⟨d.length * n, d.time * n, d.mass * n, d.charge * n, d.temperature * n⟩

/-- The dimension corresponding to length. -/
def L𝓭 : Dimension := ⟨1, 0, 0, 0, 0⟩

@[simp]
lemma L𝓭_length : L𝓭.length = 1 := by rfl

@[simp]
lemma L𝓭_time : L𝓭.time = 0 := by rfl

@[simp]
lemma L𝓭_mass : L𝓭.mass = 0 := by rfl

@[simp]
lemma L𝓭_charge : L𝓭.charge = 0 := by rfl

@[simp]
lemma L𝓭_temperature : L𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to time. -/
def T𝓭 : Dimension := ⟨0, 1, 0, 0, 0⟩

@[simp]
lemma T𝓭_length : T𝓭.length = 0 := by rfl

@[simp]
lemma T𝓭_time : T𝓭.time = 1 := by rfl

@[simp]
lemma T𝓭_mass : T𝓭.mass = 0 := by rfl

@[simp]
lemma T𝓭_charge : T𝓭.charge = 0 := by rfl

@[simp]
lemma T𝓭_temperature : T𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to mass. -/
def M𝓭 : Dimension := ⟨0, 0, 1, 0, 0⟩

@[simp]
lemma M𝓭_length : M𝓭.length = 0 := by rfl

@[simp]
lemma M𝓭_time : M𝓭.time = 0 := by rfl

@[simp]
lemma M𝓭_mass : M𝓭.mass = 1 := by rfl

@[simp]
lemma M𝓭_charge : M𝓭.charge = 0 := by rfl

@[simp]
lemma M𝓭_temperature : M𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to charge. -/
def C𝓭 : Dimension := ⟨0, 0, 0, 1, 0⟩

@[simp]
lemma C𝓭_length : C𝓭.length = 0 := by rfl

@[simp]
lemma C𝓭_time : C𝓭.time = 0 := by rfl

@[simp]
lemma C𝓭_mass : C𝓭.mass = 0 := by rfl

@[simp]
lemma C𝓭_charge : C𝓭.charge = 1 := by rfl

@[simp]
lemma C𝓭_temperature : C𝓭.temperature = 0 := by rfl

/-- The dimension corresponding to temperature. -/
def Θ𝓭 : Dimension := ⟨0, 0, 0, 0, 1⟩

@[simp]
lemma Θ𝓭_length : Θ𝓭.length = 0 := by rfl

@[simp]
lemma Θ𝓭_time : Θ𝓭.time = 0 := by rfl

@[simp]
lemma Θ𝓭_mass : Θ𝓭.mass = 0 := by rfl

@[simp]
lemma Θ𝓭_charge : Θ𝓭.charge = 0 := by rfl

@[simp]
lemma Θ𝓭_temperature : Θ𝓭.temperature = 1 := by rfl

end Dimension

/-!

## Units

-/

/-- The choice of units. -/
structure UnitChoices where
  /-- The length unit. -/
  length : LengthUnit
  /-- The time unit. -/
  time : TimeUnit
  /-- The mass unit. -/
  mass : MassUnit
  /-- The charge unit. -/
  charge : ChargeUnit
  /-- The temperature unit. -/
  temperature : TemperatureUnit

namespace UnitChoices

/-- Given two choices of units `u1` and `u2` and a dimension `d`, the
  element of `ℝ≥0` corresponding to the scaling (by definition) of a quantity of dimension `d`
  when changing from units `u1` to `u2`. -/
noncomputable def dimScale (u1 u2 : UnitChoices) (d : Dimension) : ℝ :=
  (u1.length / u2.length) ^ (d.length : ℝ) *
  (u1.time / u2.time) ^ (d.time : ℝ) *
  (u1.mass / u2.mass) ^ (d.mass : ℝ) *
  (u1.charge / u2.charge) ^ (d.charge : ℝ) *
  (u1.temperature / u2.temperature) ^ (d.temperature : ℝ)

lemma dimScale_pos (u1 u2 : UnitChoices) (d : Dimension) : 0 < dimScale u1 u2 d := by
  simp [dimScale]
  apply mul_pos; apply mul_pos; apply mul_pos; apply mul_pos
  apply Real.rpow_pos_of_pos; apply div_pos <;> exact LengthUnit.val_pos _
  apply Real.rpow_pos_of_pos; apply div_pos <;> exact TimeUnit.val_pos _
  apply Real.rpow_pos_of_pos; apply div_pos <;> exact MassUnit.val_pos _
  apply Real.rpow_pos_of_pos; apply div_pos <;> exact ChargeUnit.val_pos _
  apply Real.rpow_pos_of_pos; apply div_pos <;> exact TemperatureUnit.val_pos _

@[simp]
lemma dimScale_self (u : UnitChoices) (d : Dimension) :
    dimScale u u d = 1 := by
  simp [dimScale]

@[simp]
lemma dimScale_zero (u1 u2 : UnitChoices) :
    dimScale u1 u2 0 = 1 := by
  simp [dimScale, Dimension.zero_eq]

lemma dimScale_transitive (u1 u2 u3 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d * dimScale u2 u3 d = dimScale u1 u3 d := by
  sorry

@[simp]
lemma dimScale_mul (u1 u2 : UnitChoices) (d1 d2 : Dimension) :
    dimScale u1 u2 (d1 * d2) = dimScale u1 u2 d1 * dimScale u1 u2 d2 := by
  sorry

@[simp]
lemma dimScale_ne_zero (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d ≠ 0 := by
  apply ne_of_gt
  exact dimScale_pos u1 u2 d

lemma dimScale_inv (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d⁻¹ = (dimScale u1 u2 d)⁻¹ := by
  sorry

lemma dimScale_symm (u1 u2 : UnitChoices) (d : Dimension) :
    dimScale u1 u2 d = (dimScale u2 u1 d)⁻¹ := by
  sorry

/-- The choice of units corresponding to SI units, that is
- meters,
- seconds,
- kilograms,
- columbs,
- kelvin.
-/
noncomputable def SI : UnitChoices where
  length := LengthUnit.meters
  time := TimeUnit.seconds
  mass := MassUnit.kilograms
  charge := ChargeUnit.coulombs
  temperature := TemperatureUnit.kelvin

@[simp]
lemma SI_length : SI.length = LengthUnit.meters := rfl

@[simp]
lemma SI_time : SI.time = TimeUnit.seconds := rfl

@[simp]
lemma SI_mass : SI.mass = MassUnit.kilograms := rfl

@[simp]
lemma SI_charge : SI.charge = ChargeUnit.coulombs := rfl

@[simp]
lemma SI_temperature : SI.temperature = TemperatureUnit.kelvin := rfl

end UnitChoices

/-!

## Dimensionful

Given a type `M` with a dimension `d`, a dimensionful quantity is a
map from `UnitChoices` to `M`, which scales with the choice of unit according to `d`.

See: https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units/near/530520545

-/

/-- A quantity of type `M` which depends on a choice of units `UnitChoices` is said to be
  of dimension `d` if it scales by `UnitChoices.dimScale u1 u2 d` under a change in units. -/
def HasDimension (d : Dimension) {M : Type} [SMul ℝ M] (f : UnitChoices → M) : Prop :=
  ∀ u1 u2 : UnitChoices, f u2 = UnitChoices.dimScale u1 u2 d • f u1

lemma hasDimension_iff {d : Dimension} {M : Type} [SMul ℝ M]
    (f : UnitChoices → M) :
    HasDimension d f ↔ ∀ u1 u2 : UnitChoices, f u2 = UnitChoices.dimScale u1 u2 d • f u1 := by
  rfl

/-- The type of maps from `UnitChoices` to `M` which have dimension `d`. -/
def Dimensionful (d : Dimension) (M : Type) [SMul ℝ M] :=
  {f : UnitChoices → M // HasDimension d f}

namespace Dimensionful

/-- Applying an element of `Dimensionful d M` to a unit choice gives an element of `M`. -/
instance {d : Dimension} {M : Type} [SMul ℝ M] :
    CoeFun (Dimensionful d M) (fun _ => UnitChoices → M) where
  coe f := f.1

lemma coe_hasDimension {d : Dimension} {M : Type} [SMul ℝ M]
    (f : Dimensionful d M) :
    HasDimension d (f : UnitChoices → M) := by
  intro u1 u2
  rw [f.2 u1 u2]
