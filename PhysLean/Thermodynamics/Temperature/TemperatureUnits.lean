/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.Meta.TODO.Basic
/-!

# Units on Temperature

A unit of temperature corresponds to a choice of translationally-invariant
metric on the temperature manifold (to be defined diffeomorphic to `ℝ≥0`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `TemperatureUnit` to be equivalent to the
positive reals.

On `TemperatureUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of temperature unit.

To define specific temperature units, we first axiomise the existence of a
a given temperature unit, and then construct all other temperature units from it.
We choose to axiomise the
existence of the temperature unit of kelvin, and construct all other temperature units from that.

-/

open NNReal

/-- The choices of translationally-invariant metrics on the temperature-manifold.
  Such a choice corresponds to a choice of units for temperature. -/
structure TemperatureUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  prop : 0 < val

namespace TemperatureUnit

@[simp]
lemma val_ne_zero (x : TemperatureUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.prop)

lemma val_pos (x : TemperatureUnit) : 0 < x.val := x.prop

/-- The defualt unit of temperature. -/
def kelvin : TemperatureUnit := ⟨1, one_pos⟩

instance : Inhabited TemperatureUnit where
  default := kelvin

/-!

## Division of TemperatureUnit

-/

variable (x y : TemperatureUnit)

noncomputable instance : HDiv TemperatureUnit TemperatureUnit ℝ where
  hDiv x y := x.val / y.val

lemma div_eq_div_val : x / y = x.val / y.val := rfl

@[simp]
lemma div_ne_zero : x / y ≠ (0 : ℝ) := by
  rw [div_eq_div_val]
  simp

@[simp]
lemma div_self : x / x = (1 : ℝ) := by
  simp [div_eq_div_val, x.val_ne_zero]

lemma div_symm : x / y = (y / x)⁻¹ := by
  rw [div_eq_div_val, inv_eq_one_div, div_eq_div_val]
  simp

/-!

## The scaling of a temperature unit

-/

/-- The scaling of a temperature unit by a positive real. -/
def scale (r : ℝ) (x : TemperatureUnit) (hr : 0 < r := by norm_num) : TemperatureUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

@[simp]
lemma scale_div_self {r : ℝ} (hr : 0 < r) :
    scale r x hr / x = r := by
  simp [scale, div_eq_div_val]

@[simp]
lemma scale_one : scale 1 x = x := by
  simp [scale, mul_one]

@[simp]
lemma scale_div_scale {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    scale r x hr / scale s y hs = (r / s) * (x / y) := by
  simp [scale, div_eq_div_val]
  field_simp

@[simp]
lemma scale_scale {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : 0 < r * s) :
    scale r (scale s x hs) hr = scale (r * s) x hrs := by
  simp [scale]
  ring

/-!

## Specific choices of temperature units

To define a specific temperature units, we must first axiomise the existence of a
a given temperature unit, and then construct all other temperature units from it.
We choose to axiomise the existence of the temperature unit of kelvin.

We need an axiom since this relates something to something in the physical world.

-/

/-- The temperature unit of degrees nanokelvin (10^(-9) kelvin). -/
noncomputable def nanokelvin : TemperatureUnit := scale (1e-9) kelvin

/-- The temperature unit of degrees microkelvin (10^(-6) kelvin). -/
noncomputable def microkelvin : TemperatureUnit := scale (1e-6) kelvin

/-- The temperature unit of degrees millikelvin (10^(-3) kelvin). -/
noncomputable def millikelvin : TemperatureUnit := scale (1e-3) kelvin

/-- The temperature unit of degrees fahrenheit ((5/9) of a kelvin).
  Note, this is fahrenheit starting at `0` absolute temperature. -/
noncomputable def absoluteFahrenheit : TemperatureUnit := scale (5 / 9) kelvin

end TemperatureUnit
