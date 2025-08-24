/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.Meta.TODO.Basic
/-!

# Units on Mass

A unit of mass corresponds to a choice of translationally-invariant
metric on the mass manifold (to be defined diffeomorphic to `ℝ≥0`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `MassUnit` to be equivalent to the
positive reals.

On `MassUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of mass unit.

To define specific mass units, we first axiomise the existence of a
a given mass unit, and then construct all other mass units from it. We choose to axiomise the
existence of the mass unit of kilograms, and construct all other mass units from that.

-/

/-- The choices of translationally-invariant metrics on the mass-manifold.
  Such a choice corresponds to a choice of units for mass. -/
structure MassUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  prop : 0 < val

namespace MassUnit

@[simp]
lemma val_neq_zero (x : MassUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.prop)

lemma val_pos (x : MassUnit) : 0 < x.val := x.prop

/-- The default mass unit. -/
def kilograms : MassUnit := ⟨1, one_pos⟩

instance : Inhabited MassUnit where
  default := kilograms

/-!

## Division of MassUnit

-/

variable (x y : MassUnit)

noncomputable instance : HDiv MassUnit MassUnit ℝ where
  hDiv x y := x.val / y.val

lemma div_eq_div_val : x / y = x.val / y.val := rfl

@[simp]
lemma div_neq_zero : x / y ≠ 0 := by
  simp [div_eq_div_val]

@[simp]
lemma div_self : x / x = (1 : ℝ) := by
  simp [div_eq_div_val, x.val_neq_zero]

lemma div_symm : x / y = (y / x)⁻¹ := by
  rw [div_eq_div_val, inv_eq_one_div, div_eq_div_val]
  simp

/-!

## The scaling of a mass unit

-/

/-- The scaling of a mass unit by a positive real. -/
def scale (r : ℝ) (x : MassUnit) (hr : 0 < r := by norm_num) : MassUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

@[simp]
lemma scale_div_self (r : ℝ) (hr : 0 < r) :
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

## Specific choices of mass units

To define a specific mass units, we must first axiomise the existence of a
a given mass unit, and then construct all other mass units from it.
We choose to axiomise the existence of the mass unit of kilograms.

We need an axiom since this relates something to something in the physical world.

-/

/-- The mass unit of a microgram (10^(-9) of a kilogram). -/
noncomputable def micrograms : MassUnit := scale ((1/10) ^ 9) kilograms

/-- The mass unit of milligram (10^(-6) of a kilogram). -/
noncomputable def milligrams : MassUnit := scale ((1/10) ^ 6) kilograms

/-- The mass unit of grams (10^(-3) of a kilogram). -/
noncomputable def grams : MassUnit := scale ((1/10) ^ 3) kilograms

/-- The mass unit of (avoirdupois) ounces (0.028 349 523 125 of a kilogram). -/
noncomputable def ounces : MassUnit := scale (0.028349523125) kilograms

/-- The mass unit of (avoirdupois) pounds (0.453 592 37 of a kilogram). -/
noncomputable def pounds : MassUnit := scale (0.45359237) kilograms

/-- The mass unit of stones (14 pounds). -/
noncomputable def stones : MassUnit := scale (14) pounds

/-- The mass unit of a quarter (28 pounds). -/
noncomputable def quarters : MassUnit := scale (28) pounds

/-- The mass unit of hundredweights (112 pounds). -/
noncomputable def hundredweights : MassUnit := scale (112) pounds

/-- The mass unit of short tons (2000 pounds). -/
noncomputable def shortTons : MassUnit := scale (2000) pounds

/-- The mass unit of metric tons (1000 kilograms). -/
noncomputable def metricTons : MassUnit := scale (1000) kilograms

/-- The mass unit of long tons (2240 pounds). Also called shortweight tons. -/
noncomputable def longTons : MassUnit := scale (2240) pounds

/-- The mass unit of nominal solar masses (1.988416 × 10 ^ 30 kilograms).
  See: https://iopscience.iop.org/article/10.3847/0004-6256/152/2/41 -/
noncomputable def nominalSolarMasses : MassUnit := scale (1.988416e30) kilograms

/-!

## Relations between mass units

-/

lemma pounds_div_ounces : pounds / ounces = (16 : ℝ) := by
  simp [pounds, ounces]; norm_num

lemma shortTons_div_kilograms : shortTons / kilograms = (907.18474 : ℝ) := by
  simp [shortTons, kilograms, pounds]; norm_num

lemma longTons_div_kilograms : longTons / kilograms = (1016.0469088 : ℝ) := by
  simp [longTons, kilograms, pounds]; norm_num

end MassUnit
