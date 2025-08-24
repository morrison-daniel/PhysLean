/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.Meta.TODO.Basic
/-!

# Units on Length

A unit of length corresponds to a choice of translationally-invariant
metric on the space manifold (to be defined). Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `LengthUnit` to be equivalent to the
positive reals.

On `LengthUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of length unit.

To define specific length units, we first axiomise the existence of a
a given length unit, and then construct all other length units from it. We choose to axiomise the
existence of the length unit of meters, and construct all other length units from that.

-/

/-- The choices of translationally-invariant metrics on the space-manifold.
  Such a choice corresponds to a choice of units for length. -/
structure LengthUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  prop : 0 < val

namespace LengthUnit

@[simp]
lemma val_ne_zero (x : LengthUnit) : x.val ≠ 0 := by
  exact (ne_of_lt x.prop).symm

lemma val_pos (x : LengthUnit) : 0 < x.val := x.prop

/-- Seconds are defined as the unit of scale 1. -/
def meters : LengthUnit := ⟨1, one_pos⟩

instance : Inhabited LengthUnit where
  default := meters

/-!
## Division of LengthUnit
-/

noncomputable instance : HDiv LengthUnit LengthUnit ℝ where
  hDiv x y := x.val / y.val

variable (x y : LengthUnit)

lemma div_eq_div_val : x / y = x.val / y.val := rfl

@[simp]
lemma div_neq_zero : x / y ≠ 0 := by
  simp [div_eq_div_val]

@[simp]
lemma div_self : x / x = (1 : ℝ) := by
  simp [div_eq_div_val]

lemma div_inv_eq_div : (x / y)⁻¹ = y / x := by
  rw [inv_eq_one_div, div_eq_div_val, div_eq_div_val]
  simp

/-!
## The scaling of a time unit
-/

/-- The scaling of a time unit by a positive real. -/
def scale (r : ℝ) (x : LengthUnit) (hr : 0 < r := by norm_num) : LengthUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

lemma scale_mul {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : 0 < r*s) :
    scale (r * s) x hrs = scale r (scale s x hs) hr := by
  simp [scale, mul_assoc]

@[simp]
lemma val_scale {r : ℝ} (hr : 0 < r := by norm_num) : (scale r x hr).val = r * x.val := rfl

@[simp]
lemma scale_div_self {r : ℝ} (hr : 0 < r) : (scale r x hr) / x = r := by
  simp [scale, div_eq_div_val]

@[simp]
lemma scale_one : scale 1 x = x := by
  simp [scale, mul_one]

@[simp]
lemma scale_div_scale {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    scale r x hr / scale s y hs = (r / s) * (x / y) := by
  simp [scale, div_eq_div_val]
  field_simp

/-!

## Specific choices of Length units

To define a specific length units, we must first axiomise the existence of a
a given length unit, and then construct all other length units from it.
We choose to axiomise the existence of the length unit of meters.

We need an axiom since this relates something to something in the physical world.

-/

/-- The length unit of femtometers (10⁻¹⁵ of a meter). -/
noncomputable def femtometers : LengthUnit := scale ((1/10) ^ (15)) meters

/-- The length unit of picometers (10⁻¹² of a meter). -/
noncomputable def picometers : LengthUnit := scale ((1/10) ^ (12)) meters

/-- The length unit of nanometers (10⁻⁹ of a meter). -/
noncomputable def nanometers : LengthUnit := scale ((1/10) ^ (9)) meters

/-- The length unit of micrometers (10⁻⁶ of a meter). -/
noncomputable def micrometers : LengthUnit := scale ((1/10) ^ (6)) meters

/-- The length unit of millimeters (10⁻³ of a meter). -/
noncomputable def millimeters : LengthUnit := scale ((1/10) ^ (3)) meters

/-- The length unit of centimeters (10⁻² of a meter). -/
noncomputable def centimeters : LengthUnit := scale ((1/10) ^ (2)) meters

/-- The length unit of inch (0.0254 meters). -/
noncomputable def inches : LengthUnit := scale (0.0254) meters

/-- The length unit of link (0.201168 meters). -/
noncomputable def links : LengthUnit := scale (0.201168) meters

/-- The length unit of feet (0.3048 meters) -/
noncomputable def feet : LengthUnit := scale (0.3048) meters

/-- The length unit of a yard (0.9144 meters) -/
noncomputable def yards : LengthUnit := scale (0.9144) meters

/-- The length unit of a rod (5.0292 meters) -/
noncomputable def rods : LengthUnit := scale (5.0292) meters

/-- The length unit of a chain (20.1168 meters) -/
noncomputable def chains : LengthUnit := scale (20.1168) meters

/-- The length unit of a furlong (201.168 meters) -/
noncomputable def furlongs : LengthUnit := scale (201.168) meters

/-- The length unit of kilometers (10³ meters). -/
noncomputable def kilometers : LengthUnit := scale ((10) ^ (3)) meters

/-- The length unit of a mile (1609.344 meters). -/
noncomputable def miles : LengthUnit := scale (1609.344) meters

/-- The length unit of a nautical mile (1852 meters). -/
noncomputable def nauticalMiles : LengthUnit := scale (1852) meters

/-- The length unit of an astronomical unit (149,597,870,700 meters). -/
noncomputable def astronomicalUnits : LengthUnit := scale (149597870700) meters

/-- The length unit of a light year (9,460,730,472,580,800 meters). -/
noncomputable def lightYears : LengthUnit := scale (9460730472580800) meters

/-- The length unit of a parsec (648,000/π astronomicalUnits). -/
noncomputable def parsecs : LengthUnit := scale (648000/Real.pi) astronomicalUnits
  (by norm_num; exact Real.pi_pos)

TODO "ITXJV" "For each unit of charge give the reference the literature where it's definition
  is defined."

/-!

## Relations between length units

-/

/-- There are exactly 1760 yards in a mile. -/
lemma miles_div_yards : miles / yards = (1760 : ℝ) := by simp [miles, yards]; norm_num

/-- There are exactly 220 yards in a furlong. -/
lemma furlongs_div_yards : furlongs / yards = (220 : ℝ) := by simp [furlongs, yards]; norm_num

end LengthUnit
