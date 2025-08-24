/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import PhysLean.SpaceAndTime.Time.Basic

/-!
# Units on time
-/

/-- The choices of translationally-invariant metrics on the manifold `TimeTransMan`.
  Such a choice corresponds to a choice of units for time. -/
structure TimeUnit : Type where
  /-- The underlying scale of the unit. -/
  val : ℝ
  /-- The timescale must be positive. -/
  prop : 0 < val

namespace TimeUnit

@[simp]
lemma val_ne_zero (x : TimeUnit) : x.val ≠ 0 := by
  exact (ne_of_lt x.prop).symm

lemma val_pos (x : TimeUnit) : 0 < x.val := x.prop

/-- Seconds are defined as the unit of scale 1. -/
def seconds : TimeUnit := ⟨1, one_pos⟩

instance : Inhabited TimeUnit where
  default := seconds

/-!
## Division of TimeUnit
-/

noncomputable instance : HDiv TimeUnit TimeUnit ℝ where
  hDiv x y := x.val / y.val

variable (x y : TimeUnit)

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
def scale (r : ℝ) (x : TimeUnit) (hr : 0 < r := by norm_num) : TimeUnit :=
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
## Assigning units to `Time`
-/

variable (t : Time) (u : TimeUnit)

instance : HSMul Time TimeUnit ℝ where
  hSMul t u := t.val * u.val

theorem smul_eq : t • u = t.val * u.val := rfl

@[simp]
lemma smul_time_eq (r : ℝ) : (r • t) • u = r * (t • u) := by
  simp [smul_eq, mul_assoc]

@[simp]
lemma smul_scale_eq {r : ℝ} (hr : 0 < r) : t • (scale r u hr) = r * (t • u) := by
  simp [smul_eq]
  ring

/-!
## Specific choices of time units

To define a specific time units, we must first axiomise the existence of a
a given time unit, and then construct all other time units from it.
We choose to axiomise the existence of the time unit of seconds.

We need an axiom since this relates something to something in the physical world.
-/

/-- The time unit of femtoseconds (10⁻¹⁵ of a second). -/
noncomputable def femtoseconds : TimeUnit := scale ((1/10) ^ (15)) seconds

/-- The time unit of picoseconds (10⁻¹² of a second). -/
noncomputable def picoseconds : TimeUnit := scale ((1/10) ^ (12)) seconds

/-- The time unit of nanoseconds (10⁻⁹ of a second). -/
noncomputable def nanoseconds : TimeUnit := scale ((1/10) ^ (9)) seconds

/-- The time unit of microseconds (10⁻⁶ of a second). -/
noncomputable def microseconds : TimeUnit := scale ((1/10) ^ (6)) seconds

/-- The time unit of milliseconds (10⁻³ of a second). -/
noncomputable def milliseconds : TimeUnit := scale ((1/10) ^ (3)) seconds

/-- The time unit of centiseconds (10⁻² of a second). -/
noncomputable def centiseconds : TimeUnit := scale ((1/10) ^ (2)) seconds

/-- The time unit of deciseconds (10⁻¹ of a second). -/
noncomputable def deciseconds : TimeUnit := scale ((1/10) ^ (1)) seconds

/-- The time unit of minutes. -/
noncomputable def minutes : TimeUnit := scale 60 seconds

/-- The time unit of hours. -/
noncomputable def hours : TimeUnit := scale (60 * 60) seconds

/-- The time unit of 24 hour days. -/
noncomputable def days : TimeUnit := scale (24 * 60 * 60) seconds

/-- The time unit of 7 day weeks. -/
noncomputable def weeks : TimeUnit := scale (7 * 24 * 60 * 60) seconds

/-!
## Relations between time units
-/

lemma minutes_div_seconds : minutes / seconds = (60 : ℝ) := by
  simp [minutes]

lemma hours_div_seconds : hours / seconds = (3600 : ℝ) := by
  simp [hours]; norm_num

lemma days_div_seconds : days / seconds = (86400 : ℝ) := by
  simp [days]; norm_num

lemma weeks_div_seconds : weeks / seconds = (604800 : ℝ) := by
  simp [weeks]; norm_num

lemma days_div_minutes : days / minutes = (1440 : ℝ) := by
  simp [days, minutes]; norm_num

lemma weeks_div_minutes : weeks / minutes = (10080 : ℝ) := by
  simp [weeks, minutes]; norm_num

lemma days_div_hours : days / hours = (24 : ℝ) := by
  simp [hours, days]; norm_num

lemma weeks_div_hours : weeks / hours = (168 : ℝ) := by
  simp [weeks, hours]; norm_num

end TimeUnit
