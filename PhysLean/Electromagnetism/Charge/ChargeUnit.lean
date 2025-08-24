/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.RCLike.Basic
import PhysLean.Meta.TODO.Basic
/-!

# The units of charge

A unit of charge correspondings to a choice of translationally-invariant
metric on the charge manifold (to be defined diffeomorphic to `ℝ`).
Such a choice is (non-canonically) equivalent to a
choice of positive real number. We define the type `ChargeUnit` to be equivalent to the
positive reals.

We assume that the charge manifold is already defined with an orientation, with the
electron being in the negative direction.

On `ChargeUnit` there is an instance of division giving a real number, corresponding to the
ratio of the two scales of temperature unit.

To define specific charge units, we first axiomise the existence of a
a given charge unit, and then construct all other charge units from it.
We choose to axiomise the
existence of the charge unit of the coulomb, and construct all other charge units from that.

-/

/-- The choices of translationally-invariant metrics on the charge-manifold.
  Such a choice corresponds to a choice of units for charge.
  This assumes that an orientation has already being picked on the charge manifold. -/
structure ChargeUnit where
  /-- The underlying scale of the unit. -/
  val : ℝ
  prop : 0 < val

namespace ChargeUnit

@[simp]
lemma val_ne_zero (x : ChargeUnit) : x.val ≠ 0 := by
  exact Ne.symm (ne_of_lt x.prop)

lemma val_pos (x : ChargeUnit) : 0 < x.val := x.prop

def coulombs : ChargeUnit := ⟨1, one_pos⟩

instance : Inhabited ChargeUnit where
  default := coulombs

/-!

## Division of ChargeUnit

-/

variable (x y : ChargeUnit)

noncomputable instance : HDiv ChargeUnit ChargeUnit ℝ where
  hDiv x y := x.val / y.val

lemma div_eq_div_val : x / y = x.val / y.val := rfl

@[simp]
lemma div_ne_zero : x / y ≠ 0 := by
  rw [div_eq_div_val]
  simp

@[simp]
lemma div_self : x / x = (1 : ℝ) := by
  simp [div_eq_div_val, x.val_ne_zero]

lemma div_symm :  x / y = (y / x)⁻¹ := by
  rw [div_eq_div_val, inv_eq_one_div, div_eq_div_val]
  simp

/-!

## The scaling of a charge unit

-/

/-- The scaling of a charge unit by a positive real. -/
def scale (r : ℝ) (x : ChargeUnit) (hr : 0 < r := by norm_num) : ChargeUnit :=
  ⟨r * x.val, mul_pos hr x.val_pos⟩

@[simp]
lemma scale_div_self (r : ℝ) (hr : 0 < r) : scale r x hr / x = r := by
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

## Specific choices of charge units

To define a specific charge units, we must first axiomise the existence of a
a given charge unit, and then construct all other charge units from it.
We choose to axiomise the existence of the charge unit of coulomb.

We need an axiom since this relates something to something in the physical world.

-/

/-- The charge unit of a elementryCharge (1.602176634×10−19 coulomb). -/
noncomputable def elementaryCharge : ChargeUnit := scale (1.602176634e-19) coulombs

end ChargeUnit
