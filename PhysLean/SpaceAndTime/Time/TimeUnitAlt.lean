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
  prop : 0 < val

namespace TimeUnit

@[simp]
lemma val_ne_zero (x : TimeUnit) : x.val ≠ 0 := by
  exact (ne_of_lt x.prop).symm

def seconds : TimeUnit := ⟨1, one_pos⟩

instance : Inhabited TimeUnit where
  default := seconds

instance : HSMul Time TimeUnit ℝ where
  hSMul t u := t.val * u.val

theorem hsmul_val (t : Time) (u : TimeUnit) : t • u = t.val * u.val := rfl

def minutes : TimeUnit := ⟨60, by norm_num⟩

theorem ex1 : (60 : Time) • seconds = (1 : Time) • minutes := by
  rw [hsmul_val, hsmul_val, seconds, minutes, Time.ofNat_val, Time.ofNat_val]
  simp

instance : Coe TimeUnit Time where
  coe u := ⟨u.val⟩

theorem ex2 : (60 : Time) = minutes := by
  ext
  rw [Time.ofNat_val, minutes]
  simp

end TimeUnit
