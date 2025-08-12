/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
import PhysLean.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import PhysLean.SpaceAndTime.Space.SpaceStruct
import PhysLean.SpaceAndTime.Time.Basic

/-!
# `SpaceTimeStruct d`

This is a work in progress reimplmentation of `SpaceTime d` as a structure containing
a `Space` and a `Time`

`SpaceTime d` is planned to be deprecated in favor of `SpaceTimeStruct d`.
Once the necessary components are migrated to be compatible with `SpaceTimeStruct`,
it will become the default implementation of `SpaceTime`
-/

/--
`SpaceTimeStruct d` corresponds to `d+1` dimensional space-time with `+---` convention.
The default value of `d` is `3`. Thus `SpaceTimeStuct = SpaceTimeStruct 3`.
-/
@[ext]
structure SpaceTimeStruct (d : ℕ := 3) where
  /-- The underlying time structure. -/
  time : Time
  /-- The underlying space structure. -/
  space : SpaceStruct d

namespace SpaceTimeStruct

variable {d : ℕ}
variable (x y : SpaceTimeStruct d)
variable (s : SpaceStruct d) (t : Time)

/-!
## Relations of `SpaceTime` with `Space` and `Time`
-/

def toSpace : SpaceStruct d := x.space

@[simp]
theorem toSpace_eq_space : x.toSpace = x.space := rfl

def toTime : Time := x.time

@[simp]
theorem toTime_eq_time : x.toTime = x.time := rfl

def toTimeAndSpace : SpaceTimeStruct d ≃ Time × SpaceStruct d where
  toFun x := (x.time, x.space)
  invFun p := ⟨p.1, p.2⟩

@[simp]
theorem toTimeAndSpace_apply : x.toTimeAndSpace = (x.time, x.space) := rfl

@[simp]
theorem toTimeAndSpace_symm_apply : toTimeAndSpace.symm (t, s) = ⟨t, s⟩ := rfl

/-!
## Time slice
(from `PhysLean/SpaceAndTime/SpaceTime/TimeSlice.lean`)

Time slicing functions on spacetime, turning them into a function
`Time → Space d → M`.

This is useful when going from relativistic physics (defined using `SpaceTime`)
to non-relativistic physics (defined using `Space` and `Time`).
-/

def timeSlice {M : Type} : (SpaceTimeStruct d → M) ≃ (Time → SpaceStruct d → M) where
  toFun f := Function.curry (f ∘ toTimeAndSpace.symm)
  invFun f := Function.uncurry f ∘ toTimeAndSpace

@[simp]
theorem timeSlice_apply {M : Type} (f : SpaceTimeStruct d → M) :
  timeSlice f t s = f ⟨t, s⟩ := rfl

@[simp]
theorem timeSlice_symm_apply {M : Type} (f : Time → SpaceStruct d → M) :
  timeSlice.symm f x = f x.time x.space := rfl

/-!
## Basic operations on `SpaceTime`.
-/

instance : Zero (SpaceTimeStruct d) where
  zero := ⟨0, 0⟩

@[simp]
theorem zero_time : (0 : SpaceTimeStruct d).time = 0 := rfl

@[simp]
theorem zero_space : (0 : SpaceTimeStruct d).space = 0 := rfl

instance : Neg (SpaceTimeStruct d) where
  neg x := ⟨-x.time, -x.space⟩

@[simp]
theorem neg_time : (-x).time = - x.time := rfl

@[simp]
theorem neg_space : (-x).space = - x.space := rfl

noncomputable instance : Add (SpaceTimeStruct d) where
  add x y := ⟨x.time + y.time, x.space + y.space⟩

@[simp]
theorem add_time : (x + y).time = x.time + y.time := rfl

@[simp]
theorem add_space : (x + y).space = x.space + y.space := rfl

noncomputable instance : Sub (SpaceTimeStruct d) where
  sub x y := ⟨x.time - y.time, x.space - y.space⟩

@[simp]
theorem sub_time : (x - y).time = x.time - y.time := rfl

@[simp]
theorem sub_space : (x - y).space = x.space - y.space := rfl

noncomputable instance : AddCommGroup (SpaceTimeStruct d) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by
    ext
    · rw [add_time, zero_time, zero_add]
    · rw [add_space, zero_space, zero_add]
  add_zero x := by
    ext
    · rw [add_time, zero_time, add_zero]
    · rw [add_space, zero_space, add_zero]
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := by
    ext
    · rw [add_time, neg_time, zero_time, neg_add_cancel]
    · rw [add_space, neg_space, zero_space, neg_add_cancel]
  add_comm x y := by
    ext
    · rw [add_time, add_time, add_comm]
    · rw [add_space, add_space, add_comm]

variable (c : ℝ)

instance : SMul ℝ (SpaceTimeStruct d) where
  smul c x := ⟨c • x.time, c • x.space⟩

@[simp]
theorem smul_time : (c • x).time = c • x.time := rfl

@[simp]
theorem smul_space : (c • x).space = c • x.space := rfl

noncomputable instance : Module ℝ (SpaceTimeStruct d) where
  one_smul x := by ext; simp; sorry --simp
  mul_smul x y c := by
    ext
    · simp only [smul_time, mul_smul]
    · sorry --simp only [smul_space, mul_smul]
  smul_zero c := by ext; simp; sorry --simp
  smul_add c x y := by ext; simp; sorry --simp
  add_smul x y c := by
    ext
    · simp only [smul_time, add_time, add_smul]
    · sorry --simp only [smul_space, add_space, add_smul]
  zero_smul x := by ext; simp; sorry --simp

noncomputable instance : Inner ℝ (SpaceTimeStruct d) where
  inner x y := Inner.inner ℝ x.time y.time + Inner.inner ℝ x.space y.space

scoped notation "⟪" x ", " y "⟫" => Inner.inner ℝ x y

@[simp]
theorem inner_expand : ⟪x, y⟫ = ⟪x.time, y.time⟫ + ⟪x.space, y.space⟫ := rfl

noncomputable instance : NormedAddCommGroup (SpaceTimeStruct d) where
  norm x := √⟪x, x⟫
  dist_self x := sorry
  dist_comm := sorry
  dist_triangle := sorry
  eq_of_dist_eq_zero := sorry

noncomputable instance : InnerProductSpace ℝ (SpaceTimeStruct d) where
  norm_smul_le := sorry
  norm_sq_eq_re_inner := sorry
  conj_inner_symm := sorry
  add_left := sorry
  smul_left := sorry

/-!
## Orthonormal Basis inherited from `Space` and `Time`

`SpaceTime` has an orthonormal basis obtained by combining the bases of `Space` and `Time`
-/

noncomputable def basis : OrthonormalBasis (Fin (1 + d)) ℝ (SpaceTimeStruct d) where
  repr := sorry

/-!
## Equivalence with `Lorentz.Vector` and Tensorial Instance

Defines a linear equivalence with `Lorentz.Vector`, the tensor representation of spacetime.
-/

#check finSumFinEquiv

/-
noncomputable def toLVector : SpaceTimeStruct d ≃ₗ[ℝ] Lorentz.Vector d where
  toFun x := sorry
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry
-/

/-!
## Minkowski Product

Defines the Minkowski product on SpaceTime according to the +--- convention.
-/

noncomputable def minkowskiProduct := ⟪x.time, y.time⟫ - ⟪x.space, y.space⟫

noncomputable def minkBilin : LinearMap.BilinForm ℝ (SpaceTimeStruct d) where
  toFun x := {
    toFun y := minkowskiProduct x y
    map_add' y z := by

      sorry
    map_smul' c y := by

      sorry
  }
  map_add' x y := sorry
  map_smul' c x := sorry

scoped notation "⟪" x ", " y "⟫ₘ" => minkBilin x y

/-!
## Lightlike, Timelike, and Spacelike vectors & Causality
(from `PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.Basic`)
-/

def Lightlike : Prop := ⟪x, x⟫ₘ = 0

@[simp]
theorem zero_lightlike : (0 : SpaceTimeStruct d).Lightlike := by
  simp [Lightlike]

def Timelike : Prop := 0 < ⟪x, x⟫ₘ

def Spacelike : Prop := ⟪x, x⟫ₘ < 0

def FutureDirected := 0 < x.time

def PastDirected := x.time < 0

def interiorFutureLightCone := {y | (y - x).Timelike ∧ (y - x).FutureDirected}

def interiorPastLightCone := {y | (y - x).Timelike ∧ (y - x).FutureDirected}

def lightConeBoundary := {y | (y - x).Lightlike}

theorem self_mem_lightConeBoundary : x ∈ x.lightConeBoundary := by
  simp [lightConeBoundary]

def futureLightConeBoundary := {y | (y - x).Lightlike ∧ 0 ≤ (y - x).time}

theorem self_mem_futureLightConeBoundary : x ∈ x.futureLightConeBoundary := by
  simp [futureLightConeBoundary]

def pastLightConeBoundary := {y | (y - x).Lightlike ∧ (y - x).time ≤ 0}

theorem self_mem_pastLightConeBoundary : x ∈ x.pastLightConeBoundary := by
  simp [pastLightConeBoundary]

def CausallyFollows := y ∈ x.interiorFutureLightCone ∨ y ∈ x.futureLightConeBoundary

def CausallyPrecedes := y ∈ x.interiorPastLightCone ∨ y ∈ x.pastLightConeBoundary

def CausallyRelated := x.CausallyFollows y ∨ y.CausallyFollows x

theorem not_related_of_spacelike : ¬x.CausallyRelated y ↔ (x - y).Spacelike := by
  sorry

def CausalDiamond := {z | x.CausallyFollows z ∧ z.CausallyFollows y}

end SpaceTimeStruct
