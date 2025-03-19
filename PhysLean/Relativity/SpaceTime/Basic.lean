/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.TODO.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Basic
/-!
# Space time

This file introduce 4d Minkowski spacetime.

-/

/-- The type `Space d` representes `d` dimensional Euclidean space.
  The default value of `d` is `3`. Thus `Space = Space 3`. -/
abbrev Space (d : ℕ := 3) := EuclideanSpace ℝ (Fin d)

noncomputable section

TODO "SpaceTime should be refactored into a structure, or similar, to prevent casting."

/-- The space-time -/
abbrev SpaceTime (d : ℕ := 3) := Lorentz.Vector d

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The space part of spacetime. -/
@[simp]
def space (x : SpaceTime d) : EuclideanSpace ℝ (Fin d) :=
  fun i => x (Sum.inr i)

open realLorentzTensor

noncomputable def deriv {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) : SpaceTime d → ℝ :=
  fun y => fderiv ℝ f y ((realLorentzTensor d).tensorBasis _ (fun x => Fin.cast (by simp) μ))

lemma deriv_eq {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) (y : SpaceTime d) :
    SpaceTime.deriv μ f y =
    fderiv ℝ f y ((realLorentzTensor d).tensorBasis _ (fun x => Fin.cast (by simp) μ)) := by
  rfl

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin (1 + d)) : SpaceTime.deriv μ (fun _ => 0) = 0 := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp

lemma deriv_eq_deriv_on_coord {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) (y : SpaceTime d) :
    SpaceTime.deriv μ f y = fderiv ℝ
      (fun y => (f (((realLorentzTensor d).tensorBasis ![Color.up]).repr.symm
            (Finsupp.equivFunOnFinite.symm y))))
      ⇑(((realLorentzTensor d).tensorBasis ![Color.up]).repr y)
    ⇑(Finsupp.single  (fun x => Fin.cast (by simp) μ) 1) := by
  change _ =  fderiv ℝ (f ∘ Lorentz.Vector.fromCoordFullContinuous)  ⇑(((realLorentzTensor d).tensorBasis ![Color.up]).repr y)
    ⇑(Finsupp.single  (fun x => Fin.cast (by simp) μ) 1)
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rw [deriv_eq]
  congr
  simp [Lorentz.Vector.fromCoordFullContinuous, Lorentz.Vector.toCoordFull]
  exact (LinearEquiv.eq_symm_apply _).mpr rfl

lemma neg_deriv {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) :
    - SpaceTime.deriv μ f = SpaceTime.deriv μ (fun y => - f y) := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp only [Pi.neg_apply, fderiv_neg, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
    ContinuousLinearMap.neg_apply, neg_inj]
  rfl

lemma neg_deriv_apply {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → ℝ) (y : SpaceTime d) :
    - SpaceTime.deriv μ f y = SpaceTime.deriv μ (fun y => - f y) y:= by
  rw [← SpaceTime.neg_deriv]
  rfl

end SpaceTime

end
