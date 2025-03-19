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

lemma deriv_eq_k {d : ℕ} (μ : Fin (1 + d)) (f : SpaceTime d → (realLorentzTensor d).k) (y : SpaceTime d) :
    SpaceTime.deriv μ f y = fderiv (realLorentzTensor d).k
      (fun y => (f (((realLorentzTensor d).tensorBasis ![Color.up]).repr.symm
            (Finsupp.equivFunOnFinite.symm y))))
      ⇑(((realLorentzTensor d).tensorBasis ![Color.up]).repr y)
    ⇑(Finsupp.single  (fun x => Fin.cast (by simp) μ) 1) := by

  change _ =  fderiv (realLorentzTensor d).k (f ∘ Lorentz.Vector.fromCoordFullContinuous)  ⇑(((realLorentzTensor d).tensorBasis ![Color.up]).repr y)
    ⇑(Finsupp.single  (fun x => Fin.cast (by simp) μ) 1)
  haveI : NormedSpace (realLorentzTensor d).k  (realLorentzTensor d).k := inferInstanceAs (NormedSpace ℝ ℝ)
  haveI : NormedSpace (realLorentzTensor d).k ↑(SpaceTime d).V := inferInstanceAs (NormedSpace ℝ _)
  have h1 := @ContinuousLinearEquiv.comp_right_fderiv (realLorentzTensor d).k
    _  (((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) →
      (realLorentzTensor d).k) _ _ ↑(SpaceTime d).V _ _
  simp
  erw [ContinuousLinearEquiv.fderiv]
  have hx (y) :  fderiv (realLorentzTensor d).k g y = sorry := by
    simp [g]
    rw []
  sorry

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
