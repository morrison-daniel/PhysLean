/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Tree.Dot
import PhysLean.Relativity.Lorentz.Weyl.Metric
import PhysLean.Relativity.Lorentz.RealTensor.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Pre.Basic
import PhysLean.Relativity.Lorentz.PauliMatrices.AsTensor
/-!

## Derivative of Real Lorentz tensors

-/
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open MonoidalCategory
open TensorSpecies
namespace realLorentzTensor

/-- The derivative of a function `f : ℝT(d, cm) → ℝT(d, cn)`, giving a function
    `ℝT(d, cm) → ℝT(d, (Sum.elim cm cn) ∘ finSumFinEquiv.symm)`. -/
noncomputable def derivative {d n m : ℕ} {cm : Fin m → (realLorentzTensor d).C}
    {cn : Fin n → (realLorentzTensor d).C} (f : ℝT(d, cm) → ℝT(d, cn)) :
    ℝT(d, cm) → ℝT(d, (Sum.elim cm cn) ∘ finSumFinEquiv.symm) := fun y =>
      ((realLorentzTensor d).tensorBasis _).repr.toEquiv.symm.toFun <|
      Finsupp.equivFunOnFinite.symm <| fun g =>
  let f' := Finsupp.equivFunOnFinite ∘ ((realLorentzTensor d).tensorBasis cn).repr.toEquiv.toFun ∘
      f ∘ ((realLorentzTensor d).tensorBasis cm).repr.symm.toEquiv.toFun
      ∘ Finsupp.equivFunOnFinite.symm
  let df' :=
    @fderiv ℝ _
    (((j : Fin m) → Fin ((realLorentzTensor d).repDim (cm j))) → ℝ)
    _ _ _ (((j : Fin n) → Fin ((realLorentzTensor d).repDim (cn j))) → ℝ)
    _ _ _ f'
  let df := (df' ∘ Finsupp.equivFunOnFinite ∘
    ((realLorentzTensor d).tensorBasis cm).repr.toEquiv.toFun) y
  let g1 : ((j : Fin m) → Fin ((realLorentzTensor d).repDim (cm j))) :=
    fun j => Fin.cast (by simp) (g (finSumFinEquiv (Sum.inl j)))
  let g1Fun : ((j : Fin m) → Fin ((realLorentzTensor d).repDim (cm j))) →
    ℝ := Finsupp.equivFunOnFinite
    (Finsupp.single g1 (1 : ℝ))
  df g1Fun fun j => Fin.cast (by simp) (g (finSumFinEquiv (Sum.inr j)))

end realLorentzTensor
