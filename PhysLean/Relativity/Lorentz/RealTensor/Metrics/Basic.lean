/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ProdAssoc
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ProdComm
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ProdContr
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ContrContr
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ContrSwap
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.PermContr
import PhysLean.Relativity.Lorentz.RealTensor.Basic

/-!

## Metrics as real Lorentz tensors

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open TensorTree
open OverColor.Discrete
noncomputable section

namespace realLorentzTensor
open Fermion

/-!

## Definitions.

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
def coMetric (d : ℕ := 3) := (TensorTree.constTwoNodeE (realLorentzTensor d)
  .down .down (Lorentz.preCoMetric d)).tensor

/-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
def contrMetric (d : ℕ := 3) := (TensorTree.constTwoNodeE (realLorentzTensor d)
  .up .up (Lorentz.preContrMetric d)).tensor

/-!

## Notation

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η'" => @coMetric

/-- The metric `ηⁱⁱ` as a complex Lorentz tensors. -/
scoped[realLorentzTensor] notation "η" => @contrMetric

/-!

## Tensor nodes.

-/

/-- The definitional tensor node relation for `coMetric`. -/
lemma tensorNode_coMetric {d : ℕ} : {η' d | μ ν}ᵀ.tensor =
  (TensorTree.constTwoNodeE (realLorentzTensor d)
    .down .down (Lorentz.preCoMetric d)).tensor := by
  rfl

/-- The definitional tensor node relation for `contrMetric`. -/
lemma tensorNode_contrMetric : {η d | μ ν}ᵀ.tensor =
    (TensorTree.constTwoNodeE (realLorentzTensor d)
    .up .up (Lorentz.preContrMetric d)).tensor := by
  rfl

/-

## Group actions

-/

/-- The tensor `coMetric` is invariant under the action of `LorentzGroup d`. -/
lemma action_coMetric {d : ℕ} (g : LorentzGroup d) : {g •ₐ η' d | μ ν}ᵀ.tensor =
    {η' d | μ ν}ᵀ.tensor := by
  rw [tensorNode_coMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `contrMetric` is invariant under the action of `LorentzGroup d`. -/
lemma action_contrMetric (g : LorentzGroup d) : {g •ₐ η d | μ ν}ᵀ.tensor =
    {η d | μ ν}ᵀ.tensor := by
  rw [tensorNode_contrMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

end realLorentzTensor
