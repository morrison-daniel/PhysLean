/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.RealTensor.Metrics.Basic
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

namespace Lorentz
open realLorentzTensor

/-- Real contravariant Lorentz vector. -/
abbrev Vector (d : ℕ := 3) := ℝT[d, .up]

namespace Vector


def indexEquiv {d : ℕ} :
    ((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j)))
    ≃ Fin 1 ⊕ Fin d :=
  let e :((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j)))
    ≃ Fin (1 + d) := {
    toFun := fun f => Fin.cast (by rfl) (f 0)
    invFun := fun x => (fun j => Fin.cast (by simp) x)
    left_inv := fun f => by
      ext j
      fin_cases j
      simp
    right_inv := fun x => by rfl}
  e.trans finSumFinEquiv.symm

/-- The coordinates of a Lorentz vector -/
def toCoord {d : ℕ} (p : Vector d) : Fin 1 ⊕ Fin d → ℝ :=
  Equiv.piCongrLeft' _ indexEquiv
  (Finsupp.equivFunOnFinite
  (((realLorentzTensor d).tensorBasis _).repr p))

instance : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) := ⟨toCoord⟩

lemma tensorNode_repr_apply {d : ℕ} (p : Vector d)
    (b : (j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) :
    ((realLorentzTensor d).tensorBasis _).repr p b =
    p (finSumFinEquiv.symm (b 0)) := by
  simp [toCoord, indexEquiv]
  congr
  ext j
  fin_cases j
  simp

/-- The Minkowski product of Lorentz vectors  in the +--- convention.. -/
def innerProduct {d : ℕ} (p q : Vector d) : ℝ :=
  {η' d | μ ν ⊗ p | μ ⊗ q | ν}ᵀ.field

notation "⟪" p ", " q "⟫ₘ" => innerProduct p q

open TensorTree
lemma innerProduct_toCoord {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = p (Sum.inl 0) * q (Sum.inl 0) - ∑ i, p (Sum.inr i) * q (Sum.inr i) := by
  dsimp only [innerProduct, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue]
  rw [TensorTree.field_eq_repr]
  rw [contr_tensorBasis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, x]
    rw [prod_tensorBasis_repr_apply]
    rw [contr_tensorBasis_repr_apply_eq_fin]
    rw [tensorNode_repr_apply]
    enter [1, 2, y]
    rw [prod_tensorBasis_repr_apply]
    rw [tensorNode_repr_apply]
    enter [1]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
  simp
  conv_lhs =>
    enter [2, x, 2, 2]
    simp
    change finSumFinEquiv.symm x
  conv_lhs =>
    enter [2, x, 1, 2, y, 2, 2]
    change finSumFinEquiv.symm y
  conv_lhs =>
    enter [2, x, 1, 2, y, 1]
    simp
    change minkowskiMatrix (finSumFinEquiv.symm y) (finSumFinEquiv.symm x)
  conv_lhs =>
    enter [2, x, 1]
    rw [← finSumFinEquiv.sum_comp]
  rw [← finSumFinEquiv.sum_comp]
  simp
  congr 1
  rw [minkowskiMatrix.inl_0_inl_0]
  simp
  rw [← Finset.sum_neg_distrib]
  congr
  funext x
  rw [Finset.sum_eq_single x]
  · rw [minkowskiMatrix.inr_i_inr_i]
    simp
  · intro y _ hy
    rw [minkowskiMatrix.off_diag_zero (by simp [hy])]
    simp
  · simp

end Vector

end Lorentz
