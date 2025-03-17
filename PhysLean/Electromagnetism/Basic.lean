/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Basic
import PhysLean.Relativity.Lorentz.PauliMatrices.Basic
/-!

# Electromagnetism

In this file we define the electric field, the magnetic field, and the field strength tensor.

-/

namespace Electromagnetism

/-- The electric field is a map from `d`+1 dimensional spacetime to the vector space
  `ℝ^d`. -/
abbrev ElectricField (d : ℕ := 3) := ℝT[d, .up] → EuclideanSpace ℝ (Fin d)

/-- The magnetic field is a map from `d+1` dimensional spacetime to the vector space
  `ℝ^d`. -/
abbrev MagneticField (d : ℕ := 3) := ℝT[d, .up] → EuclideanSpace ℝ (Fin d)

open IndexNotation
open realLorentzTensor

/-- The vector potential of an electromagnetic field-/
abbrev VectorPotential (d : ℕ := 3) := ℝT[d, .up] → ℝT[d, .up]

open TensorTree in
/-- The Field strength is a tensor `F^μ^ν` which is anti-symmetric.. -/
noncomputable abbrev FieldStrength (d : ℕ := 3) :
    Submodule (realLorentzTensor d).k (ℝT[d, .up] → ℝT[d, .up, .up]) where
  carrier F := ∀ x,  {F x | μ ν = - (F x| ν μ)}ᵀ
  add_mem' {F1 F2} hF1 hF2:= by
    intro x
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.add_apply,
      TensorTree.tensorNode_tensor, Fin.isValue]
    have h1 : (TensorTree.tensorNode (F1 x + F2 x)).tensor
      = (TensorTree.add (TensorTree.tensorNode (F1 x)) (TensorTree.tensorNode (F2 x))).tensor := by
      simp
    rw [perm_tensor_eq <| neg_tensor_eq <| h1]
    rw [perm_tensor_eq <| (add_neg_neg _ _).symm]
    rw [perm_add]
    rw [add_tensor_eq_fst <| (hF1 x).symm]
    rw [add_tensor_eq_snd <| (hF2 x).symm]
    simp [add_tensor]
  smul_mem' {c F hF} := by
    intro x
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.smul_apply,
      TensorTree.tensorNode_tensor, Fin.isValue]
    have h1 : (TensorTree.tensorNode (c • F x)).tensor
      = (TensorTree.smul c (TensorTree.tensorNode (F x))).tensor := by
      simp [smul_tensor]
    rw [perm_tensor_eq <| neg_tensor_eq <| h1]
    rw [perm_tensor_eq <| (TensorTree.smul_comm_neg _ _).symm]
    rw [perm_smul]
    rw [smul_tensor_eq <| (hF x).symm]
    simp [smul_tensor]
  zero_mem' := by
    intro x
    simp [perm_tensor, neg_tensor]

namespace FieldStrength


lemma up_up_antisymmetric_iff_repr {d : ℕ} {F : ℝT[d, .up, .up]}
    (h : ∀ i j, (((realLorentzTensor d).tensorBasis _).repr F) (fun | 0 => i | 1 => j) =
    - ((((realLorentzTensor d).tensorBasis _).repr F) (fun | 0 => j | 1 => i))) :
    {F | μ ν = - (F | ν μ)}ᵀ := by
  obtain ⟨F, rfl⟩ := ((realLorentzTensor d).tensorBasis _).repr.symm.surjective F
  simp at h
  apply ((realLorentzTensor d).tensorBasis _).repr.injective
  ext b
  rw [TensorTree.perm_tensorBasis_repr_apply]
  rw [TensorTree.neg_tensorBasis_repr]
  simp
  have h1 : b = fun | 0 => b 0 | 1 => b 1 := by
    ext i
    fin_cases i
    · rfl
    · rfl
  have h2 : ((TensorSpecies.TensorBasis.congr (PhysLean.Fin.finMapToEquiv ![1, 0] ![1, 0])
      (by intro i; fin_cases i <;> rfl)) b)
      = (fun | 0 => b 1 | 1 => b 0 :
      (j : Fin 2) → Fin ((realLorentzTensor d).repDim (![Color.up, Color.up] j))) := by
    ext i
    fin_cases i
    · rfl
    · rfl
  conv_lhs => rw [h1]
  rw [h2]
  exact h (b 0) (b 1)

/-- The field strength from an electric field as an element of `ℝT[d, .up, .up]`. -/
noncomputable def ofEletricFieldAux {d : ℕ} (E : ElectricField d) (x : ℝT[d, .up]) :
    ℝT[d, .up, .up] := ((realLorentzTensor d).tensorBasis _).repr.symm <|
      Finsupp.equivFunOnFinite.symm <| fun b =>
    match b 0, b 1 with
    | 0, ⟨j + 1, hj⟩ => - E x ⟨j, by
      change j + 1 < 1 + d at hj
      omega⟩
    | ⟨j + 1, hj⟩, 0 => E x ⟨j, by
      change j + 1 < 1 + d at hj
      omega⟩
    | _, _ => 0

/-- The field strength from an eletric field. -/
noncomputable def ofElectricField {d : ℕ} :  ElectricField d →ₗ[ℝ] FieldStrength d where
  toFun E := by
    refine ⟨fun x => ofEletricFieldAux E x, ?_⟩
    simp only [C_eq_color, Nat.reduceAdd,
      Fin.isValue, Set.mem_setOf_eq]
    intro x
    apply up_up_antisymmetric_iff_repr
    intro i j
    simp [ofEletricFieldAux]
    match i, j with
    | 0, 0 => simp
    | ⟨0, h0⟩, ⟨j + 1, hj⟩ =>
      simp
    | ⟨j + 1, hj⟩, ⟨0, h0⟩ =>
      simp
    | ⟨j + 1, hj⟩, ⟨k + 1, hk⟩ =>
      simp
  map_add' E1 E2 := by
    ext x
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, AddMemClass.mk_add_mk, Pi.add_apply]
    apply ((realLorentzTensor d).tensorBasis _).repr.injective
    apply Finsupp.equivFunOnFinite.injective
    trans Finsupp.equivFunOnFinite (((realLorentzTensor d).tensorBasis ![Color.up, Color.up]).repr
      (ofEletricFieldAux E1 x)) + Finsupp.equivFunOnFinite
      (((realLorentzTensor d).tensorBasis ![Color.up, Color.up]).repr
      (ofEletricFieldAux E2 x))
    swap
    · simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, map_add]
      rfl
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, ofEletricFieldAux, Fin.isValue,
      Matrix.cons_val_zero, repDim_up, Matrix.cons_val_one, Matrix.head_cons, Pi.add_apply,
      PiLp.add_apply, neg_add_rev, Basis.repr_symm_apply, Basis.repr_linearCombination,
      Equiv.apply_symm_apply]
    funext b
    simp only [Fin.isValue, Pi.add_apply]
    split <;> abel
  map_smul' c E := by
    ext x
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.smul_apply]
    apply ((realLorentzTensor d).tensorBasis _).repr.injective
    apply Finsupp.equivFunOnFinite.injective
    simp [ofEletricFieldAux]
    ext x_1 : 1
    simp only [Fin.isValue, Finsupp.equivFunOnFinite_apply, Finsupp.coe_smul,
      Finsupp.coe_equivFunOnFinite_symm, Pi.smul_apply, smul_eq_mul]
    split
    next x_2 x_3 j hj heq heq_1 =>
      simp only [mul_neg]
    next x_2 x_3 j hj heq heq_1 =>
      simp only
    next x_2 x_3 x_4 x_5 =>
      simp only [mul_zero]

/-- The field strength from a magnetic field as an element of `ℝT[3, .up, .up]`.
  This is only defined here for 4d spacetime. -/
noncomputable def ofMagneticFieldAux (B : MagneticField) (x : ℝT[3, .up]) :
      ℝT[3, .up, .up] := ((realLorentzTensor 3).tensorBasis _).repr.symm <|
      Finsupp.equivFunOnFinite.symm <| fun b =>
    match b 0, b 1 with
    | 1, 2 => - B x 2
    | 1, 3 => B x 1
    | 2, 3 => - B x 0
    | 2, 1 => B x 2
    | 3, 1 => - B x 1
    | 3, 2 => B x 0
    | _, _ => 0

/-- The field strength from a magnetic field. -/
noncomputable def ofMagneticField : MagneticField →ₗ[ℝ] FieldStrength where
  toFun B := by
    refine ⟨fun x => ofMagneticFieldAux B x, fun x => ?_⟩
    simp only [C_eq_color, Nat.reduceAdd,
      Fin.isValue, Set.mem_setOf_eq]
    apply up_up_antisymmetric_iff_repr
    intro i j
    simp [ofMagneticFieldAux]
    fin_cases i <;> fin_cases j <;> simp
  map_add' B1 B2 := by
    ext x
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, AddMemClass.mk_add_mk, Pi.add_apply]
    apply ((realLorentzTensor 3).tensorBasis _).repr.injective
    apply Finsupp.equivFunOnFinite.injective
    simp only [Nat.reduceAdd, C_eq_color, Submodule.coe_add, Pi.add_apply,
      map_add]
    trans Finsupp.equivFunOnFinite (((realLorentzTensor 3).tensorBasis ![Color.up, Color.up]).repr
      (ofMagneticFieldAux B1 x)) + Finsupp.equivFunOnFinite
      (((realLorentzTensor 3).tensorBasis ![Color.up, Color.up]).repr
      (ofMagneticFieldAux B2 x))
    swap
    · simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, map_add]
      rfl
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, ofMagneticFieldAux, Fin.isValue,
      Matrix.cons_val_zero, repDim_up, Matrix.cons_val_one, Matrix.head_cons, Pi.add_apply,
      PiLp.add_apply, neg_add_rev, Basis.repr_symm_apply, Basis.repr_linearCombination,
      Equiv.apply_symm_apply]
    funext b
    simp only [Fin.isValue, Pi.add_apply]
    split <;> abel
  map_smul' c B := by
    ext x
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.smul_apply]
    apply ((realLorentzTensor 3).tensorBasis _).repr.injective
    apply Finsupp.equivFunOnFinite.injective
    simp [ofMagneticFieldAux]
    ext x_1 : 1
    simp only [Fin.isValue, Finsupp.equivFunOnFinite_apply, Finsupp.coe_smul,
      Finsupp.coe_equivFunOnFinite_symm, Pi.smul_apply, smul_eq_mul]
    split
    · simp only [Fin.isValue, mul_neg]
    · simp only [Fin.isValue]
    · simp only [Fin.isValue, mul_neg]
    · simp only [Fin.isValue]
    · simp only [Fin.isValue, mul_neg]
    · simp only [Fin.isValue]
    · simp only [mul_zero]

/-- The electric field given a field strength. -/
noncomputable def electricField {d : ℕ} : FieldStrength d →ₗ[ℝ] ElectricField d where
  toFun F :=  fun x j =>
    ((realLorentzTensor d).tensorBasis _).repr (F.1 x) (fun | 0 => ⟨j + 1, by simp; omega⟩ | 1 => 0)
  map_add' F1 F2 := by
    simp
    rfl
  map_smul' c F := by
    simp
    rfl


@[simp]
lemma electricField_ofElectricField {d : ℕ} (E : ElectricField d) :
    electricField (ofElectricField E) = E := by
  ext x j
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, electricField, Fin.isValue,
    Matrix.cons_val_zero, repDim_up, ofElectricField, ofEletricFieldAux, Matrix.cons_val_one,
    Matrix.head_cons, Basis.repr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun]
  conv_lhs=>
    enter [3]
    change ⟨0, Nat.pos_of_neZero _⟩

/-- The magnetic field given a field strength. -/
noncomputable def magneticField : FieldStrength →ₗ[ℝ] MagneticField where
  toFun F := fun x j =>
    match j with
    | 0 =>
      ((realLorentzTensor 3).tensorBasis _).repr (F.1 x) (fun | 0 => 3| 1 => 2)
    | 1 =>
      ((realLorentzTensor 3).tensorBasis _).repr (F.1 x)  (fun | 0 => 1| 1 => 3)
    | 2 =>
      ((realLorentzTensor 3).tensorBasis _).repr (F.1 x)  (fun | 0 => 2| 1 => 1)
  map_add' F1 F2 := by
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Submodule.coe_add, Pi.add_apply,
      map_add, Fin.isValue, Finsupp.coe_add]
    funext x j
    fin_cases j <;> simp
  map_smul' c F := by
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, SetLike.val_smul, Pi.smul_apply,
      map_smul, Fin.isValue, Finsupp.coe_smul, smul_eq_mul, RingHom.id_apply]
    funext x j
    fin_cases j <;> simp

@[simp]
lemma magneticField_ofMagneticField (B : MagneticField) :
    magneticField (ofMagneticField B) = B := by
  ext x j
  simp only [magneticField, ofMagneticField, ofMagneticFieldAux, C_eq_color,
    TensorTree.tensorNode_tensor, Fin.isValue, Set.mem_setOf_eq, up_up_antisymmetric_iff_repr,
    Basis.repr_symm_apply, Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun]
  fin_cases j <;> simp
  · rfl
  · rfl
  · rfl

@[simp]
lemma electricField_ofMagneticField (B : MagneticField) :
    electricField (ofMagneticField B) = 0 := by
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, electricField, Fin.isValue,
    Matrix.cons_val_zero, repDim_up, ofMagneticField, ofMagneticFieldAux, Matrix.cons_val_one,
    Matrix.head_cons, Basis.repr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.mk_eq_one,
    add_left_eq_self, Fin.val_eq_zero_iff, Fin.reduceEq, imp_self, implies_true, zero_ne_one]
  rfl

@[simp]
lemma magneticField_ofElectricField (E : ElectricField) :
    magneticField (ofElectricField E) = 0 := by
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, magneticField, Fin.isValue,
    ofElectricField, ofEletricFieldAux, Matrix.cons_val_zero, repDim_up, Matrix.cons_val_one,
    Matrix.head_cons, Basis.repr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.zero_eta,
    Fin.reduceEq, imp_false, IsEmpty.forall_iff, implies_true, imp_self, one_ne_zero, Fin.one_eq_mk,
    add_left_eq_self]
  funext x j
  fin_cases j <;> simp


TODO "Define the dual field strength."

end FieldStrength

TODO "Define isomorphism from `ElectricField d × MagneticField d` to `FieldStrength d`."

TODO "Show that the isomorphism between `ElectricField d × MagneticField d` and
  `ElectricField d × MagneticField d` is equivariant with respect to the Lorentz group."

end Electromagnetism
