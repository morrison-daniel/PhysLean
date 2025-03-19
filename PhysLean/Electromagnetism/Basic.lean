/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Derivative
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Relativity.Lorentz.PauliMatrices.Basic
/-!

# Electromagnetism

In this file we define the electric field, the magnetic field, and the field strength tensor.

-/

namespace Electromagnetism

/-- The electric field is a map from `d`+1 dimensional spacetime to the vector space
  `ℝ^d`. -/
abbrev ElectricField (d : ℕ := 3) := SpaceTime d → EuclideanSpace ℝ (Fin d)

/-- The magnetic field is a map from `d+1` dimensional spacetime to the vector space
  `ℝ^d`. -/
abbrev MagneticField (d : ℕ := 3) := SpaceTime d → EuclideanSpace ℝ (Fin d)

open IndexNotation
open realLorentzTensor

/-- The vector potential of an electromagnetic field-/
abbrev VectorPotential (d : ℕ := 3) := SpaceTime d → ℝT[d, .up]

open TensorTree in
/-- The Field strength is a tensor `F^μ^ν` which is anti-symmetric.. -/
noncomputable abbrev FieldStrength (d : ℕ := 3) :
    Submodule ℝ (ℝT[d, .up] → ℝT[d, .up, .up]) where
  carrier F := ∀ x, {F x | μ ν = - (F x| ν μ)}ᵀ
  add_mem' {F1 F2} hF1 hF2:= by
    intro x
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.add_apply,
      TensorTree.tensorNode_tensor, Fin.isValue]
    have h1 : (TensorTree.tensorNode (F1 x + F2 x)).tensor
      = (TensorTree.add (TensorTree.tensorNode (F1 x)) (TensorTree.tensorNode (F2 x))).tensor := by
      simp [add_tensor]
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

lemma mem_of_repr {d : ℕ} {F : ℝT[d, .up, .up]}
    (h : ∀ i j, (((realLorentzTensor d).tensorBasis _).repr F) (fun | 0 => i | 1 => j) =
    - ((((realLorentzTensor d).tensorBasis _).repr F) (fun | 0 => j | 1 => i))) :
    {F | μ ν = - (F | ν μ)}ᵀ := by
  obtain ⟨F, rfl⟩ := ((realLorentzTensor d).tensorBasis _).repr.symm.surjective F
  simp at h
  apply ((realLorentzTensor d).tensorBasis _).repr.injective
  ext b
  rw [TensorTree.perm_tensorBasis_repr_apply]
  rw [TensorTree.neg_tensorBasis_repr]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Basis.repr_symm_apply,
    TensorTree.tensorNode_tensor, Basis.repr_linearCombination, OverColor.mk_hom, Fin.isValue,
    OverColor.equivToHomEq_toEquiv, Finsupp.coe_neg, Pi.neg_apply]
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

lemma repr_symm {d : ℕ} (F : FieldStrength d) (i j : Fin (1 + d))
    (x : ℝT[d, .up]) :
    ((realLorentzTensor d).tensorBasis _).repr (F.1 x) (fun | 0 => i | 1 => j)
    = - ((realLorentzTensor d).tensorBasis _).repr (F.1 x) (fun | 0 => j | 1 => i) := by
  obtain ⟨F, hF⟩ := F
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Submodule.mem_mk,
    TensorTree.tensorNode_tensor, Fin.isValue, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk] at hF
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color]
  conv_lhs => rw [hF x]
  rw [TensorTree.perm_tensorBasis_repr_apply]
  rw [TensorTree.neg_tensorBasis_repr]
  simp only [C_eq_color, TensorTree.tensorNode_tensor, OverColor.mk_hom, Fin.isValue,
    OverColor.equivToHomEq_toEquiv, Finsupp.coe_neg, Pi.neg_apply, neg_inj]
  congr
  funext x
  fin_cases x <;> rfl

@[simp]
lemma repr_diag_zero {d : ℕ} (F : FieldStrength d) (i : Fin (1 + d))
    (x : ℝT[d, .up]) :
    ((realLorentzTensor d).tensorBasis _).repr (F.1 x) (fun | 0 => i | 1 => i)
    = 0 := by
  have h1 := repr_symm F i i x
  have hl (a : ℝ) (ha : a = -a) : a = 0 := by
    exact CharZero.eq_neg_self_iff.mp ha
  exact hl _ h1

/-- The field strength from an electric field as an element of `ℝT[d, .up, .up]`. -/
noncomputable def ofElectricFieldAux {d : ℕ} (E : ElectricField d) (x : ℝT[d, .up]) :
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
noncomputable def ofElectricField {d : ℕ} : ElectricField d →ₗ[ℝ] FieldStrength d where
  toFun E := by
    refine ⟨fun x => ofElectricFieldAux E x, ?_⟩
    simp only [C_eq_color, Nat.reduceAdd,
      Fin.isValue, Set.mem_setOf_eq]
    intro x
    apply mem_of_repr
    intro i j
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, ofElectricFieldAux, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Basis.repr_symm_apply,
      Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun]
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
      (ofElectricFieldAux E1 x)) + Finsupp.equivFunOnFinite
      (((realLorentzTensor d).tensorBasis ![Color.up, Color.up]).repr
      (ofElectricFieldAux E2 x))
    swap
    · simp_all only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, map_add]
      rfl
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, ofElectricFieldAux, Fin.isValue,
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
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, ofElectricFieldAux, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, PiLp.smul_apply,
      smul_eq_mul, Basis.repr_symm_apply, Basis.repr_linearCombination, Equiv.apply_symm_apply,
      RingHom.id_apply, SetLike.mk_smul_mk, map_smul]
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
    apply mem_of_repr
    intro i j
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, ofMagneticFieldAux, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Basis.repr_symm_apply,
      Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun]
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
  toFun F := fun x j =>
    ((realLorentzTensor d).tensorBasis _).repr (F.1 x) (fun | 0 => ⟨j + 1, by simp; omega⟩ | 1 => 0)
  map_add' F1 F2 := by
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Submodule.coe_add, Pi.add_apply,
      map_add, Fin.isValue, Matrix.cons_val_zero, Finsupp.coe_add]
    rfl
  map_smul' c F := by
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, SetLike.val_smul, Pi.smul_apply,
      map_smul, Fin.isValue, Matrix.cons_val_zero, Finsupp.coe_smul, smul_eq_mul, RingHom.id_apply]
    rfl

@[simp]
lemma electricField_ofElectricField {d : ℕ} (E : ElectricField d) :
    electricField (ofElectricField E) = E := by
  ext x j
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, electricField, Fin.isValue,
    Matrix.cons_val_zero, repDim_up, ofElectricField, ofElectricFieldAux, Matrix.cons_val_one,
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
      ((realLorentzTensor 3).tensorBasis _).repr (F.1 x) (fun | 0 => 1| 1 => 3)
    | 2 =>
      ((realLorentzTensor 3).tensorBasis _).repr (F.1 x) (fun | 0 => 2| 1 => 1)
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
    TensorTree.tensorNode_tensor, Fin.isValue, Set.mem_setOf_eq, mem_of_repr,
    Basis.repr_symm_apply, Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun]
  fin_cases j <;> simp only [LinearMap.coe_mk, AddHom.coe_mk, Basis.repr_linearCombination]
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
    ofElectricField, ofElectricFieldAux, Matrix.cons_val_zero, repDim_up, Matrix.cons_val_one,
    Matrix.head_cons, Basis.repr_symm_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_toFun, Fin.zero_eta,
    Fin.reduceEq, imp_false, IsEmpty.forall_iff, implies_true, imp_self, one_ne_zero, Fin.one_eq_mk,
    add_left_eq_self]
  funext x j
  fin_cases j <;> simp

lemma eq_ofElectricField_add_ofMagneticField (F : FieldStrength) : F =
    ofElectricField (electricField F) + ofMagneticField (magneticField F) := by
  simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd]
  ext x
  simp only [Submodule.coe_add, C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, Pi.add_apply]
  apply ((realLorentzTensor 3).tensorBasis _).repr.injective
  apply Finsupp.equivFunOnFinite.injective
  trans Finsupp.equivFunOnFinite
    ((realLorentzTensor.tensorBasis ![Color.up, Color.up]).repr
    ((ofElectricField (electricField F)).1 x))
    + Finsupp.equivFunOnFinite
    ((realLorentzTensor.tensorBasis ![Color.up, Color.up]).repr
    ((ofMagneticField (magneticField F)).1 x))
  swap
  · simp only [map_add]
    rfl
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, ofElectricField, ofElectricFieldAux,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Basis.repr_symm_apply,
    LinearMap.coe_mk, AddHom.coe_mk, Basis.repr_linearCombination, Equiv.apply_symm_apply,
    ofMagneticField, ofMagneticFieldAux]
  funext b
  simp only [Finsupp.equivFunOnFinite_apply, Fin.isValue, Pi.add_apply]
  have h1 : ∃ i j, b = (fun | 0 => i | 1 => j) := by
    use (b 0), (b 1)
    funext x
    fin_cases x <;> rfl
  obtain ⟨i, j, rfl⟩ := h1
  simp only [Fin.isValue]
  match i, j with
  | (1 : Fin 4), (2 : Fin 4) =>
    simpa [magneticField] using repr_symm F 1 2 x
  | (1 : Fin 4), (3 : Fin 4) =>
    simp only [Fin.isValue, magneticField, C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
      LinearMap.coe_mk, AddHom.coe_mk, zero_add]
    rfl
  | (2 : Fin 4), (3 : Fin 4) =>
    simpa [magneticField] using repr_symm F 2 3 x
  | (2 : Fin 4), (1 : Fin 4) =>
    simp only [Fin.isValue, magneticField, C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
      LinearMap.coe_mk, AddHom.coe_mk, zero_add]
    rfl
  | (3 : Fin 4), (1 : Fin 4) =>
    simpa [magneticField] using repr_symm F 3 1 x
  | (3 : Fin 4), (2 : Fin 4) =>
    simp only [Fin.isValue, magneticField, C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd,
      LinearMap.coe_mk, AddHom.coe_mk, zero_add]
    rfl
  | ⟨0, h0⟩, ⟨0, h0'⟩ =>
    simpa using repr_diag_zero F 0 x
  | ⟨1, h0⟩, ⟨1, h1⟩ =>
    simpa using repr_diag_zero F 1 x
  | ⟨2, h0⟩, ⟨2, h1⟩ =>
    simpa using repr_diag_zero F 2 x
  | ⟨3, h0⟩, ⟨3, h1⟩ =>
    simpa using repr_diag_zero F 3 x
  | ⟨0, h0⟩, ⟨1, h1⟩ =>
    simpa [electricField] using repr_symm F 0 1 x
  | ⟨0, h0⟩, ⟨2, h1⟩ =>
    simpa [electricField] using repr_symm F 0 2 x
  | ⟨0, h0⟩, ⟨3, h1⟩ =>
    simpa [electricField] using repr_symm F 0 3 x
  | ⟨1, h0⟩, ⟨0, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, repDim_up, Nat.reduceAdd, Fin.mk_one,
      Matrix.cons_val_one, Matrix.head_cons, Fin.zero_eta, electricField, C_eq_color,
      Nat.succ_eq_add_one, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_zero, zero_add, add_zero]
    rfl
  | ⟨2, h0⟩, ⟨0, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, repDim_up, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val_one, Matrix.head_cons, Fin.zero_eta, electricField, C_eq_color,
      Nat.succ_eq_add_one, Fin.mk_one, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_one, add_zero]
    rfl
  | ⟨3, h0⟩, ⟨0, h1⟩ =>
    simp only [Fin.isValue, Matrix.cons_val_zero, repDim_up, Nat.reduceAdd, Fin.reduceFinMk,
      Matrix.cons_val_one, Matrix.head_cons, Fin.zero_eta, electricField, C_eq_color,
      Nat.succ_eq_add_one, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_two, add_zero]
    rfl

/-- The isomorphism between the field strength and the electric and magnetic fields. -/
noncomputable def toElectricMagneticField : FieldStrength ≃ₗ[ℝ] ElectricField × MagneticField where
  toFun F := ⟨electricField F, magneticField F⟩
  invFun EM := ofElectricField EM.1 + ofMagneticField EM.2
  map_add' F1 F2 := by simp
  map_smul' c F := by simp
  left_inv F := Eq.symm (eq_ofElectricField_add_ofMagneticField F)
  right_inv EM := by
    simp only [C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd, map_add]
    rw [magneticField_ofElectricField, electricField_ofMagneticField,
      electricField_ofElectricField, magneticField_ofMagneticField]
    simp

TODO "Define the dual field strength."

/-!

## Derivative of the field strength

-/

def derivative_toElectricMagneticField (EM : ElectricField × MagneticField) :
    ∂ (toElectricMagneticField.symm EM).1 = fun (y : SpaceTime) =>
      ((realLorentzTensor 3).tensorBasis  _).repr.symm <| Finsupp.equivFunOnFinite.symm fun b =>
      match b 0, b 1, b 2 with
      | μ, 0, 1 =>  - SpaceTime.deriv μ (fun y => EM.1 y 0) y
      | μ, _, _ => sorry := by
  funext y
  apply (realLorentzTensor.tensorBasis _).repr.injective
  simp only [ Nat.reduceAdd, C_eq_color, Function.comp_apply, Fin.isValue,
    Basis.repr_symm_apply, Basis.repr_linearCombination]
  ext b
  have h_diff : DifferentiableAt ℝ (mapToBasis (toElectricMagneticField.symm EM).1)
      (Finsupp.equivFunOnFinite ((realLorentzTensor.tensorBasis _).repr y)) := by sorry
  conv_lhs => erw [derivative_repr _ _ _ h_diff]
  have h0 : (Finsupp.single (TensorSpecies.TensorBasis.prodEquiv b).1 (1 : ℝ)) =
    (Finsupp.single (fun | 0 => b 0) 1) := by
    congr
    funext x
    fin_cases x
    rfl
  have h1 :  (fun y => mapToBasis (↑(toElectricMagneticField.symm EM)) y (TensorSpecies.TensorBasis.prodEquiv b).2)
    = (fun y => mapToBasis ((toElectricMagneticField.symm EM).1) y
      (fun | (0 : Fin 2) => Fin.cast (by simp) (b 1) | (1 : Fin 2) => Fin.cast (by simp) (b 2))) := by
    ext y
    congr
    funext x
    fin_cases x
    · rfl
    · rfl
  rw [h0, h1]
  have hb : ∃ i j k, b = (fun | 0 => i | 1 => j | 2 => k) := by
    use (b 0), (b 1), (b 2)
    funext x
    fin_cases x <;> rfl
  obtain ⟨i, j, k, rfl⟩ := hb
  simp
  match i, j, k with
  | μ, ⟨0, h⟩, ⟨1, h1⟩ =>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta, Fin.mk_one]
    · conv_rhs => rw [SpaceTime.neg_deriv_apply]
      rw [SpaceTime.deriv_eq_deriv_on_coord]
      simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color,
        ContinuousLinearMap.neg_apply]
      congr 1
      · simp only [Fin.isValue, Basis.repr_symm_apply]
        apply congrFun
        apply congrArg
        ext y
        simp [mapToBasis, toElectricMagneticField,
          ofElectricField, ofElectricFieldAux, ofMagneticField, ofMagneticFieldAux]
      · simp only [DFunLike.coe_fn_eq]
        congr
        funext x
        fin_cases x
        rfl
  | μ, _, _ => sorry

end FieldStrength

TODO "Show that the isomorphism between `ElectricField d × MagneticField d` and
  `ElectricField d × MagneticField d` is equivariant with respect to the Lorentz group."

end Electromagnetism
