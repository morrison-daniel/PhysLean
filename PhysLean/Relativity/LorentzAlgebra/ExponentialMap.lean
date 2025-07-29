/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import PhysLean.Mathematics.DataStructures.Matrix.LieTraceReals
import PhysLean.Relativity.LorentzAlgebra.Basic
import PhysLean.Relativity.LorentzGroup.Basic
import PhysLean.Relativity.LorentzGroup.Proper
import PhysLean.Relativity.LorentzGroup.Orthochronous.Basic
import PhysLean.Relativity.LorentzGroup.Restricted.Basic
import PhysLean.Relativity.LorentzGroup.Restricted.FromBoostRotation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Topology.Metrizable.CompletelyMetrizable
import PhysLean.Mathematics.SO3.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Exponential map from the Lorentz algebra to the restricted Lorentz group

In 1+3 Minkowski space with metric η, the Lie algebra `lorentzAlgebra` exponentiates
onto the proper orthochronous Lorentz group (`LorentzGroup.restricted 3`).  We prove:
* exp_mem_lorentzGroup : `NormedSpace.exp ℝ A.1 ∈ LorentzGroup 3` (η-preserving).
* exp_transpose_of_mem_algebra : `exp (A.1ᵀ) = η * exp (−A.1) * η`.
* exp_isProper           : `det (exp A) = 1`.
* exp_isOrthochronous    : `(exp A)₀₀ ≥ 1`.
Hence `exp A ∈ LorentzGroup.restricted 3`.
-/

open Matrix
open minkowskiMatrix

attribute [local instance] Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.instCompleteSpace

noncomputable section

namespace lorentzAlgebra

/--
A key property of a Lorentz algebra element `A` is that its transpose
is related to its conjugation by the Minkowski metric η.
-/
lemma transpose_eq_neg_eta_conj (A : lorentzAlgebra) :
    A.1ᵀ = - (η * A.1 * η) := by
  have h := lorentzAlgebra.transpose_eta A
  calc
    A.1ᵀ = A.1ᵀ * 1             := by rw [mul_one]
    _    = A.1ᵀ * (η * η)       := by rw [minkowskiMatrix.sq]
    _    = (A.1ᵀ * η) * η       := by rw [mul_assoc]
    _    = (-η * A.1) * η       := by rw [h]
    _    = - (η * A.1 * η)      := by simp_all only [neg_mul]

/--
The exponential of the transpose of a Lorentz algebra element.
This connects `exp(Aᵀ)` to a conjugation of `exp(-A)`.
-/
lemma exp_transpose_of_mem_algebra (A : lorentzAlgebra) :
    (NormedSpace.exp ℝ) (A.1ᵀ) = η * ((NormedSpace.exp ℝ) (-A.1)) * η := by
  rw [transpose_eq_neg_eta_conj A]
  let P_gl : GL (Fin 1 ⊕ Fin 3) ℝ :=
    { val     := η,
      inv     := η,
      val_inv := minkowskiMatrix.sq,
      inv_val := minkowskiMatrix.sq }
  rw [show -(η * A.1 * η) = η * (-A.1) * η by noncomm_ring]
  erw [NormedSpace.exp_units_conj ℝ P_gl (-A.1)]
  simp [P_gl]

/--
The exponential of an element of the Lorentz algebra is a member of the Lorentz group.
-/
theorem exp_mem_lorentzGroup (A : lorentzAlgebra) : (NormedSpace.exp ℝ) A.1 ∈ LorentzGroup 3 := by
  rw [LorentzGroup.mem_iff_transpose_mul_minkowskiMatrix_mul_self]
  rw [← Matrix.exp_transpose]
  rw [exp_transpose_of_mem_algebra A]
  calc
    (η * (NormedSpace.exp ℝ) (-A.1) * η) * η * (NormedSpace.exp ℝ) A.1
    _ = η * (NormedSpace.exp ℝ) (-A.1) * (η * η) * (NormedSpace.exp ℝ) A.1 := by noncomm_ring
    _ = η * (NormedSpace.exp ℝ) (-A.1) * 1 * (NormedSpace.exp ℝ) A.1   := by rw [minkowskiMatrix.sq]
    _ = η * (NormedSpace.exp ℝ) (-A.1 + A.1)             := by
                                            rw [mul_one, mul_assoc, NormedSpace.exp_add_of_commute]
                                            exact Commute.neg_left rfl
    _ = η * (NormedSpace.exp ℝ) 0                        := by rw [neg_add_cancel]
    _ = η * 1                            := by rw [NormedSpace.exp_zero]
    _ = η                                := by rw [mul_one]

open Matrix
open minkowskiMatrix

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAlgebra
instance [UniformSpace 𝕂] : UniformSpace (Matrix m n 𝕂) := by unfold Matrix; infer_instance

/-- The trace of a matrix equals the sum of its diagonal elements. -/
lemma trace_eq_sum_diagonal (A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :
  trace A = ∑ i, A i i := by
  simp only [trace, diag_apply]

/-- The trace of any element of the Lorentz algebra is zero. -/
lemma trace_of_mem_is_zero (A : lorentzAlgebra) : trace A.1 = 0 := by
  rw [trace_eq_sum_diagonal]
  have h_diag_zero : ∀ μ, A.1 μ μ = 0 := lorentzAlgebra.diag_comp A
  simp [h_diag_zero]

/-- The exponential of an element of the Lorentz algebra is proper (has determinant 1). -/
theorem exp_isProper (A : lorentzAlgebra) : LorentzGroup.IsProper ⟨(NormedSpace.exp ℝ) A.1, exp_mem_lorentzGroup A⟩ := by
  unfold LorentzGroup.IsProper
  simp only [Subtype.coe_mk]
  have h_trace_zero : A.1.trace = 0 := trace_of_mem_is_zero A
  letI : LinearOrder (Fin 1 ⊕ Fin 3) := Sum.Lex.linearOrder
  have h_det_eq_exp_tr : (NormedSpace.exp ℝ A.1).det = Real.exp A.1.trace := by
    letI : LinearOrder (Fin 1 ⊕ Fin 3) := Sum.Lex.linearOrder
    exact Matrix.det_exp_real A.1
  rw [h_det_eq_exp_tr, h_trace_zero, Real.exp_zero]

/-- The exponential of an element of the Lorentz algebra is orthochronous. -/
theorem exp_isOrthochronous (A : lorentzAlgebra) :
    LorentzGroup.IsOrthochronous ⟨(NormedSpace.exp ℝ) A.1, exp_mem_lorentzGroup A⟩ := by
  -- The Lie algebra is a vector space, so there is a path from 0 to A.
  let γ : Path (0 : lorentzAlgebra) A :=
  { toFun := fun t => t.val • A,
    continuous_toFun := by
      apply Continuous.smul
      · exact continuous_subtype_val
      · exact continuous_const,
    source' := by simp [zero_smul],
    target' := by simp [one_smul] }
  let exp_γ : Path (1 : LorentzGroup 3) ⟨(NormedSpace.exp ℝ) A.1, exp_mem_lorentzGroup A⟩ :=
  { toFun := fun t => ⟨(NormedSpace.exp ℝ) (γ t).val, exp_mem_lorentzGroup (γ t)⟩,
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.comp
      · apply NormedSpace.exp_continuous
      · exact Continuous.comp continuous_subtype_val (γ.continuous_toFun),
    source' := by
      ext i j
      simp only [γ, zero_smul]
      simp [NormedSpace.exp_zero],
    target' := by
      ext i j
      simp only [γ, one_smul]
      simp [one_smul] }
  have h_joined : Joined (1 : LorentzGroup 3) ⟨(NormedSpace.exp ℝ) A.1, exp_mem_lorentzGroup A⟩ :=
    ⟨exp_γ⟩
  have h_connected : ⟨(NormedSpace.exp ℝ) A.1, exp_mem_lorentzGroup A⟩ ∈ connectedComponent (1 : LorentzGroup 3) :=
    pathComponent_subset_component _ h_joined
  rw [← LorentzGroup.isOrthochronous_on_connected_component h_connected]
  exact LorentzGroup.id_isOrthochronous

/-- The exponential of an element of the Lorentz algebra is a member of the
restricted Lorentz group. -/
theorem exp_mem_restricted_lorentzGroup (A : lorentzAlgebra) :
    (⟨(NormedSpace.exp ℝ) A.1, exp_mem_lorentzGroup A⟩ : LorentzGroup 3) ∈
    LorentzGroup.restricted 3 := by
  exact ⟨exp_isProper A, exp_isOrthochronous A⟩
