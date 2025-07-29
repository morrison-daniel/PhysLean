/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import PhysLean.Mathematics.DataStructures.Matrix.SchurTriangulation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Lie's Trace Formula

This file proves the formula `det (exp A) = exp (tr A)` for matrices, also known as Lie's trace
formula.

## Main results

- `Matrix.det_exp`: The determinant of the exponential of a matrix is the exponential of its trace.
-/

/-!
We give a higher priority to the canonical `1` and `*` instances coming
from `Mathlib` so that every occurrence of `1 : Matrix _ _ _` and
`A * B` uses the very same definitions.
-/
attribute [instance 100] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [instance 100] Matrix.one
namespace Matrix

variable {α k n R 𝕂 m : Type*}

section IsUpperTriangularAPI

variable [LinearOrder n][CommRing α]
variable [SMulZeroClass R α]

/-- Scalar multiplication preserves the property of being upper-triangular. -/
lemma IsUpperTriangular.smul
    {A : Matrix n n α} (hA : IsUpperTriangular A) (k : R) :
    IsUpperTriangular (k • A) := by
  intro i j hij
  simp [smul_apply, hA hij]

/-- The identity matrix is upper-triangular. -/
lemma isUpperTriangular_one  : IsUpperTriangular (1 : Matrix n n α) := by
  intro i j hij
  simp [one_apply, (ne_of_lt hij).symm];
  intro a
  subst a
  simp_all only [id_eq, lt_self_iff_false]

variable [Fintype n]
variable [SMulZeroClass R α]

/-- The product of two upper-triangular matrices is upper-triangular. -/
lemma IsUpperTriangular.mul  {A B : Matrix n n α}
    (hA : IsUpperTriangular A) (hB : IsUpperTriangular B) : IsUpperTriangular (A * B) := by
  intro i j hij
  rw [mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases h₁ : i ≤ l
  · by_cases h₂ : l ≤ j
    · exfalso; exact not_lt_of_ge (le_trans h₁ h₂) hij
    · rw [not_le] at h₂; exact hB h₂ ▸ mul_zero (A i l)
  · rw [not_le] at h₁; exact hA h₁ ▸ zero_mul (B l j)

/-- Powers of an upper-triangular matrix are upper-triangular. -/
lemma IsUpperTriangular.pow  {A : Matrix n n α}
    (hA : IsUpperTriangular A) (k : ℕ) : IsUpperTriangular (A ^ k) := by
  induction k with
  | zero =>
      rw [pow_zero]
      exact isUpperTriangular_one
  | succ k ih =>
      rw [pow_succ]
      exact IsUpperTriangular.mul ih hA

lemma diag_mul_of_isUpperTriangular {A B : Matrix n n α}
    (hA : IsUpperTriangular A) (hB : IsUpperTriangular B) : (A * B).diag = A.diag * B.diag := by
  ext i
  simp only [diag_apply, mul_apply, Pi.mul_apply]
  have sum_eq : ∑ j ∈ Finset.univ, A i j * B j i = A i i * B i i := by
    apply Finset.sum_eq_single i
    · intro j _ j_ne_i
      cases lt_or_gt_of_ne j_ne_i with
      | inl h => -- j < i
        rw [hA h, zero_mul]
      | inr h => -- j > i
        rw [hB h, mul_zero]
    · intro hi_not_in
      exact absurd (Finset.mem_univ i) hi_not_in
  rw [sum_eq]

lemma diag_pow_of_isUpperTriangular {A : Matrix n n α}
    (hA : IsUpperTriangular A) (k : ℕ) : (A ^ k).diag = A.diag ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      ext i
      simp [diag_one]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      have h_mul : (A ^ k * A).diag = (A ^ k).diag * A.diag :=
        diag_mul_of_isUpperTriangular (IsUpperTriangular.pow hA k) hA
      rw [h_mul, ih]

end IsUpperTriangularAPI

open scoped BigOperators Topology

instance [UniformSpace 𝕂] : UniformSpace (Matrix m n 𝕂) := by unfold Matrix; infer_instance

instance completeSpace_matrix
    {m n : Type*}
    {𝕂 : Type*} [NormedField 𝕂] [CompleteSpace 𝕂] :
    CompleteSpace (Matrix m n 𝕂) :=
  (by infer_instance : CompleteSpace (m → n → 𝕂))

/-- If every term of a series is zero, then its sum is zero.                       -/
private lemma tsum_eq_zero
    {β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β] [T2Space β]
    {f : ℕ → β} (h : ∀ n, f n = 0) :
    (∑' n, f n) = 0 := by
  rw [← h Nat.zero]
  simp_all only [tsum_zero, Nat.zero_eq]

/-!
 ### The determinant of the matrix exponential
 -/
section DetExp

variable [RCLike 𝕂] [IsAlgClosed 𝕂] [Fintype m] [DecidableEq m] [LinearOrder m] [LinearOrder 𝕂] [Fintype 𝕂]

omit [IsAlgClosed 𝕂] [DecidableEq m] [LinearOrder m] [LinearOrder 𝕂] [Fintype 𝕂] [Fintype m] in
/-- Apply a matrix `tsum` to a given entry.                                        -/
private theorem matrix_tsum_apply
    [CompleteSpace 𝕂] {f : ℕ → Matrix m m 𝕂} (hf : Summable f) (i j : m) :
    (∑' n, f n) i j = ∑' n, (f n) i j := by
  have h_row_summable : Summable (fun n ↦ (f n) i) := by
    have h := Pi.summable.1 hf
    exact h i
  have h_entry_summable : Summable (fun n ↦ (f n) i j) := by
    have h := Pi.summable.1 h_row_summable
    exact h j
  have h₁ : ((∑' n, f n) : Matrix m m 𝕂) i = (∑' n, (f n) i) := by
    exact tsum_apply hf
  have h₂ : ((∑' n, (f n) i) : m → 𝕂) j = (∑' n, (f n) i j) := by
    exact tsum_apply h_row_summable
  rw [h₁, h₂]

noncomputable local instance : NormedRing (Matrix m m 𝕂) := Matrix.linftyOpNormedRing
local instance : NormedAlgebra 𝕂 (Matrix m m 𝕂) := Matrix.linftyOpNormedAlgebra
local instance : CompleteSpace (Matrix m m 𝕂) := completeSpace_matrix

omit [IsAlgClosed 𝕂] [LinearOrder m] [LinearOrder 𝕂] [Fintype 𝕂] in
/-- Summability of the exponential series for matrices -/
private theorem summable_exp_series [CompleteSpace 𝕂] (A : Matrix m m 𝕂) :
  Summable (fun n => ((n.factorial : 𝕂)⁻¹) • (A ^ n)) := by
  letI : NormedAddCommGroup (Matrix m m 𝕂) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace 𝕂 (Matrix m m 𝕂) := Matrix.linftyOpNormedSpace
  exact NormedSpace.expSeries_summable' A

omit [IsAlgClosed 𝕂] [LinearOrder 𝕂] [Fintype 𝕂] in
private theorem isUpperTriangular_exp_of_isUpperTriangular
    {A : Matrix m m 𝕂} (hA : A.IsUpperTriangular) :
    (NormedSpace.exp 𝕂 A).IsUpperTriangular := by
  intro i j hij
  rw [NormedSpace.exp_eq_tsum]
  let exp_series := fun n ↦ ((n.factorial : 𝕂)⁻¹) • (A ^ n)
  change (∑' (n : ℕ), exp_series n) i j = 0
  rw [matrix_tsum_apply (summable_exp_series A) i j]
  apply tsum_eq_zero
  intro n
  have h_entry : (A ^ n) i j = 0 := by
    convert (IsUpperTriangular.pow hA n) hij
  simp [exp_series, smul_apply, h_entry]

omit [IsAlgClosed 𝕂] [LinearOrder 𝕂] [Fintype 𝕂] in
/--
For an upper–triangular matrix `A`, the `(i,i)` entry of the power `A ^ n`
is simply the `n`-th power of the original diagonal entry.
-/
private lemma diag_pow_entry_eq_pow_diag_entry {A : Matrix m m 𝕂}
    (hA : A.IsUpperTriangular) :
    ∀ n : ℕ, ∀ i : m, (A ^ n) i i = (A i i) ^ n := by
  intro n i
  have h := diag_pow_of_isUpperTriangular hA n
  calc (A ^ n) i i = ((A ^ n).diag) i := by simp [diag_apply]
    _ = (A.diag ^ n) i := by convert congrArg (fun d => d i) h
    _ = (A i i) ^ n   := by simp [Pi.pow_apply]

omit [IsAlgClosed 𝕂] [LinearOrder 𝕂] [Fintype 𝕂] in
/-- Each term in the matrix exponential series equals the corresponding scalar term on the diagonal -/
private lemma exp_series_diag_term_eq {A : Matrix m m 𝕂} (hA : A.IsUpperTriangular) (n : ℕ) (i : m) :
    ((n.factorial : 𝕂)⁻¹ • (A ^ n)) i i = (n.factorial : 𝕂)⁻¹ • (A i i) ^ n := by
  simp only [smul_apply]
  rw [diag_pow_entry_eq_pow_diag_entry hA n i]

 omit [IsAlgClosed 𝕂] [LinearOrder 𝕂] [Fintype 𝕂] in
/-- The diagonal of the matrix exponential series equals the scalar exponential series -/
private lemma matrix_exp_series_diag_eq_scalar_series {A : Matrix m m 𝕂} (hA : A.IsUpperTriangular)
    [CompleteSpace 𝕂] (i : m) :
    (∑' n, ((n.factorial : 𝕂)⁻¹ • (A ^ n)) i i) = ∑' n, (n.factorial : 𝕂)⁻¹ • (A i i) ^ n := by
  exact tsum_congr (exp_series_diag_term_eq hA · i)

omit [IsAlgClosed 𝕂] [LinearOrder 𝕂] [Fintype 𝕂] in
private theorem diag_exp_of_isUpperTriangular
    {A : Matrix m m 𝕂} (hA : A.IsUpperTriangular) :
    (NormedSpace.exp 𝕂 A).diag = fun i => NormedSpace.exp 𝕂 (A i i) := by
  funext i
  have exp_def : (NormedSpace.exp 𝕂 A) = ∑' (n : ℕ), (n.factorial : 𝕂)⁻¹ • (A ^ n) := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := 𝕂)]
  rw [exp_def, diag_apply]
  rw [matrix_tsum_apply (summable_exp_series A) i i]
  rw [matrix_exp_series_diag_eq_scalar_series hA i]
  rw [NormedSpace.exp_eq_tsum (𝕂 := 𝕂)]

-- Helper lemma for determinant of upper triangular matrices
omit [IsAlgClosed 𝕂] [LinearOrder 𝕂] [Fintype 𝕂] in
private lemma det_of_isUpperTriangular {A : Matrix m m 𝕂}
    (hA : A.IsUpperTriangular) : A.det = ∏ i, A i i := by
  exact Matrix.det_of_upperTriangular hA

-- Helper lemma for trace of upper triangular matrices
omit [IsAlgClosed 𝕂] [DecidableEq m] [LinearOrder 𝕂] [Fintype 𝕂]  in
private lemma trace_of_isUpperTriangular {A : Matrix m m 𝕂}
    (_hA : A.IsUpperTriangular) : A.trace = ∑ i, A i i := by
  rfl

omit [IsAlgClosed 𝕂] [DecidableEq m] [LinearOrder 𝕂] [Fintype 𝕂] [Fintype m]  in
-- Helper lemma for product of exponentials
private lemma Finset.prod_exp_eq_exp_sum (s : Finset m) (f : m → 𝕂) :
    ∏ i ∈ s, NormedSpace.exp 𝕂 (f i) = NormedSpace.exp 𝕂 (∑ i ∈ s, f i) := by
  letI : CompleteSpace 𝕂 := by infer_instance
  induction' s using Finset.induction with a s ha ih
  · simp [NormedSpace.exp_zero]
  · rw [Finset.prod_insert ha, Finset.sum_insert ha, NormedSpace.exp_add, ih]

omit [IsAlgClosed 𝕂] [LinearOrder m] [LinearOrder 𝕂] [Fintype 𝕂] in
/-- The trace is invariant under unitary conjugation. -/
private lemma trace_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    trace ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) = trace A := by
  have h :=
    trace_mul_cycle
      (A := (U : Matrix m m 𝕂))
      (B := A)
      (C := star (U : Matrix m m 𝕂))
  simpa [Matrix.mul_assoc,
        Matrix.one_mul] using h

omit [IsAlgClosed 𝕂] [LinearOrder m] [LinearOrder 𝕂] [Fintype 𝕂] in
/-- The determinant is invariant under unitary conjugation. -/
private lemma det_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    det ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) = det A := by
  have h_det_U : star (det (U : Matrix m m 𝕂)) * det (U : Matrix m m 𝕂) = 1 := by
    have h : star (U : Matrix m m 𝕂) * (U : Matrix m m 𝕂) = 1 :=
      UnitaryGroup.star_mul_self U
    have h_det := congrArg det h
    rw [det_mul, det_one] at h_det
    erw [det_conjTranspose] at h_det
    exact h_det
  calc
    det ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂))
        = det ((U : Matrix m m 𝕂) * A) * det (star (U : Matrix m m 𝕂)) := by
          exact det_mul ((U : Matrix m m 𝕂) * A) (star (U : Matrix m m 𝕂))
    _ = det (U : Matrix m m 𝕂) * det A * det (star (U : Matrix m m 𝕂)) := by
          rw [det_mul]
    _ = det (U : Matrix m m 𝕂) * det A * star (det (U : Matrix m m 𝕂)) := by
          rw [← det_mul, ← det_conjTranspose]; rfl
    _ = det A * (det (U : Matrix m m 𝕂) * star (det (U : Matrix m m 𝕂))) := by
          ring
    _ = det A * (star (det (U : Matrix m m 𝕂)) * det (U : Matrix m m 𝕂)) := by
          rw [mul_comm (det (U : Matrix m m 𝕂)) (star (det (U : Matrix m m 𝕂)))]
    _ = det A * 1 := by
          rw [h_det_U]
    _ = det A := by
          rw [mul_one]

omit [IsAlgClosed 𝕂] [LinearOrder 𝕂] [Fintype 𝕂] in
/-- Lie's trace formula for upper triangular matrices. -/
private theorem det_exp_of_isUpperTriangular {A : Matrix m m 𝕂} (hA : IsUpperTriangular A) :
    (NormedSpace.exp 𝕂 A).det = NormedSpace.exp 𝕂 A.trace := by
  have h_exp_upper : IsUpperTriangular (NormedSpace.exp 𝕂 A) :=
    isUpperTriangular_exp_of_isUpperTriangular hA
  rw [det_of_isUpperTriangular h_exp_upper, trace_of_isUpperTriangular hA]
  have h_diag_exp : (NormedSpace.exp 𝕂 A).diag = fun i => NormedSpace.exp 𝕂 (A i i) :=
    diag_exp_of_isUpperTriangular hA
  rw [← Finset.prod_exp_eq_exp_sum]
  exact congrArg Finset.univ.prod h_diag_exp

omit [LinearOrder 𝕂] [Fintype 𝕂] in
/-- The determinant of the exponential of a matrix is the exponential of its trace.
This is also known as **Lie's trace formula**. -/
theorem det_exp (A : Matrix m m 𝕂) :
    (NormedSpace.exp 𝕂 A).det = NormedSpace.exp 𝕂 A.trace := by
  let U := schurTriangulationUnitary A
  let T := schurTriangulation A
  have h_conj : A = U * T.val * star U := schur_triangulation A
  have h_trace_invariant : A.trace = T.val.trace := by
    simpa [h_conj] using trace_unitary_conj (A := T.val) U
  have h_exp_conj :
      NormedSpace.exp 𝕂 ((U : Matrix m m 𝕂) * T.val * star (U : Matrix m m 𝕂)) =
        (U : Matrix m m 𝕂) * NormedSpace.exp 𝕂 T.val * star (U : Matrix m m 𝕂) := by
    let Uu : (Matrix m m 𝕂)ˣ :=
      { val     := (U : Matrix m m 𝕂)
        inv     := star (U : Matrix m m 𝕂)
        val_inv := by
          simp
        inv_val := by
          simp}
    have h_units := Matrix.exp_units_conj (𝕂 := 𝕂) Uu T.val
    simpa [Uu] using h_units
  have h_det_invariant :
      (NormedSpace.exp 𝕂 A).det = (NormedSpace.exp 𝕂 T.val).det := by
    have h₁ : NormedSpace.exp 𝕂 A =
        (U : Matrix m m 𝕂) * NormedSpace.exp 𝕂 T.val * star (U : Matrix m m 𝕂) := by
      simpa [h_conj] using h_exp_conj
    have h₂ : (NormedSpace.exp 𝕂 A).det =
        det ((U : Matrix m m 𝕂) * NormedSpace.exp 𝕂 T.val * star (U : Matrix m m 𝕂)) := by
      simp [h₁]
    have h₃ :
        det ((U : Matrix m m 𝕂) * NormedSpace.exp 𝕂 T.val * star (U : Matrix m m 𝕂)) =
          (NormedSpace.exp 𝕂 T.val).det :=
      det_unitary_conj (NormedSpace.exp 𝕂 T.val) U
    simpa [h₂] using h₃
  have h_triangular_case :
      (NormedSpace.exp 𝕂 T.val).det = NormedSpace.exp 𝕂 T.val.trace :=
    det_exp_of_isUpperTriangular T.property
  simp [h_det_invariant, h_trace_invariant, h_triangular_case]

end DetExp

end Matrix
