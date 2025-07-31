/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import PhysLean.Mathematics.DataStructures.Matrix.SchurTriangulation

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
namespace IsUpperTriangular
variable {α k n R 𝕂 m : Type*}
variable [LinearOrder n][CommRing α]
variable [SMulZeroClass R α]

/-- Scalar multiplication preserves the property of being upper-triangular. -/
lemma smul
    {A : Matrix n n α} (hA : IsUpperTriangular A) (k : R) :
    IsUpperTriangular (k • A) := by
  intro i j hij
  simp [smul_apply, hA hij]

/-- The identity matrix is upper-triangular. -/
lemma one  : IsUpperTriangular (1 : Matrix n n α) := by
  intro i j hij
  simp [one_apply, (ne_of_lt hij).symm];
  intro a
  subst a
  simp_all only [id_eq, lt_self_iff_false]

variable [Fintype n]
variable [SMulZeroClass R α]

/-- The product of two upper-triangular matrices is upper-triangular. -/
lemma mul  {A B : Matrix n n α}
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
lemma pow  {A : Matrix n n α}
    (hA : IsUpperTriangular A) (k : ℕ) : IsUpperTriangular (A ^ k) := by
  induction k with
  | zero =>
      rw [pow_zero]
      exact one
  | succ k ih =>
      rw [pow_succ]
      exact IsUpperTriangular.mul ih hA

lemma diag_mul_of {A B : Matrix n n α}
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

lemma diag_pow_of {A : Matrix n n α}
    (hA : IsUpperTriangular A) (k : ℕ) : (A ^ k).diag = A.diag ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, pow_zero]
      ext i
      simp [diag_one]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      have h_mul : (A ^ k * A).diag = (A ^ k).diag * A.diag :=
        diag_mul_of (pow hA k) hA
      rw [h_mul, ih]

end IsUpperTriangular

open scoped BigOperators Topology

instance [UniformSpace 𝕂] : UniformSpace (Matrix m n 𝕂) := by unfold Matrix; infer_instance

/-- If every term of a series is zero, then its sum is zero. -/
lemma tsum_eq_zero
    {β : Type*} [TopologicalSpace β] [AddCommMonoid β]
    {f : ℕ → β} (h : ∀ n, f n = 0) :
    (∑' n, f n) = 0 := by
  rw [← h Nat.zero]
  simp_all only [tsum_zero, Nat.zero_eq]

/-!
 ### The determinant of the matrix exponential
 -/
section DetExp

open IsUpperTriangular

variable [RCLike 𝕂]--[IsAlgClosed 𝕂] [Fintype m] [DecidableEq m] [LinearOrder m]
      --[LinearOrder 𝕂] [Fintype 𝕂]

/-- Apply a matrix `tsum` to a given entry.                                        -/
lemma matrix_tsum_apply
    {f : ℕ → Matrix m m 𝕂} (hf : Summable f) (i j : m) :
    (∑' n, f n) i j = ∑' n, (f n) i j := by
  have h_row_summable : Summable (fun n ↦ (f n) i) := by
    have h := Pi.summable.1 hf
    exact h i
  have h₁ : ((∑' n, f n) : Matrix m m 𝕂) i = (∑' n, (f n) i) := by
    exact tsum_apply hf
  have h₂ : ((∑' n, (f n) i) : m → 𝕂) j = (∑' n, (f n) i j) := by
    exact tsum_apply h_row_summable
  rw [h₁, h₂]

private lemma Finset.prod_exp_eq_exp_sum [LinearOrder m] (s : Finset m) (f : m → 𝕂) :
    ∏ i ∈ s, NormedSpace.exp 𝕂 (f i) = NormedSpace.exp 𝕂 (∑ i ∈ s, f i) := by
  letI : CompleteSpace 𝕂 := by infer_instance
  induction' s using Finset.induction with a s ha ih
  · simp [NormedSpace.exp_zero]
  · rw [Finset.prod_insert ha, Finset.sum_insert ha, NormedSpace.exp_add, ih]

variable [Fintype m] [LinearOrder m]

attribute [local instance] Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.instCompleteSpace

/-- Summability of the exponential series for matrices -/
lemma summable_exp_series [CompleteSpace 𝕂] (A : Matrix m m 𝕂) :
    Summable (fun n => ((n.factorial : 𝕂)⁻¹) • (A ^ n)) := by
  letI : NormedAddCommGroup (Matrix m m 𝕂) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace 𝕂 (Matrix m m 𝕂) := Matrix.linftyOpNormedSpace
  exact NormedSpace.expSeries_summable' A

lemma isUpperTriangular_exp_of_isUpperTriangular
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

/--
For an upper–triangular matrix `A`, the `(i,i)` entry of the power `A ^ n`
is simply the `n`-th power of the original diagonal entry.
-/
lemma diag_pow_entry_eq_pow_diag_entry {A : Matrix m m 𝕂}
    (hA : A.IsUpperTriangular) :
    ∀ n : ℕ, ∀ i : m, (A ^ n) i i = (A i i) ^ n := by
  intro n i
  have h := diag_pow_of hA n
  calc (A ^ n) i i = ((A ^ n).diag) i := by simp [diag_apply]
    _ = (A.diag ^ n) i := by convert congrArg (fun d => d i) h
    _ = (A i i) ^ n   := by simp [Pi.pow_apply]

/-- Each term in the matrix exponential series equals the corresponding scalar term on the
diagonal -/
lemma exp_series_diag_term_eq {A : Matrix m m 𝕂} (hA : A.IsUpperTriangular)
    (n : ℕ) (i : m) :
    ((n.factorial : 𝕂)⁻¹ • (A ^ n)) i i = (n.factorial : 𝕂)⁻¹ • (A i i) ^ n := by
  simp only [smul_apply]
  rw [diag_pow_entry_eq_pow_diag_entry hA n i]

/-- The diagonal of the matrix exponential series equals the scalar exponential series -/
lemma matrix_exp_series_diag_eq_scalar_series {A : Matrix m m 𝕂} (hA : A.IsUpperTriangular)
    (i : m) :
    (∑' n, ((n.factorial : 𝕂)⁻¹ • (A ^ n)) i i) = ∑' n, (n.factorial : 𝕂)⁻¹ • (A i i) ^ n := by
  exact tsum_congr (exp_series_diag_term_eq hA · i)

theorem diag_exp_of_isUpperTriangular
    {A : Matrix m m 𝕂} (hA : A.IsUpperTriangular) :
    (NormedSpace.exp 𝕂 A).diag = fun i => NormedSpace.exp 𝕂 (A i i) := by
  funext i
  have exp_def : (NormedSpace.exp 𝕂 A) = ∑' (n : ℕ), (n.factorial : 𝕂)⁻¹ • (A ^ n) := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := 𝕂)]
  rw [exp_def, diag_apply]
  rw [matrix_tsum_apply (summable_exp_series A) i i]
  rw [matrix_exp_series_diag_eq_scalar_series hA i]
  rw [NormedSpace.exp_eq_tsum (𝕂 := 𝕂)]

lemma det_of_isUpperTriangular {A : Matrix m m 𝕂}
    (hA : A.IsUpperTriangular) : A.det = ∏ i, A i i := by
  exact Matrix.det_of_upperTriangular hA

omit [LinearOrder m] in
lemma trace_of_isUpperTriangular {A : Matrix m m 𝕂} : A.trace = ∑ i, A i i := by
  rfl

/-- The trace is invariant under unitary conjugation. -/
lemma trace_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    trace ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) = trace A := by
  have h :=
    trace_mul_cycle
      (A := (U : Matrix m m 𝕂))
      (B := A)
      (C := star (U : Matrix m m 𝕂))
  simpa [Matrix.mul_assoc,
        Matrix.one_mul] using h

/-- The determinant is invariant under unitary conjugation. -/
lemma det_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
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

/-- Lie's trace formula for upper triangular matrices. -/
lemma det_exp_of_isUpperTriangular {A : Matrix m m 𝕂} (hA : IsUpperTriangular A) :
    (NormedSpace.exp 𝕂 A).det = NormedSpace.exp 𝕂 A.trace := by
  have h_exp_upper : IsUpperTriangular (NormedSpace.exp 𝕂 A) :=
    isUpperTriangular_exp_of_isUpperTriangular hA
  letI : LinearOrder m := by infer_instance
  rw [det_of_isUpperTriangular h_exp_upper];
  have h_diag_exp : (NormedSpace.exp 𝕂 A).diag = fun i => NormedSpace.exp 𝕂 (A i i) :=
    diag_exp_of_isUpperTriangular hA
  erw [← Finset.prod_exp_eq_exp_sum Finset.univ]
  exact congrArg Finset.univ.prod h_diag_exp

/-- The exponential of a matrix commutes with unitary conjugation. -/
lemma exp_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    NormedSpace.exp 𝕂 ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) =
      (U : Matrix m m 𝕂) * NormedSpace.exp 𝕂 A * star (U : Matrix m m 𝕂) := by
  let Uu : (Matrix m m 𝕂)ˣ :=
    { val     := (U : Matrix m m 𝕂)
      inv     := star (U : Matrix m m 𝕂)
      val_inv := by simp
      inv_val := by simp}
  have h_units := Matrix.exp_units_conj (𝕂 := 𝕂) Uu A
  simpa [Uu] using h_units

lemma det_exp_unitary_conj (A : Matrix m m 𝕂) (U : unitaryGroup m 𝕂) :
    (NormedSpace.exp 𝕂 ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂))).det =
    (NormedSpace.exp 𝕂 A).det := by
  have h_exp_conj := exp_unitary_conj A U
  have h₁ : NormedSpace.exp 𝕂 ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂)) =
      (U : Matrix m m 𝕂) * NormedSpace.exp 𝕂 A * star (U : Matrix m m 𝕂) := h_exp_conj
  have h₂ : (NormedSpace.exp 𝕂 ((U : Matrix m m 𝕂) * A * star (U : Matrix m m 𝕂))).det =
      det ((U : Matrix m m 𝕂) * NormedSpace.exp 𝕂 A * star (U : Matrix m m 𝕂)) := by
    simp [h₁]
  have h₃ :
      det ((U : Matrix m m 𝕂) * NormedSpace.exp 𝕂 A * star (U : Matrix m m 𝕂)) =
        (NormedSpace.exp 𝕂 A).det :=
    det_unitary_conj (NormedSpace.exp 𝕂 A) U
  simpa [h₂] using h₃

/-- The determinant of the exponential of a matrix is the exponential of its trace.
This is also known as **Lie's trace formula**. -/
theorem det_exp {𝕂 m : Type*} [RCLike 𝕂] [IsAlgClosed 𝕂] [Fintype m] [LinearOrder m]
    (A : Matrix m m 𝕂) :
    (NormedSpace.exp 𝕂 A).det = NormedSpace.exp 𝕂 A.trace := by
  let U := schurTriangulationUnitary A
  let T := schurTriangulation A
  have h_conj : A = U * T.val * star U := schur_triangulation A
  have h_trace_invariant : A.trace = T.val.trace := by
    simpa [h_conj] using trace_unitary_conj (A := T.val) U
  have h_det_invariant :
      (NormedSpace.exp 𝕂 A).det = (NormedSpace.exp 𝕂 T.val).det := by
    simpa [h_conj] using det_exp_unitary_conj T.val U
  have h_triangular_case :
      (NormedSpace.exp 𝕂 T.val).det = NormedSpace.exp 𝕂 T.val.trace :=
    det_exp_of_isUpperTriangular T.property
  simp [h_det_invariant, h_trace_invariant, h_triangular_case]

end DetExp

-- `Matrix.map` commutes with an absolutely convergent series.
lemma map_tsum {α β m n : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β]
    (f : α →+ β) (hf : Continuous f) {s : ℕ → Matrix m n α} (hs : Summable s) :
    (∑' k, s k).map f = ∑' k, (s k).map f := by
  let F : Matrix m n α →+ Matrix m n β := AddMonoidHom.mapMatrix f
  have hF : Continuous F := Continuous.matrix_map continuous_id hf
  exact (hs.hasSum.map F hF).tsum_eq.symm

attribute [local instance] Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.instCompleteSpace

lemma map_pow {α β m : Type*}
    [Fintype m] [DecidableEq m] [Semiring α] [Semiring β]
    (f : α →+* β) (A : Matrix m m α) (k : ℕ) :
    (A ^ k).map f = (A.map f) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.map_one]; all_goals aesop
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.map_mul, ih]

end Matrix

lemma NormedSpace.exp_map_algebraMap {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) :
    (exp ℝ A).map (algebraMap ℝ ℂ) = exp ℂ (A.map (algebraMap ℝ ℂ)) := by
  letI : SeminormedRing (Matrix n n ℝ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix n n ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℝ) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix n n ℝ) := inferInstance
  letI : SeminormedRing (Matrix n n ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix n n ℂ) := inferInstance
  simp only [exp_eq_tsum]
  have hs : Summable (fun k => (k.factorial : ℝ)⁻¹ • A ^ k) := by
    exact NormedSpace.expSeries_summable' A
  erw [Matrix.map_tsum (algebraMap ℝ ℂ).toAddMonoidHom RCLike.continuous_ofReal hs]
  apply tsum_congr
  intro k
  erw [Matrix.map_smul, Matrix.map_pow]
  all_goals aesop
section DetExp
namespace Matrix
/--
Lie's trace formula over ℝ: det(exp(A)) = exp(tr(A)) for any real matrix A.
This is proved by transferring the result from ℂ using the naturality of polynomial identities.
-/
theorem det_exp_real {n : Type*} [Fintype n] [LinearOrder n]
    (A : Matrix n n ℝ) : (NormedSpace.exp ℝ A).det = Real.exp A.trace := by
  let A_ℂ := A.map (algebraMap ℝ ℂ)
  have h_complex : (NormedSpace.exp ℂ A_ℂ).det = Complex.exp A_ℂ.trace := by
    haveI : IsAlgClosed ℂ := Complex.isAlgClosed
    rw [Complex.exp_eq_exp_ℂ, ← Matrix.det_exp]
  have h_trace_comm : A_ℂ.trace = (algebraMap ℝ ℂ) A.trace := by
    simp only [A_ℂ, trace, diag_map, map_sum]
    rfl
  have h_det_comm : (algebraMap ℝ ℂ) ((NormedSpace.exp ℝ A).det) = (NormedSpace.exp ℂ A_ℂ).det := by
    rw [@RingHom.map_det]
    rw [← NormedSpace.exp_map_algebraMap]
    rfl
  rw [← h_det_comm] at h_complex
  rw [h_trace_comm] at h_complex
  have h_exp_comm : Complex.exp ((algebraMap ℝ ℂ) A.trace) =
      (algebraMap ℝ ℂ) (Real.exp A.trace) := by
    erw [← Complex.ofReal_exp]
    simp_all only [Complex.coe_algebraMap, Algebra.id.map_eq_id, RingHom.id_apply,
      Complex.ofReal_exp, A_ℂ]
  rw [h_exp_comm] at h_complex
  exact Complex.ofReal_injective h_complex
