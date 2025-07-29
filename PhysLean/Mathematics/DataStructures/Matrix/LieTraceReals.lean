import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import PhysLean.Mathematics.DataStructures.Matrix.LieTrace
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic

open Matrix
namespace Matrix
-- `Matrix.map` commutes with an absolutely convergent series.
lemma map_tsum {α β m n : Type*} [Fintype m] [Fintype n]
    [AddCommMonoid α] [AddCommMonoid β] [TopologicalSpace α] [TopologicalSpace β]
    [ContinuousAdd α] [ContinuousAdd β] [T2Space α] [T2Space β]
    (f : α →+ β) (hf : Continuous f) {s : ℕ → Matrix m n α} (hs : Summable s) :
    (∑' k, s k).map f = ∑' k, (s k).map f := by
  let F : Matrix m n α →+ Matrix m n β := AddMonoidHom.mapMatrix f
  have hF : Continuous F := Continuous.matrix_map continuous_id hf
  have hs' : Summable (fun k => F (s k)) := hs.map F hF
  exact (hs.hasSum.map F hF).tsum_eq.symm
end Matrix

attribute [local instance] Matrix.linftyOpNormedAlgebra
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.instCompleteSpace

lemma Matrix.map_pow {α β m : Type*}
    [Fintype m] [DecidableEq m] [Semiring α] [Semiring β]
    (f : α →+* β) (A : Matrix m m α) (k : ℕ) :
    (A ^ k).map f = (A.map f) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.map_one]; all_goals aesop
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.map_mul, ih]

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

/--
Lie's trace formula over ℝ: det(exp(A)) = exp(tr(A)) for any real matrix A.
This is proved by transferring the result from ℂ using the naturality of polynomial identities.
-/
lemma Matrix.det_exp_real {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n]
    (A : Matrix n n ℝ) : (NormedSpace.exp ℝ A).det = Real.exp A.trace := by
  let A_ℂ := A.map (algebraMap ℝ ℂ)
  have h_complex : (NormedSpace.exp ℂ A_ℂ).det = Complex.exp A_ℂ.trace := by
    haveI : IsAlgClosed ℂ := Complex.isAlgClosed
    rw [@det_exp]; rw [← Complex.exp_eq_exp_ℂ]
  have h_trace_comm : A_ℂ.trace = (algebraMap ℝ ℂ) A.trace := by
    simp only [A_ℂ, trace, diag_map, map_sum]
    rfl
  have h_det_comm : (algebraMap ℝ ℂ) ((NormedSpace.exp ℝ A).det) = (NormedSpace.exp ℂ A_ℂ).det := by
    rw [@RingHom.map_det]
    rw [← NormedSpace.exp_map_algebraMap]
    rfl
  rw [← h_det_comm] at h_complex
  rw [h_trace_comm] at h_complex
  have h_exp_comm : Complex.exp ((algebraMap ℝ ℂ) A.trace) = (algebraMap ℝ ℂ) (Real.exp A.trace) := by
    erw [← Complex.ofReal_exp]
    simp_all only [Complex.coe_algebraMap, Algebra.id.map_eq_id, RingHom.id_apply, Complex.ofReal_exp, A_ℂ]
  rw [h_exp_comm] at h_complex
  exact Complex.ofReal_injective h_complex
