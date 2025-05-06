/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.ClassicalMechanics.Space.VectorIdentities
import PhysLean.ClassicalMechanics.Time.Basic
/-!
# Wave equation

The general wave equation.

-/

namespace ClassicalMechanics

open Space
open Time

/-- The general form of the wave equation where `c` is the propagation speed. -/
def WaveEquation (f : Time → Space d → EuclideanSpace ℝ (Fin d))
  (t : Time) (x : Space d) (c : ℝ) : Prop :=
  c^2 • Δ (f t) x - ∂ₜ (fun t => (∂ₜ (fun t => f t x) t)) t = 0

/-- A vector-valued plane wave travelling in the direction of `s` with propagation speed `c`. -/
noncomputable def PlaneWave (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
  (c : ℝ) (s : Space d) : Time → Space d → EuclideanSpace ℝ (Fin d) :=
  fun t x => f₀ (inner x s - c * t)

/-- The plane wave satisfies the wave equation. -/
theorem planeWave_isWave (c : ℝ) (s : Space d)
    (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (f₀' : ℝ →L[ℝ] EuclideanSpace ℝ (Fin d))
    (h' : ∀ x, HasFDerivAt f₀ f₀' x) :
    WaveEquation (PlaneWave f₀ c s) t x c := by
  unfold WaveEquation PlaneWave
  have hdt : ∂ₜ (fun t => f₀ (inner x s - c * t)) = fun t => -c • f₀' 1 := by
    unfold Time.deriv
    ext t i
    change fderiv ℝ (f₀ ∘ fun t => (inner x s - c * t)) t 1 i = _
    rw [fderiv_comp, fderiv_const_sub, fderiv_const_mul]
    simp only [fderiv_id', ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_smulₛₗ,
      RingHom.id_apply, ContinuousLinearMap.comp_id, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
      neg_mul, neg_inj, mul_eq_mul_left_iff]
    left
    rw [HasFDerivAt.fderiv (h' (inner x s - c * t))]
    repeat fun_prop
  conv_lhs =>
    enter [2, 1, t]
    rw [hdt]
  have hdt' : ∂ₜ (fun t => -c • f₀' 1) = 0 := by
    unfold Time.deriv
    ext t i
    rw [fderiv_const_smul]
    simp
    · fun_prop
  conv_lhs =>
    enter [2]
    rw [hdt']
  simp only [Pi.zero_apply, sub_zero, smul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    pow_eq_zero_iff]
  right
  unfold laplacian_vec laplacian coord basis Space.deriv
  simp only [EuclideanSpace.basisFun_apply]
  ext i
  have hdx (u v : Fin d) : (fun x' => fderiv ℝ (fun x => (inner (f₀ (inner x s - c * t))
  (EuclideanSpace.single u 1):ℝ)) x' (EuclideanSpace.single v 1))
  =
  fun x' => (inner (f₀' (inner s (EuclideanSpace.single v 1))) (EuclideanSpace.single u 1):ℝ) := by
    ext x'
    rw [fderiv_inner_apply]
    simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
      zero_add]
    conv_lhs =>
      enter [1]
      change fderiv ℝ (f₀ ∘ fun x => (inner x s - c * t)) x' (EuclideanSpace.single v 1)
    rw [fderiv_comp]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [HasFDerivAt.fderiv (h' (inner x' s - c * t))]
    have hdi : (fderiv ℝ (fun x => inner x s - c * t) x') (EuclideanSpace.single v 1)
    =
    inner s (EuclideanSpace.single v 1) := by
      rw [fderiv_sub]
      simp only [fderiv_const, Pi.zero_apply, sub_zero]
      rw [fderiv_inner_apply]
      simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, inner_zero_right,
        fderiv_id', ContinuousLinearMap.coe_id', id_eq, zero_add]
      rw [real_inner_comm]
      repeat fun_prop
      apply DifferentiableAt.inner
      repeat fun_prop
    rw [hdi]
    · fun_prop
    · apply DifferentiableAt.sub
      apply DifferentiableAt.inner
      repeat fun_prop
    · apply DifferentiableAt.comp
      · fun_prop
      · apply DifferentiableAt.sub
        apply DifferentiableAt.inner
        repeat fun_prop
    · fun_prop
  conv_lhs =>
    enter [2, i', 1, 2]
    rw [hdx]
  simp
