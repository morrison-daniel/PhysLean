/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.Electromagnetism.Homogeneous
import PhysLean.ClassicalMechanics.WaveEquation.Basic
import Mathlib.LinearAlgebra.CrossProduct
/-!
# Electromagnetism wave equation

The electromagnetic wave eqaution as a consequence of the charge and current free
Maxwell's Equations in homogeneous isotropic medium.

-/

namespace Electromagnetism

open Space
open Time
open ClassicalMechanics

variable (OM : OpticalMedium)

local notation "ε" => OM.ε
local notation "μ" => OM.μ

/-- The electromagnetic wave equation for electric field. -/
theorem waveEquation_electricField_of_freeMaxwellEquations
    (E : ElectricField) (B : MagneticField) (h : OM.FreeMaxwellEquations E B)
    (hE : ContDiff ℝ 2 ↿E) (hB : ContDiff ℝ 2 ↿B) :
    WaveEquation E t x (Real.sqrt (μ • ε)⁻¹) := by
  rw [WaveEquation, Real.sq_sqrt]
  have hdt : ∀ t, (∂ₜ (fun t => E t x) t) = (μ • ε)⁻¹ • (∇ × B t) x := by
    intro t
    rw [OM.ampereLaw_of_free E B]
    · simp [← smul_assoc, mul_assoc, OM.mu_ge_zero, ne_of_gt, OM.eps_ge_zero]
    · exact h
  have hdt2 : ∂ₜ (fun t => ∂ₜ (fun t => E t x) t) t =
      ∂ₜ (fun t => (μ • ε)⁻¹ • (∇ × B t) x) t := by aesop
  rw [hdt2]
  have hd0 : (∇ ⬝ (E t)) = 0 := by
    ext x
    simp [funext, Pi.zero_apply, OM.gaussLawElectric_of_free E B, h]
  have hlpE : Δ (E t) = - ((fun x => ∇ (∇ ⬝ (E t)) - Δ (E t)) x) := by simp [hd0]
  rw [hlpE, ← curl_of_curl]
  have hcE : curl (E t) = fun x => - ∂ₜ (fun t => B t x) t := by
    funext x
    simp [OM.faradayLaw_of_free E B, h]
  rw [hcE]
  have hcn : curl (fun x => -∂ₜ (fun t => B t x) t) =
      - curl (fun x => ∂ₜ (fun t => B t x) t) := by
    trans - (1:ℝ) • curl (fun x => ∂ₜ (fun t => B t x) t)
    rw [← curl_smul, neg_smul, one_smul]
    rfl
    · exact fun x ↦ fderiv_curry_differentiableAt_fst_comp_snd (hf := hB) ..
    · exact neg_one_smul ..
  simp only [hcn, smul_eq_mul, mul_inv_rev, Pi.neg_apply, neg_neg]
  rw [← time_deriv_curl_commute]
  have hdt_smul : ∂ₜ (fun t => (OM.ε⁻¹ * OM.μ⁻¹) • curl (B t) x) t =
      (OM.ε⁻¹ * OM.μ⁻¹) • ∂ₜ (fun t => curl (B t) x) t := by
    rw [deriv_smul]
    unfold curl Space.deriv coord basis
    simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
      EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    apply differentiable_pi''
    intro i _
    fin_cases i <;>
    apply DifferentiableAt.sub <;>
    exact differentiableAt_fderiv_coord_single B hB
  rw [hdt_smul, sub_self]
  · exact hB
  · exact hE.uncurry ..
  · rw [inv_nonneg]
    exact smul_nonneg (le_of_lt OM.mu_ge_zero) (le_of_lt OM.eps_ge_zero)

/-- The electromagnetic wave equation for magnetic field. -/
theorem waveEquation_magneticField_of_freeMaxwellEquations
    (E : ElectricField) (B : MagneticField) (h : OM.FreeMaxwellEquations E B)
    (hE : ContDiff ℝ 2 ↿E) (hB : ContDiff ℝ 2 ↿B) :
    WaveEquation B t x (Real.sqrt (μ • ε)⁻¹) := by
  rw [WaveEquation, Real.sq_sqrt]
  have hdt : ∀ t, (∂ₜ (fun t => B t x) t) = - (∇ × E t) x := by
    intro t
    rwa [OM.faradayLaw_of_free E B, neg_neg]
  have hdt2 : ∂ₜ (fun t => ∂ₜ (fun t => B t x) t) t =
      - ∂ₜ (fun t => (∇ × E t) x) t := by
    trans - (1:ℝ) • ∂ₜ (fun t => (∇ × E t) x) t
    rw [← deriv_smul]
    simp only [neg_smul, one_smul]
    congr
    funext t
    rw [hdt]
    · unfold curl Space.deriv coord basis
      simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
        EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      apply differentiable_pi''
      intro i t
      fin_cases i <;>
      · simp only [Fin.isValue]
        apply DifferentiableAt.sub <;>
        exact differentiableAt_fderiv_coord_single E hE
    simp
  rw [hdt2]
  have hd0 : (∇ ⬝ (B t)) = 0 := by
    ext x
    simp [Pi.zero_apply, OM.gaussLawMagnetic_of_free E B, h]
  have hlpB : Δ (B t) = - ((fun x => ∇ (∇ ⬝ (B t)) - Δ (B t)) x) := by simp [hd0]
  rw [hlpB, ← curl_of_curl]
  have hcB : curl (B t) = OM.μ • OM.ε • fun x => ∂ₜ (fun t => E t x) t := by
    funext x
    rw [OM.ampereLaw_of_free E B]
    · rfl
    · exact h
  rw [hcB]
  have hcn : (OM.μ • OM.ε)⁻¹ • (-(fun x =>
      curl (OM.μ • OM.ε • fun x => ∂ₜ (fun t => E t x) t)) x) x =
      - curl (fun x => ∂ₜ (fun t => E t x) t) x := by
    simp only [smul_eq_mul, mul_inv_rev, Pi.neg_apply, smul_neg, neg_inj]
    change ((OM.ε⁻¹ * OM.μ⁻¹) • (curl (OM.μ • OM.ε • fun x => ∂ₜ (fun t => E t x) t))) x = _
    rw [← curl_smul]
    simp only [← smul_assoc, smul_eq_mul, mul_assoc, ne_eq, OM.mu_ge_zero, ne_of_gt,
      not_false_eq_true, inv_mul_cancel_left₀, OM.eps_ge_zero, inv_mul_cancel₀, one_smul]
    · unfold Time.deriv
      rw [← smul_assoc]
      change Differentiable ℝ (fun x => (OM.μ • OM.ε) • (fderiv ℝ (fun t => E t x) t) 1)
      apply Differentiable.const_smul
      apply fderiv_curry_differentiableAt_fst_comp_snd (hf := hE)
  rw [time_deriv_curl_commute, hcn, sub_self]
  · exact hE
  · exact hB.uncurry (x := t)
  · rw [inv_nonneg]
    exact smul_nonneg (le_of_lt OM.mu_ge_zero) (le_of_lt OM.eps_ge_zero)

/-- A electric plane wave travelling in the direction of `s` with propagation speed `c`. -/
@[nolint unusedArguments]
noncomputable def electricPlaneWave (E₀ : ℝ → EuclideanSpace ℝ (Fin 3))
    (c : ℝ) (s : Space) (hs : inner s s = (1:ℝ)) : ElectricField :=
    planeWave E₀ c s hs

/-- A magnetic plane wave travelling in the direction of `s` with propagation speed `c`. -/
@[nolint unusedArguments]
noncomputable def magneticPlaneWave (B₀ : ℝ → EuclideanSpace ℝ (Fin 3))
    (c : ℝ) (s : Space) (hs : inner s s = (1:ℝ)) : MagneticField :=
    planeWave B₀ c s hs

open Matrix

lemma wave_fderiv_inner_coord_sub {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {s : Space} {u v : Fin 3}
    {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)} (h' : ∀ x, HasFDerivAt f₀ (f₀' x) x) :
    c * ((fun x' => (fderiv ℝ (fun x => inner (f₀ (inner x s - c * t))
    (EuclideanSpace.single u 1)) x') (EuclideanSpace.single v 1)) x -
    (fun x' => (fderiv ℝ (fun x => inner (f₀ (inner x s - c * t))
    (EuclideanSpace.single v 1)) x') (EuclideanSpace.single u 1)) x)
    =
    s u * ∂ₜ (fun t => f₀ (inner x s - c * t)) t v -
    s v * ∂ₜ (fun t => f₀ (inner x s - c * t)) t u := by
  rw [wave_dx h', wave_dx h', wave_dt h']
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, EuclideanSpace.single_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, PiLp.smul_apply,
    smul_eq_mul, neg_mul, mul_neg, sub_neg_eq_add]
  rw [← mul_one (s u), ← smul_eq_mul (s u), ContinuousLinearMap.map_smul]
  rw [← mul_one (s v), ← smul_eq_mul (s v), ContinuousLinearMap.map_smul]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_one]
  ring

lemma dt_electricPlaneWave_eq_s_cross_dt_B (E₀ : ℝ → EuclideanSpace ℝ (Fin 3))
    (E₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)) (s : Space) (hc : c = (Real.sqrt (μ • ε)⁻¹))
    (hs : inner s s = (1:ℝ)) (E : ElectricField) (B : MagneticField)
    (hE : E = electricPlaneWave E₀ c s hs) (h' : ∀ x, HasFDerivAt E₀ (E₀' x) x)
    (hm : OM.FreeMaxwellEquations E B) :
    (Real.sqrt (μ • ε)⁻¹) • ∂ₜ (fun t => B t x) t = (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (WithLp.equiv _ _ s ×₃ WithLp.equiv _ _ (∂ₜ (fun t => E t x) t)) := by
  rw [crossProduct, ← neg_neg (∂ₜ (fun t => B t x) t),
      ← OM.faradayLaw_of_free E B, hE, electricPlaneWave, ← hc]
  unfold planeWave curl coord basis Space.deriv
  ext i
  fin_cases i <;>
  · simp [-PiLp.inner_apply]
    rw [wave_fderiv_inner_coord_sub h']
  exact hm

lemma dt_mageneticPlaneWave_eq_s_cross_neg_dt_E (B₀ : ℝ → EuclideanSpace ℝ (Fin 3))
    (B₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3)) (s : Space) (hc : c = (Real.sqrt (μ • ε)⁻¹))
    (hs : inner s s = (1:ℝ)) (E : ElectricField) (B : MagneticField)
    (hB : B = magneticPlaneWave B₀ c s hs) (h' : ∀ x, HasFDerivAt B₀ (B₀' x) x)
    (hm : OM.FreeMaxwellEquations E B) :
    (Real.sqrt (μ • ε)) • ∂ₜ (fun t => E t x) t = - (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (WithLp.equiv _ _ s ×₃ WithLp.equiv _ _ (∂ₜ (fun t => B t x) t)) := by
  have h : (Real.sqrt (μ • ε)) = (Real.sqrt (μ • ε)⁻¹) • (μ • ε) := by
    nth_rewrite 3 [← Real.sq_sqrt (le_of_lt (smul_pos OM.mu_ge_zero OM.eps_ge_zero))]
    rw [pow_two, Real.sqrt_inv]
    simp [← mul_assoc]
  have hdt : ∀ t, (∂ₜ (fun t => E t x) t) = (μ • ε)⁻¹ • (∇ × B t) x := by
    intro t
    rw [OM.ampereLaw_of_free E B]
    simp only [smul_eq_mul, _root_.mul_inv_rev, ← smul_assoc, mul_assoc, ne_eq, OM.mu_ge_zero,
      ne_of_gt, not_false_eq_true, inv_mul_cancel_left₀, OM.eps_ge_zero, inv_mul_cancel₀, one_smul]
    exact hm
  rw [crossProduct, h, smul_assoc, hdt, hB, magneticPlaneWave, ← hc]
  unfold planeWave curl coord basis Space.deriv
  ext i
  fin_cases i <;>
  · simp [-PiLp.inner_apply, ← mul_assoc, OM.mu_ge_zero, OM.eps_ge_zero, ne_of_gt]
    rw [wave_fderiv_inner_coord_sub h']

theorem electricPlaneWave_eq_s_cross_B (E : ElectricField) (B : MagneticField) :
    (Real.sqrt (μ • ε)⁻¹) • (B t x) = (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (WithLp.equiv _ _ s ×₃ WithLp.equiv _ _ (E t x)) := by
  sorry

theorem mageneticPlaneWave_eq_s_cross_neg_E (E : ElectricField) (B : MagneticField) :
    (Real.sqrt (μ • ε)⁻¹) • (E t x) = (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (WithLp.equiv _ _ s ×₃ WithLp.equiv _ _ (B t x)) := by
  sorry

/-

0. Prove the two theorems above by integrating with respect to t
1. E B s form an orthogonal triad
2. Define MulAction SO(d) on Space d
3. wave equation is invariant under MulAction SO(3)
4. It is justified to assume propagation direction in z (s = (EuclideanSpace.single 2 1))
    and ElectricField lies in xy-plane

-/
