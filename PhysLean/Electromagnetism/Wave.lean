/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.Electromagnetism.Homogeneous
/-!
# Electromagnetism wave equation

The electromagnetic wave eqaution as a consequence of the charge and current free
Maxwell's Equations in homogeneous isotropic medium.

-/

namespace Electromagnetism

open Space
open Time
open ClassicalMechanics

/-- The general form of the wave equation. -/
def WaveEquation (f : Time → Space d → EuclideanSpace ℝ (Fin d))
    (t : Time) (x : Space d) (c : ℝ) : Prop :=
    c^2 • Δ (f t) x -  ∂ₜ (fun t => (∂ₜ (fun t => f t x) t)) t  = 0

variable (OM : OpticalMedium)

local notation "ε" => OM.ε
local notation "μ" => OM.μ

/-- The electromagnetic wave equation. -/
theorem ElectroMagneticWave (E : ElectricField) (B : MagneticField)
    (h : OM.FreeMaxwellEquations E B)
    (hE : ContDiff ℝ 2 ↿E) (hB : ContDiff ℝ 2 ↿B) :
    WaveEquation E t x (Real.sqrt (μ • ε)⁻¹) := by
  rw [WaveEquation]
  rw [Real.sq_sqrt]
  have hdt : ∀ t, (∂ₜ (fun t => E t x) t) = (μ • ε)⁻¹ • (∇ × B t) x := by
    intro t
    rw [OM.ampereLaw_of_free E B]
    simp only [smul_eq_mul, mul_inv_rev, ← smul_assoc, mul_assoc, ne_eq, OM.mu_ge_zero, ne_of_gt,
      not_false_eq_true, inv_mul_cancel_left₀, OM.eps_ge_zero, inv_mul_cancel₀, one_smul]
    exact h
  have hdt2 : ∂ₜ (fun t => ∂ₜ (fun t => E t x) t) t =
      ∂ₜ (fun t => (μ • ε)⁻¹ • (∇ × B t) x) t := by
    congr
    funext t
    rw [hdt]
  rw [hdt2]
  have hd0 : (∇ ⬝ (E t)) = 0 := by
    ext x
    simp only [Pi.zero_apply]
    rw [OM.gaussLawElectric_of_free E B]
    exact h
  have hlpE : Δ (E t) = - ((fun x => ∇ (∇ ⬝ (E t)) - Δ (E t)) x) := by
    simp only [hd0, grad_zero, zero_sub, neg_neg]
  rw [hlpE]
  rw [← curl_of_curl]
  have hcE : curl (E t) = fun x => - ∂ₜ (fun t => B t x) t := by
    funext x
    rw [OM.faradayLaw_of_free E B]
    exact h
  rw [hcE]
  have hcn : curl (fun x => -∂ₜ (fun t => B t x) t) =
      - curl (fun x => ∂ₜ (fun t => B t x) t) := by
    trans - (1:ℝ) • curl (fun x => ∂ₜ (fun t => B t x) t)
    rw [← curl_smul]
    simp only [neg_smul, one_smul]
    rfl
    · unfold Time.deriv
      intro x
      apply fderiv_curry_differentiableAt_fst_comp_snd (hf := hB)
    simp
  rw [hcn]
  simp only [smul_eq_mul, mul_inv_rev, Pi.neg_apply, neg_neg]
  rw [← time_deriv_curl_commute]
  have hdt_smul : ∂ₜ (fun t => (OM.ε⁻¹ * OM.μ⁻¹) • curl (B t) x) t =
      (OM.ε⁻¹ * OM.μ⁻¹) • ∂ₜ (fun t => curl (B t) x) t := by
    rw [deriv_smul]
    · unfold curl Space.deriv coord basis
      simp only [Fin.isValue, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
        EuclideanSpace.single_apply, RCLike.inner_apply, conj_trivial, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      apply differentiable_pi''
      intro i t
      fin_cases i <;>
      · simp only [Fin.isValue]
        apply DifferentiableAt.sub
        repeat
          apply differentiableAt_fderiv_coord_single
          exact hB
  rw [hdt_smul]
  rw [sub_self]
  exact hB
  exact hE.uncurry (x := t)
  rw [inv_nonneg]
  exact smul_nonneg (le_of_lt OM.mu_ge_zero) (le_of_lt OM.eps_ge_zero)
