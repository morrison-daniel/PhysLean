/-
Copyright (c) 2025 Afiq Hatta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Afiq Hatta
-/
import PhysLean.QuantumMechanics.OneDimension.Operators.Parity
import PhysLean.QuantumMechanics.OneDimension.Operators.Momentum
import PhysLean.QuantumMechanics.OneDimension.Operators.Position
import PhysLean.SpaceAndTime.Space.VectorIdentities
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.Mathematics.Trigonometry.Tanh
import PhysLean.Meta.Linters.Sorry
/-!

# 1d Reflectionless Potential

The quantum reflectionless potential in 1d.
This file contains
- the definition of the reflectionless potential as defined https://arxiv.org/pdf/2411.14941
- properties of reflectionless potentials

## TODO
- Define creation and annihilation operators for reflectionless potentials
- Write the proof of the general solution of the reflectionless potential using the creation and
annihilation operators
- Show reflectionless properties
-/

namespace QuantumMechanics
open Real
open Space
open SchwartzMap
open HilbertSpace
open NNReal
open Field
namespace OneDimension

/-- A reflectionless potential is specified by three
  real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, the
  parameter `κ`, as well as a positive integer family number `N`.
  All of these parameters are assumed to be positive. --/
structure ReflectionlessPotential where
  /-- mass of the particle -/
  m : ℝ
  /-- parameter of the reflectionless potential -/
  κ : ℝ
  /-- Planck's constant -/
  ℏ : ℝ
  /-- family number, positive integer -/
  N : ℕ
  m_pos : 0 < m -- mass of the particle is positive
  κ_pos : 0 < κ -- parameter of the reflectionless potential is positive
  N_pos : 0 < N -- family number is positive
  ℏ_pos : 0 < ℏ -- Planck's constant is positive

namespace ReflectionlessPotential

variable (Q : ReflectionlessPotential)

/-!
## Theorems
TODO: Add theorems about reflectionless potential - the main result is the actual 1d solution
-/

/-- Define the reflectionless potential as
  V(x) = - (ℏ^2 * κ^2 * N * (N + 1)) / (2 * m * (cosh (κ * x)) ^ 2) --/
noncomputable def reflectionlessPotential (x : ℝ) : ℝ :=
  - (Q.ℏ^2 * Q.κ^2 * Q.N * (Q.N + 1)) / ((2 : ℝ) * Q.m * (Real.cosh (Q.κ * x)) ^ 2)

/-- Define tanh(κ X) operator -/
noncomputable def tanhOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => Real.tanh (Q.κ * x) * ψ x

/-- Pointwise multiplication by a function of temperate growth -/
noncomputable def mulByTemperateGrowth {g : ℝ → ℂ} (hg : g.HasTemperateGrowth) :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hg

-- First, you need a theorem that the scaled tanh has temperate growth
theorem scaled_tanh_hasTemperateGrowth (κ : ℝ) :
    Function.HasTemperateGrowth (fun x => (Real.tanh (κ * x))) := by
  exact tanh_const_mul_hasTemperateGrowth κ

-- Scaled tanh embedded into the complex numbers has temperate growth
@[sorryful]
theorem scaled_tanh_complex_hasTemperateGrowth (κ : ℝ) :
    Function.HasTemperateGrowth (fun x => (Real.tanh (κ * x) : ℂ)) := by
  sorry

/-- Define tanh(κ X) multiplication pointwise as a Schwartz map -/
@[sorryful]
noncomputable def tanhOperatorSchwartz (Q : ReflectionlessPotential) :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := by
  -- We need to handle the Real → Complex coercion
  let scaled_tanh_complex : ℝ → ℂ := fun x => (Real.tanh (Q.κ * x) : ℂ)
  have h2 : Function.HasTemperateGrowth scaled_tanh_complex :=
    scaled_tanh_complex_hasTemperateGrowth Q.κ
  exact bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) h2

/-- Creation operator: a† as defined in https://arxiv.org/pdf/2411.14941
  a† = 1/√(2m) (P + iℏκ tanh(κX)) -/
noncomputable def creationOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  let factor : ℝ := 1 / Real.sqrt (2 * Q.m)
  fun x => factor * (momentumOperator ψ x + Complex.I * Q.ℏ * Q.κ * Q.tanhOperator ψ x)

/-- Annihilation operator: a as defined in https://arxiv.org/pdf/2411.14941
  a = 1/√(2m) (P - iℏκ tanh(κX)) -/
noncomputable def annihilationOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  let factor : ℝ := 1 / Real.sqrt (2 * Q.m)
  fun x => factor * (momentumOperator ψ x - Complex.I * Q.ℏ * Q.κ * Q.tanhOperator ψ x)

/-- creation operator defined as a Schwartz map -/
@[sorryful]
noncomputable def creationOperatorSchwartz (Q : ReflectionlessPotential) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)
    where
  toFun ψ := (1 / Real.sqrt (2 * Q.m)) • momentumOperatorSchwartz ψ +
    ((Complex.I * Q.ℏ * Q.κ) / Real.sqrt (2 * Q.m)) • Q.tanhOperatorSchwartz ψ
  map_add' ψ1 ψ2 := by
    simp only [Nat.ofNat_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, map_add, smul_add,
      Complex.ofReal_mul]
    abel
  map_smul' ψ1 ψ2 := by
    simp only [Nat.ofNat_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, map_smul, Complex.ofReal_mul,
      RingHom.id_apply, smul_add]
    rw [smul_comm]
    nth_rewrite 1 [smul_comm ψ1 ((Complex.I * ↑Q.ℏ * ↑Q.κ) / (√2 * √Q.m))]
    rfl
  cont := by
    fun_prop

/-- annihilation operator defined as a Schwartz map -/
@[sorryful]
noncomputable def annihilationOperatorSchwartz (Q : ReflectionlessPotential) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)
    where
  toFun ψ := (1 / Real.sqrt (2 * Q.m)) • momentumOperatorSchwartz ψ -
    ((Complex.I * Q.ℏ * Q.κ) / Real.sqrt (2 * Q.m)) • Q.tanhOperatorSchwartz ψ
  map_add' ψ1 ψ2 := by
    simp only [Nat.ofNat_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, map_add, smul_add,
      Complex.ofReal_mul]
    abel
  map_smul' ψ1 ψ2 := by
    simp only [Nat.ofNat_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, map_smul, Complex.ofReal_mul,
      RingHom.id_apply]
    rw [smul_sub, smul_comm]
    nth_rewrite 1 [smul_comm ψ1 ((Complex.I * ↑Q.ℏ * ↑Q.κ) / (√2 * √Q.m))]
    rfl
  cont := by
    fun_prop

end ReflectionlessPotential
end OneDimension
end QuantumMechanics
