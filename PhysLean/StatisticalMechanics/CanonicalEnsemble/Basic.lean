/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Thermodynamics.Temperature.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Calculus.ParametricIntegral
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Meta.Linters.Sorry
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.Prod
/-!

# Canonical Ensemble: General Theory

A canonical ensemble describes a physical system in thermal equilibrium with a heat bath at a
fixed temperature.

In this file we define the canonical ensemble, its partition function, the
probability of being in a given microstate, the mean energy, the entropy and
the Helmholtz free energy

We also define the addition of two canonical ensembles, and prove results related
to the properties of additions of canonical ensembles

We develop a general measure-theoretic framework designed to be applicable to both classical
continuous systems (like an ideal gas) and discrete systems (like a spin lattice).

## The Semi-Classical Framework

In classical statistical mechanics quantities like the partition function and entropy must be
dimensionless to be physically meaningful. A naive integration over a classical
phase space yields dimensionful quantities, leading to ambiguities (e.g., the Gibbs paradox).

Following the "semi-classical" approach (see references) we introduce a constant with
units of action (`phase_space_unit`, identified with Planck's constant `h`) and the number of
degrees of freedom (`dof`) to correctly normalize the phase space volume.

This file distinguishes between:
1.  **Mathematical quantities**: Raw results of integration over the given measure
    (e.g., `mathematicalPartitionFunction`, `differentialEntropy`).
2.  **Physical/Thermodynamic quantities**: Dimensionless, physically meaningful quantities derived
    from the mathematical ones using the semi-classical normalization
    (e.g., `partitionFunction`, `helmholtzFreeEnergy`, `thermodynamicEntropy`).

## Main Definitions

- `CanonicalEnsemble`: The core structure, including `energy`, `dof`, and `phase_space_unit`.
- `mathematicalPartitionFunction`: The raw integral of the Boltzmann factor, `∫ exp(-βE) dμ`.
- `partitionFunction`: The dimensionless physical partition function, `Z = Z_math / h^dof`.
- `probability`: The probability density function.
- `meanEnergy`: The expectation value of the energy.
- `differentialEntropy`: The entropy defined as `-k_B ∫ ρ log ρ dμ`, which can be negative.
- `helmholtzFreeEnergy`: The physical free energy `F = -k_B T log(Z)`.
- `thermodynamicEntropy`: The absolute physical entropy, defined via `S = (U - F) / T`.

## Key Theorems

- The relationship between the mathematical `helmholtzPotential` and the physical
  `helmholtzFreeEnergy`.
- The connection between `thermodynamicEntropy` and `differentialEntropy`, showing
  they differ by a constant related to the `phase_space_unit`.

## References
- L. D. Landau and E. M. Lifshitz, *Statistical Physics, Part 1*.
- https://www.damtp.cam.ac.uk/user/tong/statphys/statmechhtml/S1.html#E23.

-/

open MeasureTheory Real Temperature
open scoped Temperature

/-- A Canonical ensemble is described by a type `ι`, corresponding to the type of microstates,
and a map `ι → ℝ` which associates which each microstate an energy
and physical constants needed to define dimensionless thermodynamic quantities. -/
structure CanonicalEnsemble (ι : Type) [MeasurableSpace ι] : Type where
  /-- The energy of associated with a mircrostate of the canonical ensemble. -/
  energy : ι → ℝ
  /-- The number of degrees of freedom, used to make the partition function dimensionless.
  For a classical system of N particles in 3D, this is `3N`. For a system of N spins,
  this is typically `0` as the state space is already discrete. -/
  dof : ℕ
  /-- The unit of action used to make the phase space volume dimensionless.
  This constant is necessary to define an absolute (rather than relative) thermodynamic
  entropy. In the semi-classical approach, this unit is identified with Planck's constant `h`.
  For discrete systems with a counting measure, this unit should be set to `1`. -/
  phase_space_unit : ℝ := 1
  /-- Assumption that the phase space unit is positive. -/
  h_pos : 0 < phase_space_unit := by positivity
  energy_measurable : Measurable energy
  /-- The measure on the indexing set of microstates. -/
  μ : MeasureTheory.Measure ι := by volume_tac
  [μ_sigmaFinite : SigmaFinite μ]

namespace CanonicalEnsemble
open Real Temperature

variable {ι ι1 : Type} [MeasurableSpace ι]
  [MeasurableSpace ι1] (𝓒 : CanonicalEnsemble ι) (𝓒1 : CanonicalEnsemble ι1)

instance : SigmaFinite 𝓒.μ := 𝓒.μ_sigmaFinite

@[ext]
lemma ext {𝓒 𝓒' : CanonicalEnsemble ι} (h_energy : 𝓒.energy = 𝓒'.energy)
    (h_dof : 𝓒.dof = 𝓒'.dof) (h_h : 𝓒.phase_space_unit = 𝓒'.phase_space_unit)
    (h_μ : 𝓒.μ = 𝓒'.μ) : 𝓒 = 𝓒' := by
  cases 𝓒; cases 𝓒'; simp_all

@[fun_prop]
lemma energy_measurable' : Measurable 𝓒.energy := 𝓒.energy_measurable

/-- The addition of two `CanonicalEnsemble`. The degrees of freedom are added.
Note: This is only physically meaningful if the two systems share the same `phase_space_unit`. -/
noncomputable instance {ι1 ι2 : Type} [MeasurableSpace ι1] [MeasurableSpace ι2] :
    HAdd (CanonicalEnsemble ι1) (CanonicalEnsemble ι2)
    (CanonicalEnsemble (ι1 × ι2)) where
  hAdd := fun 𝓒1 𝓒2 => {
    energy := fun (i : ι1 × ι2) => 𝓒1.energy i.1 + 𝓒2.energy i.2
    dof := 𝓒1.dof + 𝓒2.dof
    phase_space_unit := 𝓒1.phase_space_unit
    h_pos := 𝓒1.h_pos
    μ := 𝓒1.μ.prod 𝓒2.μ
    energy_measurable := by fun_prop
  }

/-- The canonical ensemble with no microstates. -/
def empty : CanonicalEnsemble Empty where
  energy := isEmptyElim
  dof := 0
  μ := 0
  energy_measurable := by fun_prop

/-- Given a measurable equivalence `e : ι1 ≃ᵐ ι`, this is the corresponding canonical ensemble
on `ι1`. The physical properties (`dof`, `phase_space_unit`) are unchanged. -/
noncomputable def congr (e : ι1 ≃ᵐ ι) : CanonicalEnsemble ι1 where
  energy := fun i => 𝓒.energy (e i)
  dof := 𝓒.dof
  phase_space_unit := 𝓒.phase_space_unit
  h_pos := 𝓒.h_pos
  μ := 𝓒.μ.map e.symm
  energy_measurable := by
    apply Measurable.comp
    · fun_prop
    · exact MeasurableEquiv.measurable e
  μ_sigmaFinite := MeasurableEquiv.sigmaFinite_map e.symm

@[simp]
lemma congr_energy_comp_symmm (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).energy ∘ e.symm = 𝓒.energy := by
  funext i
  simp [congr]

/-- Scalar multiplication of `CanonicalEnsemble`, defined such that
`nsmul n 𝓒` represents `n` non-interacting, distinguishable copies of the ensemble `𝓒`. -/
noncomputable def nsmul (n : ℕ) (𝓒 : CanonicalEnsemble ι) : CanonicalEnsemble (Fin n → ι) where
  energy := fun f => ∑ i, 𝓒.energy (f i)
  dof := n * 𝓒.dof
  phase_space_unit := 𝓒.phase_space_unit
  h_pos := 𝓒.h_pos
  μ := MeasureTheory.Measure.pi fun _ => 𝓒.μ
  energy_measurable := by fun_prop

set_option linter.unusedVariables false in
/-- The microstates of a canonical ensemble. -/
@[nolint unusedArguments]
abbrev microstates (𝓒 : CanonicalEnsemble ι) : Type := ι

/-! ## Properties of physical parameters -/

@[simp]
lemma dof_add (𝓒1 : CanonicalEnsemble ι) (𝓒2 : CanonicalEnsemble ι1) :
    (𝓒1 + 𝓒2).dof = 𝓒1.dof + 𝓒2.dof := rfl

@[simp]
lemma phase_space_unit_add (𝓒1 : CanonicalEnsemble ι) (𝓒2 : CanonicalEnsemble ι1) :
    (𝓒1 + 𝓒2).phase_space_unit = 𝓒1.phase_space_unit := rfl

@[simp]
lemma dof_nsmul (n : ℕ) : (nsmul n 𝓒).dof = n * 𝓒.dof := rfl

@[simp]
lemma phase_space_unit_nsmul (n : ℕ) :
    (nsmul n 𝓒).phase_space_unit = 𝓒.phase_space_unit := rfl

@[simp]
lemma dof_congr (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).dof = 𝓒.dof := rfl

@[simp]
lemma phase_space_unit_congr (e : ι1 ≃ᵐ ι) :
    (𝓒.congr e).phase_space_unit = 𝓒.phase_space_unit := rfl

/-! ## The measure -/

lemma μ_add : (𝓒 + 𝓒1).μ = 𝓒.μ.prod 𝓒1.μ := rfl

lemma μ_nsmul (n : ℕ) : (nsmul n 𝓒).μ = MeasureTheory.Measure.pi fun _ => 𝓒.μ := rfl

lemma μ_nsmul_zero_eq : (nsmul 0 𝓒).μ = Measure.pi (fun _ => 0) := by
  simp [nsmul, μ_nsmul]
  congr
  funext x
  exact Fin.elim0 x

/-!

## The energy of the microstates

-/

@[simp]
lemma energy_add_apply (i : microstates (𝓒 + 𝓒1)) :
    (𝓒 + 𝓒1).energy i = 𝓒.energy i.1 + 𝓒1.energy i.2 := rfl

@[simp]
lemma energy_nsmul_apply (n : ℕ) (f : Fin n → microstates 𝓒) :
    (nsmul n 𝓒).energy f = ∑ i, 𝓒.energy (f i) := rfl

@[simp]
lemma energy_congr_apply (e : ι1 ≃ᵐ ι) (i : ι1) :
    (𝓒.congr e).energy i = 𝓒.energy (e i) := rfl

/-! ## Induction for nsmul -/

open MeasureTheory

lemma nsmul_succ (n : ℕ) [SigmaFinite 𝓒.μ] : nsmul n.succ 𝓒 = (𝓒 + nsmul n 𝓒).congr
    (MeasurableEquiv.piFinSuccAbove (fun _ => ι) 0) := by
  ext1
  · ext x
    simp only [Nat.succ_eq_add_one, energy_nsmul_apply, congr_energy_comp_symmm,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero, Fin.consEquiv_symm_apply,
      energy_add_apply, MeasurableEquiv.symm_apply_apply]
    exact Fin.sum_univ_succAbove (fun i => 𝓒.energy (x i)) 0
  · simp [Nat.succ_eq_add_one, Nat.succ_mul, dof_nsmul, add_comm, add_left_comm, add_assoc]
  · simp
  · refine Eq.symm (MeasureTheory.MeasurePreserving.map_eq ?_)
    refine MeasurePreserving.symm _ ?_
    exact MeasureTheory.measurePreserving_piFinSuccAbove (n := n) (fun _ => 𝓒.μ) 0

/-!

## Non zero nature of the measure

-/

instance [NeZero 𝓒.μ] [NeZero 𝓒1.μ] : NeZero (𝓒 + 𝓒1).μ := by
  simp [μ_add]
  refine { out := ?_ }
  rw [← @Measure.measure_univ_pos]
  have h1 : (𝓒.μ.prod (𝓒1.μ)) Set.univ =
      (𝓒.μ Set.univ) * (𝓒1.μ Set.univ) := by
    rw [← @Measure.prod_prod]
    simp
  rw [h1]
  exact NeZero.pos (𝓒.μ Set.univ * 𝓒1.μ Set.univ)

instance μ_neZero_congr [NeZero 𝓒.μ] (e : ι1 ≃ᵐ ι) :
    NeZero (𝓒.congr e).μ := by
  refine { out := ?_ }
  rw [← @Measure.measure_univ_pos]
  simp only [Measure.measure_univ_pos, ne_eq]
  refine (Measure.map_ne_zero_iff ?_).mpr ?_
  · fun_prop
  · exact Ne.symm (NeZero.ne' _)

instance [NeZero 𝓒.μ] (n : ℕ) : NeZero (nsmul n 𝓒).μ := by
  induction n with
  | zero =>
    rw [μ_nsmul_zero_eq]
    rw [@neZero_iff]
    simp only [ne_eq]
    refine Measure.measure_univ_ne_zero.mp ?_
    simp
  | succ n ih =>
    rw [nsmul_succ]
    infer_instance

/-!

## The Boltzmann measure

-/

/-- The Boltzmann measure on the space of microstates. -/
noncomputable def μBolt (T : Temperature) : MeasureTheory.Measure ι :=
  𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- T.β * 𝓒.energy i)))

instance (T : Temperature) : SigmaFinite (𝓒.μBolt T) :=
  inferInstanceAs
    (SigmaFinite (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β T * 𝓒.energy i)))))

@[simp]
lemma μBolt_add (T : Temperature) :
    (𝓒 + 𝓒1).μBolt T = (𝓒.μBolt T).prod (𝓒1.μBolt T) := by
  simp_rw [μBolt, μ_add]
  rw [MeasureTheory.prod_withDensity]
  congr
  funext i
  rw [← ENNReal.ofReal_mul, ← Real.exp_add]
  simp only [energy_add_apply, neg_mul]
  ring_nf
  · exact exp_nonneg _
  · fun_prop
  · fun_prop

lemma μBolt_congr (e : ι1 ≃ᵐ ι) (T : Temperature) : (𝓒.congr e).μBolt T =
    (𝓒.μBolt T).map e.symm := by
  simp [congr, μBolt]
  refine Measure.ext_of_lintegral _ fun φ hφ ↦ ?_
  rw [lintegral_withDensity_eq_lintegral_mul₀]
  rw [lintegral_map, lintegral_map, lintegral_withDensity_eq_lintegral_mul₀]
  congr
  funext i
  simp only [Pi.mul_apply, MeasurableEquiv.apply_symm_apply]
  repeat fun_prop

lemma μBolt_nsmul [SigmaFinite 𝓒.μ] (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).μBolt T = MeasureTheory.Measure.pi fun _ => (𝓒.μBolt T) := by
  induction n with
  | zero =>
    simp [nsmul, μBolt]
    congr
    funext x
    exact Fin.elim0 x
  | succ n ih =>
    rw [nsmul_succ, μBolt_congr]
    rw [μBolt_add]
    refine MeasurePreserving.map_eq ?_
    refine MeasurePreserving.symm _ ?_
    rw [ih]
    exact MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => 𝓒.μBolt T) 0

  lemma μBolt_ne_zero_of_μ_ne_zero (T : Temperature) (h : 𝓒.μ ≠ 0) :
    𝓒.μBolt T ≠ 0 := by
  simp [μBolt] at ⊢ h
  rw [Measure.ext_iff'] at ⊢ h
  simp only [Measure.coe_zero, Pi.zero_apply]
  have hs : {x | ENNReal.ofReal (rexp (-(↑T.β * 𝓒.energy x))) ≠ 0} = Set.univ := by
    ext i
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exp_pos _
  conv =>
    enter [1, s]
    rw [MeasureTheory.withDensity_apply_eq_zero' (by fun_prop), hs]
    simp
  simpa using h

instance (T : Temperature) [NeZero 𝓒.μ] : NeZero (𝓒.μBolt T) := by
  refine { out := ?_ }
  apply μBolt_ne_zero_of_μ_ne_zero
  exact Ne.symm (NeZero.ne' 𝓒.μ)

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [IsFiniteMeasure (𝓒1.μBolt T)] :
    IsFiniteMeasure ((𝓒 + 𝓒1).μBolt T) := by
  simp only [μBolt_add]; infer_instance

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] (n : ℕ) :
    IsFiniteMeasure ((nsmul n 𝓒).μBolt T) := by
  simp [μBolt_nsmul]; infer_instance

/-!

## The Mathematical Partition Function

-/

/-- The mathematical partition function, defined as the integral of the Boltzmann factor.
This quantity may have physical dimensions. See `CanonicalEnsemble.partitionFunction` for
the dimensionless physical version. -/
noncomputable def mathematicalPartitionFunction (T : Temperature) : ℝ := (𝓒.μBolt T).real Set.univ

lemma mathematicalPartitionFunction_eq_integral (T : Temperature) :
    mathematicalPartitionFunction 𝓒 T = ∫ i, exp (- T.β * 𝓒.energy i) ∂𝓒.μ := by
  trans ∫ i, 1 ∂𝓒.μBolt T
  · simp only [integral_const, smul_eq_mul, mul_one]
    rfl
  rw [μBolt]
  erw [integral_withDensity_eq_integral_smul]
  congr
  funext x
  simp [HSMul.hSMul, SMul.smul]
  · exact exp_nonneg _
  · fun_prop

lemma mathematicalPartitionFunction_add {T : Temperature} :
    (𝓒 + 𝓒1).mathematicalPartitionFunction T =
    𝓒.mathematicalPartitionFunction T * 𝓒1.mathematicalPartitionFunction T := by
  simp_rw [mathematicalPartitionFunction, μBolt_add]
  rw [← measureReal_prod_prod, Set.univ_prod_univ]

@[simp]
lemma mathematicalPartitionFunction_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).mathematicalPartitionFunction T = 𝓒.mathematicalPartitionFunction T := by
  rw [mathematicalPartitionFunction_eq_integral, mathematicalPartitionFunction_eq_integral]
  simp only [congr]
  rw [integral_map_equiv]
  simp

/-- The `mathematicalPartitionFunction_nsmul` function of `n` copies of a canonical ensemble. -/
lemma mathematicalPartitionFunction_nsmul (n : ℕ) (T : Temperature) :
    (nsmul n 𝓒).mathematicalPartitionFunction T = (𝓒.mathematicalPartitionFunction T) ^ n := by
  simp_rw [mathematicalPartitionFunction, μBolt_nsmul, measureReal_def, Measure.pi_univ]
  simp [ENNReal.toReal_prod]

lemma mathematicalPartitionFunction_nonneg (T : Temperature) :
    0 ≤ 𝓒.mathematicalPartitionFunction T := by
  rw [mathematicalPartitionFunction]; exact measureReal_nonneg

lemma mathematicalPartitionFunction_eq_zero_iff (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] :
    mathematicalPartitionFunction 𝓒 T = 0 ↔ 𝓒.μ = 0 := by
  simp [mathematicalPartitionFunction]
  rw [measureReal_def]
  rw [ENNReal.toReal_eq_zero_iff]
  simp only [measure_ne_top, or_false]
  rw [μBolt]
  rw [MeasureTheory.withDensity_apply_eq_zero']
  simp only [neg_mul, ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.inter_univ]
  let s : Set ι := {x | 0 < rexp (-(T.β * 𝓒.energy x))}
  have h : s = Set.univ := by
    ext i
    simp [s]
    exact exp_pos (-(T.β * 𝓒.energy i))
  change 𝓒.μ s = 0 ↔ 𝓒.μ = 0
  rw [h]
  simp only [Measure.measure_univ_eq_zero, s]
  fun_prop

open NNReal

lemma mathematicalPartitionFunction_comp_ofβ_apply (β : ℝ≥0) :
    𝓒.mathematicalPartitionFunction (ofβ β) =
    (𝓒.μ.withDensity (fun i => ENNReal.ofReal (exp (- β * 𝓒.energy i)))).real Set.univ := by
  simp only [mathematicalPartitionFunction, μBolt, β_ofβ, neg_mul]

/-- The partition function is strictly positive provided the underlying
measure is non-zero and the Boltzmann measure is finite. -/
lemma mathematicalPartitionFunction_pos (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    0 < 𝓒.mathematicalPartitionFunction T := by
  have hμ : 𝓒.μBolt T ≠ 0 := (NeZero.ne (𝓒.μBolt T))
  simp [mathematicalPartitionFunction]

open NNReal Constants

/-! ## The probability density -/

/-- The probability density function of the canonical ensemble.
Note: In the general measure-theoretic case, this is a density with respect to the
underlying measure `𝓒.μ` and is not necessarily less than or equal to 1. In the
case of a finite ensemble with the counting measure, this value corresponds to the
probability of the microstate. -/
noncomputable def probability (T : Temperature) (i : ι) : ℝ :=
  (exp (- T.β * 𝓒.energy i)) / 𝓒.mathematicalPartitionFunction T

/-! ## The probability measure -/

lemma probability_add {T : Temperature} (i : ι × ι1) :
    (𝓒 + 𝓒1).probability T i = 𝓒.probability T i.1 * 𝓒1.probability T i.2 := by
  simp [probability, mathematicalPartitionFunction_add, mul_add, Real.exp_add]
  ring

@[simp]
lemma probability_congr (e : ι1 ≃ᵐ ι) (T : Temperature) (i : ι1) :
    (𝓒.congr e).probability T i = 𝓒.probability T (e i) := by
  simp [probability]

lemma probability_nsmul (n : ℕ) (T : Temperature) (f : Fin n → ι) :
    (nsmul n 𝓒).probability T f = ∏ i, 𝓒.probability T (f i) := by
  induction n with
  | zero =>
    simp [probability, mathematicalPartitionFunction_nsmul]
  | succ n ih =>
    rw [nsmul_succ]
    rw [probability_congr]
    rw [probability_add]
    simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_zero,
      Fin.consEquiv_symm_apply]
    rw [ih]
    exact Eq.symm (Fin.prod_univ_succAbove (fun i => 𝓒.probability T (f i)) 0)

/-- The probability measure associated with the Boltzmann distribution of a
  canonical ensemble. -/
noncomputable def μProd (T : Temperature) : MeasureTheory.Measure ι :=
  (𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T

instance (T : Temperature) : SigmaFinite (𝓒.μProd T) :=
  inferInstanceAs (SigmaFinite ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T))

instance (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)]
  [NeZero 𝓒.μ] : IsProbabilityMeasure (𝓒.μProd T) := inferInstanceAs <|
  IsProbabilityMeasure ((𝓒.μBolt T Set.univ)⁻¹ • 𝓒.μBolt T)

instance {T} : IsFiniteMeasure (𝓒.μProd T) := by
  rw [μProd]
  infer_instance

lemma μProd_add {T : Temperature} [IsFiniteMeasure (𝓒.μBolt T)]
    [IsFiniteMeasure (𝓒1.μBolt T)] : (𝓒 + 𝓒1).μProd T = (𝓒.μProd T).prod (𝓒1.μProd T) := by
  rw [μProd, μProd, μProd, μBolt_add]
  rw [MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.prod_smul_right]
  rw [smul_smul]
  congr
  trans ((𝓒.μBolt T) Set.univ * (𝓒1.μBolt T) Set.univ)⁻¹
  swap
  · by_cases h : (𝓒.μBolt T) Set.univ = 0
    · simp [h]
    by_cases h1 : (𝓒1.μBolt T) Set.univ = 0
    · simp [h1]
    rw [ENNReal.mul_inv]
    · simp
    · simp
  · rw [← @Measure.prod_prod]
    simp

lemma μProd_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).μProd T = (𝓒.μProd T).map e.symm := by
  simp [μProd, μBolt_congr]
  congr 2
  rw [MeasurableEquiv.map_apply]
  simp

lemma μProd_nsmul (n : ℕ) (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] :
    (nsmul n 𝓒).μProd T = MeasureTheory.Measure.pi fun _ => 𝓒.μProd T := by
  induction n with
  | zero =>
    simp [nsmul, μProd, μBolt]
    congr
    funext x
    exact Fin.elim0 x
  | succ n ih =>
    rw [nsmul_succ]
    rw [μProd_congr]
    rw [μProd_add]
    refine MeasurePreserving.map_eq ?_
    refine MeasurePreserving.symm _ ?_
    rw [ih]
    exact MeasureTheory.measurePreserving_piFinSuccAbove (fun _ => 𝓒.μProd T) 0

/-!

## Integrability of energy

-/

@[fun_prop]
lemma integrable_energy_add (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)]
    [IsFiniteMeasure (𝓒1.μBolt T)]
    (h : Integrable 𝓒.energy (𝓒.μProd T)) (h1 : Integrable 𝓒1.energy (𝓒1.μProd T)) :
    Integrable (𝓒 + 𝓒1).energy ((𝓒 + 𝓒1).μProd T) := by
  rw [μProd_add]
  refine Integrable.add'' ?_ ?_
  · have h1 : (fun (i : ι × ι1) => 𝓒.energy i.1)
      = fun (i : ι × ι1) => 𝓒.energy i.1 * (fun (i : ι1) => 1) i.2 := by
      funext i
      simp
    rw [h1]
    apply Integrable.mul_prod (f := 𝓒.energy) (g := (fun (i : ι1) => 1))
    · fun_prop
    · fun_prop
  · have h1 : (fun (i : ι × ι1) => 𝓒1.energy i.2)
      = fun (i : ι × ι1) => (fun (i : ι) => 1) i.1 * 𝓒1.energy i.2 := by
      funext i
      simp
    rw [h1]
    apply Integrable.mul_prod (f := (fun (i : ι) => 1)) (g := 𝓒1.energy)
    · fun_prop
    · fun_prop

@[fun_prop]
lemma integrable_energy_congr (T : Temperature) (e : ι1 ≃ᵐ ι)
    (h : Integrable 𝓒.energy (𝓒.μProd T)) :
    Integrable (𝓒.congr e).energy ((𝓒.congr e).μProd T) := by
  simp [μProd_congr]
  refine (integrable_map_equiv e.symm (𝓒.congr e).energy).mpr ?_
  simp only [congr_energy_comp_symmm]
  exact h

@[fun_prop]
lemma integrable_energy_nsmul (n : ℕ) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)]
    (h : Integrable 𝓒.energy (𝓒.μProd T)) :
    Integrable (nsmul n 𝓒).energy ((nsmul n 𝓒).μProd T) := by
  induction n with
  | zero =>
    simp [nsmul, μProd_nsmul]
  | succ n ih =>
    rw [nsmul_succ]
    apply integrable_energy_congr
    apply integrable_energy_add
    · exact h
    · exact ih

/-!

## The mean energy

-/

/-- The mean energy of the canonical ensemble at temperature `T`. -/
noncomputable def meanEnergy (T : Temperature) : ℝ := ∫ i, 𝓒.energy i ∂𝓒.μProd T

lemma meanEnergy_add {T : Temperature}
    [IsFiniteMeasure (𝓒1.μBolt T)] [IsFiniteMeasure (𝓒.μBolt T)]
    [NeZero 𝓒.μ] [NeZero 𝓒1.μ]
    (h1 : Integrable 𝓒.energy (𝓒.μProd T))
    (h2 : Integrable 𝓒1.energy (𝓒1.μProd T)) :
    (𝓒 + 𝓒1).meanEnergy T = 𝓒.meanEnergy T + 𝓒1.meanEnergy T := by
  rw [meanEnergy]
  simp only [energy_add_apply]
  rw [μProd_add]
  rw [MeasureTheory.integral_prod]
  simp only
  conv_lhs =>
    enter [2, x]
    rw [integral_add (integrable_const _) h2]
    rw [integral_const]
    simp
  rw [integral_add h1 (integrable_const _)]
  rw [integral_const]
  simp
  rfl
  · simpa [μProd_add] using integrable_energy_add 𝓒 𝓒1 T h1 h2

lemma meanEnergy_congr (e : ι1 ≃ᵐ ι) (T : Temperature) :
    (𝓒.congr e).meanEnergy T = 𝓒.meanEnergy T := by
  simp [meanEnergy, μProd_congr]
  refine MeasurePreserving.integral_comp' ?_ 𝓒.energy
  refine { measurable := ?_, map_eq := ?_ }
  · exact MeasurableEquiv.measurable e
  · exact MeasurableEquiv.map_map_symm e

lemma meanEnergy_nsmul (n : ℕ) (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (h1 : Integrable 𝓒.energy (𝓒.μProd T)) :
    (nsmul n 𝓒).meanEnergy T = n * 𝓒.meanEnergy T := by
  induction n with
  | zero =>
    simp [nsmul, meanEnergy, μProd_nsmul]
  | succ n ih =>
    rw [nsmul_succ, meanEnergy_congr, meanEnergy_add, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
    · exact h1
    · exact integrable_energy_nsmul 𝓒 n T h1

/-!

## The differential entropy

-/

/-- The (differential) entropy of the canonical ensemble. In the continuous case, this quantity
is not absolute but depends on the choice of units for the measure. It can be negative.
See `thermodynamicEntropy` for the absolute physical quantity. -/
noncomputable def differentialEntropy (T : Temperature) : ℝ :=
  - kB * ∫ i, log (probability 𝓒 T i) ∂𝓒.μProd T

/-- Probabilities are non-negative,
assuming a positive partition function. -/
lemma probability_nonneg
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 ≤ 𝓒.probability T i := by
  -- Use positivity of the (mathematical) partition function (already defined above)
  have hpos := mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T)
  simp [CanonicalEnsemble.probability, div_nonneg, Real.exp_nonneg, hpos.le]

/-- Probabilities are strictly positive. -/
lemma probability_pos
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] (i : ι) :
    0 < 𝓒.probability T i := by
  have hZpos := mathematicalPartitionFunction_pos (𝓒:=𝓒) (T:=T)
  simp [probability, div_pos, Real.exp_pos, hZpos]

/-- General entropy non-negativity under a pointwise upper bound `probability ≤ 1`.
This assumption holds automatically in the finite/counting case (since sums bound each term),
but can fail in general (continuous) settings; hence we separate it as a hypothesis.
Finite case: see `CanonicalEnsemble.entropy_nonneg` in `Finite`. -/
lemma differentialEntropy_nonneg_of_prob_le_one
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hInt : Integrable (fun i => Real.log (𝓒.probability T i)) (𝓒.μProd T))
    (hP_le_one : ∀ i, 𝓒.probability T i ≤ 1) :
    0 ≤ 𝓒.differentialEntropy T := by
  have hPoint :
      (fun i => Real.log (𝓒.probability T i)) ≤ᵐ[𝓒.μProd T] fun _ => 0 := by
    refine Filter.Eventually.of_forall ?_
    intro i
    have hpos := probability_pos (𝓒:=𝓒) (T:=T) i
    have hle  := hP_le_one i
    have hle' : 𝓒.probability T i ≤ Real.exp 0 := by
      simpa [Real.exp_zero] using hle
    exact (log_le_iff_le_exp hpos).mpr hle'
  have hInt0 : Integrable (fun _ : ι => (0 : ℝ)) (𝓒.μProd T) := integrable_const _
  have hIntLe : (∫ i, Real.log (𝓒.probability T i) ∂𝓒.μProd T)
      ≤ (∫ _i, (0 : ℝ) ∂𝓒.μProd T) :=
    integral_mono_ae hInt hInt0 hPoint
  have hent :
      𝓒.differentialEntropy T
        = - kB * (∫ i, Real.log (𝓒.probability T i) ∂𝓒.μProd T) := rfl
  have hkB : 0 ≤ kB := kB_nonneg
  have hIle0 : (∫ i, Real.log (𝓒.probability T i) ∂𝓒.μProd T) ≤ 0 := by
    simpa [integral_const] using hIntLe
  have hProd :
      0 ≤ - kB * (∫ i, Real.log (𝓒.probability T i) ∂𝓒.μProd T) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hkB) hIle0
  simpa [hent] using hProd

/-!

## Thermodynamic Quantities

These are the dimensionless physical quantities derived from the mathematical definitions
by incorporating the fundamental phase space volume `𝓒.phase_space_unit ^ 𝓒.dof`.
-/

open Constants

/-- The dimensionless thermodynamic partition function, `Z = Z_math / h^dof`. -/
noncomputable def partitionFunction (T : Temperature) : ℝ :=
  𝓒.mathematicalPartitionFunction T / (𝓒.phase_space_unit ^ 𝓒.dof)

/-- The Helmholtz free energy, `F = -k_B T log(Z)`. This is the central
quantity from which other thermodynamic properties are derived. -/
noncomputable def helmholtzFreeEnergy (T : Temperature) : ℝ :=
  - kB * T.val * Real.log (𝓒.partitionFunction T)

/-- The absolute thermodynamic entropy, defined via the fundamental relation `S = (U - F) / T`.

The hypothesis `hT : 0 < T.val` encodes the physically required strict positivity of the
temperature. It is intentionally retained (even though not needed for mere division by `T.val`)
so that subsequent lemmas may rely on it (e.g. for monotonicity, differentiability,
or asymptotic considerations near absolute zero). We mark it as an unused argument explicitly. -/
noncomputable def thermodynamicEntropy (T : Temperature) (hT : 0 < T.val) : ℝ :=
  let _h : T.val ≠ 0 := ne_of_gt hT
  (𝓒.meanEnergy T - 𝓒.helmholtzFreeEnergy T) / T.val

/-!

## Relations between Mathematical and Thermodynamic Quantities

-/

/-- An intermediate potential defined from the mathematical partition function. See
`helmholtzFreeEnergy` for the physical thermodynamic quantity. -/
noncomputable def helmholtzPotential (T : Temperature) : ℝ :=
  - kB * T.val * Real.log (𝓒.mathematicalPartitionFunction T)

/-- The relationship between the physical Helmholtz Free Energy and the Helmholtz Potential. -/
lemma helmholtzFreeEnergy_eq_helmholtzPotential_add_correction (T : Temperature)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ] :
    𝓒.helmholtzFreeEnergy T = 𝓒.helmholtzPotential T +
      kB * T.val * 𝓒.dof * Real.log (𝓒.phase_space_unit) := by
  have hZ_pos := mathematicalPartitionFunction_pos 𝓒 T
  have h_pow_pos : 0 < 𝓒.phase_space_unit ^ 𝓒.dof := pow_pos 𝓒.h_pos _
  simp_rw [helmholtzFreeEnergy, helmholtzPotential, partitionFunction,
    Real.log_div hZ_pos.ne' h_pow_pos.ne']
  have h_log_pow : Real.log (𝓒.phase_space_unit ^ 𝓒.dof)
      = (𝓒.dof : ℝ) * Real.log 𝓒.phase_space_unit := by
    simp
  simp [sub_eq_add_neg, h_log_pow, mul_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc]

/-- General identity: S_diff = kB β ⟨E⟩ + kB log Z_math.
This connects the differential entropy to the mean energy and the mathematical partition function.
Integrability of `log (probability …)` follows from the pointwise formula. -/
lemma differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ
    (T : Temperature) [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hE : Integrable 𝓒.energy (𝓒.μProd T)) :
    𝓒.differentialEntropy T = kB * (T.β : ℝ) * 𝓒.meanEnergy T +
      kB * Real.log (𝓒.mathematicalPartitionFunction T) := by
  set Z := 𝓒.mathematicalPartitionFunction T
  have hZpos := mathematicalPartitionFunction_pos 𝓒 T
  have h_log_prob : ∀ i, Real.log (𝓒.probability T i) =
      - (T.β : ℝ) * 𝓒.energy i - Real.log Z := by
    intro i
    have : 0 < Z := hZpos
    rw [probability, Real.log_div (exp_pos _).ne' this.ne', Real.log_exp]
  have h_int_log :
      Integrable (fun i => Real.log (𝓒.probability T i)) (𝓒.μProd T) := by
    simp_rw [h_log_prob]
    exact (hE.const_mul _).add (integrable_const _)
  unfold differentialEntropy
  rw [integral_congr_ae (ae_of_all _ h_log_prob)]
  have h_split :
      (fun i => - (T.β : ℝ) * 𝓒.energy i - Real.log Z)
        = (fun i => (- (T.β : ℝ)) * 𝓒.energy i + (- Real.log Z)) := by
    funext i; ring
  simp_rw [h_split]
  have h_int1 : Integrable (fun _ : ι => - Real.log Z) (𝓒.μProd T) :=
    (integrable_const _)
  have h_intE : Integrable (fun i => (- (T.β : ℝ)) * 𝓒.energy i) (𝓒.μProd T) :=
    (hE.const_mul _)
  rw [integral_add h_intE h_int1,
      integral_const_mul, meanEnergy, integral_const]
  have hμ : (𝓒.μProd T) Set.univ = 1 := measure_univ
  simp [hμ, mul_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
        mul_comm, mul_left_comm, mul_assoc, differentialEntropy, probability,
       mul_comm, mul_left_comm, mul_assoc, h_int_log]

/--  Auxiliary identity: `kB · β = 1 / T`.
`β` is defined as `1 / (kB · T)` (see `Temperature.β`).
The proof just clears denominators with `field_simp`. -/
@[simp]
private lemma kB_mul_beta (T : Temperature) (hT : 0 < T.val) :
    (kB : ℝ) * (T.β : ℝ) = 1 / T.val := by
  have hkB : (kB : ℝ) ≠ 0 := kB_neq_zero
  have hT0 : (T.val : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hT)
  field_simp [Temperature.β, hkB, hT0]
  rw [mul_div_mul_left (↑T.val) T.toReal hkB]
  erw [propext (div_eq_one_iff_eq hT0)]

/-- Fundamental relation between thermodynamic and differential entropy:
S_thermo = S_diff - kB * dof * log h. -/
theorem thermodynamicEntropy_eq_differentialEntropy_sub_correction
    (T  : Temperature) (hT : 0 < T.val)
    [IsFiniteMeasure (𝓒.μBolt T)] [NeZero 𝓒.μ]
    (hE : Integrable 𝓒.energy (𝓒.μProd T)) :
    𝓒.thermodynamicEntropy T hT
      = 𝓒.differentialEntropy T
        - kB * 𝓒.dof * Real.log 𝓒.phase_space_unit := by
  set U : ℝ := 𝓒.meanEnergy T
  have h_kBβ : (kB : ℝ) * (T.β : ℝ) = 1 / T.val := by
    unfold Temperature.β
    change kB * (⟨1 / (kB * (T : ℝ)), _⟩ : ℝ≥0) = 1 / T.val
    simp [Temperature.toReal, one_div, mul_comm, mul_left_comm, mul_assoc,
      kB_neq_zero, (ne_of_gt hT)]
  have hDiff :=
    𝓒.differentialEntropy_eq_kB_beta_meanEnergy_add_kB_log_mathZ T hE
  have hS :
      𝓒.differentialEntropy T
        = U / T.val +
            kB * Real.log (𝓒.mathematicalPartitionFunction T) := by
    rw [hDiff]
    simp [U, h_kBβ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have h_log_partition :
      Real.log (𝓒.partitionFunction T)
        = Real.log (𝓒.mathematicalPartitionFunction T)
            - (𝓒.dof : ℝ) * Real.log 𝓒.phase_space_unit := by
    have hZ_pos := mathematicalPartitionFunction_pos 𝓒 T
    have h_pow_pos : 0 < 𝓒.phase_space_unit ^ 𝓒.dof := pow_pos 𝓒.h_pos _
    have h_log_pow :
        Real.log (𝓒.phase_space_unit ^ 𝓒.dof)
          = (𝓒.dof : ℝ) * Real.log 𝓒.phase_space_unit := by
      have hne : (𝓒.phase_space_unit : ℝ) ≠ 0 := ne_of_gt 𝓒.h_pos
      simp
    simp [partitionFunction,
      Real.log_div hZ_pos.ne' h_pow_pos.ne', h_log_pow,
      sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
  set A :=
    Real.log (𝓒.mathematicalPartitionFunction T)
      - (𝓒.dof : ℝ) * Real.log 𝓒.phase_space_unit
  have hA : Real.log (𝓒.partitionFunction T) = A := by
    simpa [A] using h_log_partition
  have hF :
      𝓒.helmholtzFreeEnergy T = - kB * T.val * A := by
    simp [helmholtzFreeEnergy, hA, A]
  have hLHS :
      𝓒.thermodynamicEntropy T hT
        = U / T.val + kB * A := by
    unfold thermodynamicEntropy
    have hval0 : (T.val : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hT)
    simp [hF, U, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc, mul_add, add_mul, hval0]
  have hRHS :
      U / T.val + kB * A
        = 𝓒.differentialEntropy T
            - kB * 𝓒.dof * Real.log 𝓒.phase_space_unit := by
    simp_rw [hS, A]
    have hDistrib :
        kB * (Real.log (𝓒.mathematicalPartitionFunction T)
              - (𝓒.dof : ℝ) * Real.log 𝓒.phase_space_unit)
          =
          kB * Real.log (𝓒.mathematicalPartitionFunction T)
            - kB * (𝓒.dof : ℝ) * Real.log 𝓒.phase_space_unit := by
      ring
    simp [hDistrib, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc, U]
    ring
  exact hLHS.trans hRHS

end CanonicalEnsemble
