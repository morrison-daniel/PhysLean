/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.ClassicalMechanics.WaveEquation.Basic
/-!
# Harmonic Wave

Time-harmonic waves.

The complex representation which finds major applications in optics and
signal processing is also introduced.

The mathematics may have overlap with quantum mechanics and may require refactoring in the future.

Note TODO `EGQUA` may require considerable effort to be made rigorous and may heavily depend on
the status of Fourier theory in Mathlib.

-/

namespace ClassicalMechanics

/-- General form of time-harmonic wave in terms of angular frequency `ω` and wave vector `k`. -/
noncomputable def harmonicWave (a ω g: Space → ℝ) (k : Space) :
    Time → Space → ℝ :=
    fun t r => a r * Real.cos (ω k * t - g r)

TODO "EGQUA" "Show that the wave equation is invariant under rotations and any direction `s`
    can be rotated to `EuclideanSpace.single 2 1` if only one wave is concerened."

set_option linter.unusedVariables false in
/-- Transverse monochromatic time-harmonic plane wave where the direction of propagation
  is taken to be `EuclideanSpace.single 2 1`. -/
@[nolint unusedArguments]
noncomputable def TransverseHarmonicPlaneWave {c : ℝ} {k : Space} {E₀x E₀y ω δx δy : ℝ}
    {Ex Ey : Time → Space → ℝ} (hk : k = EuclideanSpace.single 2 (ω/c))
    (hx : Ex = harmonicWave (fun _ => E₀x) (fun _ => ω) (fun r => inner ℝ k r - δx) k)
    (hy : Ey = harmonicWave (fun _ => E₀y) (fun _ => ω) (fun r => inner ℝ k r - δy) k) :
    Time → Space → EuclideanSpace ℝ (Fin 3) :=
    fun t x => Ex t x • EuclideanSpace.single 0 1 + Ey t x • EuclideanSpace.single 1 1

/-- The transverse harmonic planewave representation is equivalent to the general planewave
  expression with `c = ω/k`. -/
theorem TransverseHarmonicPlaneWaveisPlaneWave {c : ℝ} {k : Space} {E₀x E₀y ω δx δy : ℝ}
    {Ex Ey : Time → Space → ℝ} (hc_non_zero : c ≠ 0) (hk : k = EuclideanSpace.single 2 (ω/c))
    (hx : Ex = harmonicWave (fun _ => E₀x) (fun _ => ω) (fun r => inner ℝ k r - δx) k)
    (hy : Ey = harmonicWave (fun _ => E₀y) (fun _ => ω) (fun r => inner ℝ k r - δy) k) :
    (TransverseHarmonicPlaneWave hk hx hy) = planeWave
    (fun p => (E₀x * Real.cos (-(ω/c)*p + δx)) • (EuclideanSpace.single 0 1) +
    (E₀y * Real.cos (-(ω/c)*p + δy)) • (EuclideanSpace.single 1 1)) c
    (EuclideanSpace.single 2 1) (by simp) := by
  unfold TransverseHarmonicPlaneWave planeWave
  ext1 t
  ext1 x
  rw [hx, hy, harmonicWave, harmonicWave, hk]
  simp
  ring_nf
  simp [hc_non_zero]

TODO "EGQUA" "Show that any disturbance (subject to certian conditions) can be expressed
    as a superposition of harmonic plane waves via Fourier integral."

/-!

## Complex representation of harmonic waves

-/
