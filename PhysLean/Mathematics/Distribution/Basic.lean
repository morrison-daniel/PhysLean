/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Distributions

This file defines distributions, which are continuous linear functionals that take in as test
functions those `ℝ → E` that are smooth functions with rapidly decreasing iterated derivatives.
(The space of all these test functions is called the Schwartz space `𝓢(ℝ, E)`.)

`E` can be a normed vector space over `ℝ` or `ℂ`, and the continuous linear functionals are also
required to output values in `ℝ` or `ℂ` respectively.

## Important Results
- `Distribution.ofLinear`: constructs a distribution from a linear functional `F` and some
  conditions that implies that `F` is continuous.

## Examples
- `Distribution.diracDelta`: takes in a direction `v : E`, and returns the Dirac delta distribution
  in that direction. Given the test function `η`, `diracDelta v η = ⟨v, η 0⟩`.
- `Distribution.diracDelta'`: a slight generalisation of `diracDelta` where the inner product
  `⟨v, ─⟩` is replaced by a continuous linear map `E →L[𝕜] 𝕜`.

-/

open SchwartzMap NNReal
noncomputable section

/-- A distribution on `E` (normed vector space over `𝕜`) is a continuous linear map
`𝓢(ℝ, E) →L[𝕜] 𝕜` where `𝒮(ℝ, E)` is the Schwarz space of smooth functions `ℝ → E` with rapidly
decreasing iterated derivatives. This is notated as `ℝ →d[𝕜] E`. -/
def Distribution (𝕜 : Type) [RCLike 𝕜] (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] : Type :=
  𝓢(ℝ, E) →L[𝕜] 𝕜

@[inherit_doc] notation:25 "ℝ→d[" 𝕜:25 "] " E:0 => Distribution 𝕜 E

variable (𝕜 : Type) [RCLike 𝕜] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Distribution

section NormedSpace

variable [NormedSpace 𝕜 E]

/-- We construct a distribution from the following data:
1. We take a finite set `s` of pairs `(k, n) ∈ ℕ × ℕ` that will be explained later.
2. We take a linear map `f` that evaluates the given Schwartz function `η`. At this stage we don't
   need `f` to be continuous.
3. Recall that a Schwartz function `η` satisfies a bound
   `|x|ᵏ * ‖(dⁿ/dxⁿ) η‖ < Mₙₖ` where `Mₙₖ : ℝ` only depends on `(k, n) : ℕ × ℕ`.
4. This step is where `s` is used: for each test function `η`, the norm `‖f η‖` is required to be
   bounded by `C * (|x|ᵏ * ‖(dⁿ/dxⁿ) η‖)` for some `x : ℝ` and for some `(k, n) ∈ s`, where
   `C ≥ 0` is a global scalar.
-/
def ofLinear (s : Finset (ℕ × ℕ)) (f : 𝓢(ℝ, E) →ₗ[𝕜] 𝕜)
    (hf : ∃ C : ℝ≥0, ∀ η : 𝓢(ℝ, E), ∃ (k : ℕ) (n : ℕ) (x : ℝ), (k, n) ∈ s ∧
      ‖f η‖ ≤ C * (|x| ^ k * ‖iteratedDeriv n η x‖)) : ℝ→d[𝕜] E where
  __ := f
  cont := Seminorm.cont_withSeminorms_normedSpace 𝕜 (schwartz_withSeminorms 𝕜 ℝ E) f <| by
    obtain ⟨C, hf⟩ := hf
    refine ⟨s, C, fun η ↦ ?_⟩
    obtain ⟨k, n, x, hkn, hη⟩ := hf η
    have hs : s.Nonempty := ⟨(k, n), hkn⟩
    refine hη.trans <| mul_le_mul_of_nonneg_left ((le_seminorm' 𝕜 k n η x).trans ?_) C.2
    rw [Seminorm.finset_sup_apply]
    refine (NNReal.coe_le_coe (r₁ := ⟨SchwartzMap.seminorm 𝕜 k n η, apply_nonneg _ _⟩)).2 ?_
    convert s.le_sup hkn
      (f := fun kn : ℕ × ℕ ↦ (⟨SchwartzMap.seminorm 𝕜 kn.1 kn.2 η, apply_nonneg _ _⟩ : ℝ≥0))

/-- Dirac delta given a continuous linear function `dir : E →L[𝕜] 𝕜`. This is a generalisation of
`diracDelta` which takes in a specified direction `v`, and evaluate the test function `η` to give
`⟨v, η 0⟩`. Here `dir` acts like `⟨v, ─⟩`. -/
def diracDelta' (dir : E →L[𝕜] 𝕜) : ℝ→d[𝕜] E :=
  ofLinear 𝕜 E { (0, 0) }
    { toFun η := dir (η 0)
      map_add' η₁ η₂ := by simp
      map_smul' c η := by simp } <| by
    obtain ⟨M, hMpos, hM⟩ := dir.isBoundedLinearMap.bound
    refine ⟨⟨M, le_of_lt hMpos⟩, fun η ↦ ⟨0, 0, 0, by simp, ?_⟩⟩
    calc
      ‖dir (η 0)‖
        ≤ M * ‖η 0‖ := hM (η 0)
      _ = M * (|0| ^ 0 * ‖iteratedDeriv 0 η 0‖) := by simp

end NormedSpace


section InnerProductSpace

variable [InnerProductSpace 𝕜 E]

/-- Dirac delta given a direction `v`. It evaluates a test function `η` to give `⟨v, η 0⟩`.
For a generalisation repalcing `⟨v, ─⟩` with a continuous linear function, use `diracDelta'`. -/
def diracDelta (v : E) : ℝ→d[𝕜] E :=
  diracDelta' 𝕜 E (innerSL 𝕜 v)

end InnerProductSpace

end Distribution
