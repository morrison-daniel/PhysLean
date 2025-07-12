/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Analysis.Distribution.SchwartzSpace

/-!
# Distributions

This file defines distributions, which are continuous linear functionals that take in as test
functions those `ℝ → E` that are Schwartz functions, i.e. smooth functions with rapidly decreasing iterated derivatives. `E` can be a normed vector space over `ℝ` or `ℂ`, and the linear functionals
also respectively output `ℝ` or `ℂ`.

## Examples
- `Distribution.diracDelta'`: takes in a "direction" in the form of a continuous linear map
  `E →L[𝕜] 𝕜` (the direction `v` corresponds to the inner product `⟨v, -⟩`), and returns the Dirac
  delta distribution in that direction. This is a distribution that evaluates the test function `η`
  at `0` and then take the inner product with `v`, i.e. `⟨v, η 0⟩`.

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

variable (𝕜 : Type) [RCLike 𝕜] (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [SMulCommClass ℝ 𝕜 E]

namespace Distribution

/-- We construct a distribution from the following data:
1. We take a linear map `f` that evaluates the given Schwartz function `η`. At this stage we don't
   need `f` to be continuous.
2. Recall that a Schwartz function `η` satisfies that
   `{ |x| ^ k * ‖iteratedDeriv n η x‖ ∣ x : ℝ }` is bounded for any pair `(k, n) ∈ ℕ × ℕ`.
3. We take a finite set `s` of pairs `(k, n) ∈ ℕ × ℕ` such that for each test function `η`, the
   norm `‖f η‖` is controlled by `|x| ^ k * ‖(d^n/dx^n) η‖` for some `x : ℝ` and for some
   `(k, n) ∈ s`, up to a global scalar `C ≥ 0`.
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

/-- Dirac delta in a given direction (represented by `E →L[𝕜] 𝕜`). -/
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

end Distribution
