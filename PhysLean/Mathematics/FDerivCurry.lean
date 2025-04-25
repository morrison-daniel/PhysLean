/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.FDeriv.Mul
/-!
# fderiv currying lemmas

Various lemmas related to fderiv on curried/uncurried functions.

-/
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma fderiv_uncurry (f : X → Y → Z) (xy : X × Y) (dy : Y)
    (h : DifferentiableAt 𝕜 (↿f) xy) :
    fderiv 𝕜 (↿f) xy (0, dy) =
    fderiv 𝕜 (fun x => f xy.1 x) xy.2 dy := by
  rw [show (fun x => f xy.1 x) =
    (↿f) ∘ (fun x => (xy.1, x)) by {ext w; rfl}]
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  rw [(hasFDerivAt_prodMk_right (𝕜 := 𝕜) xy.1 xy.2).fderiv]
  rfl

lemma fderiv_uncurry' (f : X → Y → Z) (xy : X × Y) (dx : X)
    (h : DifferentiableAt 𝕜 (↿f) xy) :
    fderiv 𝕜 (↿f) xy (dx, 0) =
    fderiv 𝕜 (fun x => f x xy.2) xy.1 dx := by
  rw [show (fun x => f x xy.2) =
    (↿f) ∘ (fun x => (x, xy.2)) by {ext w; rfl}]
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  rw [(hasFDerivAt_prodMk_left (𝕜 := 𝕜) xy.1 xy.2).fderiv]
  rfl

lemma fderiv_curry (f : X × Y → Z) (x : X) (y : Y)
    (h : DifferentiableAt 𝕜 f (x, y)) (dy : Y) :
    fderiv 𝕜 (Function.curry f x) y dy = fderiv 𝕜 (f) (x, y) (0, dy) := by
  have h1 : f = ↿(Function.curry f) := by
    ext x
    rfl
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry]
  exact h

lemma fderiv_curry' (f : X × Y → Z) (x : X) (y : Y)
    (h : DifferentiableAt 𝕜 f (x, y)) (dx : X) :
    fderiv 𝕜 (fun x => Function.curry f x y) x dx = fderiv 𝕜 f (x, y) (dx, 0) := by
  have h1 : f = ↿(Function.curry f) := by
    ext x
    rfl
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry']
  exact h

lemma fderiv_uncurry_sum (f : X → Y → Z) (xy dxy : X × Y) :
    fderiv 𝕜 (↿f) xy dxy
    =
    fderiv 𝕜 (↿f) xy (dxy.1, 0) + fderiv 𝕜 (↿f) xy (0, dxy.2) := by
  rw [← ContinuousLinearMap.map_add]
  simp

theorem fderiv_uncurry'' (f : X → Y → Z) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 ↿f
    =
    fun xy =>
      (fderiv 𝕜 (f · xy.2) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
      +
      (fderiv 𝕜 (f xy.1 ·) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) := by
  funext xy
  apply ContinuousLinearMap.ext
  intro dxy
  rw [fderiv_uncurry_sum]
  rw [fderiv_uncurry, fderiv_uncurry']
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_fst', Function.comp_apply, ContinuousLinearMap.coe_snd']
  fun_prop
  fun_prop

theorem fderiv_wrt_prod'' (f : X × Y → Z) (hf : Differentiable 𝕜 f) :
    fderiv 𝕜 f
    =
    fun xy =>
      (fderiv 𝕜 (fun x' => f (x',xy.2)) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
      +
      (fderiv 𝕜 (fun y' => f (xy.1,y')) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) :=
  fderiv_uncurry'' (fun x y => f (x,y)) hf

theorem fderiv_clm_apply' (f : X → Y →L[𝕜] Z) (y : Y) (x dx : X) (h : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x dx y
    =
    fderiv 𝕜 (f · y) x dx := by
  rw [fderiv_clm_apply] <;> first | simp | fun_prop
