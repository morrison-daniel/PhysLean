import PhysLean.Relativity.SpaceTime.TimeSlice
import PhysLean.ClassicalMechanics.Space.VectorIdentities
import Mathlib.Tactic.FunProp.Differentiable

section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
    {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

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
  rw [SpaceTime.fderiv_uncurry, SpaceTime.fderiv_uncurry']
  simp
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

end

namespace SpaceTime

open Space
open Time

lemma dt_dist (f : Time → Space → EuclideanSpace ℝ (Fin 3)) :
    (fderiv ℝ (fun t => (fderiv ℝ (fun x => f t x u) x) dx1) t -
    fderiv ℝ (fun t => (fderiv ℝ (fun x => f t x v) x) dx2) t) 1
    =
    (fderiv ℝ (fun t => (fderiv ℝ (fun x => f t x u) x) dx1) t) 1 -
    (fderiv ℝ (fun t => (fderiv ℝ (fun x => f t x v) x) dx2) t) 1 := by
  rfl

lemma fderiv_coord (f : Time → Space → EuclideanSpace ℝ (Fin 3)) (t dt : Time)
    (hf : Differentiable ℝ (↿f)) :
    (fun x => (fderiv ℝ (fun t => f t x i) t) dt)
    =
    (fun x => (fderiv ℝ (fun t => f t x) t) dt i) := by
  ext x
  rw [fderiv_pi]
  symm
  change (fderiv ℝ (fun t => f t x i) t) dt = _
  rfl
  intro i
  fun_prop

theorem fderiv_swap (f : Time → Space → EuclideanSpace ℝ (Fin 3)) (t dt : Time) (x : Space)
    (dx : EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 ↿f) :
    fderiv ℝ (fun t' => fderiv ℝ (fun x' => f t' x' i) x dx) t dt
    =
    (fderiv ℝ (fun x' => fderiv ℝ (fun t' => f t' x' i) t dt) x dx) := by
  have hf' : IsSymmSndFDerivAt ℝ (↿f) (t,x) := by
    apply ContDiffAt.isSymmSndFDerivAt (n := 2)
    · exact ContDiff.contDiffAt hf
    · simp
  have hd : Differentiable ℝ (↿f) :=
    ContDiff.differentiable hf (by simp)
  have hdd (xt : Time × Space) : Differentiable ℝ (fderiv ℝ (↿f)) :=  by
    change ContDiff ℝ (1 + 1) ↿f at hf
    rw [contDiff_succ_iff_fderiv] at hf
    have hd2 := hf.2.2
    apply ContDiff.differentiable hd2
    rfl
  let inclT (x' : Space) : Time → Time × Space := fun t' => (t', x')
  let inclX (t' : Time) : Space → Time × Space := fun x' => (t', x')
  have h_fderiv_t_differentiable (dt : Time) :
        Differentiable ℝ (fun x' => (fderiv ℝ (fun t' => f t' x') t) dt):= by
    intro x'
    have hl (x' : Space) : (fun t' => f t' x') = ↿f ∘ inclT x' := by
      funext x'
      rfl
    have hdl (x' : Space) : (fderiv ℝ (fun t' => f t' x') t) dt
      = (fderiv ℝ (↿f) (inclT x' t)) ((fderiv ℝ (inclT x') t) dt) := by
      rw [hl]
      rw [fderiv_comp]
      simp [-fderiv_eq_smul_deriv]
      · fun_prop
      · fun_prop
    conv_lhs =>
      enter [x']
      rw [hdl x']
    refine DifferentiableAt.clm_apply ?_ ?_
    · simp [inclT]
      change DifferentiableAt ℝ  (fderiv ℝ (↿f) ∘ inclX t ) x'
      refine DifferentiableAt.comp x' ?_ ?_
      · exact hdd (inclT x t) (inclX t x')
      · fun_prop
    · have hl(x' : Space) : (fderiv ℝ (inclT x') t) dt = (dt, 0) := by
        simp only [inclT]
        rw [(hasFDerivAt_prodMk_left (𝕜 := ℝ) t x').fderiv ]
        simp
      conv_lhs =>
        enter [x']
        rw [hl x']
      fun_prop
  have h := IsSymmSndFDerivAt.eq hf' (dt,0) (0,dx)
  rw[fderiv_wrt_prod''] at h
  rw[fderiv_wrt_prod''] at h
  simp [-fderiv_eq_smul_deriv, Function.HasUncurry.uncurry] at h
  rw[fderiv_clm_apply'] at h
  rw[fderiv_clm_apply'] at h
  simp [-fderiv_eq_smul_deriv] at h
  let drop : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ  := {
      toFun x := x i
      map_add' := by simp
      map_smul' := by simp
      cont := by fun_prop
    }
  change (fderiv ℝ
      (fun t' => (fderiv ℝ (drop ∘ (fun x' => f t' x')) x) dx) t) dt = _
  trans (fderiv ℝ
      (fun t' => ((fderiv ℝ (⇑drop) (f t' x)).comp (fderiv ℝ (fun x' => f t' x') x)) dx) t) dt
  · congr
    funext t'
    rw [fderiv_comp]
    · fun_prop
    · let inclX : Space → Time × Space := fun x' => (t', x')
      have hl : (fun x' => f t' x') = ↿f ∘ inclX := by
        funext x'
        rfl
      rw [hl]
      apply DifferentiableAt.comp
      · fun_prop
      · fun_prop
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp',
    Function.comp_apply,  smul_eq_mul]
  rw [fderiv_comp']
  simp [-fderiv_eq_smul_deriv]
  rw [h]
  change _ =
    (fderiv ℝ (fun x' => (fderiv ℝ (drop ∘ (fun t' => f t' x')) t) dt) x) dx
  trans (fderiv ℝ (fun x' => ((fderiv ℝ (⇑drop) (f t x')).comp (fderiv ℝ (fun t' => f t' x') t)) dt) x) dx
  swap
  · congr
    funext x'
    rw [fderiv_comp]
    · fun_prop
    · let inclT : Time → Time × Space := fun t' => (t', x')
      have hl : (fun t' => f t' x') = ↿f ∘ inclT := by
        funext x'
        rfl
      rw [hl]
      apply DifferentiableAt.comp
      · fun_prop
      · fun_prop
  simp  [-fderiv_eq_smul_deriv]
  rw [fderiv_comp']
  simp
  /- Start of differenitablity conditions. -/
  · fun_prop
  · exact h_fderiv_t_differentiable dt x
  · fun_prop
  · have hl (t' : Time) : (fun x' => f t' x') = ↿f ∘ inclX t' := by
      funext x'
      rfl
    have hdl (t' : Time) : (fderiv ℝ (fun x' => f t' x') x) dx
      = (fderiv ℝ (↿f) (inclX t' x)) ((fderiv ℝ (inclX t') x) dx) := by
      rw [hl]
      rw [fderiv_comp]
      simp [-fderiv_eq_smul_deriv]
      · fun_prop
      · fun_prop
    conv_lhs =>
      enter [x']
      rw [hdl x']
    refine DifferentiableAt.clm_apply ?_ ?_
    · simp [inclT]
      change DifferentiableAt ℝ  (fderiv ℝ (↿f) ∘ inclT x ) t
      refine DifferentiableAt.comp t ?_ ?_
      · exact hdd (inclT x t) (inclT x t)
      · fun_prop
    · have hl(t' : ℝ) : (fderiv ℝ (inclX t') x) dx = (0, dx) := by
        simp only [inclT]
        rw [(hasFDerivAt_prodMk_right (𝕜 := ℝ) t' x).fderiv ]
        simp
      conv_lhs =>
        enter [x']
        rw [hl x']
      fun_prop
  · refine (DifferentiableAt.add_iff_right ?_).mpr ?_
    · refine DifferentiableAt.clm_comp ?_ ?_
      · -- DifferentiableAt ℝ (fun y' => fderiv ℝ (fun x' => f x' y') t) x
        have hl (x' : Space) : (fun t' => f t' x') = ↿f ∘ inclT x' := by
          funext x'
          rfl
        have hdl (x' : Space) : (fderiv ℝ (fun t' => f t' x') t)
          =  (fderiv ℝ (↿f) (inclT x' t)).comp (fderiv ℝ (inclT x') t) := by
          rw [hl]
          rw [fderiv_comp]
          · fun_prop
          · fun_prop
        conv_lhs =>
          enter [x']
          rw [hdl x']
        simp
        apply DifferentiableAt.clm_comp
        · apply DifferentiableAt.comp
          · exact hdd (inclT x t) (inclT x t)
          · fun_prop
        · have hl(x' : Space) : (fderiv ℝ (inclT x') t)  =  ContinuousLinearMap.inl ℝ Time Space := by
            simp only [inclT]
            rw [(hasFDerivAt_prodMk_left (𝕜 := ℝ) t x').fderiv ]
          conv_lhs =>
            enter [x']
            rw [hl x']
          fun_prop
      · fun_prop
    · refine DifferentiableAt.clm_comp ?_ ?_
      · -- DifferentiableAt ℝ (fderiv ℝ fun y' => f t y') x
        have hl (t' : Time) : (fun x' => f t' x') = ↿f ∘ inclX t' := by
          funext x'
          rfl
        have hdl (x' : Space) : fderiv ℝ (fun y' => f t y') x'
          = (fderiv ℝ (↿f) (inclX t x')).comp (fderiv ℝ (inclX t) x')   := by
          rw [hl]
          rw [fderiv_comp]
          · fun_prop
          · fun_prop
        conv_lhs =>
          enter [x']
          rw [hdl x']
        apply DifferentiableAt.clm_comp
        · apply DifferentiableAt.comp
          · exact hdd (inclT x t) (inclT x t)
          · fun_prop
        · fun_prop
      · fun_prop
  · refine (DifferentiableAt.add_iff_right ?_).mpr ?_
    · refine DifferentiableAt.clm_comp ?_ ?_
      · --  DifferentiableAt ℝ (fderiv ℝ fun x' => f x' x) t
        have hl (x' : Space) : (fun t' => f t' x') = ↿f ∘ inclT x' := by
          funext x'
          rfl
        have hdl (x' : Space) : (fderiv ℝ (fun t' => f t' x') )
          =  fun x => (fderiv ℝ (↿f) (inclT x' x)).comp (fderiv ℝ (inclT x') x) := by
          rw [hl]
          funext x
          rw [fderiv_comp]
          · fun_prop
          · fun_prop
        conv_lhs =>
          rw [hdl ]
        simp
        apply DifferentiableAt.clm_comp
        · apply DifferentiableAt.comp
          · exact hdd (inclT x t) (inclT x t)
          · fun_prop
        · fun_prop
      · fun_prop
    · refine DifferentiableAt.clm_comp ?_ ?_
      · -- DifferentiableAt ℝ (fun x' => fderiv ℝ (fun y' => f x' y') x) t
        have hl (t' : Time) : (fun x' => f t' x') = ↿f ∘ inclX t' := by
          funext x'
          rfl
        have hdl (t' : Time) : (fderiv ℝ (fun x' => f t' x') x)
          =  (fderiv ℝ (↿f) (inclX t' x)).comp (fderiv ℝ (inclX t') x) := by
          rw [hl]
          rw [fderiv_comp]
          · fun_prop
          · fun_prop
        conv_lhs =>
          enter [x']
          rw [hdl x']
        apply DifferentiableAt.clm_comp
        · apply DifferentiableAt.comp
          · exact hdd (inclT x t) (inclT x t)
          · fun_prop
        · have hl(t' : Time) : (fderiv ℝ (inclX t') x)  = ContinuousLinearMap.inr ℝ Time Space := by
            simp only [inclT]
            rw [(hasFDerivAt_prodMk_right (𝕜 := ℝ) t' x).fderiv ]
          conv_lhs =>
            enter [x']
            rw [hl x']
          fun_prop
      · fun_prop
  · fun_prop
  · exact hdd (inclT x t)

lemma differentiable_fderiv_coord_single (ft : Time → Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 ↿ft) :
    DifferentiableAt ℝ (fun t =>
    (fderiv ℝ (fun x => ft t x u) x) (EuclideanSpace.single v 1)) t := by
  apply Differentiable.clm_apply
  . let incl : Space →L[ℝ] Time × Space := {
      toFun w := (0, w)
      map_add' := by simp
      map_smul' := by simp
      }
    let inclL : Time → Time × Space := fun t => (t, x)
    let ftt : Time → Space → ℝ := fun t x => ft t x u
    let drop : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ  := {
      toFun x := x u
      map_add' := by simp
      map_smul' := by simp
      cont := by fun_prop
    }
    have hd : ContDiff ℝ 2 (↿ftt) := by
      change ContDiff ℝ 2 (fun x => (↿ft) x u)
      change ContDiff ℝ 2 (drop ∘ (↿ft))
      apply ContDiff.comp
      · exact ContinuousLinearMap.contDiff drop
      · exact hf
    have hdd : Differentiable ℝ (↿ftt) := by
      apply ContDiff.differentiable hd
      simp
    have h1 (y : ℝ) : fderiv ℝ (fun x => ftt y x) x
      = fderiv ℝ (↿ftt) (y, x) ∘L incl:= by
      ext w
      simp [incl]
      rw [fderiv_uncurry]
      exact hdd (y, x)
    conv =>
      enter [2, y]
      change fderiv ℝ (fun x => ftt y x) x
      rw [h1]
    refine Differentiable.clm_comp ?_ ?_
    · have hn (y : ℝ) :  fderiv ℝ (↿ftt) (y, x)=
        fderiv ℝ (↿ftt) (inclL y) := rfl
      conv =>
        enter [2, y]
        rw [hn]
      refine Differentiable.comp' ?_ ?_
      · have hd'' : ContDiff ℝ (1 + 1) (Function.uncurry ftt) := hd
        rw [contDiff_succ_iff_fderiv] at hd''
        have hd2 := hd''.2.2
        apply ContDiff.differentiable hd2
        rfl
      · fun_prop
    · fun_prop
  · fun_prop

lemma time_deriv_curl_commute (fₜ : Time → Space → EuclideanSpace ℝ (Fin 3)) (t : Time) (x : Space) (hf : ContDiff ℝ 2 ↿fₜ) :
    ∂ₜ (fun t => (∇ × fₜ t) x) t = (∇ × fun x => (∂ₜ (fun t => fₜ t x) t)) x:= by
  funext i
  unfold Time.deriv
  rw [fderiv_pi]
  change (fderiv ℝ (fun t => curl (fₜ t) x i) t) 1 = _
  unfold curl Space.deriv Space.coord Space.basis
  fin_cases i <;>
  . simp [-fderiv_eq_smul_deriv]
    have hd : Differentiable ℝ ↿fₜ := ContDiff.differentiable hf (hn := by decide)
    rw [fderiv_sub]
    rw [dt_dist]
    rw [fderiv_swap, fderiv_swap]
    rw [fderiv_coord, fderiv_coord]
    repeat exact hd
    repeat exact hf
    repeat
      apply differentiable_fderiv_coord_single
      exact hf
  · intro i
    unfold curl Space.deriv Space.coord Space.basis
    fin_cases i <;>
    · simp
      apply DifferentiableAt.sub
      repeat
        apply differentiable_fderiv_coord_single
        exact hf
