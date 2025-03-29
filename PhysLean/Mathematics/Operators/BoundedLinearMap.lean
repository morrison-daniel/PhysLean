import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Seminorm

open InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] -- [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] -- [CompleteSpace F]

-- def IsBounded (f : E →ₗ[𝕜] F) := ∃ (M : ℝ), ∀ (x : E), ‖f x‖ ≤ M * ‖x‖

variable (𝕜 E F)

structure BoundedLinearMap extends E →ₗ[𝕜] F where
  bounded : ∃ (M : ℝ), 0 ≤ M ∧ ∀ (x : E), ‖toFun x‖ ≤ M * ‖x‖

notation E "→ᵇₗ[" 𝕜 "]" F => BoundedLinearMap 𝕜 E F

namespace BoundedLinearMap

instance instFunLike : FunLike (BoundedLinearMap 𝕜 E F) E F where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

@[ext]
theorem ext {f g : E →ᵇₗ[𝕜] F} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

def eq_toLinearMap (f : E →ᵇₗ[𝕜] F) (x : E) : f x = f.toLinearMap x := rfl

instance instCoe : Coe (E →ᵇₗ[𝕜] F) (E →ₗ[𝕜] F) where
  coe f := f.toLinearMap

instance instZero : Zero (E →ᵇₗ[𝕜] F) where
  zero := BoundedLinearMap.mk 0 (by
    use 0
    simp only [le_refl, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.zero_apply,
      norm_zero, zero_mul, implies_true, and_self]
  )

theorem zero_apply (x : E) : (0 : E →ᵇₗ[𝕜] F) x = 0 := rfl

@[to_additive]
instance : AddMonoidHomClass (E →ᵇₗ[𝕜] F) E F where
  map_add f := by
    intro x y
    simp only [eq_toLinearMap, map_add]
  map_zero f := by
    simp only [eq_toLinearMap, map_zero]

variable {𝕜 E F}

noncomputable def opNorm (f : E →ᵇₗ[𝕜] F) :=
  sInf {c : ℝ | 0 ≤ c ∧ ∀ (x : E), ‖f x‖ ≤ c * ‖x‖}

noncomputable instance hasOpNorm : Norm (E →ᵇₗ[𝕜] F) where
  norm := opNorm

theorem norm_def (f : E →ᵇₗ[𝕜] F) :
    ‖f‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ (x : E), ‖f x‖ ≤ c * ‖x‖} := rfl

theorem bounds_nonempty {f : E →ᵇₗ[𝕜] F} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } := by
  obtain ⟨M, ⟨Mnneg, hM⟩⟩ := f.bounded
  use M
  simp only [Set.mem_setOf_eq]
  exact ⟨Mnneg, hM⟩

theorem bounds_bddBelow {f : E →ᵇₗ[𝕜] F} : BddBelow { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

open Set in
theorem isLeast_opNorm (f : E →ᵇₗ[𝕜] F) :
    IsLeast {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [setOf_and, setOf_forall]
  refine isClosed_Ici.inter <| isClosed_iInter fun _ ↦ isClosed_le ?_ ?_ <;> continuity

theorem opNorm_nonneg (f : E →ᵇₗ[𝕜] F) : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg fun _ ↦ And.left

theorem opNorm_zero : ‖(0 : E →ᵇₗ[𝕜] F)‖ = 0 := by
  rw [norm_def]
  apply le_antisymm
  · rw [Real.sInf_le_iff (bounds_bddBelow) (bounds_nonempty)]
    intro ε εpos
    use 0
    rw [Set.mem_setOf_eq]
    simp only [le_refl, zero_mul, norm_le_zero_iff, true_and, zero_add]
    exact ⟨by intro x; rw [zero_apply], εpos⟩
  · apply Real.le_sInf ?_ (le_refl 0)
    simp only [Set.mem_setOf_eq, and_imp]
    intro _ h _
    exact h

theorem le_opNorm (f : E →ᵇₗ[𝕜] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ := (isLeast_opNorm f).1.2 x

theorem zero_iff_zero_opNorm (f : E →ᵇₗ[𝕜] F) : f = 0 ↔ ‖f‖ = 0 := by
  constructor
  · intro h
    rw [h]
    exact opNorm_zero
  · intro h
    ext x
    rw [zero_apply, ← norm_eq_zero]
    apply le_antisymm
    · rw [← zero_mul ‖x‖, ← h]
      exact le_opNorm f x
    · apply norm_nonneg

theorem continuous_of_bounded {f : E →ᵇₗ[𝕜] F} : Continuous f := by
  by_cases h : f = 0
  · rw [h]
    exact continuous_of_const fun x => congrFun rfl
  · apply Metric.continuous_iff.mpr
    simp only [dist_eq_norm]
    intro x ε εpos
    use ε / ‖f‖
    have hnorm : ‖f‖ > 0 := by
      apply lt_of_le_of_ne (ge_iff_le.mpr (opNorm_nonneg f))
      intro hnorm
      apply h
      symm at hnorm
      exact (zero_iff_zero_opNorm f).mpr hnorm
    constructor
    · rw [gt_iff_lt]
      apply div_pos (gt_iff_lt.mp εpos) hnorm
    · intro y hxy
      rw [← mul_div_cancel₀ ε (ne_of_gt hnorm), ← map_sub]
      apply lt_of_le_of_lt (le_opNorm f _)
      apply mul_lt_mul_of_pos_left hxy (gt_iff_lt.mp hnorm)


theorem bounded_of_continuous_at_zero {f : E →ₗ[𝕜] F} (hf : ContinuousAt f 0) :
    ∃ M, 0 ≤ M ∧ ∀ (x : E), ‖f x‖ ≤ M * ‖x‖ := by
  rw [Metric.continuousAt_iff] at hf
  specialize hf 1
  simp only [gt_iff_lt, zero_lt_one, dist_zero_right, map_zero, forall_const] at hf
  obtain ⟨δ, δpos, hδ⟩ := hf
  use 2/δ
  constructor
  · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, δpos, le_of_lt]
  · intro x
    by_cases h : x = 0
    · simp only [h, map_zero, norm_zero, mul_zero, le_refl]
    · have normx : ‖x‖ ≠ 0 := by simp only [ne_eq, norm_eq_zero]; exact h
      have scalex : ‖(δ / (2 * ‖x‖) : 𝕜) • x‖ = δ / 2 := by
        rw [norm_smul]
        simp only [norm_mul, norm_div, norm_algebraMap', Real.norm_eq_abs,
          RCLike.norm_ofNat, norm_norm, abs_norm]
        rw [abs_of_pos δpos, ← div_div, div_mul_cancel₀ _ normx]
      have scalepos : δ / (2 * ‖x‖) > 0 := by
        rw [gt_iff_lt, div_pos_iff]
        left
        exact ⟨δpos, by linarith [norm_pos_iff.mpr h]⟩
      have simp : (2 * ‖x‖) / δ * ‖f ((δ / (2 * ‖x‖) : 𝕜) • x)‖ = ‖f x‖ := by
        rw [map_smul, norm_smul]
        simp only [norm_div, norm_algebraMap', Real.norm_eq_abs, abs_of_pos δpos, norm_mul,
          RCLike.norm_ofNat, abs_norm]
        ring_nf
        rw [mul_inv_cancel_right₀ (ne_of_gt δpos), mul_inv_cancel₀ normx, one_mul]
      rw [← simp, ← mul_one (2 / δ * ‖x‖)]
      apply mul_le_mul
      · apply le_of_eq
        ring
      · apply le_of_lt
        apply hδ
        linarith [scalex]
      · exact norm_nonneg _
      · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, δpos, mul_nonneg_iff_of_pos_left,
        norm_nonneg]

def ofContinuousLinearMap {f : E →ₗ[𝕜] F} (hf : Continuous f) : E →ᵇₗ[𝕜] F where
  toFun := f.toFun
  map_add' := f.map_add'
  map_smul' := f.map_smul'
  bounded := bounded_of_continuous_at_zero hf.continuousAt

end BoundedLinearMap
