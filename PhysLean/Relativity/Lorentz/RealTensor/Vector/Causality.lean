/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Basic

/-!

## Causality of Lorentz vectors

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open TensorTree
open OverColor.Discrete
noncomputable section

namespace Lorentz
open realLorentzTensor

namespace Vector

/-- Classification of lorentz vectors based on their causal character. -/
inductive CausalCharacter
  | timeLike
  | lightLike
  | spaceLike

deriving DecidableEq

/-- A Lorentz vector `p` is
- `lightLike` if `⟪p, p⟫ₘ = 0`.
- `timeLike` if `0 < ⟪p, p⟫ₘ`.
- `spaceLike` if `⟪p, p⟫ₘ < 0`.
Note that `⟪p, p⟫ₘ` is defined in the +--- convention.
-/
def causalCharacter {d : ℕ} (p : Vector d) : CausalCharacter :=
  let v0 := ⟪p, p⟫ₘ
  if v0 = 0 then CausalCharacter.lightLike
  else if 0 < v0 then CausalCharacter.timeLike
  else CausalCharacter.spaceLike

/-- `causalCharacter` are invariant under an action of the Lorentz group. -/
lemma causalCharacter_invariant {d : ℕ} (p : Vector d)
    (Λ : LorentzGroup d) :
    causalCharacter (((realLorentzTensor d).F.obj _).ρ Λ p) = causalCharacter p := by
  simp only [causalCharacter, C_eq_color, Nat.succ_eq_add_one, Nat.reduceAdd]
  rw [innerProduct_invariant]

lemma timeLike_iff_norm_sq_pos {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.timeLike ↔ 0 < ⟪p, p⟫ₘ := by
  simp only [causalCharacter]
  split
  · rename_i h
    simp only [reduceCtorEq, h, lt_self_iff_false]
  · split
    · rename_i h
      simp only [h]
    · rename_i h
      simp only [reduceCtorEq, false_iff, not_lt]
      linarith

lemma lightLike_iff_norm_sq_zero {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.lightLike ↔ ⟪p, p⟫ₘ = 0 := by
  simp only [causalCharacter]
  split
  · rename_i h
    simp only [reduceCtorEq, h, eq_self_iff_true]
  · rename_i h
    simp [h]
    split
    · simp
    · simp

lemma spaceLike_iff_norm_sq_neg {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.spaceLike ↔ ⟪p, p⟫ₘ < 0 := by
  simp only [causalCharacter]
  split
  · rename_i h
    simp only [reduceCtorEq, h, lt_self_iff_false]
  · split
    · rename_i h
      simp only [reduceCtorEq, false_iff, not_lt]
      exact le_of_lt h
    · rename_i h1 h2
      simp only [true_iff]
      rw [not_lt_iff_eq_or_lt] at h2
      rw [eq_comm] at h2
      simp_all

/-- The Lorentz vector `p` and `-p` have the same causalCharacter -/
lemma neg_causalCharacter_eq_self {d : ℕ} (p : Vector d) :
    causalCharacter (-p) = causalCharacter p := by
  have h : ⟪-p, -p⟫ₘ = ⟪p, p⟫ₘ := by
    simp [innerProduct_toCoord, toCoord]
  simp [causalCharacter, h]

/-- The future light cone of a Lorentz vector `p` is defined as those
  vectors `q` such that
- `causalCharacter (q - p)` is `timeLike` and
- `(q - p) (Sum.inl 0)` is positive. -/
def interiorFutureLightCone {d : ℕ} (p : Vector d) : Set (Vector d) :=
    {q | causalCharacter (q - p) = .timeLike ∧ 0 < (q - p) (Sum.inl 0)}

/-- The backward light cone of a Lorentz vector `p` is defined as those
  vectors `q` such that
- `causalCharacter (q - p)` is `timeLike` and
- `(q - p) (Sum.inl 0)` is negative. -/
def interiorPastLightCone {d : ℕ} (p : Vector d) : Set (Vector d) :=
    {q | causalCharacter (q - p) = .timeLike ∧ (q - p) (Sum.inl 0) < 0}

/-- The light cone boundary (null surface) of a spacetime point `p`. -/
def lightConeBoundary {d : ℕ} (p : Vector d) : Set (Vector d) :=
  {q | causalCharacter (q - p) = .lightLike}

/-- The future light cone boundary (null surface) of a spacetime point `p`. -/
def futureLightConeBoundary {d : ℕ} (p : Vector d) : Set (Vector d) :=
  {q | causalCharacter (q - p) = .lightLike ∧ 0 ≤ (q - p) (Sum.inl 0)}

/-- The past light cone boundary (null surface) of a spacetime point `p`. -/
def pastLightConeBoundary {d : ℕ} (p : Vector d) : Set (Vector d) :=
  {q | causalCharacter (q - p) = .lightLike ∧ (q - p) (Sum.inl 0) ≤ 0}

/-- Any point `p` lies on its own light cone boundary, as `p - p = 0` has
    zero Minkowski norm squared. -/
lemma self_mem_lightConeBoundary {d : ℕ} (p : Vector d) : p ∈ lightConeBoundary p := by
  simp [lightConeBoundary]
  have : p - p = 0 := by simp
  rw [← this]
  simp only [causalCharacter]
  have h0 : ⟪(0 : Vector d), 0⟫ₘ = 0 := by
    simp [innerProduct_zero_left]
  simp [h0]

/-- A proposition which is true if `q` is in the causal future of event `p`. -/
def causallyFollows {d : ℕ} (p q : Vector d) : Prop :=
  q ∈ interiorFutureLightCone p ∨ q ∈ futureLightConeBoundary p

/-- A proposition which is true if `q` is in the causal past of event `p`. -/
def causallyPrecedes {d : ℕ} (p q : Vector d) : Prop :=
  q ∈ interiorPastLightCone p ∨ q ∈ pastLightConeBoundary p

/-- Events `p` and `q` are causally related. -/
def causallyRelated {d : ℕ} (p q : Vector d) : Prop :=
  causallyFollows p q ∨ causallyFollows q p

/-- Events p and q are causally unrelated (spacelike separated). -/
def causallyUnrelated {d : ℕ} (p q : Vector d) : Prop :=
  causalCharacter (p - q) = CausalCharacter.spaceLike

/-- The causal diamond between events p and q, where p is assumed to causally precede q. -/
def causalDiamond {d : ℕ} (p q : Vector d) : Set (Vector d) :=
  {r | causallyFollows p r ∧ causallyFollows r q}

-- Zero vector has zero Minkowski norm squared
@[simp]
lemma causalCharacter_zero {d : ℕ} : causalCharacter (0 : Vector d) =
  CausalCharacter.lightLike := by
  simp  [causalCharacter, lightLike_iff_norm_sq_zero]

/-- Causally preceding is reflexive -/
@[simp]
lemma causallyPrecedes_refl {d : ℕ} (p : Vector d) : causallyPrecedes p p := by
  right; simp [pastLightConeBoundary]

/-- For timelike vectors in Minkowski space, the squared time component exceeds
    the sum of squared spatial components -/
@[simp]
lemma timelike_time_dominates_space {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ∑ i, v (Sum.inr i) * v (Sum.inr i) < v (Sum.inl 0) * v (Sum.inl 0) := by
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [innerProduct_toCoord] at hv
  simp at hv
  linarith

/-- For two lightlike vectors with equal time components, their spatial parts
    have equal Euclidean norms -/
@[simp]
lemma lightlike_equal_time_eq_spatial_norm {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_time : v (Sum.inl 0) = w (Sum.inl 0)) :
    ∑ i, v (Sum.inr i) * v (Sum.inr i) = ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
  rw [lightLike_iff_norm_sq_zero, innerProduct_toCoord] at hv hw
  have hv_eq : v (Sum.inl 0) * v (Sum.inl 0) = ∑ i, v (Sum.inr i) * v (Sum.inr i) := by
    dsimp only [Fin.isValue]; linarith
  have hw_eq : w (Sum.inl 0) * w (Sum.inl 0) = ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    dsimp only [Fin.isValue];linarith
  have h_time_sq : v (Sum.inl 0) * v (Sum.inl 0) = w (Sum.inl 0) * w (Sum.inl 0) := by
    rw [h_time]
  rw [← hv_eq, ← hw_eq, h_time_sq]

/-- The Cauchy-Schwarz inequality for vectors in ℝⁿ -/
@[simp]
lemma cauchy_schwarz {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) :
    (∑ i, v i * w i)^2 ≤ (∑ i, v i * v i) * (∑ i, w i * w i) :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (fun i _ => mul_self_nonneg (v i))
    (fun i _ => mul_self_nonneg (w i))
    (fun i _ => by ring)

-- Define spatial part extractors
/-- Extract spatial components from a Lorentz vector,
    returning them as a vector in Euclidean space. -/
def spatialPart {d : ℕ} (v : Vector d) : EuclideanSpace ℝ (Fin d) :=
  fun i => v (Sum.inr i)

-- Alternative version using sum notation instead of inner product
lemma spatial_cauchy_schwarz_sum {d : ℕ} (v w : Vector d) :
    (∑ i, (spatialPart v) i * (spatialPart w) i)^2 ≤
    (∑ i, (spatialPart v) i * (spatialPart v) i) * (∑ i,
    (spatialPart w) i * (spatialPart w) i) := by
      exact cauchy_schwarz (spatialPart v) (spatialPart w)

/-- Cauchy-Schwarz inequality for the spatial components of Lorentz vectors -/
lemma spatial_cauchy_schwarz {d : ℕ} (v w : Vector d) :
    (∑ i, v (Sum.inr i) * w (Sum.inr i))^2 ≤
    (∑ i, v (Sum.inr i) * v (Sum.inr i)) * (∑ i, w (Sum.inr i) * w (Sum.inr i)) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ ?_ ?_ ?_
  · intro i _; exact mul_self_nonneg (v (Sum.inr i))
  · intro i _; exact mul_self_nonneg (w (Sum.inr i))
  · intro i _; rw [pow_two, ← pow_two]; ring

/-- For nonzero timelike vectors, the time component is nonzero -/
@[simp]
lemma time_component_ne_zero_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    v (Sum.inl 0) ≠ 0 := by
  by_contra h
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [innerProduct_toCoord] at hv
  simp at hv
  rw [h] at hv
  simp at hv
  have h_spatial_nonneg : 0 ≤ ∑ i, v (Sum.inr i) * v (Sum.inr i) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (v (Sum.inr i)))
  exact lt_irrefl 0 (h_spatial_nonneg.trans_lt hv)

/-- Time component squared is positive for timelike vectors -/
@[simp]
lemma time_squared_pos_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    0 < (v (Sum.inl 0))^2 := by
  have h_nonzero : v (Sum.inl 0) ≠ 0 := time_component_ne_zero_of_timelike hv
  exact pow_two_pos_of_ne_zero h_nonzero

/-- If a vector has zero norm, then all its components are zero -/
lemma vector_zero_of_sum_sq_zero {d : ℕ} {v : EuclideanSpace ℝ (Fin d)}
    (h : ∑ i, v i * v i = 0) : ∀ i, v i = 0 := by
  intro i
  have h_each_zero : v i * v i = 0 := by
    have h_all_nonneg : ∀ j ∈ Finset.univ, 0 ≤ v j * v j :=
      fun j _ => mul_self_nonneg (v j)
    have h_all_zero : ∀ j ∈ Finset.univ, v j * v j = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg h_all_nonneg).mp
      exact h
    exact h_all_zero i (Finset.mem_univ i)
  exact zero_eq_mul_self.mp (id (Eq.symm h_each_zero))

/-- The zero vector is proportional to any vector -/
@[simp]
lemma zero_parallel_to_any {d : ℕ} {v : Vector d} :
    ∃ (r : ℝ), (∀ (a : Fin 1), r = 0 ∨ v (Sum.inl a) = 0) ∧
    ∀ (b : Fin d), r = 0 ∨ v (Sum.inr b) = 0 := by
  use 0
  constructor
  · intro a; left; rfl
  · intro b; left; rfl

/-- For Cauchy-Schwarz equality, if one vector has zero norm squared,
    then the vectors are proportional -/
@[simp]
lemma parallel_of_cauchy_eq_of_zero_norm {d : ℕ} {v w : EuclideanSpace ℝ (Fin d)}
    (h_v_zero : ∑ i, v i * v i = 0) :
    ∃ (r : ℝ), ∀ i, v i = r * w i := by
  have h_v_comp_zero : ∀ i, v i = 0 := vector_zero_of_sum_sq_zero h_v_zero
  use 0; intro i; rw [h_v_comp_zero i, zero_mul]

/- For Cauchy-Schwarz equality with non-zero vectors, there's a specific relationship
   between the vectors' inner product and their norms -/
@[simp]
lemma scalar_ratio_of_cauchy_eq {d : ℕ} {v w : EuclideanSpace ℝ (Fin d)}
    (h_eq : (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i))
    (h_w_nonzero : ∑ i, w i * w i ≠ 0) :
    let r := (∑ i, v i * w i) / (∑ i, w i * w i)
    (∑ i, (v i - r * w i) * (v i - r * w i)) = 0 := by
  intro r
  calc ∑ i, (v i - r * w i) * (v i - r * w i)
    _ = ∑ i, v i * v i - 2 * r * ∑ i, v i * w i + r^2 * ∑ i, w i * w i := by
      simp_rw [sub_mul, mul_sub]
      simp_rw [Finset.sum_sub_distrib]
      have : ∑ i, v i * v i - ∑ i, v i * (r * w i) -
            (∑ i, r * w i * v i - ∑ i, r * w i * (r * w i)) =
             ∑ i, v i * v i - 2 * r * ∑ i, v i * w i + r^2 * ∑ i, w i * w i := by
        have h1 : ∑ i, v i * (r * w i) = r * ∑ i, v i * w i := by
          have : ∀ i, v i * (r * w i) = r * (v i * w i) := by
            intro i; ring
          simp_rw [this]
          exact Eq.symm (Finset.mul_sum Finset.univ (fun i => v i * w i) r)
        have h2 : ∑ i, r * w i * v i = r * ∑ i, w i * v i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [mul_comm (w i) (v i)];
          ring
        have h3 : ∑ i, r * w i * (r * w i) = r^2 * ∑ i, w i * w i := by
          have : ∀ i, r * w i * (r * w i) = r^2 * (w i * w i) := by
            intro i; ring
          simp_rw [this]; rw [Finset.mul_sum]
        rw [h1, h2, h3]
        have h4 : ∑ i, w i * v i = ∑ i, v i * w i := by
          apply Finset.sum_congr rfl; intro i _; rw [mul_comm]
        rw [h4]; ring
      exact this
    _ = ∑ i, v i * v i - 2 * (∑ i, v i * w i)^2 / (∑ i, w i * w i) +
        (∑ i, v i * w i)^2 / (∑ i, w i * w i) := by
      unfold r
      have h_middle : 2 * ((∑ i, v i * w i) / (∑ i, w i * w i)) * (∑ i, v i * w i) =
                          2 * (∑ i, v i * w i)^2 / (∑ i, w i * w i) := by
            have h1 : 2 * ((∑ i, v i * w i) / (∑ i, w i * w i)) * (∑ i, v i * w i) =
                      2 * (∑ i, v i * w i) * ((∑ i, v i * w i) / (∑ i, w i * w i)) := by ring
            rw [h1]; ring
      have h_last : ((∑ i, v i * w i) / (∑ i, w i * w i))^2 * (∑ i, w i * w i) =
                   (∑ i, v i * w i)^2 / (∑ i, w i * w i) := by
        field_simp [h_w_nonzero]; ring
      rw [h_middle, h_last]
    _ = ∑ i, v i * v i - (∑ i, v i * w i)^2 / (∑ i, w i * w i) := by
      ring
    _ = ∑ i, v i * v i - (∑ i, v i * v i) := by
      rw [h_eq, mul_div_cancel_right₀ _ h_w_nonzero]
    _ = 0 := by simp only [sub_self]

/-- For Cauchy-Schwarz equality with non-zero second vector,
    the first vector is proportional to the second -/
@[simp]
lemma parallel_of_cauchy_eq_second_nonzero {d : ℕ} {v w : EuclideanSpace ℝ (Fin d)}
    (h_eq : (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i))
    (h_w_nonzero : ∑ i, w i * w i ≠ 0) :
    ∃ (r : ℝ), ∀ i, v i = r * w i := by
  let r := (∑ i, v i * w i) / (∑ i, w i * w i)
  have h_zero_diff : ∑ i, (v i - r * w i) * (v i - r * w i) = 0 :=
    scalar_ratio_of_cauchy_eq h_eq h_w_nonzero
  have h_each_zero : ∀ i, v i - r * w i = 0 := vector_zero_of_sum_sq_zero h_zero_diff
  use r; intro i; exact eq_of_sub_eq_zero (h_each_zero i)

/-- When vectors aren't parallel, the Cauchy-Schwarz inequality is strict -/
@[simp]
lemma cauchy_schwarz_eq_iff_parallel_of_nonzero {d : ℕ} {v w : EuclideanSpace ℝ (Fin d)}
    (hw : ∑ i, w i * w i ≠ 0) :
    (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i) ↔
    ∃ (r : ℝ), ∀ i, v i = r * w i := by
  constructor
  · intro h_eq
    exact parallel_of_cauchy_eq_second_nonzero h_eq hw
  · intro h_parallel
    rcases h_parallel with ⟨r, h_r⟩
    have h_left : ∑ i, v i * w i = r * ∑ i, w i * w i := by
      simp_rw [h_r]
      simp [mul_assoc]; exact Eq.symm (Finset.mul_sum Finset.univ (fun i => w i * w i) r)
    have h_right : ∑ i, v i * v i = r^2 * ∑ i, w i * w i := by
      simp_rw [h_r]
      simp only [mul_assoc]
      have h_substitution : ∀ i, r * (w i * (r * w i)) = r^2 * (w i * w i) := by
          intro i; ring
      simp_rw [h_substitution]
      simp [Finset.mul_sum]
    calc (∑ i, v i * w i)^2
      _ = (r * ∑ i, w i * w i)^2 := by rw [h_left]
      _ = r^2 * (∑ i, w i * w i)^2 := by ring
      _ = (r^2 * ∑ i, w i * w i) * (∑ i, w i * w i) := by ring
      _ = (∑ i, v i * v i) * (∑ i, w i * w i) := by rw [h_right]

/-- If one vector is a scalar multiple of another, they are parallel -/
@[simp]
lemma parallel_of_scalar_multiple {d : ℕ} {v w : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (h : ∀ i, v i = r * w i) : ∃ (s : ℝ), ∀ i, v i = s * w i := by
  exists r

/-- For orthogonal vectors (inner product zero), Cauchy-Schwarz is an equality
    iff one of them is zero -/
@[simp]
lemma cauchy_schwarz_eq_of_orthogonal {d : ℕ} {v w : EuclideanSpace ℝ (Fin d)}
    (h_ortho : ∑ i, v i * w i = 0) :
    (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i) ↔
    (∑ i, v i * v i = 0) ∨ (∑ i, w i * w i = 0) := by
  rw [h_ortho, pow_two, zero_mul]
  constructor
  · intro h
    rw [eq_comm] at h
    exact mul_eq_zero.mp h
  · intro h
    rw [eq_comm]
    exact mul_eq_zero.mpr h

/-- For non-parallel vectors, the Cauchy-Schwarz inequality is strict -/
@[simp]
lemma strict_cauchy_schwarz_of_not_parallel {d : ℕ} {v w : EuclideanSpace ℝ (Fin d)}
    (h_not_parallel : ¬∃ (r : ℝ), ∀ i, v i = r * w i)
    (h_w_nonzero : ∑ i, w i * w i ≠ 0) :
    (∑ i, v i * w i)^2 < (∑ i, v i * v i) * (∑ i, w i * w i) := by
  have h_cs := cauchy_schwarz v w
  by_contra h
  push_neg at h
  rw [←not_lt] at h
  have h_eq : (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i) := by
    apply le_antisymm
    · exact h_cs
    · exact le_of_not_lt h
  have h_parallel := parallel_of_cauchy_eq_second_nonzero h_eq h_w_nonzero
  exact h_not_parallel h_parallel

/-- If two lightlike vectors have parallel spatial components, their temporal components
must also be proportional, which implies the entire vectors are proportional -/
@[simp]
lemma lightlike_spatial_parallel_implies_proportional {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_spatial_parallel : ∃ (r : ℝ), ∀ i, v (Sum.inr i) = r * w (Sum.inr i)) :
    ∃ (r : ℝ), |v (Sum.inl 0)| = |r| * |w (Sum.inl 0)| := by
  rcases h_spatial_parallel with ⟨r, hr⟩
  rw [lightLike_iff_norm_sq_zero] at hv hw
  rw [innerProduct_toCoord] at hv hw
  have hv_eq : v (Sum.inl 0) * v (Sum.inl 0) = ∑ i, v (Sum.inr i) * v (Sum.inr i) := by
    simp_all only [Fin.isValue]
    linarith
  have hw_eq : w (Sum.inl 0) * w (Sum.inl 0) = ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    simp_all only [Fin.isValue, sub_self]
    linarith
  have h_spatial_sum : ∑ i, v (Sum.inr i) * v (Sum.inr i) =
      r^2 * ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    calc ∑ i, v (Sum.inr i) * v (Sum.inr i)
      _ = ∑ i, (r * w (Sum.inr i)) * (r * w (Sum.inr i)) := by
          simp_rw [hr]
      _ = ∑ i, r^2 * (w (Sum.inr i) * w (Sum.inr i)) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ = r^2 * ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
          rw [Finset.mul_sum]
  have h_time_sq : v (Sum.inl 0) * v (Sum.inl 0) = r^2 * (w (Sum.inl 0) * w (Sum.inl 0)) := by
    rw [hv_eq, h_spatial_sum, hw_eq]
  have h_abs : |v (Sum.inl 0)| * |v (Sum.inl 0)| = |r|^2 * (|w (Sum.inl 0)| *
      |w (Sum.inl 0)|) := by
    have h2 : |w (Sum.inl 0)|^2 = |w (Sum.inl 0)| * |w (Sum.inl 0)| := by ring
    have h3 : |v (Sum.inl 0)|^2 = |v (Sum.inl 0) * v (Sum.inl 0)| := by rw [pow_two, ← abs_mul]
    have h4 : |w (Sum.inl 0)|^2 = |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [pow_two, ← abs_mul]
    have h5 : |v (Sum.inl 0) * v (Sum.inl 0)| = |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| := by
      rw [h_time_sq]
    have h6 : |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| =
      |r^2| * |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [abs_mul]
    have h7 : |r^2| = |r|^2 := by rw [abs_pow]
    calc |v (Sum.inl 0)| * |v (Sum.inl 0)|
      _ = |v (Sum.inl 0)|^2 := by rw [pow_two]
      _ = |v (Sum.inl 0) * v (Sum.inl 0)| := h3
      _ = |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| := h5
      _ = |r^2| * |w (Sum.inl 0) * w (Sum.inl 0)| := h6
      _ = |r|^2 * |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [h7]
      _ = |r|^2 * |w (Sum.inl 0) * w (Sum.inl 0)| := by rfl
      _ = |r|^2 * |w (Sum.inl 0)|^2 := by rw [← h4]
      _ = |r|^2 * (|w (Sum.inl 0)| * |w (Sum.inl 0)|) := by
        rw [pow_two]; exact congrArg (HMul.hMul (|r| * |r|)) h2
  have h_abs_eq : |v (Sum.inl 0)| = |r| * |w (Sum.inl 0)| := by
    have h_sq : |v (Sum.inl 0)|^2 = (|r| * |w (Sum.inl 0)|)^2 := by
      calc |v (Sum.inl 0)|^2
        _ = |v (Sum.inl 0)| * |v (Sum.inl 0)| := by rw [pow_two]
        _ = |r|^2 * (|w (Sum.inl 0)| * |w (Sum.inl 0)|) := by exact h_abs
        _ = |r|^2 * |w (Sum.inl 0)|^2 := by rw [← pow_two]
        _ = (|r| * |w (Sum.inl 0)|)^2 := by ring
    have h_both_nonneg : |v (Sum.inl 0)| ≥ 0 ∧ |r| * |w (Sum.inl 0)| ≥ 0 := by
      constructor
      · exact abs_nonneg (v (Sum.inl 0))
      · exact mul_nonneg (abs_nonneg r) (abs_nonneg (w (Sum.inl 0)))
    have h_sqrt : ∀ (a b : ℝ), a ≥ 0 → b ≥ 0 → a^2 = b^2 → a = b := by
      intros a b ha hb h_eq
      apply le_antisymm
      · by_contra h_not_le
        push_neg at h_not_le
        have : a^2 > b^2 := by
          exact (sq_lt_sq₀ hb ha).mpr h_not_le
        linarith
      · by_contra h_not_ge
        push_neg at h_not_ge
        have : a^2 < b^2 := by
          exact (sq_lt_sq₀ ha hb).mpr h_not_ge
        linarith
    exact h_sqrt |v (Sum.inl 0)| (|r| * |w (Sum.inl 0)|)
      h_both_nonneg.1 h_both_nonneg.2 h_sq
  use r
