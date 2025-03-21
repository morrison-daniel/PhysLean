/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Pre.NormOne
import PhysLean.Relativity.Lorentz.Group.Proper
/-!
# Boosts in the Lorentz group

-/

noncomputable section

open Matrix
open Complex
open ComplexConjugate

namespace LorentzGroup

variable {d : ℕ}
variable (Λ : LorentzGroup d)

/-- The Lorentz boost with in the space direction `i` with speed `β` with
  `|β| < 1`. -/
def boost (i : Fin d) (β : ℝ) (hβ : |β| < 1) : LorentzGroup d :=
  ⟨let γ := 1 / Real.sqrt (1 - β^2)
  fun j k =>
    if k = Sum.inl 0 ∧ j = Sum.inl 0 then γ
    else if k = Sum.inl 0 ∧ j = Sum.inr i then - γ * β
    else if k = Sum.inr i ∧ j = Sum.inl 0 then - γ * β
    else if k = Sum.inr i ∧ j = Sum.inr i then γ else
    if j = k then 1 else 0, h⟩
where
  h := by
    rw [mem_iff_dual_mul_self]
    ext j k
    rw [Matrix.mul_apply]
    conv_lhs =>
      enter [2, x]
      rw [minkowskiMatrix.dual_apply]
    simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton]
    rw [minkowskiMatrix.inl_0_inl_0]
    simp
    conv_lhs =>
      enter [2, 2, x]
      rw [minkowskiMatrix.inr_i_inr_i]
    simp
    have hb1 : √(1 - β ^ 2) ^ 2 = 1 - β ^ 2 := by
      refine Real.sq_sqrt ?_
      simp
      exact le_of_lt hβ
    have hb2 : 1 - β ^ 2 ≠ 0 := by
      simp [sub_ne_zero, hb1]
      by_contra h
      have hl : 1 ^ 2 = β ^ 2 := by
        rw [← h]
        simp
      rw [sq_eq_sq_iff_abs_eq_abs] at hl
      rw [← hl] at hβ
      simp at hβ
    by_cases hj : j = Sum.inl 0
    · subst hj
      simp [minkowskiMatrix.inl_0_inl_0]
      rw [Finset.sum_eq_single i]
      · simp
        by_cases hk : k = Sum.inl 0
        · subst hk
          simp
          ring_nf
          field_simp [hb1, hb2]
          ring
        · simp [hk]
          by_cases hk' : k = Sum.inr i
          · simp [hk']
            ring
          · simp [hk', hk]
            rw [one_apply_ne fun a => hk (id (Eq.symm a))]
            rw [if_neg (by exact fun a => hk (id (Eq.symm a)))]
            rw [if_neg (by exact fun a => hk' (id (Eq.symm a)))]
            simp
      · intro b _ hb
        simp [hb]
      · simp
    · match j with
      | Sum.inl 0 => simp at hj
      | Sum.inr j =>
      rw [minkowskiMatrix.inr_i_inr_i]
      rw [Finset.sum_eq_single j]
      · by_cases hj' : j = i
        · subst hj'
          conv_lhs =>
            enter [1, 1, 2]
            simp only [Fin.isValue]
          conv_lhs =>
            enter [2, 1, 1, 2]
            simp only [Fin.isValue]
          match k with
          | Sum.inl 0 =>
            simp
            ring
          | Sum.inr k =>
          by_cases hk : k = j
          · subst hk
            simp
            ring_nf
            field_simp [hb1, hb2]
            ring
          · rw [one_apply]
            simp [hk]
            rw [if_neg (fun a => hk (id (Eq.symm a))), if_neg (fun a => hk (id (Eq.symm a)))]
        · conv_lhs =>
            enter [1, 1, 2]
            simp [hj']
          conv_lhs =>
            enter [2, 1, 1, 2]
            simp [hj']
          simp
          rw [one_apply]
          simp [hj']
      · intro b _ hb
        simp only [Fin.isValue, one_div, neg_mul, reduceCtorEq, and_self, ↓reduceIte,
          Sum.inr.injEq, false_and, and_false, hb, mul_ite, one_mul, mul_zero, mul_neg, ite_mul,
          zero_mul, mul_one]
        match k with
        | Sum.inl 0 =>
          simp
          intro h1 h2
          subst h1 h2
          simp at hb
        | Sum.inr k =>
        simp
        by_cases hb' : b = i
        · simp [hb']
          subst hb'
          simp [Ne.symm hb]
        · simp [hb']
      · simp

@[simp]
lemma boost_transpose_eq_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    transpose (boost i β hβ) = boost i β hβ := by
  ext j k
  simp [transpose, boost]
  match j, k with
  | Sum.inl 0, Sum.inl 0 => rfl
  | Sum.inl 0, Sum.inr k =>
    simp
  | Sum.inr i, Sum.inl 0 =>
    simp
  | Sum.inr j, Sum.inr k =>
    simp only [Fin.isValue, reduceCtorEq, and_self, ↓reduceIte, Sum.inr.injEq, false_and, and_false]
    conv_lhs =>
      enter [1]
      rw [and_comm]
    conv_lhs =>
      enter [3, 1]
      rw [eq_comm]

@[simp]
lemma boost_transpose_matrix_eq_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    Matrix.transpose (boost i β hβ).1 = (boost i β hβ).1 := by
  rw [← transpose_val, boost_transpose_eq_self]

@[simp]
lemma boost_zero_eq_id (i : Fin d) : boost i (β := 0) (by simp) = 1 := by
  ext j k
  simp [boost]
  match j, k with
  | Sum.inl 0, Sum.inl 0 => rfl
  | Sum.inl 0, Sum.inr k =>
    simp
  | Sum.inr i, Sum.inl 0 =>
    simp
  | Sum.inr j, Sum.inr k =>
    rw [one_apply]
    simp only [Fin.isValue, reduceCtorEq, and_self, ↓reduceIte, Sum.inr.injEq, false_and, and_false,
      ite_eq_right_iff, and_imp]
    intro h1 h2
    subst h1 h2
    simp

lemma boost_inverse (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    (boost i β hβ)⁻¹ = boost i (-β) (by simpa using hβ) := by
  rw [lorentzGroupIsGroup_inv]
  ext j k
  simp
  rw [minkowskiMatrix.dual_apply]
  match j, k with
  | Sum.inl 0, Sum.inl 0 =>
    rw [minkowskiMatrix.inl_0_inl_0]
    simp [boost]
  | Sum.inl 0, Sum.inr k =>
    rw [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
    simp [boost]
    split
    · simp
    · simp
  | Sum.inr j, Sum.inl 0 =>
    rw [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
    simp [boost]
  | Sum.inr j, Sum.inr k =>
    rw [minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.inr_i_inr_i]
    simp [boost]
    split
    · simp
      rw [if_pos]
      simp_all
    · rename_i h
      conv_rhs =>
        rw [if_neg (fun a => h (And.symm a))]
      split
      · rename_i h2
        rw [if_pos (Eq.symm h2)]
        simp
      · rename_i h2
        rw [if_neg (fun a => h2 (Eq.symm a))]
        simp

end LorentzGroup

end
