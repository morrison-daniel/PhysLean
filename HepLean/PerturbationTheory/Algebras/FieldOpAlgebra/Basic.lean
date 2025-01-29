/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.SuperCommute
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.TwoSidedIdeal.Operations
/-!

# Field operator algebra

-/

namespace FieldSpecification
open CrAnAlgebra
open HepLean.List
open FieldStatistic

variable (𝓕 : FieldSpecification)

/-- The set contains the super-commutors equal to zero in the operator algebra.
  This contains e.g. the super-commutor of two creation operators. -/
def fieldOpIdealSet : Set (CrAnAlgebra 𝓕) :=
  { x |
    (∃ (φ1 φ2 φ3 : 𝓕.CrAnStates),
        x = [ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca)
    ∨ (∃ (φc φc' : 𝓕.CrAnStates) (_ : 𝓕 |>ᶜ φc = .create) (_ : 𝓕 |>ᶜ φc' = .create),
      x = [ofCrAnState φc, ofCrAnState φc']ₛca)
    ∨ (∃ (φa φa' : 𝓕.CrAnStates) (_ : 𝓕 |>ᶜ φa = .annihilate) (_ : 𝓕 |>ᶜ φa' = .annihilate),
      x = [ofCrAnState φa, ofCrAnState φa']ₛca)
    ∨ (∃ (φ φ' : 𝓕.CrAnStates) (_ : ¬ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φ')),
      x = [ofCrAnState φ, ofCrAnState φ']ₛca)}

/-- The algebra spanned by cr and an parts of fields, with appropriate super-commutors
  set to zero. -/
abbrev FieldOpAlgebra : Type := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.Quotient

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-- The instance of a setoid on `CrAnAlgebra` from the ideal `TwoSidedIdeal`. -/
instance : Setoid (CrAnAlgebra 𝓕) := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.toSetoid

lemma equiv_iff_sub_mem_ideal (x y : CrAnAlgebra 𝓕) :
    x ≈ y ↔ x - y ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [← TwoSidedIdeal.rel_iff]
  rfl

/-- The projection of `CrAnAlgebra` down to `FieldOpAlgebra` as an algebra map. -/
def ι : CrAnAlgebra 𝓕 →ₐ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.mk'
  map_one' := by rfl
  map_mul' x y := by rfl
  map_zero' := by rfl
  map_add' x y := by rfl
  commutes' x := by rfl

lemma ι_surjective : Function.Surjective (@ι 𝓕) := by
  intro x
  obtain ⟨x⟩ := x
  use x
  rfl

lemma ι_apply (x : CrAnAlgebra 𝓕) : ι x = Quotient.mk _ x := rfl

lemma ι_of_mem_fieldOpIdealSet (x : CrAnAlgebra 𝓕) (hx : x ∈ 𝓕.fieldOpIdealSet) :
    ι x = 0 := by
  rw [ι_apply]
  change ⟦x⟧ = ⟦0⟧
  simp only [ringConGen, Quotient.eq]
  refine RingConGen.Rel.of x 0 ?_
  simpa using hx

lemma ι_superCommute_of_create_create (φc φc' : 𝓕.CrAnStates) (hφc : 𝓕 |>ᶜ φc = .create)
    (hφc' : 𝓕 |>ᶜ φc' = .create) : ι [ofCrAnState φc, ofCrAnState φc']ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_and_left, Set.mem_setOf_eq]
  simp only [exists_prop]
  right
  left
  use φc, φc', hφc, hφc'

lemma ι_superCommute_of_annihilate_annihilate (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕 |>ᶜ φa = .annihilate) (hφa' : 𝓕 |>ᶜ φa' = .annihilate) :
    ι [ofCrAnState φa, ofCrAnState φa']ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_and_left, Set.mem_setOf_eq]
  simp only [exists_prop]
  right
  right
  left
  use φa, φa', hφa, hφa'

lemma ι_superCommute_of_diff_statistic {φ ψ : 𝓕.CrAnStates}
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) : ι [ofCrAnState φ, ofCrAnState ψ]ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq]
  right
  right
  right
  use φ, ψ

lemma ι_superCommute_zero_of_fermionic (φ ψ : 𝓕.CrAnStates)
    (h : [ofCrAnState φ, ofCrAnState ψ]ₛca ∈ statisticSubmodule fermionic) :
    ι [ofCrAnState φ, ofCrAnState ψ]ₛca = 0 := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton] at h ⊢
  rcases statistic_neq_of_superCommute_fermionic h with h | h
  · simp [ofCrAnList_singleton]
    apply ι_superCommute_of_diff_statistic
    simpa using h
  · simp [h]

lemma ι_superCommute_ofCrAnState_ofCrAnState_bosonic_or_zero (φ ψ : 𝓕.CrAnStates) :
    [ofCrAnState φ, ofCrAnState ψ]ₛca ∈ statisticSubmodule bosonic ∨
    ι [ofCrAnState φ, ofCrAnState ψ]ₛca = 0 := by
  rcases superCommute_ofCrAnList_ofCrAnList_bosonic_or_fermionic [φ] [ψ] with h | h
  · simp_all [ofCrAnList_singleton]
  · simp_all [ofCrAnList_singleton]
    right
    exact ι_superCommute_zero_of_fermionic _ _ h

/-!

## Super-commutes are in the center

-/

@[simp]
lemma ι_superCommute_ofCrAnState_superCommute_ofCrAnState_ofCrAnState (φ1 φ2 φ3 : 𝓕.CrAnStates) :
    ι [ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq]
  left
  use φ1, φ2, φ3

@[simp]
lemma ι_superCommute_superCommute_ofCrAnState_ofCrAnState_ofCrAnState (φ1 φ2 φ3 : 𝓕.CrAnStates) :
    ι [[ofCrAnState φ1, ofCrAnState φ2]ₛca, ofCrAnState φ3]ₛca = 0 := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rcases superCommute_ofCrAnList_ofCrAnList_bosonic_or_fermionic [φ1] [φ2] with h | h
  · rw [bonsonic_superCommute_symm h]
    simp [ofCrAnList_singleton]
  · rcases ofCrAnList_bosonic_or_fermionic [φ3] with h' | h'
    · rw [superCommute_bonsonic_symm h']
      simp [ofCrAnList_singleton]
    · rw [superCommute_fermionic_fermionic_symm h h']
      simp [ofCrAnList_singleton]

@[simp]
lemma ι_superCommute_superCommute_ofCrAnState_ofCrAnState_ofCrAnList (φ1 φ2 : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates) :
    ι [[ofCrAnState φ1, ofCrAnState φ2]ₛca, ofCrAnList φs]ₛca = 0 := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rcases superCommute_ofCrAnList_ofCrAnList_bosonic_or_fermionic [φ1] [φ2] with h | h
  · rw [superCommute_bosonic_ofCrAnList_eq_sum _ _ h]
    simp [ofCrAnList_singleton]
  · rw [superCommute_fermionic_ofCrAnList_eq_sum _ _ h]
    simp [ofCrAnList_singleton]

@[simp]
lemma ι_superCommute_superCommute_ofCrAnState_ofCrAnState_crAnAlgebra (φ1 φ2 : 𝓕.CrAnStates)
    (a : 𝓕.CrAnAlgebra) : ι [[ofCrAnState φ1, ofCrAnState φ2]ₛca, a]ₛca = 0 := by
  change (ι.toLinearMap ∘ₗ superCommute [ofCrAnState φ1, ofCrAnState φ2]ₛca) a = _
  have h1 : (ι.toLinearMap ∘ₗ superCommute [ofCrAnState φ1, ofCrAnState φ2]ₛca) = 0 := by
    apply (ofCrAnListBasis.ext fun l ↦ ?_)
    simp
  rw [h1]
  simp

lemma ι_commute_crAnAlgebra_superCommute_ofCrAnState_ofCrAnState (φ1 φ2 : 𝓕.CrAnStates)
    (a : 𝓕.CrAnAlgebra) : ι a * ι [ofCrAnState φ1, ofCrAnState φ2]ₛca -
    ι [ofCrAnState φ1, ofCrAnState φ2]ₛca * ι a = 0 := by
  rcases ι_superCommute_ofCrAnState_ofCrAnState_bosonic_or_zero φ1 φ2 with h | h
  swap
  · simp [h]
  trans - ι [[ofCrAnState φ1, ofCrAnState φ2]ₛca, a]ₛca
  · rw [bosonic_superCommute h]
    simp
  · simp

lemma ι_superCommute_ofCrAnState_ofCrAnState_mem_center (φ ψ : 𝓕.CrAnStates) :
    ι [ofCrAnState φ, ofCrAnState ψ]ₛca ∈ Subalgebra.center ℂ 𝓕.FieldOpAlgebra := by
  rw [Subalgebra.mem_center_iff]
  intro a
  obtain ⟨a, rfl⟩ := ι_surjective a
  have h0 := ι_commute_crAnAlgebra_superCommute_ofCrAnState_ofCrAnState φ ψ a
  trans ι ((superCommute (ofCrAnState φ)) (ofCrAnState ψ)) * ι a + 0
  swap
  simp
  rw [← h0]
  abel

/-!

## The kernal of ι
-/

lemma ι_eq_zero_iff_mem_ideal (x : CrAnAlgebra 𝓕) :
    ι x = 0 ↔ x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [ι_apply]
  change ⟦x⟧ = ⟦0⟧ ↔ _
  simp only [ringConGen, Quotient.eq]
  rw [TwoSidedIdeal.mem_iff]
  simp only
  rfl

lemma bosonicProj_mem_fieldOpIdealSet_or_zero (x : CrAnAlgebra 𝓕) (hx : x ∈ 𝓕.fieldOpIdealSet) :
    x.bosonicProj.1 ∈ 𝓕.fieldOpIdealSet ∨ x.bosonicProj = 0 := by
  have hx' := hx
  simp [fieldOpIdealSet] at hx
  rcases hx with ⟨φ1, φ2, φ3, rfl⟩ | ⟨φc, φc', hφc, hφc', rfl⟩ | ⟨φa, φa', hφa, hφa', rfl⟩ |
    ⟨φ, φ', hdiff, rfl⟩
  · rcases superCommute_superCommute_ofCrAnState_bosonic_or_fermionic φ1 φ2 φ3 with h | h
    · left
      rw [bosonicProj_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProj_of_mem_fermionic _ h]
  · rcases superCommute_ofCrAnState_ofCrAnState_bosonic_or_fermionic φc φc' with h | h
    · left
      rw [bosonicProj_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProj_of_mem_fermionic _ h]
  · rcases superCommute_ofCrAnState_ofCrAnState_bosonic_or_fermionic φa φa' with h | h
    · left
      rw [bosonicProj_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProj_of_mem_fermionic _ h]
  · rcases superCommute_ofCrAnState_ofCrAnState_bosonic_or_fermionic φ φ' with h | h
    · left
      rw [bosonicProj_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProj_of_mem_fermionic _ h]

lemma fermionicProj_mem_fieldOpIdealSet_or_zero (x : CrAnAlgebra 𝓕) (hx : x ∈ 𝓕.fieldOpIdealSet) :
    x.fermionicProj.1 ∈ 𝓕.fieldOpIdealSet ∨ x.fermionicProj = 0 := by
  have hx' := hx
  simp [fieldOpIdealSet] at hx
  rcases hx with ⟨φ1, φ2, φ3, rfl⟩ | ⟨φc, φc', hφc, hφc', rfl⟩ | ⟨φa, φa', hφa, hφa', rfl⟩ |
    ⟨φ, φ', hdiff, rfl⟩
  · rcases superCommute_superCommute_ofCrAnState_bosonic_or_fermionic φ1 φ2 φ3 with h | h
    · right
      rw [fermionicProj_of_mem_bosonic _ h]
    · left
      rw [fermionicProj_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommute_ofCrAnState_ofCrAnState_bosonic_or_fermionic φc φc' with h | h
    · right
      rw [fermionicProj_of_mem_bosonic _ h]
    · left
      rw [fermionicProj_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommute_ofCrAnState_ofCrAnState_bosonic_or_fermionic φa φa' with h | h
    · right
      rw [fermionicProj_of_mem_bosonic _ h]
    · left
      rw [fermionicProj_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommute_ofCrAnState_ofCrAnState_bosonic_or_fermionic φ φ' with h | h
    · right
      rw [fermionicProj_of_mem_bosonic _ h]
    · left
      rw [fermionicProj_of_mem_fermionic _ h]
      simpa using hx'

lemma bosonicProj_mem_ideal (x : CrAnAlgebra 𝓕) (hx : x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) :
    x.bosonicProj.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hx
  let p {k : Set 𝓕.CrAnAlgebra} (a : CrAnAlgebra 𝓕) (h : a ∈ AddSubgroup.closure k) : Prop :=
    a.bosonicProj.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet
  change p x hx
  apply AddSubgroup.closure_induction
  · intro x hx
    simp [p]
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨d, hd, y, hy, rfl⟩ := Set.mem_mul.mp ha
    rw [bosonicProj_mul, bosonicProj_mul, fermionicProj_mul]
    simp [mul_add, add_mul]
    rcases fermionicProj_mem_fieldOpIdealSet_or_zero y hy with hfy | hfy
      <;> rcases bosonicProj_mem_fieldOpIdealSet_or_zero y hy with hby | hby
    · apply TwoSidedIdeal.add_mem
      apply TwoSidedIdeal.add_mem
      · /- boson, boson, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProj d) * ↑(bosonicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProj d
          simp
          use (bosonicProj y).1
          simp [hby]
        · use ↑(bosonicProj b)
          simp
      · /- fermion, fermion, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProj d) * ↑(fermionicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProj d
          simp
          use (fermionicProj y).1
          simp [hby, hfy]
        · use ↑(bosonicProj b)
          simp
      apply TwoSidedIdeal.add_mem
      · /- boson, fermion, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProj d) * ↑(fermionicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProj d
          simp
          use (fermionicProj y).1
          simp [hby, hfy]
        · use ↑(fermionicProj b)
          simp
      · /- fermion, boson, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProj d) * ↑(bosonicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProj d
          simp
          use (bosonicProj y).1
          simp [hby, hfy]
        · use ↑(fermionicProj b)
          simp
    · simp [hby]
      apply TwoSidedIdeal.add_mem
      · /- fermion, fermion, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProj d) * ↑(fermionicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProj d
          simp
          use (fermionicProj y).1
          simp [hby, hfy]
        · use ↑(bosonicProj b)
          simp
      · /- boson, fermion, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProj d) * ↑(fermionicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProj d
          simp
          use (fermionicProj y).1
          simp [hby, hfy]
        · use ↑(fermionicProj b)
          simp
    · simp [hfy]
      apply TwoSidedIdeal.add_mem
      · /- boson, boson, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProj d) * ↑(bosonicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProj d
          simp
          use (bosonicProj y).1
          simp [hby]
        · use ↑(bosonicProj b)
          simp
      · /- fermion, boson, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProj d) * ↑(bosonicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProj d
          simp
          use (bosonicProj y).1
          simp [hby, hfy]
        · use ↑(fermionicProj b)
          simp
    · simp [hfy, hby]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p]
    apply TwoSidedIdeal.add_mem
    exact hpx
    exact hpy
  · intro x hx
    simp [p]

lemma fermionicProj_mem_ideal (x : CrAnAlgebra 𝓕) (hx : x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) :
    x.fermionicProj.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  have hb := bosonicProj_mem_ideal x hx
  rw [← ι_eq_zero_iff_mem_ideal] at hx hb ⊢
  rw [← bosonicProj_add_fermionicProj x] at hx
  simp at hx
  simp_all

lemma ι_eq_zero_iff_ι_bosonicProj_fermonicProj_zero (x : CrAnAlgebra 𝓕) :
    ι x = 0 ↔ ι x.bosonicProj.1 = 0 ∧ ι x.fermionicProj.1 = 0 := by
  apply Iff.intro
  · intro h
    rw [@ι_eq_zero_iff_mem_ideal] at h ⊢
    rw [ι_eq_zero_iff_mem_ideal]
    apply And.intro
    · exact bosonicProj_mem_ideal x h
    · exact fermionicProj_mem_ideal x h
  · intro h
    rw [← bosonicProj_add_fermionicProj x]
    simp_all

end FieldOpAlgebra
end FieldSpecification
