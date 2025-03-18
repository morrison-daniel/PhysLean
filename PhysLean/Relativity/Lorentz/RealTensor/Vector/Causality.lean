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

lemma self_mem_lightConeBoundary {d : ℕ} (p : Vector d) : p ∈ lightConeBoundary p := by
  simp [lightConeBoundary, causalCharacter]

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

end Vector

end Lorentz
