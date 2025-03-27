import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import PhysLean.Mathematics.Operators.BoundedLinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension

open InnerProductSpace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

structure UnboundedLinearMap extends E →ₗ[𝕜] F where
  domain : Subspace 𝕜 E
  dense : Dense (X := E) domain

notation E "→ᵘₗ[" 𝕜 "]" F => UnboundedLinearMap 𝕜 E F

/- Following Quantum Theory for Mathematicians - Hall, Chapter 9 -/

-- bounded operators are also unbounded

-- in finite dimensions unbounded = bounded
#check LinearMap.continuous_of_finiteDimensional

-- continuous unbounded => bounded

/- Adjoint -/

-- domain is φ such that ⟪φ, A -⟫ is bounded

-- A† φ is such that ⟪φ, A ψ⟫ = ⟪A† φ, ψ⟫ for all ψ ∈ Dom(A)
