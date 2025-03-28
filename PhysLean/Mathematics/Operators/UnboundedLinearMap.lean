import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import PhysLean.Mathematics.Operators.BoundedLinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension

open InnerProductSpace LinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] -- [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] -- [CompleteSpace F]

variable (𝕜 E F)

@[ext]
structure UnboundedLinearMap extends E →ₗ[𝕜] F where
  domain : Subspace 𝕜 E
  dense : Dense (X := E) domain

notation E "→ᵘₗ[" 𝕜 "]" F => UnboundedLinearMap 𝕜 E F

namespace UnboundedLinearMap

instance instFunLike : CoeFun (E →ᵘₗ[𝕜] F) fun _ => E → F where
  coe f := f.toFun

def eq_toLinearMap (f : E →ᵘₗ[𝕜] F) (x : E) : f x = f.toLinearMap x := rfl

instance instCoe : Coe (E →ᵘₗ[𝕜] F) (E →ₗ[𝕜] F) where
  coe f := f.toLinearMap

def _root_.LinearMap.toUnbounded (f : E →ₗ[𝕜] F) : E →ᵘₗ[𝕜] F where
  toFun := f.toFun
  map_add' := f.map_add'
  map_smul' := f.map_smul'
  domain := ⊤
  dense := by
    rw [Submodule.top_coe]
    exact dense_univ

instance instZero : Zero (E →ᵘₗ[𝕜] F) where
  zero := (0 : E →ₗ[𝕜] F).toUnbounded

theorem zero_apply (x : E) : (0 : E →ᵘₗ[𝕜] F) x = 0 := rfl

/- Following Quantum Theory for Mathematicians - Hall, Chapter 9 -/

-- bounded operators are also unbounded
def _root_.BoundedLinearMap.toUnbounded (f : E →ᵇₗ[𝕜] F) : E →ᵘₗ[𝕜] F where
  toFun := f.toFun
  map_add' := f.map_add'
  map_smul' := f.map_smul'
  domain := ⊤
  dense := by
    rw [Submodule.top_coe]
    exact dense_univ

-- in finite dimensions unbounded => bounded
def toBounded_of_finiteDimensional [FiniteDimensional 𝕜 E] (f : E →ᵘₗ[𝕜] F) : E →ᵇₗ[𝕜] F :=
  BoundedLinearMap.ofContinuousLinearMap (LinearMap.continuous_of_finiteDimensional f.toLinearMap)

/- Adjoint -/

-- domain is φ such that ⟪φ, A -⟫ is bounded

-- A† φ is such that ⟪φ, A ψ⟫ = ⟪A† φ, ψ⟫ for all ψ ∈ Dom(A)


end UnboundedLinearMap
