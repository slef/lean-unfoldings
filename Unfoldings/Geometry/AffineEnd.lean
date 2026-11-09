module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A finite-dimensional affine isometric self-embedding is surjective and open. -/

@[expose] public section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem affineIsometryEnd_surjective (A : E →ᵃⁱ[ℝ] E) : Function.Surjective A :=
  A.toAffineMap.linear_surjective_iff.mp
    (LinearMap.surjective_of_injective A.linearIsometry.injective)

theorem affineIsometryEnd_isOpenMap (A : E →ᵃⁱ[ℝ] E) : IsOpenMap A := by
  let e : E ≃ᵢ E := ⟨Equiv.ofBijective A ⟨A.injective, affineIsometryEnd_surjective A⟩, A.isometry⟩
  exact e.toHomeomorph.isOpenMap

end Unfoldings
