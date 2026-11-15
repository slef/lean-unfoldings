module

public import Unfoldings.Roof.RestrictedEmbedding
public import Unfoldings.Topology.ConvexJordanBoundary

/-! Convex whole-face roof patches retain every actual intrinsic point under projection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- Convexity of the actual face union rules out vertex pinches in its intrinsic restriction. -/
theorem restrictProjection_injective_of_convex (U : Set Face) (nonempty : U.Nonempty)
    (convex : Convex ℝ (K.restrictedCarrier U)) : Function.Injective (K.restrictProjection U) := by
  obtain ⟨f, selected⟩ := nonempty
  have inside : (interior (K.restrictedCarrier U)).Nonempty :=
    (K.projectedTriangle f).interior_nonempty.mono
      (interior_mono (Set.subset_iUnion (fun g : {g : Face // g ∈ U} =>
        (K.projectedTriangle g.val).carrier) ⟨f, selected⟩))
  exact K.restrictProjection_injective_of_Jordan U ⟨f, selected⟩
    (PlanarTopology.isJordanCurve_frontier_of_convex convex inside
      (K.compact_restrictedCarrier U).isBounded)

end Unfoldings.ConvexRoof
