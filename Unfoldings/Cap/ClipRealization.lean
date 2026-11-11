module

public import Unfoldings.Cap.ClipEmbedding
public import Unfoldings.Cap.ClipDisk

/-! The assembled physical roof triangles realize the actual compact roof disk. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- Intrinsic gluing and actual spatial topology agree on a conforming physical roof clip. -/
def pairedRoofHomeomorph (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    T.pairedComplex.Realization Set.univ ≃ₜ K.clippedRoof Z :=
  (T.pairedFolding.surfaceHomeomorph (T.pairedFolding_embedded conforming)).trans
    (Homeomorph.setCongr T.pairedFolding_surface)

/-- Projection of the intrinsic physical clip onto its actual convex footprint. -/
def pairedFootprintHomeomorph (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    T.pairedComplex.Realization Set.univ ≃ₜ K.clipFootprint Z :=
  (T.pairedRoofHomeomorph conforming).trans (K.clipProjectionHomeomorph Z).symm

theorem pairedFootprintHomeomorph_apply
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (x : T.pairedComplex.Realization Set.univ) :
    (T.pairedFootprintHomeomorph conforming x).val =
      Cap.horizontal (T.pairedFolding.toSpace Set.univ x) := rfl

theorem pairedFootprintHomeomorph_pointCopy
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (i : T.Index) (p : Plane)
    (member : p ∈ (T.projectedTriangle i).carrier) :
    (T.pairedFootprintHomeomorph conforming (T.pointCopy i p member)).val = p := by
  rw [T.pairedFootprintHomeomorph_apply, T.pointCopy_toSpace, K.horizontal_roofPoint]

/-- Preconnectedness is inherited from the actual convex footprint, including empty clips. -/
theorem paired_preconnectedSpace (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    PreconnectedSpace (T.pairedComplex.Realization Set.univ) := by
  let := Subtype.preconnectedSpace (K.convex_clipFootprint Z).isPreconnected
  exact (T.pairedFootprintHomeomorph conforming).symm.surjective.denseRange.preconnectedSpace
    (T.pairedFootprintHomeomorph conforming).symm.continuous

theorem pairedRoofHomeomorph_apply (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (x : T.pairedComplex.Realization Set.univ) :
    (T.pairedRoofHomeomorph conforming x).val = T.pairedFolding.toSpace Set.univ x := rfl

/-- A genuine disk realization of the physical whole-edge complex, not just of its point set. -/
def pairedDisk (conforming : TriangleFamily.Conforming T.projectedTriangle)
    {q : Plane} (member : q ∈ K.footprint) (positive : 0 < K.roofHeight q) (lower : Z < 0) :
    T.pairedComplex.Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  (T.pairedRoofHomeomorph conforming).trans (K.clippedRoofDisk member positive lower)

/-- Every constructed common refinement has the actual roof as its metric realization. -/
def refinedRoofHomeomorph : T.refined.pairedComplex.Realization Set.univ ≃ₜ K.clippedRoof Z :=
  T.refined.pairedRoofHomeomorph T.refined_conforming

/-- No conformity certificate is required for the constructed refined disk. -/
def refinedDisk {q : Plane} (member : q ∈ K.footprint) (positive : 0 < K.roofHeight q)
    (lower : Z < 0) :
    T.refined.pairedComplex.Realization Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  T.refined.pairedDisk T.refined_conforming member positive lower

end Unfoldings.ConvexCap.ClipSpatialTriangles
