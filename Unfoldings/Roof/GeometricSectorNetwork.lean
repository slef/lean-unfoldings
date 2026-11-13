module

public import Unfoldings.Roof.GeometricHeightNetwork
public import Unfoldings.Geometry.AffineHeightNetwork

/-! One sector network includes every geometric tree whose edge directions lie in that sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {t : ℝ} {origin : Plane} (M : K.SectorForest t origin)
  {outer : Set Plane} (F : K.SkirtTailFamily outer (origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1)

abbrev GeometricSectorEdge (i : FiveSector) := {w : F.GeometricVertex //
  w ∉ (M.geometricParents F covered positive small).roots ∧
    F.geometricPosition (M.geometricParent F covered w) - F.geometricPosition w ∈
      closedFiveSector t i}

/-- A common sector compares different components as well as different branches of one tree.
Forward uniqueness is inherited from the complete actual geometric forest. -/
def sectorHeightNetwork (i : FiveSector) :
    HeightSegmentNetwork (M.GeometricSectorEdge F covered positive small i) :=
  HeightSegmentNetwork.ofAffineSegments
    (centeredPlaneFrame (origin) (fiveSectorFrame t positive small i).place)
    (fun e => F.geometricPosition e.val)
    (fun e => F.geometricPosition (M.geometricParent F covered e.val))
    (fun e => by
      have bound := M.geometricSweepHeight_parent_lt F covered positive small i e.val
        e.property.1 e.property.2
      change (centeredPlaneFrame _ _ _).re + (centeredPlaneFrame _ _ _).im <
        (centeredPlaneFrame _ _ _).re + (centeredPlaneFrame _ _ _).im
      simpa only [centeredPlaneFrame_apply, geometricSweepHeight] using bound)
    (fun a b x first first_not_end last last_not_end => by
      let ae : {w : F.GeometricVertex //
          w ∉ (M.geometricParents F covered positive small).roots} := ⟨a.val, a.property.1⟩
      let be : {w : F.GeometricVertex //
          w ∉ (M.geometricParents F covered positive small).roots} := ⟨b.val, b.property.1⟩
      have equal := M.geometric_halfOpen_parent_unique F covered positive small ae be
        first first_not_end last last_not_end
      have vertices : a.val = b.val :=
        congrArg (fun e : {w : F.GeometricVertex //
          w ∉ (M.geometricParents F covered positive small).roots} => e.val) equal
      exact Subtype.ext vertices)

end Unfoldings.ConvexRoof.SectorForest
