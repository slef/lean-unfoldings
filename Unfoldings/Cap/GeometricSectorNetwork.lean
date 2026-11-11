module

public import Unfoldings.Cap.GeometricHeightNetwork
public import Unfoldings.Geometry.AffineHeightNetwork

/-! One sector network includes every geometric tree whose edge directions lie in that sector. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

abbrev GeometricSectorEdge (i : FiveSector) := {w : F.GeometricVertex //
  w ∉ (M.geometricParents F covered positive small lower).roots ∧
    F.geometricPosition (M.geometricParent F covered w) - F.geometricPosition w ∈
      closedFiveSector t i}

/-- A common sector compares different components as well as different branches of one tree.
Forward uniqueness is inherited from the complete actual geometric forest. -/
def sectorHeightNetwork (i : FiveSector) :
    HeightSegmentNetwork (M.GeometricSectorEdge F covered positive small lower i) :=
  HeightSegmentNetwork.ofAffineSegments
    (centeredPlaneFrame (K.projectedVertex origin) (fiveSectorFrame t positive small i).place)
    (fun e => F.geometricPosition e.val)
    (fun e => F.geometricPosition (M.geometricParent F covered e.val))
    (fun e => by
      have bound := M.geometricSweepHeight_parent_lt F covered positive small lower i e.val
        e.property.1 e.property.2
      change (centeredPlaneFrame _ _ _).re + (centeredPlaneFrame _ _ _).im <
        (centeredPlaneFrame _ _ _).re + (centeredPlaneFrame _ _ _).im
      simpa only [centeredPlaneFrame_apply, geometricSweepHeight] using bound)
    (fun a b x first first_not_end last last_not_end => by
      let ae : {w : F.GeometricVertex //
          w ∉ (M.geometricParents F covered positive small lower).roots} := ⟨a.val, a.property.1⟩
      let be : {w : F.GeometricVertex //
          w ∉ (M.geometricParents F covered positive small lower).roots} := ⟨b.val, b.property.1⟩
      have equal := M.geometric_halfOpen_parent_unique F covered positive small lower ae be
        first first_not_end last last_not_end
      have vertices : a.val = b.val :=
        congrArg (fun e : {w : F.GeometricVertex //
          w ∉ (M.geometricParents F covered positive small lower).roots} => e.val) equal
      exact Subtype.ext vertices)

end Unfoldings.ConvexCap.SectorForest
