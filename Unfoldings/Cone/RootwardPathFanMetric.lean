module

public import Unfoldings.Complex.RootwardPathFans
public import Unfoldings.Cone.BoundaryFanRestoration

/-! Original rootward reference fans preserve the actual tangent-cell metric point for point. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  {P : AscendingParents (C.Vertex Set.univ)} (S : P.EdgeSelection C.seamGraph)
  (roots : P.roots = C.relativeCutRoots Set.univ)
  (Q : C.BoundaryContour (C.selectedRetain S))
  (starts : C.contourOriginalVertex S Q 0 ∈ P.roots)
  (i : Fin (Q.length + 1))
  (fresh : C.contourOriginalVertex S Q i ∉ (C.contourFrontier S Q i).processed)
  (single : (C.contourFrontier S Q i).contactTime (C.contourOriginalVertex S Q i) = 1)

include F roots starts fresh single in
/-- Construct the actual intrinsic tangent-fan isometry to the original path-cut fan.
Every original supporting-wedge point is fixed, including reentrant fans. -/
theorem exists_rootward_path_fan_isometry (j k : C.RootwardBank S Q i)
    (parent : P.parent (C.contourOriginalVertex S Q j.val) =
      C.contourOriginalVertex S Q k.val) :
    let current := C.processedParentRetain S (C.contourFrontier S Q i)
    let reference := C.ancestorPathRetain S (P.parent (C.contourOriginalVertex S Q i))
    let p := C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1
    let vertex := C.boundaryEndVertex current p
    ∃ E : C.TangentFan current vertex ≃ᵢ
      C.TangentFan reference (C.vertexForgetCuts (C.rootwardPathInclusion S Q i single) vertex),
      ∀ (q : C.CornerAt current vertex) (x : C.TangentCell current vertex q),
        E (C.tangentFaceMap current vertex q x) =
          C.tangentFaceMap reference
            (C.vertexForgetCuts (C.rootwardPathInclusion S Q i single) vertex)
            (C.restoreCorner (C.rootwardPathInclusion S Q i single) q) x := by
  obtain ⟨first, last⟩ := F.rootward_path_fan_terminal_banks S roots Q starts i fresh j k parent
  exact C.exists_boundaryFanRestorationIsometry (C.rootwardPathInclusion S Q i single)
    (C.survivingBoundaryEnd (Q.cycle.point k.val) k.property.2.1) first last

end Unfoldings.SpatialFolding
