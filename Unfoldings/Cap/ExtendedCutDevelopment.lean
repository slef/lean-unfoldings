module

public import Unfoldings.Cap.ExtendedCutForest
public import Unfoldings.Cap.RadialForestDevelopment

/-! The constructed extended roof cuts give an actual cut disk and a local isometric development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ}

/-- No cut-disk or safe-cut hypothesis is needed: the outward forest and its disk are constructed
from the supplied original forest and the actual meshed supporting-plane roof. -/
theorem cornerExtended_exists_development (positive : 0 < t) (small : t < 1)
    (T : K.ClipSpatialTriangles Z) (internal : ¬ C.IsBoundaryVertex Set.univ origin)
    (source_height : 0 < K.roofHeight (K.projectedVertex origin)) (lower : Z < 0)
    (conforming : TriangleFamily.Conforming T.projectedTriangle)
    (height : ∀ f, (3 : ℝ) / 4 ≤ K.normal f 2) :
    let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
    let F := T.cornerTails inside source_height lower
    let L := F.mesh T lower
    letI := @Fintype.ofFinite _ L.partition.finite
    let R := M.cornerExtendedForest positive small T internal source_height lower
    ∃ E : FacewiseDevelopment L.partition.pairedComplex R.retain,
      ∀ x, ‖(R.cutDisk x).val‖ < 1 → ∃ r > 0,
        Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) := by
  let inside := (K.projectedVertex_mem_interior_iff origin).mpr internal
  let F := T.cornerTails inside source_height lower
  let L := F.mesh T lower
  let := @Fintype.ofFinite _ L.partition.finite
  let R := M.cornerExtendedForest positive small T internal source_height lower
  exact R.exists_development
    (M.extended_cut_curvature_covered T internal source_height lower conforming height)

end Unfoldings.ConvexCap.SectorForest
