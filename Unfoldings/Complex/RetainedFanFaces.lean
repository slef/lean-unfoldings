module

public import Unfoldings.Complex.Folding
public import Unfoldings.Complex.RegionalCorners
public import Unfoldings.Complex.RestoredLinkChain

/-! An actual retained cap corner fan determines its original whole-face selection. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Original faces incident to this very retained vertex copy, rather than all original copies. -/
def retainedFanFaces (retain : Set C.Seam) (w : C.Vertex retain) : Set Face :=
  {f | ∃ i, C.vertexOfCorner retain (f, i) = w}

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)
  (retain : Set C.Seam) (w : C.Vertex retain)

include F in
/-- A rigid original face cannot contain two corners of the same intrinsic vertex. -/
theorem cornerAt_face_injective (vertex : C.Vertex Set.univ) :
    Function.Injective (fun c : C.CornerAt Set.univ vertex => c.val.1) := by
  rintro ⟨⟨f, i⟩, first⟩ ⟨⟨g, j⟩, last⟩ same
  change f = g at same
  subst g
  have points := congrArg (C.vertexPoint Set.univ) (first.trans last.symm)
  have positions := (F.faceMap_isometry Set.univ f).injective points
  have corners := (C.triangle f).vertex_injective (congrArg Subtype.val positions)
  exact Subtype.ext (Prod.ext rfl corners)

include F in
/-- In the original spatial folding, one face has at most one corner at the same original vertex.
Thus the face selection retains exactly this fan's original corners. -/
theorem corner_mem_retainedFan_iff (c : C.Corner) :
    C.vertexOfCorner retain c = w ↔
      c.1 ∈ C.retainedFanFaces retain w ∧ C.vertexOfCorner Set.univ c =
        C.vertexForgetCuts (Set.subset_univ retain) w := by
  constructor
  · intro member
    exact ⟨⟨c.2, member⟩, congrArg (C.vertexForgetCuts (Set.subset_univ retain)) member⟩
  · rintro ⟨⟨i, member⟩, original⟩
    let a : C.CornerAt Set.univ (C.vertexForgetCuts (Set.subset_univ retain) w) := ⟨c, original⟩
    let b : C.CornerAt Set.univ (C.vertexForgetCuts (Set.subset_univ retain) w) :=
      ⟨(c.1, i), congrArg (C.vertexForgetCuts (Set.subset_univ retain)) member⟩
    have same : a = b := F.cornerAt_face_injective _ rfl
    have corners : c = (c.1, i) := congrArg Subtype.val same
    rw [corners]
    exact member

include F in
open Classical in
/-- Every original corner weight is preserved, including actual intrinsic or projected angles. -/
theorem regionalCornerSum_retainedFanFaces (weight : C.Corner → ℝ) :
    C.regionalCornerSum (C.retainedFanFaces retain w) weight
        (C.vertexForgetCuts (Set.subset_univ retain) w) =
      ∑ c : C.Corner, if C.vertexOfCorner retain c = w then weight c else 0 := by
  classical
  simp only [TriangleComplex.regionalCornerSum, ← F.corner_mem_retainedFan_iff]

include F in
/-- The actual intrinsic fan angle is an exact regional sum on original faces. -/
theorem totalAngle_eq_regional_retainedFanFaces :
    C.totalAngle retain w =
      C.regionalCornerSum (C.retainedFanFaces retain w)
        (fun c => (C.triangle c.1).cornerAngle c.2)
        (C.vertexForgetCuts (Set.subset_univ retain) w) :=
  (F.regionalCornerSum_retainedFanFaces retain w _).symm

end Unfoldings.SpatialFolding

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  {retain large : Set C.Seam} (inclusion : retain ⊆ large)
  (p : C.BoundaryEnd retain)
  (first : C.IsBoundaryEdge large (C.germEdge p.val))
  (last : C.IsBoundaryEdge large (C.germEdge (C.boundaryMate retain p).val))

include first last in
/-- Surviving banks preserve the complete original face selection, as well as its total angle. -/
theorem retainedFanFaces_restore :
    C.retainedFanFaces large (C.vertexForgetCuts inclusion (C.boundaryEndVertex retain p)) =
      C.retainedFanFaces retain (C.boundaryEndVertex retain p) := by
  ext f
  change (∃ i, C.vertexOfCorner large (f, i) = _) ↔
    ∃ i, C.vertexOfCorner retain (f, i) = _
  simp only [C.boundary_fan_corners_iff inclusion p first last]

end Unfoldings.TriangleComplex
