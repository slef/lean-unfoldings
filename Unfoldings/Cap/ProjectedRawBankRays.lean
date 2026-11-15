module

public import Unfoldings.Cap.ProjectedBankRays
public import Unfoldings.Roof.FaceRestriction
public import Unfoldings.Polyhedron.BoundaryDirections
public import Unfoldings.Complex.FaceRestrictionLinks

/-! Compare physical directions of raw original banks across independent face restrictions. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- A physical outgoing ray and its positive occupied side recover the raw original bank
without supplying a vertex-copy, edge-length or face identification. -/
theorem projected_positive_raw_germ_unique_of_positive_scale (p q : C.Germ)
    (apex : (K.projectedTriangle p.1.1).vertex p.1.2 =
      (K.projectedTriangle q.1.1).vertex q.1.2)
    (positive_p : 0 < K.projectedGermOrientation p)
    (positive_q : 0 < K.projectedGermOrientation q) {r : ℝ} (positive : 0 < r)
    (direction : Cap.horizontal (K.folding.germDirection p) =
      r • Cap.horizontal (K.folding.germDirection q)) : p = q := by
  let w := C.vertexOfCorner Set.univ p.1
  let left : C.LinkGerm Set.univ w := ⟨p, rfl⟩
  have at_right : C.vertexOfCorner Set.univ q.1 = w :=
    K.projectedVertex_injective apex.symm
  let right : C.LinkGerm Set.univ w := ⟨q, at_right⟩
  have ray : K.projectedGermRay left = r • K.projectedGermRay right := by
    rw [← K.horizontal_germDirection left, ← K.horizontal_germDirection right]
    exact direction
  exact congrArg (fun s : C.LinkGerm Set.univ w => s.val)
    (K.projected_positive_germ_unique_of_positive_scale left right
      positive_p positive_q positive ray)

open Classical in
/-- Equal included original raw banks have exactly equal physical projected base points. -/
theorem restricted_boundaryPosition_eq_of_raw (U V : Set Face)
    {leftRetain : Set (C.restrictFaces U).Seam}
    {rightRetain : Set (C.restrictFaces V).Seam}
    (p : (C.restrictFaces U).BoundaryEnd leftRetain)
    (q : (C.restrictFaces V).BoundaryEnd rightRetain)
    (same : C.includeRestrictedGerm U p.val = C.includeRestrictedGerm V q.val) :
    Cap.horizontal ((K.folding.restrictFaces U).boundaryPosition p) =
      Cap.horizontal ((K.folding.restrictFaces V).boundaryPosition q) := by
  simpa only [SpatialFolding.boundaryPosition_raw] using! congrArg
    (fun r : C.Germ => Cap.horizontal (K.folding.place r.1.1
      ((C.triangle r.1.1).vertex r.1.2))) same

open Classical in
/-- Equal included raw germs keep the complete physical directed bank vector. -/
theorem restricted_germDirection_eq_of_raw (U V : Set Face)
    (p : (C.restrictFaces U).Germ) (q : (C.restrictFaces V).Germ)
    (same : C.includeRestrictedGerm U p = C.includeRestrictedGerm V q) :
    Cap.horizontal ((K.folding.restrictFaces U).germDirection p) =
      Cap.horizontal ((K.folding.restrictFaces V).germDirection q) := by
  simpa only using! congrArg (fun r : C.Germ =>
    Cap.horizontal (K.folding.germDirection r)) same

end Unfoldings.ConvexCap
