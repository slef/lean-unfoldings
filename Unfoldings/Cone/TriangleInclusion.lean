module

public import Unfoldings.Cone.SurfaceTags

/-!
# Original triangles inside their tangent wedges

The inclusion retains the original planar coordinates. Its values agree across
every original edge incident to the chosen vertex, using scale one in the
constructed tangent seam relation.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

/-- Coordinate inclusion of an original bounded face in its supporting corner wedge. -/
def tangentInclude (c : C.CornerAt retain v) (x : C.Cell c.val.1) :
    C.TangentCell retain v c :=
  ⟨x.val, (C.triangle c.val.1).carrier_subset_cornerWedge c.val.2 x.property⟩

theorem tangentInclude_isometry (c : C.CornerAt retain v) :
    Isometry (C.tangentInclude retain v c) := fun _ _ => rfl

theorem tangentRadialPoint_one (c : C.CornerAt retain v) (x : C.Cell c.val.1) :
    C.tangentRadialPoint retain v c x 1 zero_le_one = C.tangentInclude retain v c x := by
  apply Subtype.ext
  exact AffineMap.lineMap_apply_one _ _

theorem tangentInclude_seam (s : C.TangentSeam retain v)
    (x : C.TangentDomain retain v s) :
    C.tangentFaceMap retain v (C.tangentLeft retain v s)
      (C.tangentInclude retain v (C.tangentLeft retain v s)
        ((C.triangle (C.seamSide s.val.1 s.val.2.1).face).edgeMap
          (C.seamSide s.val.1 s.val.2.1).edge x)) =
    C.tangentFaceMap retain v (C.tangentRight retain v s)
      (C.tangentInclude retain v (C.tangentRight retain v s)
        ((C.triangle (C.seamSide s.val.1 (!s.val.2.1)).face).edgeMap
          (C.seamSide s.val.1 (!s.val.2.1)).edge (C.across s.val.1 s.val.2.1 x))) := by
  apply MetricGluing.point_eq_of_glue
  refine ⟨s, x, 1, zero_le_one, ?_, ?_⟩
  · apply congrArg (Sigma.mk (C.tangentLeft retain v s))
    exact (C.tangentRadialPoint_one retain v _ _).symm
  · apply congrArg (Sigma.mk (C.tangentRight retain v s))
    exact (C.tangentRadialPoint_one retain v _ _).symm

/-- A chosen incident corner provides a tangent map on its original triangle. -/
def surfaceTangentCell (f : Face) (x : C.Cell f) : C.TangentFan retain v := by
  classical
  exact if incident : ∃ c : C.CornerAt retain v, c.val.1 = f then
    let c := incident.choose
    C.tangentFaceMap retain v c ⟨x.val,
      (C.triangle c.val.1).carrier_subset_cornerWedge c.val.2 (by
        change x.val ∈ (C.triangle incident.choose.val.1).carrier
        rw [incident.choose_spec]
        exact x.property)⟩
  else C.tangentOrigin retain v

theorem surfaceTangentCell_lipschitz (f : Face) :
    LipschitzWith 1 (C.surfaceTangentCell retain v f) := by
  classical
  by_cases incident : ∃ c : C.CornerAt retain v, c.val.1 = f
  · let c := incident.choose
    let inclusion (x : C.Cell f) : C.TangentCell retain v c :=
      ⟨x.val, (C.triangle c.val.1).carrier_subset_cornerWedge c.val.2 (by
        change x.val ∈ (C.triangle incident.choose.val.1).carrier
        rw [incident.choose_spec]
        exact x.property)⟩
    have iso : Isometry inclusion := fun _ _ => rfl
    unfold surfaceTangentCell
    simp only [dite_eq_left incident]
    change LipschitzWith 1 (C.tangentFaceMap retain v c ∘ inclusion)
    simpa only [one_mul] using
      (C.tangentFaceMap_lipschitz retain v c).comp iso.lipschitzWith
  · unfold surfaceTangentCell
    simp only [dite_eq_right incident]
    exact LipschitzWith.const' (C.tangentOrigin retain v)

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

theorem surfaceTangentCell_eq (c : C.CornerAt retain v) (x : C.Cell c.val.1) :
    C.surfaceTangentCell retain v c.val.1 x =
      C.tangentFaceMap retain v c (C.tangentInclude retain v c x) := by
  classical
  have incident : ∃ d : C.CornerAt retain v, d.val.1 = c.val.1 := ⟨c, rfl⟩
  have unchosen (d : C.CornerAt retain v) (faces : d.val.1 = c.val.1)
      (inside : x.val ∈ (C.triangle d.val.1).cornerWedge d.val.2) :
      C.tangentFaceMap retain v d ⟨x.val, inside⟩ =
        C.tangentFaceMap retain v c (C.tangentInclude retain v c x) := by
    have equal : d = c := F.cornerAt_faces_injective retain v faces
    subst d
    rfl
  simp only [TriangleComplex.surfaceTangentCell, dite_eq_left incident]
  exact unchosen incident.choose incident.choose_spec _

theorem surfaceTangentCell_apex (c : C.CornerAt retain v) :
    C.surfaceTangentCell retain v c.val.1
      ⟨(C.triangle c.val.1).vertex c.val.2, (C.triangle c.val.1).vertex_mem c.val.2⟩ =
      C.tangentOrigin retain v := by
  rw [F.surfaceTangentCell_eq retain v c]
  exact (C.tangentOrigin_eq retain v c).symm

theorem surfaceTangentCell_surfaceTag (a : C.TangentTotal retain v)
    (inside : a.2.val ∈ (C.triangle a.1.val.1).carrier) :
    C.surfaceTangentCell retain v a.1.val.1 ⟨a.2.val, inside⟩ =
      C.tangentPoint retain v a := by
  rw [F.surfaceTangentCell_eq retain v a.1]
  rfl

omit F in
theorem tangentSurfaceTag_include (c : C.CornerAt retain v) (x : C.Cell c.val.1) :
    C.tangentSurfaceTag retain v ⟨c, C.tangentInclude retain v c x⟩ =
      C.faceMap retain c.val.1 x :=
  C.tangentSurfaceTag_of_mem retain v _ x.property

end Unfoldings.SpatialFolding
