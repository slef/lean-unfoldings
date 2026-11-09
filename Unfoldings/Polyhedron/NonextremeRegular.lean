module

public import Unfoldings.Polyhedron.IncidentCrease
public import Unfoldings.Polyhedron.PrescribedHinge
public import Unfoldings.Polyhedron.TangentHinge
public import Unfoldings.Polyhedron.LocallyPlanar
public import Unfoldings.Cone.SpatialHinge
public import Unfoldings.Geometry.StrictHingeSupport

/-!
# Every nonextreme subdivision vertex is intrinsically regular

There are at most two incident planes. Coincident planes give the constructed
planar chart. Distinct planes meet along an actual incident seam, whose outward
placement parametrizes the entire support hinge. The intrinsic tangent metric
is Euclidean by the proved piecewise rigid parametrization theorem.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

include P

theorem isRegularPoint_of_vertexHinge_seam {v : C.Vertex Set.univ}
    (s : C.TangentSeam Set.univ v) (H : F.VertexHinge v)
    (left : H.left = C.tangentLeft Set.univ v s)
    (right : H.right = C.tangentRight Set.univ v s)
    (different : LinearMap.range (F.place (C.tangentLeft Set.univ v s).val.1).linear ≠
      LinearMap.range (F.place (C.tangentRight Set.univ v s).val.1).linear) :
    C.IsRegularPoint Set.univ (C.vertexPoint Set.univ v) := by
  let l := C.seamSide s.val.1 s.val.2.1
  let r := C.seamSide s.val.1 (!s.val.2.1)
  let T := C.triangle l.face
  let U := C.triangle r.face
  let identify := C.across s.val.1 s.val.2.1
  let E : HingePlacement T U l.edge r.edge identify := hingePlacement _ _ _ _ identify
  have joined (x : T.Edge l.edge) : F.place l.face x.val = F.place r.face (identify x).val :=
    F.place_across s.val.1 s.val.2.1 x
  have inverse_joined (x : U.Edge r.edge) :
      F.place r.face x.val = F.place l.face (identify.symm x).val := by
    have equal := joined (identify.symm x)
    rw [identify.apply_symm_apply] at equal
    exact equal.symm
  have left_level (p : Plane) : H.leftFunctional (F.place l.face p) = H.leftLevel := by
    have equal := H.left_plane p
    rwa [left] at equal
  have right_level (p : Plane) : H.rightFunctional (F.place r.face p) = H.rightLevel := by
    have equal := H.right_plane p
    rwa [right] at equal
  have planes_ne : LinearMap.range (F.place l.face).linear ≠
      LinearMap.range (F.place r.face).linear := different
  have left_cross : H.rightFunctional (F.place l.face (T.opposite l.edge)) < H.rightLevel := by
    apply strict_opposite_of_distinct_support_planes T l.edge (F.place l.face)
      (F.place r.face) H.rightFunctional H.rightLevel H.right_nonzero right_level
      (fun x => by rw [joined, right_level]) _ planes_ne
    exact H.right_supported _ (F.faceImage_subset_vertexHull l.face
      ⟨_, T.vertex_mem _, rfl⟩)
  have right_cross : H.leftFunctional (F.place r.face (U.opposite r.edge)) < H.leftLevel := by
    apply strict_opposite_of_distinct_support_planes U r.edge (F.place r.face)
      (F.place l.face) H.leftFunctional H.leftLevel H.left_nonzero left_level
      (fun x => by rw [inverse_joined, left_level]) _ planes_ne.symm
    exact H.left_supported _ (F.faceImage_subset_vertexHull r.face
      ⟨_, U.vertex_mem _, rfl⟩)
  let S : SpatialHinge E :=
    { left := F.place l.face
      right := F.place r.face
      joined := joined
      leftFunctional := H.leftFunctional
      rightFunctional := H.rightFunctional
      leftLevel := H.leftLevel
      rightLevel := H.rightLevel
      left_range := by
        have range := H.left_range
        rw [left] at range
        exact range
      right_range := by
        have range := H.right_range
        rw [right] at range
        exact range
      left_cross := left_cross
      right_cross := right_cross }
  exact isRegularPoint_of_spatial_hinge P.embedded S (P.tangent_range_eq_vertexHinge H)

theorem isRegularPoint_nonextreme_vertex (v : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ v) ∉ F.vertexHull.extremePoints ℝ) :
    C.IsRegularPoint Set.univ (C.vertexPoint Set.univ v) := by
  classical
  obtain ⟨a, b, cover⟩ := P.exists_two_incident_planes v not_extreme
  by_cases equal : LinearMap.range (F.place a.val.1).linear =
      LinearMap.range (F.place b.val.1).linear
  · apply P.isRegularPoint_of_incident_planes_eq v a
    intro c
    rcases cover c with first | second
    · exact first
    · exact second.trans equal.symm
  · obtain ⟨s, different⟩ := P.exists_incident_crease a b equal
    have seam_cover (c : C.CornerAt Set.univ v) :
        LinearMap.range (F.place c.val.1).linear =
          LinearMap.range (F.place (C.tangentLeft Set.univ v s).val.1).linear ∨
        LinearMap.range (F.place c.val.1).linear =
          LinearMap.range (F.place (C.tangentRight Set.univ v s).val.1).linear := by
      rcases cover (C.tangentLeft Set.univ v s) with left_a | left_b <;>
        rcases cover (C.tangentRight Set.univ v s) with right_a | right_b
      · exact (different (left_a.trans right_a.symm)).elim
      · rw [left_a, right_b]
        exact cover c
      · rw [left_b, right_a]
        exact (cover c).symm
      · exact (different (left_b.trans right_b.symm)).elim
    obtain ⟨H, left, right⟩ := P.exists_vertexHinge_of_incident_planes
      (C.tangentLeft Set.univ v s) (C.tangentRight Set.univ v s) seam_cover
    exact P.isRegularPoint_of_vertexHinge_seam s H left right different

end Unfoldings.SpatialFolding.ConvexBoundary
