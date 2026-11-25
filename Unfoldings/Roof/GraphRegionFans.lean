module

public import Unfoldings.Roof.GraphRegionFaces
public import Unfoldings.Roof.ProjectedSeamCompletion
public import Unfoldings.Roof.ProjectedConformity
public import Unfoldings.Roof.SharpRestrictedSection
public import Unfoldings.Topology.EpigraphNeighborhood
public import Unfoldings.Geometry.ConformingLocalStar
public import Unfoldings.Complex.ProjectedEmbedding
public import Unfoldings.Complex.FaceRestrictionWeights
public import Unfoldings.Complex.FaceRestrictionPairings
public import Unfoldings.Polyhedron.BoundaryDirections

/-! Local epigraphs identify the actual restricted roof fans and their angle excess. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open PlanarTopology Filter Topology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

set_option maxHeartbeats 1000000 in
open Classical in
/-- At a point whose restricted geometric star is locally connected after puncturing,
all incident restricted corner copies represent one actual vertex. -/
theorem restricted_vertex_eq_of_punctured_neighborhood (U : Set Face) {p : Plane}
    (neighborhood : ∀ r > 0, ∃ N : Set Plane, IsOpen N ∧ p ∈ N ∧ N ⊆ Metric.ball p r ∧
      IsPreconnected ((K.restrictedCarrier U ∩ N) \ {p}))
    (x y : (C.restrictFaces U).Vertex Set.univ)
    (at_x : K.projectedVertex (C.includeRestrictedVertexUniv U x) = p)
    (at_y : K.projectedVertex (C.includeRestrictedVertexUniv U y) = p) : x = y := by
  let R := C.restrictFaces U
  let A (f : {f : Face // f ∈ U}) := K.projectFaceEquiv f.val
  let T := R.affineProjectedTriangle A
  have joined : ∀ s z, A (R.left s).face z.val =
      A (R.right s).face (R.identify s z).val :=
    fun s z => K.projectedTriangle_joined s.val z
  let value (i : {i // p ∈ (T i).carrier}) :=
    R.projectedPointCopy A i.val p i.property
  have across (i j : {i // p ∈ (T i).carrier}) (t : R.Seam)
      (left : (R.left t).face = i.val) (right : (R.right t).face = j.val)
      (on_left : p ∈ (T (R.left t).face).edge (R.left t).edge) : value i = value j := by
    let a : {i // p ∈ (T i).carrier} := ⟨(R.left t).face, left.symm ▸ i.property⟩
    let b : {i // p ∈ (T i).carrier} := ⟨(R.right t).face, right.symm ▸ j.property⟩
    have shared : value a = value b :=
      R.projectedPointCopy_across_seam A joined t on_left
    exact (congrArg value (Subtype.ext left : a = i)).symm.trans
      (shared.trans (congrArg value (Subtype.ext right : b = j)))
  have agree (i j : {i // p ∈ (T i).carrier}) (e d : Fin 3)
      (same : (T i.val).edge e = (T j.val).edge d) (member : p ∈ (T i.val).edge e) :
      value i = value j := by
    by_cases ij : i.val = j.val
    · exact congrArg value (Subtype.ext ij)
    obtain ⟨s, ⟨left, right⟩ | ⟨right, left⟩⟩ :=
      K.exists_seam_of_projected_shared_edge
        (a := ⟨i.val.val, e⟩) (b := ⟨j.val.val, d⟩)
        (fun same => ij (Subtype.ext same)) same
    · obtain ⟨t, first, last⟩ :=
        C.exists_restricted_seam_of_names U i.val j.val e d s left right
      exact across i j t (congrArg EdgeRef.face first) (congrArg EdgeRef.face last)
        (by rw [first]; exact member)
    · obtain ⟨t, first, last⟩ :=
        C.exists_restricted_seam_of_names U j.val i.val d e s right left
      exact (across j i t (congrArg EdgeRef.face first) (congrArg EdgeRef.face last)
        (by rw [first, ← same]; exact member)).symm
  have copies (i j : {i // p ∈ (T i).carrier}) : value i = value j :=
    TriangleFamily.incident_values_eq_of_punctured_neighborhood T rfl
      (fun f g different z member => K.projectedTriangles_conforming f.val g.val
        (fun same => different (Subtype.ext same)) z member)
      (fun _ _ different => K.projectedTriangles_nonoverlapping (fun same => different (Subtype.ext same)))
      p neighborhood value agree i j
  have name (z : R.Vertex Set.univ) (position : K.projectedVertex (C.includeRestrictedVertexUniv U z) = p) :
      ∃ i, value i = R.vertexPoint Set.univ z := by
    obtain ⟨corner, rfl⟩ := R.vertexOfCorner_surjective Set.univ z
    have pos : (T corner.1).vertex corner.2 = p := by
      change K.projectedVertex (C.vertexOfCorner Set.univ (corner.1.val, corner.2)) = p at position
      rwa [K.projectedVertex_ofCorner] at position
    have here : p ∈ (T corner.1).carrier :=
      pos ▸ (T corner.1).vertex_mem corner.2
    refine ⟨⟨corner.1, here⟩, ?_⟩
    change R.faceMap Set.univ corner.1 ⟨(A corner.1).symm p, _⟩ =
      R.faceMap Set.univ corner.1 ⟨(R.triangle corner.1).vertex corner.2, _⟩
    apply congrArg (R.faceMap Set.univ corner.1)
    apply Subtype.ext
    change (A corner.1).symm p = (R.triangle corner.1).vertex corner.2
    exact (congrArg (A corner.1).symm pos.symm).trans ((A corner.1).symm_apply_apply _)
  obtain ⟨i, xi⟩ := name x at_x
  obtain ⟨j, yj⟩ := name y at_y
  exact R.vertexPoint_injective Set.univ (xi.symm.trans ((copies i j).trans yj))

set_option maxHeartbeats 800000 in
open Classical in
/-- At an original vertex with a unique selected copy, its actual turn error
is exactly the negative regional angle excess at that vertex. -/
theorem restrictedBoundaryTurnError_eq_neg_regional_of_unique (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    (unique : ∀ z : (C.restrictFaces U).Vertex Set.univ,
      C.includeRestrictedVertexUniv U z =
        C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) →
      z = (C.restrictFaces U).boundaryEndVertex Set.univ p) :
    K.restrictedBoundaryTurnError U p = -K.regionalAngleExcess U
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)) := by
  let R := C.restrictFaces U
  let z := R.boundaryEndVertex Set.univ p
  let w := C.includeRestrictedVertexUniv U z
  have eq_iff (y : R.Vertex Set.univ) : C.includeRestrictedVertexUniv U y = w ↔ y = z :=
    ⟨unique y, congrArg (C.includeRestrictedVertexUniv U)⟩
  have total := C.totalAngle_restricted_vertex_fiber U w
  simp only [eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at total
  have projected := C.regionalCornerSum_restricted_vertex_fiber U
    (fun c => (K.projectedTriangle c.1).cornerAngle c.2) w
  simp only [eq_iff, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at projected
  change (Real.pi - R.totalAngle Set.univ z) -
      (Real.pi - R.regionalCornerSum Set.univ
        (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) z) =
    -K.regionalAngleExcess U w
  rw [total, projected]
  have excess : K.regionalAngleExcess U w =
      C.regionalCornerSum U (fun c => (C.triangle c.1).cornerAngle c.2) w -
      C.regionalCornerSum U (fun c => (K.projectedTriangle c.1).cornerAngle c.2) w := by
    simp only [regionalAngleExcess, TriangleComplex.regionalCornerSum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp
  rw [excess]
  ring

end Unfoldings.ConvexRoof
