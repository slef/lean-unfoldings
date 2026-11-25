module

public import Unfoldings.Convex.AffineFloorMesh
public import Unfoldings.Complex.GeometricPairings
public import Unfoldings.Complex.ProjectedEmbedding
public import Unfoldings.Roof.ProjectedFaces

/-! Match the actual physical seams of a conforming mesh cut by an affine floor. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {floor : Plane →ᵃ[ℝ] ℝ} {extra : J → Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  (T : FloorMesh family floor extra Z)

local instance floorRoofIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

theorem triangle_edge (i : T.Index) (e : Fin 3) : (T.triangle i).edge e =
    ((family (T.support i)).project).symm '' (T.projectedTriangle i).edge e :=
  (T.projectedTriangle i).affineImage_edge
    ((family (T.support i)).project).symm.toAffineMap
    ((family (T.support i)).project).symm.injective e

/-- Projection is an equivalence on the whole edge, without asserting a projected metric. -/
def edgeProjection (i : T.Index) (e : Fin 3) :
    (T.triangle i).Edge e ≃ (T.projectedTriangle i).Edge e where
  toFun x := ⟨(family (T.support i)).project x.val, by
    have member := (T.triangle_edge i e).subset x.property
    obtain ⟨p, member, equal⟩ := member
    rw [← equal]
    change ((family (T.support i)).project) (((family (T.support i)).project).symm p) ∈ _
    rw [((family (T.support i)).project).apply_symm_apply]
    exact member⟩
  invFun y := ⟨((family (T.support i)).project).symm y.val, by
    rw [T.triangle_edge]
    exact ⟨y.val, y.property, rfl⟩⟩
  left_inv x := Subtype.ext (((family (T.support i)).project).symm_apply_apply x.val)
  right_inv y := Subtype.ext (((family (T.support i)).project).apply_symm_apply y.val)

/-- The physical transition associated to two equal projected whole edges. -/
def edgeTransition {a b : EdgeRef T.Index}
    (same : TriangleFamily.edgeCarrier T.projectedTriangle a =
      TriangleFamily.edgeCarrier T.projectedTriangle b) :
    (T.triangle a.face).Edge a.edge ≃ (T.triangle b.face).Edge b.edge :=
  (T.edgeProjection a.face a.edge).trans
    (((T.projectedTriangle a.face).sharedEdgeIdentification (T.projectedTriangle b.face)
      a.edge b.edge same).toEquiv.trans (T.edgeProjection b.face b.edge).symm)

theorem edgeTransition_projection {a b : EdgeRef T.Index}
    (same : TriangleFamily.edgeCarrier T.projectedTriangle a =
      TriangleFamily.edgeCarrier T.projectedTriangle b)
    (x : (T.triangle a.face).Edge a.edge) :
    (family (T.support b.face)).project (T.edgeTransition same x).val =
      (family (T.support a.face)).project x.val := by
  dsimp only [edgeTransition, Equiv.trans_apply, Equiv.symm_apply_apply,
    Triangle.sharedEdgeIdentification, edgeProjection]
  change ((family (T.support b.face)).project)
    (((family (T.support b.face)).project).symm ((family (T.support a.face)).project x.val)) = _
  exact ((family (T.support b.face)).project).apply_symm_apply _

/-- Both physical banks represent exactly the same spatial roof point. -/
theorem edgeTransition_joined {a b : EdgeRef T.Index}
    (same : TriangleFamily.edgeCarrier T.projectedTriangle a =
      TriangleFamily.edgeCarrier T.projectedTriangle b)
    (x : (T.triangle a.face).Edge a.edge) :
    T.placement a.face x.val = T.placement b.face (T.edgeTransition same x).val := by
  rw [T.placement_eq_point a.face ((T.triangle a.face).edge_subset a.edge x.property),
    T.placement_eq_point b.face ((T.triangle b.face).edge_subset b.edge
      (T.edgeTransition same x).property), T.edgeTransition_projection]

/-- The transition preserves physical lengths even when projection changes those lengths. -/
def edgeIdentification {a b : EdgeRef T.Index}
    (same : TriangleFamily.edgeCarrier T.projectedTriangle a =
      TriangleFamily.edgeCarrier T.projectedTriangle b) :
    (T.triangle a.face).Edge a.edge ≃ᵢ (T.triangle b.face).Edge b.edge where
  toEquiv := T.edgeTransition same
  isometry_toFun x y := by
    change edist (T.edgeTransition same x).val (T.edgeTransition same y).val = edist x.val y.val
    rw [← (T.placement b.face).isometry.edist_eq,
      ← T.edgeTransition_joined same x, ← T.edgeTransition_joined same y]
    exact (T.placement a.face).isometry.edist_eq x.val y.val

/-- Pair every matching projected whole edge using its actual spatial isometry. -/
def pairedComplex : TriangleComplex T.Index where
  triangle := T.triangle
  Seam := TriangleFamily.GeometricSeam T.projectedTriangle
  finiteSeam := Fintype.ofFinite _
  left s := (TriangleFamily.seamPair T.projectedTriangle s).first
  right s := (TriangleFamily.seamPair T.projectedTriangle s).last
  distinct s := fun equal =>
    (TriangleFamily.seamPair T.projectedTriangle s).different_faces (congrArg EdgeRef.face equal)
  identify s := T.edgeIdentification (TriangleFamily.seamPair T.projectedTriangle s).carrier_eq
  unique s t shared := by
    apply Subtype.ext
    rw [TriangleFamily.seamPair_labels, TriangleFamily.seamPair_labels]
    exact TriangleFamily.sharedPair_eq_of_shared_edge T.projectedTriangle T.separated _ _ shared

/-- The resulting physical triangle complex folds onto the actual clipped roof. -/
def pairedFolding : SpatialFolding T.pairedComplex where
  place := T.placement
  joined s := T.edgeTransition_joined (TriangleFamily.seamPair T.projectedTriangle s).carrier_eq

/-- Keep an actual physical seam unless its whole projection lies in the cuts. -/
def retainOutside (cuts : Set Plane) : Set T.pairedComplex.Seam :=
  {s | ¬ (T.projectedTriangle (T.pairedComplex.left s).face).edge
    (T.pairedComplex.left s).edge ⊆ cuts}

theorem paired_seam_projected_edge (s : T.pairedComplex.Seam) :
    (T.projectedTriangle (T.pairedComplex.left s).face).edge (T.pairedComplex.left s).edge =
      (T.projectedTriangle (T.pairedComplex.right s).face).edge (T.pairedComplex.right s).edge :=
  (TriangleFamily.seamPair T.projectedTriangle s).carrier_eq

theorem paired_seam_projection (s : T.pairedComplex.Seam)
    (x : (T.triangle (T.pairedComplex.left s).face).Edge (T.pairedComplex.left s).edge) :
    (family (T.support (T.pairedComplex.right s).face)).project (T.pairedComplex.identify s x).val =
      (family (T.support (T.pairedComplex.left s).face)).project x.val :=
  T.edgeTransition_projection (TriangleFamily.seamPair T.projectedTriangle s).carrier_eq x

/-- The inherited whole-face projection is the actual prescribed projected triangle. -/
theorem affineProjectedTriangle_eq (i : T.Index) :
    T.pairedComplex.affineProjectedTriangle
      (fun i => (family (T.support i)).project) i = T.projectedTriangle i := by
  apply Triangle.eq_of_vertex_eq
  intro j
  change (family (T.support i)).project
    ((family (T.support i)).project.symm ((T.projectedTriangle i).vertex j)) = _
  exact (family (T.support i)).project.apply_symm_apply _

/-- Complete geometric pairing identifies exactly the same physical projected points. -/
theorem pairedProjection_injective :
    Function.Injective (fun x : T.pairedComplex.Realization Set.univ =>
      Cap.horizontal (T.pairedFolding.toSpace Set.univ x)) := by
  let C := T.pairedComplex
  let A := fun i => (family (T.support i)).project
  have triangles : C.affineProjectedTriangle A = T.projectedTriangle :=
    funext (T.affineProjectedTriangle_eq)
  have joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val :=
    fun s x => (T.paired_seam_projection s x).symm
  have convex : Convex ℝ (⋃ i, (C.affineProjectedTriangle A i).carrier) := by
    rw [triangles, ← T.cover]
    exact convex_clipAbove family floor Z
  have conforming' : TriangleFamily.Conforming (C.affineProjectedTriangle A) :=
    triangles.symm ▸ T.conforming
  have separated : Pairwise (fun i j =>
      Disjoint (interior (C.affineProjectedTriangle A i).carrier)
        (interior (C.affineProjectedTriangle A j).carrier)) := triangles.symm ▸ T.separated
  have complete : ∀ f g : T.Index, f ≠ g → ∀ e d : Fin 3,
      (C.affineProjectedTriangle A f).edge e = (C.affineProjectedTriangle A g).edge d →
      ∃ s, (C.left s = ⟨f, e⟩ ∧ C.right s = ⟨g, d⟩) ∨
        (C.left s = ⟨g, d⟩ ∧ C.right s = ⟨f, e⟩) := by
    intro f g different e d same
    rw [triangles] at same
    exact TriangleFamily.pairedComplex_complete T.projectedTriangle T.separated different same
  intro x y same
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) x
  obtain ⟨b, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue Set.univ) y
  change Cap.horizontal (T.placement a.1 a.2.val) = Cap.horizontal (T.placement b.1 b.2.val) at same
  dsimp only [placement] at same
  rw [(family (T.support a.1)).horizontal_place,
    (family (T.support b.1)).horizontal_place] at same
  exact (C.point_eq_iff Set.univ a b).mpr
    (C.related_of_affine_projection_eq A joined convex conforming' separated complete a b same)

/-- The projected physical surface is exactly the prescribed slanted section. -/
theorem pairedFolding_footprint :
    Cap.horizontal '' T.pairedFolding.surface = clipAbove family floor Z := by
  ext x
  rw [T.cover]
  constructor
  · rintro ⟨z, on_roof, rfl⟩
    obtain ⟨i, p, member, rfl⟩ := Set.mem_iUnion.mp on_roof
    exact Set.mem_iUnion.mpr ⟨i, (T.triangle_carrier i).subset member |>.elim
      (fun q ⟨projects, at_point⟩ => by
        change Cap.horizontal ((family (T.support i)).place p) ∈ _
        rw [← at_point, (family (T.support i)).horizontal_place, AffineEquiv.apply_symm_apply]
        exact projects)⟩
  · intro member
    obtain ⟨i, in_triangle⟩ := Set.mem_iUnion.mp member
    let q := (family (T.support i)).project.symm x
    have in_face : q ∈ (T.triangle i).carrier := (T.triangle_carrier i).symm.subset
      ⟨x, in_triangle, rfl⟩
    refine ⟨T.placement i q, Set.mem_iUnion.mpr ⟨i, q, in_face, rfl⟩, ?_⟩
    exact (family (T.support i)).horizontal_place q |>.trans
      ((family (T.support i)).project.apply_symm_apply x)

/-- Supporting planes, complete original physical pairings, and a conforming partition
construct all the geometric roof fields; no embedding or disk certificate is supplied. -/
def roof (inside : (interior (clipAbove family floor Z)).Nonempty) : ConvexRoof T.pairedComplex where
  folding := T.pairedFolding
  normal i := (family (T.support i)).normal
  normal_unit i := (family (T.support i)).normal_unit
  normal_upward i := (family (T.support i)).normal_upward
  normal_tangent i := (family (T.support i)).normal_tangent
  supporting i j x := by
    change inner ℝ (family (T.support i)).normal
      (T.placement j x.val - (family (T.support i)).place 0) ≤ 0
    rw [T.placement_eq_point j x.property]
    exact point_supporting family (T.support i) _
  projection_injective := T.pairedProjection_injective
  convex_projection := by
    rw [T.pairedFolding_footprint]
    exact convex_clipAbove family floor Z
  interior_projection := by
    rw [T.pairedFolding_footprint]
    exact inside

/-- The physical roof projects to the identical constrained triangles. -/
theorem roof_projectedTriangle (inside : (interior (clipAbove family floor Z)).Nonempty)
    (i : T.Index) : (T.roof inside).projectedTriangle i = T.projectedTriangle i := by
  apply Triangle.eq_of_vertex_eq
  intro k
  rw [ConvexRoof.projectedTriangle_vertex]
  change Cap.horizontal ((family (T.support i)).place ((T.triangle i).vertex k)) = _
  rw [(family (T.support i)).horizontal_place]
  exact (family (T.support i)).project.apply_symm_apply _

theorem roof_footprint (inside : (interior (clipAbove family floor Z)).Nonempty) :
    (T.roof inside).footprint = clipAbove family floor Z := T.pairedFolding_footprint

end Unfoldings.SpatialEnvelope.FloorMesh
