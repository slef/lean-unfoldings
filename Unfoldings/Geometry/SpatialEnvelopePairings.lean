module

public import Unfoldings.Geometry.SpatialEnvelopeTriangles
public import Unfoldings.Complex.GeometricPairings
public import Unfoldings.Complex.Folding

/-! Actual physical whole-edge seams on finite affine-roof sections. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z : ℝ} (T : Triangulation family Z)

local instance : Fintype T.Index := @Fintype.ofFinite _ T.finite

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

theorem paired_seam_projected_edge (s : T.pairedComplex.Seam) :
    (T.projectedTriangle (T.pairedComplex.left s).face).edge (T.pairedComplex.left s).edge =
      (T.projectedTriangle (T.pairedComplex.right s).face).edge (T.pairedComplex.right s).edge :=
  (TriangleFamily.seamPair T.projectedTriangle s).carrier_eq

theorem paired_seam_projection (s : T.pairedComplex.Seam)
    (x : (T.triangle (T.pairedComplex.left s).face).Edge (T.pairedComplex.left s).edge) :
    (family (T.support (T.pairedComplex.right s).face)).project (T.pairedComplex.identify s x).val =
      (family (T.support (T.pairedComplex.left s).face)).project x.val :=
  T.edgeTransition_projection (TriangleFamily.seamPair T.projectedTriangle s).carrier_eq x

theorem pairedFolding_surface : T.pairedFolding.surface = surface family Z :=
  T.spatial_cover.symm

end Unfoldings.SpatialEnvelope.Triangulation
