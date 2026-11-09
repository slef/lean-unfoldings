module

public import Unfoldings.PolygonalLayout
public import Unfoldings.Source.CutSegments

/-!
# A finite nonoverlapping polygonal source net

This constructs an ordinary finite polygonal layout with one rigid original-face
map on each whole closed piece. Its footprint is the actual completed source
domain and all piece maps agree with the constructed endpoint projection.
The completed disk, intrinsic cut metric, radial shortest paths, and exact cut
boundary are supplied by the preceding source construction.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary)

open AffineArrangement

theorem exists_source_polygonal_net :
    letI := P.metricSpace
    ∀ {source : C.Realization Set.univ} (R : SourceFrame source),
      ∃ (Piece : Type) (_ : Fintype Piece) (D : FacePolygonalLayout C Piece),
        D.Nonoverlapping ∧ D.footprint = R.domain ∧
          ∀ i (x : D.region i), ∃ z : R.domain, z.val = x.val ∧
            R.projection (P.sourcePathCoordinate_injective R) z = D.fold Set.univ i x := by
  let := P.metricSpace
  intro source R
  obtain ⟨L, finite_L, _, S, finite_S, polygons, disjoint, cover⟩ :=
    P.exists_finite_source_polygon_pieces R
  let := finite_L.fintype
  let := finite_S.fintype
  let equations (l : L) := l.val
  have specifications (a : S) : ∃ (f : Face) (A : Plane ≃ᵃⁱ[ℝ] Plane), ∀ z : R.domain,
      z.val ∈ closedChamber equations a.val → ∃ y : C.Cell f, z.val = A y.val ∧
        R.projection (P.sourcePathCoordinate_injective R) z = C.faceMap Set.univ f y :=
    (polygons a.val a.property).2.2.2.2
  choose face motion formula using specifications
  have included (a : S) : closedChamber equations a.val ⊆ R.domain :=
    (polygons a.val a.property).2.2.2.1
  let D : FacePolygonalLayout C S :=
    { finite_pieces := inferInstance
      region := fun a => closedChamber equations a.val
      halfplanes := fun a => Set.range (fun l : L => signed l.val (a.val l))
      finite_halfplanes := fun _ => Set.finite_range _
      region_eq := by
        intro a
        ext x
        change (∀ l : L, 0 ≤ signed l.val (a.val l) x) ↔
          ∀ h ∈ Set.range (fun l : L => signed l.val (a.val l)), 0 ≤ h x
        exact (Set.forall_mem_range
          (f := fun l : L => signed l.val (a.val l))
          (p := fun h : Plane →ᵃ[ℝ] ℝ => 0 ≤ h x)).symm
      compact_region := fun a => (polygons a.val a.property).1
      interior_nonempty := fun a => (polygons a.val a.property).2.2.1
      face := face
      foldPlacement := fun a => (motion a).symm
      in_face := by
        intro a x hx
        let z : R.domain := ⟨x, included a hx⟩
        obtain ⟨y, developed, _⟩ := formula a z hx
        have inverse : (motion a).symm x = y.val := by
          change x = motion a y.val at developed
          rw [developed, (motion a).symm_apply_apply]
        exact inverse.symm ▸ y.property }
  refine ⟨S, inferInstance, D, ?_, ?_, ?_⟩
  · intro a b different
    exact disjoint a.property b.property (fun equal => different (Subtype.ext equal))
  · ext x
    constructor
    · intro member
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp member
      exact included a ha
    · intro member
      obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp (cover ▸ member)
      exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hx⟩
  · intro a x
    let z : R.domain := ⟨x.val, included a x.property⟩
    obtain ⟨y, developed, image⟩ := formula a z x.property
    refine ⟨z, rfl, image.trans ?_⟩
    apply congrArg (C.faceMap Set.univ (face a))
    apply Subtype.ext
    change y.val = (motion a).symm x.val
    change x.val = motion a y.val at developed
    rw [developed, (motion a).symm_apply_apply]

end Unfoldings.SpatialFolding.ConvexBoundary
