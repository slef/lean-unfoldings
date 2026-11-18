module

public import Unfoldings.Complex.Subdivision
public import Unfoldings.Complex.PhysicalCutEquiv
public import Unfoldings.Metric.FlatPhysicalCutRefinement

/-! Rigid geometric subdivisions construct exact physical cut refinements. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  (S : C.Subdivision D) (F : SpatialFolding C) (G : SpatialFolding D)
  (spatial : ∀ g x, F.place (S.parent g) (S.place g x) = G.place g x)

/-- Fine triangles expressed in the exact rigid coordinates of one whole original face. -/
def physicalPiece (f : Face) (g : {g // S.parent g = f}) : Set Plane :=
  S.place g.val '' (D.triangle g.val).carrier

theorem physicalPiece_closed (f : Face) (g : {g // S.parent g = f}) :
    IsClosed (S.physicalPiece f g) :=
  (S.place g.val).toHomeomorph.isClosedMap _ (D.triangle g.val).compact_carrier.isClosed

theorem physicalPiece_convex (f : Face) (g : {g // S.parent g = f}) :
    Convex ℝ (S.physicalPiece f g) :=
  (D.triangle g.val).convex_carrier.affine_image (S.place g.val).toAffineMap

theorem physicalPiece_full (f : Face) (g : {g // S.parent g = f}) :
    (interior (S.physicalPiece f g)).Nonempty := by
  change (interior ((S.place g.val).toHomeomorph '' (D.triangle g.val).carrier)).Nonempty
  rw [← Homeomorph.image_interior]
  exact (D.triangle g.val).interior_nonempty.image _

theorem physicalPiece_cover (f : Face) : (C.triangle f).carrier = ⋃ g, S.physicalPiece f g := by
  ext p
  constructor
  · intro member
    obtain ⟨g, y, parent, same⟩ := S.cover f ⟨p, member⟩
    exact Set.mem_iUnion.mpr ⟨⟨g, parent⟩, y.val, y.property, same⟩
  · rintro member
    obtain ⟨g, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨y, contained, rfl⟩ := member
    have inside := S.inside g.val y contained
    rwa [g.property] at inside

include spatial in
theorem physicalPiece_image (f : Face) (g : {g // S.parent g = f}) :
    F.place f '' S.physicalPiece f g = G.faceImage g.val := by
  ext p
  constructor
  · rintro ⟨q, ⟨y, member, rfl⟩, rfl⟩
    refine ⟨y, member, ?_⟩
    exact (spatial g.val y).symm.trans
      (congrArg (fun f => F.place f (S.place g.val y)) g.property)
  · rintro ⟨y, member, rfl⟩
    refine ⟨S.place g.val y, ⟨y, member, rfl⟩, ?_⟩
    exact (congrArg (fun f => F.place f (S.place g.val y)) g.property).symm.trans
      (spatial g.val y)

/-- Physical containment and complete rigid face coverage derive the exact cut metric data. -/
def physicalCutRefinement (cuts : Set Space) (closed : IsClosed cuts)
    (outside : ∀ f, Disjoint (interior (C.triangle f).carrier) (F.place f ⁻¹' cuts)) :
    MetricGluing.PhysicalCutRefinement F.faceImage G.faceImage
      (fun g => (G.compact_faceImage g).isClosed) cuts :=
  MetricGluing.flatPhysicalCutRefinement (E := Plane) (F := Space) F.faceImage G.faceImage
    (fun g => (G.compact_faceImage g).isClosed) cuts S.parent (fun f => F.place f)
    (fun f => (F.place f).isometry) (fun f => (C.triangle f).carrier) S.physicalPiece
    S.physicalPiece_closed S.physicalPiece_convex S.physicalPiece_full
    (fun f => (C.triangle f).convex_carrier) S.physicalPiece_cover (fun _ => rfl)
    (S.physicalPiece_image F G spatial)
    (fun f => closed.preimage (F.place f).continuous) outside

theorem physicalCutRefinement_of (cuts : Set Space) (closed : IsClosed cuts)
    (outside : ∀ f, Disjoint (interior (C.triangle f).carrier) (F.place f ⁻¹' cuts))
    (g : Child) (y : D.Cell g) :
    (S.physicalCutRefinement F G spatial cuts closed outside).isometryEquiv
      (fun f => (F.compact_faceImage f).isClosed) (G.faceMapToPhysicalCut cuts g y) =
        F.faceMapToPhysicalCut cuts (S.parent g) (S.parentCell g y) := by
  change MetricGluing.of (fun f => F.faceImage f)
    (F.physicalCutSeams cuts).relation (S.parent g) _ =
    MetricGluing.of (fun f => F.faceImage f) (F.physicalCutSeams cuts).relation (S.parent g) _
  apply congrArg (fun p : F.faceImage (S.parent g) =>
    MetricGluing.of (fun f => F.faceImage f) (F.physicalCutSeams cuts).relation (S.parent g) p)
  exact Subtype.ext (spatial g y.val).symm

/-- Exact parent-point maps determine retained seam correspondence in both directions. -/
theorem conforming_of_injective_pointMap {retain : Set C.Seam} {fineRetain : Set D.Seam}
    (mapping : D.Realization fineRetain → C.Realization retain)
    (injective : Function.Injective mapping)
    (points : ∀ a : D.Total, mapping (MetricGluing.point D.Cell (D.glue fineRetain) a) =
      MetricGluing.point C.Cell (C.glue retain) (S.parentPoint a)) :
    S.Conforming retain fineRetain := by
  constructor
  · intro a b joined
    apply (C.point_eq_iff retain _ _).mp
    rw [← points a, ← points b]
    exact congrArg mapping (MetricGluing.point_eq_of_glue D.Cell joined)
  · intro a b related
    apply (D.point_eq_iff fineRetain _ _).mp
    apply injective
    rw [points a, points b]
    exact MetricGluing.point_eq_of_eqvGen C.Cell related

end Unfoldings.TriangleComplex.Subdivision
