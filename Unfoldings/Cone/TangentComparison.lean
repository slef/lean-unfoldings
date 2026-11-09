module

public import Unfoldings.Cone.TriangleInclusion
public import Unfoldings.Complex.Neighborhood
public import Unfoldings.Metric.LocalSeams

/-!
# Local metric comparison from original surfaces to tangent fans

Only incident original faces occur in a sufficiently small vertex ball.
The tangent maps agree across every incident retained edge, so the closed
seam localization theorem makes them nonexpanding on that whole ball.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

/-- Any sufficiently near tagged point belongs to a face incident to this vertex copy. -/
theorem exists_radius_cornerAt_face :
    ∃ r > 0, ∀ a : C.Total,
      edist (C.vertexPoint retain v) (MetricGluing.point C.Cell (C.glue retain) a) <
        ENNReal.ofReal r → ∃ c : C.CornerAt retain v, c.val.1 = a.1 := by
  obtain ⟨root, root_eq⟩ := C.vertexOfCorner_surjective retain v
  obtain ⟨r, positive, transport⟩ := C.exists_class_transport retain (C.cornerPoint root)
  refine ⟨r, positive, ?_⟩
  intro a near
  have root_point : MetricGluing.point C.Cell (C.glue retain) (C.cornerPoint root) =
      C.vertexPoint retain v := congrArg (C.vertexPoint retain) root_eq
  rw [← root_point] at near
  obtain ⟨q, related, _⟩ := MetricGluing.exists_classPoint_of_edist_lt C.Cell
    (C.glue retain) (C.cornerPoint root) positive le_rfl
    (C.finite_classIn retain _) transport a near
  have vertex : C.IsVertex ⟨a.1, q⟩ :=
    (C.eqvGen_preserves_vertex retain related).mp (C.isVertex_cornerPoint root)
  obtain ⟨d, equal⟩ := C.exists_cornerPoint_of_isVertex vertex
  have same_vertex : C.vertexOfCorner retain d = v := by
    apply C.vertexPoint_injective retain
    change MetricGluing.point C.Cell (C.glue retain) (C.cornerPoint d) = _
    rw [equal, ← root_point]
    exact ((C.point_eq_iff retain _ _).mpr related).symm
  refine ⟨⟨d, same_vertex⟩, ?_⟩
  exact congrArg (fun p : C.Total => p.1) equal

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

theorem surfaceTangentCell_incident (root : C.CornerAt retain v)
    (s : (C.closedSeams retain).Seam)
    (incident : (C.closedSeams retain).Incident (C.cornerPoint root.val) s) :
    ∀ x, C.surfaceTangentCell retain v ((C.closedSeams retain).left s)
        ((C.closedSeams retain).toLeft s x) =
      C.surfaceTangentCell retain v ((C.closedSeams retain).right s)
        ((C.closedSeams retain).toRight s x) := by
  have star := C.vertexStar_keeps_incident retain root.val s.val s.property
    (C.seamIncident_of_closedSeams_incident retain _ s incident)
  obtain ⟨_, b, endpoint⟩ := (C.mem_vertexStarSeams_iff retain _ s.val).mp star
  let tangent : C.TangentSeam retain v :=
    ⟨(s.val, false, b), s.property, endpoint.trans root.property⟩
  intro x
  change C.surfaceTangentCell retain v (C.left s.val).face
      ((C.triangle (C.left s.val).face).edgeMap (C.left s.val).edge x) =
    C.surfaceTangentCell retain v (C.right s.val).face
      ((C.triangle (C.right s.val).face).edgeMap (C.right s.val).edge (C.identify s.val x))
  exact (F.surfaceTangentCell_eq retain v (C.tangentLeft retain v tangent) _).trans
    ((C.tangentInclude_seam retain v tangent x).trans
      (F.surfaceTangentCell_eq retain v (C.tangentRight retain v tangent) _).symm)

/-- The original tagged maps into the tangent fan are nonexpanding near the vertex. -/
theorem exists_surfaceTangentCell_edist_le :
    ∃ r > 0, ∀ a b : C.Total,
      edist (C.vertexPoint retain v) (MetricGluing.point C.Cell (C.glue retain) a) <
        ENNReal.ofReal r →
      edist (C.vertexPoint retain v) (MetricGluing.point C.Cell (C.glue retain) b) <
        ENNReal.ofReal r →
      edist (C.surfaceTangentCell retain v a.1 a.2)
          (C.surfaceTangentCell retain v b.1 b.2) ≤
        edist (MetricGluing.point C.Cell (C.glue retain) a)
          (MetricGluing.point C.Cell (C.glue retain) b) := by
  obtain ⟨corner, eq_corner⟩ := C.vertexOfCorner_surjective retain v
  let root : C.CornerAt retain v := ⟨corner, eq_corner⟩
  have finite : ∀ i, (MetricGluing.classIn C.Cell
      (C.closedSeams retain).relation (C.cornerPoint corner) i).Finite := by
    simpa only [C.closedSeams_relation] using C.finite_classIn retain (C.cornerPoint corner)
  have result := (C.closedSeams retain).exists_radius_map_edist_le
    (C.cornerPoint corner) finite (C.surfaceTangentCell retain v)
    (C.surfaceTangentCell_lipschitz retain v) (F.surfaceTangentCell_incident retain v root)
  rw [C.closedSeams_relation] at result
  have root_point : MetricGluing.point C.Cell (C.glue retain) (C.cornerPoint corner) =
      C.vertexPoint retain v := congrArg (C.vertexPoint retain) eq_corner
  rw [root_point] at result
  exact result

/-- On every incident triangle, the original and tangent vertex distances agree exactly. -/
theorem surfaceTangentCell_radial (c : C.CornerAt retain v) (x : C.Cell c.val.1) :
    edist (C.tangentOrigin retain v) (C.surfaceTangentCell retain v c.val.1 x) =
      edist (C.vertexPoint retain v) (C.faceMap retain c.val.1 x) := by
  rw [F.surfaceTangentCell_eq retain v c]
  have radial := F.tangentSurfaceTag_radial retain v
    ⟨c, C.tangentInclude retain v c x⟩ x.property
  rw [tangentSurfaceTag_include retain v c x] at radial
  exact radial.symm

end Unfoldings.SpatialFolding
