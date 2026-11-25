module

public import Unfoldings.Roof.SpatialEnvelopeInteriorSeams
public import Unfoldings.Convex.PhysicalModelMesh
public import Unfoldings.Geometry.PrescribedSegments

/-! Mesh a physical extension along any finite family of prescribed segments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.FiniteSlopeModel

variable {E : SlopeEnvelope} (M : E.FiniteSlopeModel)
  {J : Type} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, extra j ≠ 0)
  {n : ℕ} (first last : Fin n → Plane) (different : ∀ i, first i ≠ last i)
  {a : ℝ} (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes)
  {Z : ℝ} {q : Plane} (inside : Z < -E.height q)

local notation "lines" => Sum.elim extra (segmentEquations first last different)

include proper in
theorem prescribedLines_ne_zero :
    ∀ k : J ⊕ (Fin n × Fin 3), lines k ≠ 0
  | .inl j => proper j
  | .inr k => segmentEquations_ne_zero first last different k

/-- Refine the spatial graph section along the supplied lines, segment carriers,
and endpoint lines. This construction does not use a routing potential. -/
def prescribedSegmentMesh : SpatialEnvelope.ConstrainedTriangulation M.plane lines Z :=
  M.mesh lines (prescribedLines_ne_zero extra proper first last different)
    positive inner_disk (q := q) inside

local notation "meshOfSegments" =>
  M.prescribedSegmentMesh extra proper first last different positive inner_disk inside

theorem prescribedSegmentMesh_conforming :
    TriangleFamily.Conforming (meshOfSegments).projectedTriangle :=
  M.mesh_conforming lines (prescribedLines_ne_zero extra proper first last different)
    positive inner_disk (q := q) inside

/-- Each prescribed segment is exactly a union of edges of the physical mesh,
including at every original bend and segment endpoint. -/
theorem prescribedSegmentMesh_edge_cover (i : Fin n)
    (start_inside : E.height (first i) ≤ -Z) (end_inside : E.height (last i) ≤ -Z) :
    let T := meshOfSegments
    segment ℝ (first i) (last i) =
      ⋃ e : {e : T.Index × Fin 3 // (T.projectedTriangle e.1).edge e.2 ⊆
          segment ℝ (first i) (last i)}, (T.projectedTriangle e.val.1).edge e.val.2 := by
  let T := meshOfSegments
  let aligned : SpatialEnvelope.ConstrainedTriangulation M.plane
      (segmentEquations first last different) Z := {
    toTriangulation := T.toTriangulation
    signs e k := T.signs e (.inr k)
    constrained e x present k := T.constrained e x present (.inr k) }
  apply aligned.prescribed_segment_eq_union_subedges <;>
    rw [M.clip_eq_sublevel] <;> assumption

end Unfoldings.SlopeEnvelope.FiniteSlopeModel
