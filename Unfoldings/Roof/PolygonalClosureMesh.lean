module

public import Unfoldings.Geometry.ConstraintInteriors
public import Unfoldings.Geometry.PolygonalClosureEquations
public import Unfoldings.Geometry.SpatialEnvelopeAlignment
public import Unfoldings.Roof.SpatialEnvelopeCoordinates
public import Unfoldings.Cap.JordanAngleBalance

/-! Construct physical cap meshes respecting every actual link of a polygonal Jordan closure. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : Triangulation family Z) {n : ℕ} (P : PolygonalChain Plane n) (source c : Plane)
  (inside : (interior (clip family Z)).Nonempty)

/-- Universal lifts keep the prescribed finite constraints compatible with any mesh universe. -/
def alignToClosure : ConstrainedTriangulation family
    (fun i : ULift.{u} (Fin n ⊕ Fin 4) => P.closureEquations source c i.down) Z :=
  T.alignToLines _ (fun i => P.closureEquations_ne_zero source c i.down) inside

theorem alignToClosure_conforming : TriangleFamily.Conforming
    (T.alignToClosure P source c inside).projectedTriangle :=
  T.alignToLines_conforming
    (fun i : ULift.{u} (Fin n ⊕ Fin 4) => P.closureEquations source c i.down)
    (fun i => P.closureEquations_ne_zero source c i.down) inside

theorem alignToClosure_avoids (i : (T.alignToClosure P source c inside).Index) :
    Disjoint (interior ((T.alignToClosure P source c inside).projectedTriangle i).carrier)
      (P.threeSegmentClosure source c) := by
  apply (T.alignToClosure P source c inside).interior_avoids_supported_curve
    (fun j => P.closureEquations_ne_zero source c j.down)
  intro p hp
  obtain ⟨j, zero⟩ := P.closureEquations_support source c p hp
  exact ⟨ULift.up j, zero⟩

local instance polygonalClosureMeshIndexFintype : Fintype
    (T.alignToClosure P source c inside).Index :=
  @Fintype.ofFinite _ (T.alignToClosure P source c inside).finite

/-- The constrained physical refinement is an actual convex cap with its original support labels. -/
def closureCap : ConvexCap (T.alignToClosure P source c inside).pairedComplex :=
  (T.alignToClosure P source c inside).toTriangulation.normalizedCap
    (T.alignToClosure_conforming P source c inside) inside

theorem closureCap_footprint : (T.closureCap P source c inside).footprint = clip family Z :=
  (T.alignToClosure P source c inside).toTriangulation.normalizedCap_footprint
    (T.alignToClosure_conforming P source c inside) inside

theorem closureCap_avoids (i : (T.alignToClosure P source c inside).Index) :
    Disjoint (interior ((T.closureCap P source c inside).projectedTriangle i).carrier)
      (P.threeSegmentClosure source c) := by
  change Disjoint (interior (((T.alignToClosure P source c inside).toTriangulation.normalizedCap
    (T.alignToClosure_conforming P source c inside) inside).projectedTriangle i).carrier) _
  rw [(T.alignToClosure P source c inside).toTriangulation.normalizedCap_projectedTriangle_carrier]
  exact T.alignToClosure_avoids P source c inside i

open scoped Classical in
/-- Exact geometric angle balance on the constructed physical closure mesh. -/
theorem closureCap_jordan_angle_balance
    (jordan : Schoenflies.IsJordanCurve (P.threeSegmentClosure source c))
    (contained : P.threeSegmentClosure source c ⊆ interior (clip family Z)) :
    let K := T.closureCap P source c inside
    (∑ w : (T.alignToClosure P source c inside).pairedComplex.Vertex Set.univ,
      if K.projectedVertex w ∈ P.threeSegmentClosure source c then
        K.regionalAngleExcess (K.jordanFaces (P.threeSegmentClosure source c)) w else 0) =
          ∑ w : (T.alignToClosure P source c inside).pairedComplex.Vertex Set.univ,
            if K.projectedVertex w ∈ interior
                (PlanarTopology.closedJordanDomain (P.threeSegmentClosure source c)) then
              (T.alignToClosure P source c inside).pairedComplex.interiorAngularDefect Set.univ w
            else 0 := by
  apply (T.closureCap P source c inside).jordan_boundary_angle_balance jordan
  · rwa [T.closureCap_footprint]
  · exact T.closureCap_avoids P source c inside

end Unfoldings.SpatialEnvelope.Triangulation
