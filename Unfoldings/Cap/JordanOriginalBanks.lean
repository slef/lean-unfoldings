module

public import Unfoldings.Complex.BoundaryEdgeDetection
public import Unfoldings.Complex.FaceRestrictionLinks
public import Unfoldings.Cap.JordanBoundary

/-! Construct actual Jordan banks from original mesh edges on the curve. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)
  {J : Set Plane} (jordan : Schoenflies.IsJordanCurve J) (contains : J ⊆ K.footprint)
  (avoids : ∀ f, Disjoint (interior (K.projectedTriangle f).carrier) J)

include jordan contains avoids in
open Classical in
/-- An original mesh edge on the curve is an actual unpaired edge of the selected patch.
Boundary status is derived from one regular point of the physical edge. -/
theorem jordan_selected_edge_isBoundary (f : {f : Face // f ∈ K.jordanFaces J})
    (edge : Fin 3) (on_curve : (K.projectedTriangle f.val).edge edge ⊆ J) :
    (C.restrictFaces (K.jordanFaces J)).IsBoundaryEdge Set.univ ⟨f, edge⟩ := by
  let R := C.restrictFaces (K.jordanFaces J)
  obtain ⟨x, regular⟩ := (R.triangle f).exists_edge_nonvertex edge
  have projected : K.toRoof.restrictProjection (K.jordanFaces J)
      (R.faceMap Set.univ f ((R.triangle f).edgeMap edge x)) ∈ J := by
    apply on_curve
    rw [ConvexCap.projectedTriangle, Triangle.affineImage_edge]
    exact ⟨x.val, x.property, rfl⟩
  exact R.isBoundaryEdge_of_regular_bankBoundary Set.univ ⟨f, edge⟩ x regular
    ((K.jordan_bankBoundary_iff jordan contains avoids _).mpr projected)

include jordan contains avoids in
open Classical in
/-- The selected original incident face and the physical edge on the curve construct the
actual Jordan bank, preserving its exact raw face, corner and endpoint flag. -/
theorem exists_jordan_bank_of_original_germ (p : C.Germ)
    (selected : p.1.1 ∈ K.jordanFaces J)
    (on_curve : (K.projectedTriangle p.1.1).edge (C.germEdge p).edge ⊆ J) :
    ∃ q : (C.restrictFaces (K.jordanFaces J)).BoundaryEnd Set.univ,
      C.includeRestrictedGerm (K.jordanFaces J) q.val = p := by
  let f : {f : Face // f ∈ K.jordanFaces J} := ⟨p.1.1, selected⟩
  let germ : (C.restrictFaces (K.jordanFaces J)).Germ := ((f, p.1.2), p.2)
  have boundary := K.jordan_selected_edge_isBoundary jordan contains avoids f
    (C.germEdge p).edge on_curve
  exact ⟨⟨germ, boundary⟩, rfl⟩

end Unfoldings.ConvexCap
