module

public import Unfoldings.Cap.SectionAngles
public import Unfoldings.Geometry.FiniteConvexTrace

/-!
# Constructed finite original-face traces of cap sections

Every straight projected segment in the convex footprint has a finite strictly
ordered partition into whole pieces contained in original projected triangles.
The original face labels and the actual concave roof agree on each piece.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- Actual projected-face membership identifies the roof with that face's supporting plane. -/
theorem roofHeight_eq_supportHeight_of_mem (f : Face) {p : Plane}
    (inside : p ∈ (K.projectedTriangle f).carrier) : K.roofHeight p = K.supportHeight f p := by
  rw [projectedTriangle, Triangle.affineImage_carrier] at inside
  obtain ⟨x, carrier, rfl⟩ := inside
  exact (K.roofHeight_face f ⟨x, carrier⟩).trans (K.supportHeight_face f x).symm

/-- Construct the face trace from the actual finite convex cover. -/
theorem exists_section_face_partition {p q : Plane} (first : p ∈ K.footprint)
    (last : q ∈ K.footprint) :
    ∃ n : ℕ, 0 < n ∧ ∃ time : Fin (n + 1) → unitInterval,
      StrictMono time ∧ time 0 = 0 ∧ time (Fin.last n) = 1 ∧
      ∃ face : Fin n → Face, ∀ i, ∀ t ∈ Set.Icc (time i.castSucc) (time i.succ),
        AffineMap.lineMap p q (t : ℝ) ∈ (K.projectedTriangle (face i)).carrier := by
  apply exists_finite_closed_convex_segment_partition
    (fun f => (K.projectedTriangle f).carrier)
    (fun f => (K.projectedTriangle f).compact_carrier.isClosed)
    (fun f => (K.projectedTriangle f).convex_carrier) p q
  intro x member
  exact Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset
    (K.convex_projection.segment_subset first last member))

end Unfoldings.ConvexCap
