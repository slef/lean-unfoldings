module

public import Unfoldings.Geometry.SpatialEnvelopeOpenSeams
public import Unfoldings.Geometry.PrescribedSubedge
public import Unfoldings.Geometry.PrescribedSegments
public import Unfoldings.Geometry.AffineSupportBoundary

/-! Prescribed geometric segment constraints construct the exact original triangle cut metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.ConstrainedTriangulation

universe u

variable {A : Type u} (first last : A → Plane) (different : ∀ a, first a ≠ last a)
  {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane} {Z : ℝ}
  (T : ConstrainedTriangulation family (segmentEquations first last different) Z)

local instance prescribedCutMetricIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- The supporting and endpoint lines make every prescribed cut a union of whole mesh edges
at all nonvertex edge points. No metric or seam matching certificate is assumed. -/
theorem prescribed_cut_aligned (f : T.Index) (e : Fin 3)
    (x : (T.projectedTriangle f).Edge e) (regular : ¬ (T.projectedTriangle f).IsVertex x.val)
    (member : x.val ∈ ⋃ a, segment ℝ (first a) (last a)) :
    (T.projectedTriangle f).edge e ⊆ ⋃ a, segment ℝ (first a) (last a) := by
  obtain ⟨a, on_segment⟩ := Set.mem_iUnion.mp member
  let U := triangleWithEdge (first a) (last a) (different a)
  have contained : (T.projectedTriangle f).edge e ⊆ U.edge 0 :=
    U.edge_subset_of_signed_coords (T.projectedTriangle f) (fun k => T.signs f (a, k))
      (fun k p hp => T.constrained f p hp (a, k)) 0 e x regular on_segment
  intro p hp
  exact Set.mem_iUnion.mpr ⟨a, contained hp⟩

/-- The actual prescribed segments avoid every original open triangle interior. -/
theorem prescribed_cut_disjoint_interior (f : T.Index) :
    Disjoint (interior (T.projectedTriangle f).carrier)
      (⋃ a, segment ℝ (first a) (last a)) := by
  apply Set.disjoint_left.mpr
  intro p inside member
  obtain ⟨a, on_segment⟩ := Set.mem_iUnion.mp member
  let U := triangleWithEdge (first a) (last a) (different a)
  have zero : segmentEquations first last different (a, 2) p = 0 :=
    U.coord_edge_eq_zero 0 ⟨p, on_segment⟩
  exact not_mem_interior_of_affine_lower_bound
    (AffineArrangement.signed (segmentEquations first last different (a, 2)) (T.signs f (a, 2)))
    (AffineArrangement.signed_ne_zero _ (segmentEquations_ne_zero first last different (a, 2)) _)
    (fun z hz => T.constrained f z hz (a, 2))
    ((AffineArrangement.signed_eq_zero_iff _ _ _).mpr zero) inside

/-- A conforming mesh constrained by the prescribed segment lines yields the actual
complete cut metric of its original retained triangle complex, including original corners. -/
def prescribedCutGraphEquiv (conforming : TriangleFamily.Conforming T.projectedTriangle) :
    T.pairedComplex.Realization (T.toTriangulation.retainOutside
      (⋃ a, segment ℝ (first a) (last a))) ≃ᵢ
        T.toTriangulation.graphPartition.Cut (⋃ a, segment ℝ (first a) (last a)) :=
  T.toTriangulation.alignedCutGraphEquiv conforming (⋃ a, segment ℝ (first a) (last a))
    (T.prescribed_cut_aligned first last different)

end Unfoldings.SpatialEnvelope.ConstrainedTriangulation
