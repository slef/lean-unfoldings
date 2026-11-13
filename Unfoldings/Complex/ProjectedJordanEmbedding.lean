module

public import Unfoldings.Complex.ProjectedEmbedding
public import Unfoldings.Geometry.ConformingJordanStar

/-! Exact intrinsic fibers for conforming projections onto Jordan disks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (A : Face → Plane ≃ᵃ[ℝ] Plane)

/-- A conforming Jordan-disk projection identifies every copy in each vertex star. -/
theorem projectedPointCopy_eq_of_ambientDisk
    (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
    (h : Plane ≃ₜ Plane)
    (image : h '' (⋃ f, (C.affineProjectedTriangle A f).carrier) = Metric.closedBall (0 : Plane) 1)
    (conforming : TriangleFamily.Conforming (C.affineProjectedTriangle A))
    (separated : Pairwise (fun f g => Disjoint
      (interior (C.affineProjectedTriangle A f).carrier)
      (interior (C.affineProjectedTriangle A g).carrier)))
    (complete : ∀ f g : Face, f ≠ g → ∀ e d : Fin 3,
      (C.affineProjectedTriangle A f).edge e = (C.affineProjectedTriangle A g).edge d →
        ∃ s, (C.left s = ⟨f, e⟩ ∧ C.right s = ⟨g, d⟩) ∨
          (C.left s = ⟨g, d⟩ ∧ C.right s = ⟨f, e⟩))
    (p : Plane) {f g : Face} (first : p ∈ (C.affineProjectedTriangle A f).carrier)
    (last : p ∈ (C.affineProjectedTriangle A g).carrier) :
    C.projectedPointCopy A f p first = C.projectedPointCopy A g p last := by
  let value (a : {f // p ∈ (C.affineProjectedTriangle A f).carrier}) :=
    C.projectedPointCopy A a.val p a.property
  apply TriangleFamily.incident_values_eq_of_ambientDisk (C.affineProjectedTriangle A) h image rfl
    conforming separated p value _ ⟨f, first⟩ ⟨g, last⟩
  intro a b e d same member
  by_cases different : a.val = b.val
  · exact congrArg value (Subtype.ext different)
  obtain ⟨s, ⟨left, right⟩ | ⟨right, left⟩⟩ := complete a.val b.val different e d same
  · have at_left : p ∈ (C.affineProjectedTriangle A (C.left s).face).edge (C.left s).edge := by
      simpa only [left] using member
    simpa only [left, right, value] using C.projectedPointCopy_across_seam A joined s at_left
  · have at_left : p ∈ (C.affineProjectedTriangle A (C.left s).face).edge (C.left s).edge := by
      have at_b : p ∈ (C.affineProjectedTriangle A b.val).edge d := same ▸ member
      simpa only [right] using at_b
    simpa only [left, right, value] using (C.projectedPointCopy_across_seam A joined s at_left).symm

/-- Equality in a conforming projection is precisely actual finite seam identification. -/
theorem related_of_affine_projection_eq_of_ambientDisk
    (joined : ∀ s x, A (C.left s).face x.val = A (C.right s).face (C.identify s x).val)
    (h : Plane ≃ₜ Plane)
    (image : h '' (⋃ f, (C.affineProjectedTriangle A f).carrier) = Metric.closedBall (0 : Plane) 1)
    (conforming : TriangleFamily.Conforming (C.affineProjectedTriangle A))
    (separated : Pairwise (fun f g => Disjoint
      (interior (C.affineProjectedTriangle A f).carrier)
      (interior (C.affineProjectedTriangle A g).carrier)))
    (complete : ∀ f g : Face, f ≠ g → ∀ e d : Fin 3,
      (C.affineProjectedTriangle A f).edge e = (C.affineProjectedTriangle A g).edge d →
        ∃ s, (C.left s = ⟨f, e⟩ ∧ C.right s = ⟨g, d⟩) ∨
          (C.left s = ⟨g, d⟩ ∧ C.right s = ⟨f, e⟩))
    (a b : C.Total) (same : A a.1 a.2.val = A b.1 b.2.val) :
    Relation.EqvGen (C.glue Set.univ) a b := by
  have member (a : C.Total) : A a.1 a.2.val ∈ (C.affineProjectedTriangle A a.1).carrier :=
    ((C.triangle a.1).affineImage_carrier (A a.1).toAffineMap
      (A a.1).injective).symm.subset ⟨a.2.val, a.2.property, rfl⟩
  have point (a : C.Total) : C.projectedPointCopy A a.1 (A a.1 a.2.val) (member a) =
      MetricGluing.point C.Cell (C.glue Set.univ) a := by
    change C.faceMap Set.univ a.1 ⟨(A a.1).symm (A a.1 a.2.val), _⟩ = C.faceMap Set.univ a.1 a.2
    apply congrArg (C.faceMap Set.univ a.1)
    exact Subtype.ext ((A a.1).symm_apply_apply _)
  have both := C.projectedPointCopy_eq_of_ambientDisk A joined h image conforming separated complete
    (A a.1 a.2.val) (member a) (same.symm ▸ member b)
  apply (C.point_eq_iff Set.univ a b).mp
  rw [← point a, ← point b]
  simpa only [same] using both

end Unfoldings.TriangleComplex
