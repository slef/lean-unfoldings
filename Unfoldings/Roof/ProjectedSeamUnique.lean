module

public import Unfoldings.Roof.ProjectedOpening
public import Unfoldings.Complex.RegularSeamUnique

/-! An actual projected nonvertex seam point determines its unique original seam. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

/-- Distinct actual original seams can meet in projection only at original vertices. -/
theorem projected_seam_unique_at_regular_point (s t : C.Seam) {z : Plane}
    (first : z ∈ (K.projectedTriangle (C.left s).face).edge (C.left s).edge)
    (last : z ∈ (K.projectedTriangle (C.left t).face).edge (C.left t).edge)
    (regular : ∀ f j, z ≠ (K.projectedTriangle f).vertex j) : s = t := by
  rw [projectedTriangle, Triangle.affineImage_edge] at first last
  obtain ⟨a, ha, first⟩ := first
  obtain ⟨b, hb, last⟩ := last
  let x : (C.triangle (C.left s).face).Edge (C.left s).edge := ⟨a, ha⟩
  let y : (C.triangle (C.left t).face).Edge (C.left t).edge := ⟨b, hb⟩
  have raw_regular : ¬ C.IsVertex (C.edgePoint (C.left s) x) := by
    rintro ⟨j, corner⟩
    exact regular (C.left s).face j (first.symm.trans (congrArg (K.projectFace _) corner.symm))
  have equal : C.faceMap Set.univ (C.left s).face
      ((C.triangle (C.left s).face).edgeMap (C.left s).edge x) =
    C.faceMap Set.univ (C.left t).face
      ((C.triangle (C.left t).face).edgeMap (C.left t).edge y) :=
    K.projection_injective (first.trans last.symm)
  exact C.seams_eq_of_related_regular_edgePoints s t x y raw_regular
    ((C.faceMap_eq_iff Set.univ _ _ _ _).mp equal)

end Unfoldings.ConvexRoof
