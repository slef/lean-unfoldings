module

public import Unfoldings.Roof.DevelopmentOrientation
public import Unfoldings.Geometry.PlanarConjugation

/-!
# A common developed frame preserving the actual projection orientation

One reference face selects a frame. Connectedness of the retained dual graph
then makes the signed area of every original projected pair have the same sign
as the corresponding actual developed pair in this frame.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexRoof C)

/-- One fixed global frame, selected by one actual projected-to-developed face chart. -/
def roofProjectionFrame (reference : Face) : Plane ≃ₗᵢ[ℝ] Plane :=
  if 0 < orientationScale (D.roofPlacement K reference).toAffineMap then
    LinearIsometryEquiv.refl ℝ Plane else planeConjugation

/-- Every original face has a positive determinant in the same projection-preserving frame. -/
theorem roofProjectionFrame_positive (connected : C.DuallyConnected retain)
    (reference f : Face) (a b : Plane) (positive : 0 < orient 0 a b) :
    0 < orient 0 (D.roofProjectionFrame K reference (D.roofDirection K f a))
      (D.roofProjectionFrame K reference (D.roofDirection K f b)) := by
  have signs := D.roofPlacement_sign_constant K connected reference f
  by_cases first : 0 < orientationScale (D.roofPlacement K reference).toAffineMap
  · simp only [roofProjectionFrame, ite_eq_left first]
    change 0 < orient 0 (D.roofDirection K f a) (D.roofDirection K f b)
    rw [D.roofDirection_orient]
    exact mul_pos (signs.mp first) positive
  · simp only [roofProjectionFrame, ite_eq_right first, orient_planeConjugation]
    rw [D.roofDirection_orient]
    have negative : orientationScale (D.roofPlacement K f).toAffineMap < 0 :=
      lt_of_le_of_ne (le_of_not_gt (fun h => first (signs.mpr h)))
        (D.roofPlacement_scale_ne_zero K f)
    exact neg_pos.mpr (mul_neg_of_neg_of_pos negative positive)

end Unfoldings.FacewiseDevelopment
