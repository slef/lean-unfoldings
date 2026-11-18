module

public import Unfoldings.Roof.NestedFaceAngles
public import Unfoldings.Complex.SubdivisionCornerAngles

/-! Nested physical subdivisions preserve the full sum of fine angles over every old corner. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

universe u

variable {I : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {Z W : ℝ} (T : Triangulation family Z) (U : Triangulation family W)

local instance nestedAnglesOldFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite
local instance nestedAnglesNewFintype : Fintype U.Index := @Fintype.ofFinite _ U.finite

open Classical in
/-- Fine corners in one face patch are precisely the corners with that original parent. -/
def nestedFaceCornerEquiv (f : T.Index) : (T.nestedFaceComplex U f).Corner ≃
    {d : (T.nestedComplex U).Corner // T.nestedParent U d.1 = f} where
  toFun c := ⟨(⟨c.1.val, f, c.1.property⟩, c.2), T.nestedParent_eq U _ c.1.property⟩
  invFun d := (⟨d.val.1.val, by
    have contained := T.nestedParent_contains U d.val.1
    rwa [d.property] at contained⟩, d.val.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable (conforming : TriangleFamily.Conforming U.projectedTriangle)
  (inside : (interior (clip family W)).Nonempty) (cover : T.FaceRefinement U)

include conforming inside in
open Classical in
/-- Every old Euclidean corner has exactly its original angle in the new physical subdivision. -/
theorem nestedSubdivision_cornerAnglePreserving :
    (T.nestedSubdivision U cover).CornerAnglePreserving := by
  classical
  rintro ⟨f, k⟩
  let weight (d : (T.nestedComplex U).Corner) : ℝ :=
    if (T.nestedSubdivision U cover).place d.1 (((T.nestedComplex U).triangle d.1).vertex d.2) =
        (T.triangle f).vertex k then ((T.nestedComplex U).triangle d.1).cornerAngle d.2 else 0
  calc
    _ = ∑ d : (T.nestedComplex U).Corner, if T.nestedParent U d.1 = f then weight d else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases parent : T.nestedParent U d.1 = f <;>
        simp [TriangleComplex.Subdivision.RefinesCorner, nestedSubdivision, weight, parent,
          pairedComplex]
    _ = ∑ d : {d : (T.nestedComplex U).Corner // T.nestedParent U d.1 = f}, weight d.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) weight
    _ = ∑ c : (T.nestedFaceComplex U f).Corner, weight (T.nestedFaceCornerEquiv U f c).val :=
      (Equiv.sum_comp (T.nestedFaceCornerEquiv U f) (fun d => weight d.val)).symm
    _ = (T.triangle f).cornerAngle k := by
      convert T.nestedFace_sum_cornerAngles U conforming inside cover f k using 1
      apply Finset.sum_congr rfl
      intro c _
      have parent := T.nestedParent_eq U (⟨c.1.val, f, c.1.property⟩ : T.nestedPieceSet U)
        c.1.property
      change (if T.nestedCoordinates U c.1.val
          (T.nestedParent U ⟨c.1.val, f, c.1.property⟩)
          ((U.triangle c.1.val).vertex c.2) = (T.triangle f).vertex k
        then (U.triangle c.1.val).cornerAngle c.2 else 0) =
        (if T.nestedCoordinates U c.1.val f ((U.triangle c.1.val).vertex c.2) =
          (T.triangle f).vertex k then (U.triangle c.1.val).cornerAngle c.2 else 0)
      rw [parent]

end Unfoldings.SpatialEnvelope.Triangulation
