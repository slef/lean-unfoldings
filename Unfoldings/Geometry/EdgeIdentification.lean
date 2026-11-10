module

public import Unfoldings.Geometry.Affine
public import Unfoldings.Geometry.Endpoints

/-! Construct full-edge identifications from equal lengths and endpoint labels. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

variable (T U : Triangle) (e f : Fin 3) (reverse : Bool)
  (length : dist (T.vertex e) (T.vertex (next e)) =
    dist (U.endpoint f reverse).val (U.endpoint f (!reverse)).val)

def edgeMotion : Plane ≃ᵃⁱ[ℝ] Plane :=
  twoPointIsometry (T.vertex e) (T.vertex (next e))
    (U.endpoint f reverse).val (U.endpoint f (!reverse)).val

theorem edgeMotion_first : edgeMotion T U e f reverse (T.vertex e) =
    (U.endpoint f reverse).val := twoPointIsometry_left _ _ _ _

include length in
theorem edgeMotion_last : edgeMotion T U e f reverse (T.vertex (next e)) =
    (U.endpoint f (!reverse)).val := twoPointIsometry_right _ _ _ _ length

include length in
theorem edgeMotion_image : edgeMotion T U e f reverse '' T.edge e = U.edge f := by
  change (edgeMotion T U e f reverse).toAffineEquiv.toAffineMap ''
    segment ℝ (T.vertex e) (T.vertex (next e)) = _
  rw [image_segment]
  change segment ℝ (edgeMotion T U e f reverse (T.vertex e))
    (edgeMotion T U e f reverse (T.vertex (next e))) = _
  rw [edgeMotion_first, edgeMotion_last T U e f reverse length]
  cases reverse
  · rfl
  · exact segment_symm ℝ _ _

def edgeIdentification : T.Edge e ≃ᵢ U.Edge f where
  toEquiv :=
    { toFun x := ⟨edgeMotion T U e f reverse x.val, by
        rw [← edgeMotion_image T U e f reverse length]
        exact ⟨x.val, x.property, rfl⟩⟩
      invFun y := ⟨(edgeMotion T U e f reverse).symm y.val, by
        have image : y.val ∈ edgeMotion T U e f reverse '' T.edge e :=
          (edgeMotion_image T U e f reverse length).symm.subset y.property
        obtain ⟨x, hx, equal⟩ := image
        rw [← equal, (edgeMotion T U e f reverse).symm_apply_apply]
        exact hx⟩
      left_inv x := Subtype.ext ((edgeMotion T U e f reverse).symm_apply_apply x.val)
      right_inv y := Subtype.ext ((edgeMotion T U e f reverse).apply_symm_apply y.val) }
  isometry_toFun := (edgeMotion T U e f reverse).isometry.comp isometry_subtype_coe

@[simp] theorem edgeIdentification_first :
    (edgeIdentification T U e f reverse length (T.endpoint e false)).val =
      (U.endpoint f reverse).val := edgeMotion_first T U e f reverse

@[simp] theorem edgeIdentification_last :
    (edgeIdentification T U e f reverse length (T.endpoint e true)).val =
      (U.endpoint f (!reverse)).val := edgeMotion_last T U e f reverse length

end Unfoldings.Triangle
