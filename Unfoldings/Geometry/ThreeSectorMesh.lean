module

public import Unfoldings.Geometry.ThreeSectorAcute
public import Unfoldings.Geometry.MeshLinearProgress

/-! Original mesh edges enter each of the three acute source-centered sectors. -/

@[expose] public section

noncomputable section

namespace Unfoldings

theorem threeSectorCoordinates_injective {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    (i : Fin 3) : Function.Injective (threeSectorCoordinates t i) := by
  intro u v equal
  have first := threeSector_reconstruct t i u
  rw [equal] at first
  have scaled := first.trans (threeSector_reconstruct t i v).symm
  have recovered := congrArg (fun z : Plane => (threeSectorDet t i)⁻¹ • z) scaled
  simpa only [smul_smul, inv_mul_cancel₀ (threeSectorDet_pos nonnegative small i).ne', one_smul]
    using recovered

theorem threeSectorCoordinates_affine_injective {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    (i : Fin 3) : Function.Injective (threeSectorCoordinates t i).toAffineMap :=
  threeSectorCoordinates_injective nonnegative small i

def threeSectorEquiv {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1) (i : Fin 3) :
    Plane ≃ₗ[ℝ] Plane :=
  LinearEquiv.ofBijective (threeSectorCoordinates t i)
    ⟨threeSectorCoordinates_injective nonnegative small i,
      LinearMap.surjective_of_injective (threeSectorCoordinates_injective nonnegative small i)⟩

/-- All three transformed mesh families are acute with a single positive numerical parameter. -/
theorem exists_threeSector_acute_triangles {α : ℝ} (positive : 0 < α) (small : α < Real.pi / 2) :
    ∃ (t : ℝ) (bounds : t ∈ Set.Ioo (0 : ℝ) (1 / 4)), ∀ (i : Fin 3) (T : Triangle),
      (∀ j, T.cornerAngle j ≤ Real.pi / 2 - α) →
        ∀ j, (T.affineImage (threeSectorCoordinates t i).toAffineMap
          (threeSectorCoordinates_affine_injective bounds.1.le
            (bounds.2.trans (by norm_num : (1 : ℝ) / 4 < 1)) i)).cornerAngle j <
            Real.pi / 2 := by
  obtain ⟨t, bounds, estimate⟩ := exists_acute_threeSectorCoordinates positive small
  refine ⟨t, bounds, fun i T acute j => ?_⟩
  have first : T.vertex (Triangle.next j) - T.vertex j ≠ 0 :=
    sub_ne_zero.mpr (T.affineIndependent_vertices.injective.ne (by fin_cases j <;> decide))
  have last : T.vertex (Triangle.next (Triangle.next j)) - T.vertex j ≠ 0 :=
    sub_ne_zero.mpr (T.affineIndependent_vertices.injective.ne (by fin_cases j <;> decide))
  have bound := estimate i _ _ first last (acute j)
  apply lt_of_not_ge
  intro wide
  have nonpositive := InnerProductGeometry.inner_nonpos_iff_pi_div_two_le_angle.mpr wide
  change inner ℝ (threeSectorCoordinates t i (T.vertex (Triangle.next j)) -
      threeSectorCoordinates t i (T.vertex j))
    (threeSectorCoordinates t i (T.vertex (Triangle.next (Triangle.next j))) -
      threeSectorCoordinates t i (T.vertex j)) ≤ 0 at nonpositive
  rw [← map_sub, ← map_sub] at nonpositive
  exact (not_lt_of_ge nonpositive) bound

/-- A prescribed sector supplies an actual incident original edge at every internal mesh vertex. -/
theorem exists_mesh_threeSector_edge {Face : Type*} [Finite Face]
    (triangle : Face → Triangle) {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    (i : Fin 3) (region : Set Plane) (cover : region ⊆ ⋃ f, (triangle f).carrier) (center : Plane)
    (inside : center ∈ interior region)
    (corner : ∀ f, center ∈ (triangle f).carrier → ∃ j, (triangle f).vertex j = center)
    (acute : ∀ f j, ((triangle f).affineImage (threeSectorCoordinates t i).toAffineMap
      (threeSectorCoordinates_affine_injective nonnegative small i)).cornerAngle j <
          Real.pi / 2) :
    ∃ f j, (triangle f).vertex j = center ∧
      (((triangle f).vertex (Triangle.next j) - center) ∈ strictThreeSector t i ∨
        ((triangle f).vertex (Triangle.next (Triangle.next j)) - center) ∈
          strictThreeSector t i) := by
  exact exists_mesh_linear_quadrant_edge triangle (threeSectorEquiv nonnegative small i)
    region cover center inside corner acute

end Unfoldings
