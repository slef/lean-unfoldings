module

public import Unfoldings.Geometry.CornerFrame
public import Unfoldings.Geometry.CornerSpan
public import Unfoldings.Cone.SectorCoordinates

/-!
# Actual triangle wedges in angular coordinates

The normalized rigid frame has second-ray argument equal to the triangle's
actual Euclidean corner angle. Its affine image of the supporting wedge is
exactly the positive-span sector at that angle.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle.CornerFrame

variable {T : Triangle} {i : Fin 3} (frame : T.CornerFrame i)

theorem second_ne_zero : frame.place (T.vertex (Triangle.next (Triangle.next i))) ≠ 0 := by
  intro zero
  have positive := frame.upper
  rw [zero, Complex.zero_im] at positive
  exact lt_irrefl 0 positive

theorem arg_second :
    (frame.place (T.vertex (Triangle.next (Triangle.next i)))).arg = T.cornerAngle i := by
  have mapped := frame.place.toAffineIsometry.angle_map
    (T.vertex (Triangle.next i)) (T.vertex i) (T.vertex (Triangle.next (Triangle.next i)))
  change EuclideanGeometry.angle (frame.place (T.vertex (Triangle.next i)))
    (frame.place (T.vertex i)) (frame.place (T.vertex (Triangle.next (Triangle.next i)))) =
      T.cornerAngle i at mapped
  rw [frame.first, frame.apex] at mapped
  change InnerProductGeometry.angle
    ((dist (T.vertex i) (T.vertex (Triangle.next i)) : ℂ) - 0)
    (frame.place (T.vertex (Triangle.next (Triangle.next i))) - 0) = T.cornerAngle i at mapped
  simp only [sub_zero] at mapped
  have length_positive : 0 < dist (T.vertex i) (T.vertex (Triangle.next i)) :=
    dist_pos.mpr (T.edge_endpoints_ne i)
  have real_vector : (dist (T.vertex i) (T.vertex (Triangle.next i)) : ℂ) =
      dist (T.vertex i) (T.vertex (Triangle.next i)) • (1 : ℂ) := by
    simp [Complex.real_smul]
  rw [real_vector, InnerProductGeometry.angle_smul_left_of_pos _ _ length_positive,
    Complex.angle_one_left frame.second_ne_zero,
    abs_of_nonneg (Complex.arg_nonneg_iff.mpr frame.upper.le)] at mapped
  exact mapped

theorem norm_second :
    ‖frame.place (T.vertex (Triangle.next (Triangle.next i)))‖ =
      dist (T.vertex i) (T.vertex (Triangle.next (Triangle.next i))) := by
  calc
    _ = dist (frame.place (T.vertex i))
        (frame.place (T.vertex (Triangle.next (Triangle.next i)))) := by
      rw [frame.apex, dist_zero_left]
    _ = _ := frame.place.isometry.dist_eq _ _

theorem second_polar :
    frame.place (T.vertex (Triangle.next (Triangle.next i))) =
      (dist (T.vertex i) (T.vertex (Triangle.next (Triangle.next i))) : ℂ) *
        polarRay (T.cornerAngle i) := by
  have identity := (Complex.norm_mul_exp_arg_mul_I
    (frame.place (T.vertex (Triangle.next (Triangle.next i))))).symm
  change frame.place (T.vertex (Triangle.next (Triangle.next i))) =
    (‖frame.place (T.vertex (Triangle.next (Triangle.next i)))‖ : ℂ) *
      polarRay (frame.place (T.vertex (Triangle.next (Triangle.next i)))).arg at identity
  rwa [frame.arg_second, frame.norm_second] at identity

theorem map_cornerCombination (a b : ℝ) :
    frame.place (T.cornerCombination i a b) =
      a • frame.place (T.vertex (Triangle.next i)) +
        b • frame.place (T.vertex (Triangle.next (Triangle.next i))) := by
  change frame.place ((a • (T.vertex (Triangle.next i) -ᵥ T.vertex i) +
    b • (T.vertex (Triangle.next (Triangle.next i)) -ᵥ T.vertex i)) +ᵥ T.vertex i) = _
  rw [frame.place.map_vadd, map_add, map_smul, map_smul,
    frame.place.map_vsub, frame.place.map_vsub]
  simp only [frame.apex, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero]

theorem map_cornerCombination_polar (a b : ℝ) :
    frame.place (T.cornerCombination i a b) =
      ((a * dist (T.vertex i) (T.vertex (Triangle.next i)) : ℝ) : ℂ) +
        (b * dist (T.vertex i) (T.vertex (Triangle.next (Triangle.next i)))) •
          polarRay (T.cornerAngle i) := by
  rw [frame.map_cornerCombination, frame.first, frame.second_polar]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The normalized rigid image is the whole angular sector, including both banks. -/
theorem image_cornerWedge : frame.place '' T.cornerWedge i = planarSector (T.cornerAngle i) := by
  let left := dist (T.vertex i) (T.vertex (Triangle.next i))
  let right := dist (T.vertex i) (T.vertex (Triangle.next (Triangle.next i)))
  have left_pos : 0 < left := dist_pos.mpr (T.edge_endpoints_ne i)
  have right_ne : T.vertex i ≠ T.vertex (Triangle.next (Triangle.next i)) := by
    intro equal
    apply T.edge_endpoints_ne (Triangle.next (Triangle.next i))
    simpa only [Triangle.next_next_next] using equal.symm
  have right_pos : 0 < right := dist_pos.mpr right_ne
  ext z
  constructor
  · rintro ⟨x, inside, rfl⟩
    obtain ⟨a, ha, b, hb, equal⟩ := (T.mem_cornerWedge_iff_cornerCombination i x).mp inside
    rw [← equal, frame.map_cornerCombination_polar]
    exact ⟨a * left, mul_nonneg ha left_pos.le, b * right, mul_nonneg hb right_pos.le, rfl⟩
  · rintro ⟨c, hc, d, hd, equal⟩
    refine ⟨T.cornerCombination i (c / left) (d / right), ?_, ?_⟩
    · exact (T.mem_cornerWedge_iff_cornerCombination i _).mpr
        ⟨c / left, div_nonneg hc left_pos.le, d / right, div_nonneg hd right_pos.le, rfl⟩
    · rw [frame.map_cornerCombination_polar]
      change ((c / left * left : ℝ) : ℂ) + (d / right * right) • polarRay (T.cornerAngle i) = z
      rw [div_mul_cancel₀ _ left_pos.ne', div_mul_cancel₀ _ right_pos.ne']
      exact equal.symm

/-- Every actual triangle wedge is isometric to the sector of its actual corner angle. -/
def sectorIsometry : T.cornerWedge i ≃ᵢ planarSector (T.cornerAngle i) where
  toEquiv := (frame.place.toAffineEquiv.toEquiv.image (T.cornerWedge i)).trans
    (Set.equivOfEq frame.image_cornerWedge)
  isometry_toFun := by
    intro x y
    change edist (frame.place x.val) (frame.place y.val) = edist x.val y.val
    exact frame.place.isometry.edist_eq x.val y.val

@[simp] theorem sectorIsometry_apply (x : T.cornerWedge i) :
    (frame.sectorIsometry x).val = frame.place x.val := rfl

end Unfoldings.Triangle.CornerFrame
