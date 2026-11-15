module

public import Unfoldings.Geometry.LineCoordinate
public import Unfoldings.Geometry.RayAvoidance

/-! A positive ray has one open forward halfplane containing no omitted part of its line. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- The open forward halfplane beyond the base of a directed line. -/
def rayForwardHalfspace (a b : Plane) : Set Plane :=
  {x | 0 < lineCoordinate a b x}

theorem isOpen_rayForwardHalfspace (a b : Plane) : IsOpen (rayForwardHalfspace a b) :=
  isOpen_lt continuous_const (lineCoordinate a b).continuous_of_finiteDimensional

theorem lineMap_mem_rayForwardHalfspace {a b : Plane} (different : a ≠ b)
    {t : ℝ} (positive : 0 < t) : AffineMap.lineMap a b t ∈ rayForwardHalfspace a b := by
  change 0 < lineCoordinate a b (AffineMap.lineMap a b t)
  rwa [lineCoordinate_lineMap different]

/-- On the supporting line, this open halfplane consists exactly of positive ray points. -/
theorem exists_positive_ray_parameter {a b x : Plane} (different : a ≠ b)
    (forward : x ∈ rayForwardHalfspace a b) (zero : orientMap a b x = 0) :
    ∃ t : ℝ, 0 < t ∧ x = AffineMap.lineMap a b t := by
  obtain ⟨t, rfl⟩ := exists_lineMap_of_orient_eq_zero different (by
    simpa only [orientMap_apply] using zero)
  exact ⟨t, by simpa only [rayForwardHalfspace, Set.mem_ofPred_eq,
    lineCoordinate_lineMap different] using forward, rfl⟩

end Unfoldings
