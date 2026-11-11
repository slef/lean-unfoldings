module

public import Unfoldings.Geometry.AffineArrangement
public import Unfoldings.Geometry.EdgeSides
public import Unfoldings.Geometry.Affine

/-! Generic lines from a fixed nonexceptional origin avoid any finite prescribed set of points. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A genuine line has a nonzero affine signed-area equation. -/
theorem orientMap_ne_zero {a b : Plane} (different : a ≠ b) : orientMap a b ≠ 0 := by
  intro zero
  have first := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f (a + WithLp.toLp 2 ![0, 1])) zero
  have last := congrArg (fun f : Plane →ᵃ[ℝ] ℝ => f (a + WithLp.toLp 2 ![1, 0])) zero
  norm_num [orientMap_apply, orient, PiLp.add_apply] at first last
  apply different
  ext i
  fin_cases i
  · change a 0 = b 0
    exact (sub_eq_zero.mp first).symm
  · change a 1 = b 1
    exact sub_eq_zero.mp last

/-- A nonzero signed area excludes the point from the whole line, including both extended rays. -/
theorem lineMap_ne_of_orient_ne_zero {a b q : Plane} (regular : orient a b q ≠ 0) (t : ℝ) :
    AffineMap.lineMap a q t ≠ b := by
  intro equal
  have zero := orient_lineMap a q t
  rw [equal] at zero
  apply regular
  have reverse : orient a b q = -orient a q b := by unfold orient; ring
  rw [reverse, zero, neg_zero]

/-- Avoid all exceptional lines while keeping the endpoint in a prescribed nonempty open set. -/
theorem exists_open_endpoint_line_avoids {ι : Type*} [Finite ι]
    (a : Plane) (point : ι → Plane) (different : ∀ i, a ≠ point i)
    {U : Set Plane} (open_U : IsOpen U) (nonempty : U.Nonempty) :
    ∃ q ∈ U, ∀ i, orient a (point i) q ≠ 0 := by
  let equation (i : ι) := orientMap a (point i)
  have dense := AffineArrangement.dense_regular equation (fun i => orientMap_ne_zero (different i))
  obtain ⟨q, regular, inside⟩ := dense.exists_mem_open open_U nonempty
  refine ⟨q, inside, fun i => ?_⟩
  simpa only [equation, orientMap_apply] using regular i

end Unfoldings
