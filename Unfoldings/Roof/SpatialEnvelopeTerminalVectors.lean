module

public import Unfoldings.Roof.SpatialEnvelopeFoldingGraph
public import Unfoldings.Convex.ExteriorSpatialRays
public import Unfoldings.Polyhedron.BankLengths

/-! Directed terminal-bank endpoints determine the full spatial edge vector and length. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.Triangulation

variable {G : SlopeEnvelope} {V : Type*} (R : G.ExteriorPlan V) (M : G.FiniteSlopeModel)
  {Z : ℝ} (T : Triangulation M.plane Z)

local instance terminalVectorsIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

variable {retain : Set T.pairedComplex.Seam}

/-- A directed bank on an original terminal ray has its exact full spatial velocity. -/
theorem germDirection_eq_terminal_spatialDirection (v : V)
    (p : T.pairedComplex.BoundaryEnd retain) {s t : ℝ} (first_nonnegative : 0 ≤ s)
    (last_nonnegative : 0 ≤ t)
    (first : Cap.horizontal (T.pairedFolding.boundaryPosition p) = R.ray v s)
    (last : Cap.horizontal (T.pairedFolding.boundaryPosition
      (T.pairedComplex.boundaryTurn retain p)) = R.ray v t) :
    T.pairedFolding.germDirection p.val = (t - s) • R.spatialDirection v := by
  have first_spatial : T.pairedFolding.boundaryPosition p = point M.plane (R.ray v s) :=
    (T.toSpace_eq_point retain _).trans (congrArg (point M.plane) first)
  have last_spatial : T.pairedFolding.boundaryPosition (T.pairedComplex.boundaryTurn retain p) =
      point M.plane (R.ray v t) :=
    (T.toSpace_eq_point retain _).trans (congrArg (point M.plane) last)
  rw [T.pairedFolding.germDirection_boundary_positions, first_spatial, last_spatial]
  exact R.spatial_ray_sub M v last_nonnegative first_nonnegative

/-- Original terminal time and full spatial speed measure the actual intrinsic fine edge. -/
theorem boundaryBankLength_eq_terminal_time (v : V)
    (p : T.pairedComplex.BoundaryEnd retain) {s t : ℝ} (nonnegative : 0 ≤ s) (forward : s ≤ t)
    (first : Cap.horizontal (T.pairedFolding.boundaryPosition p) = R.ray v s)
    (last : Cap.horizontal (T.pairedFolding.boundaryPosition
      (T.pairedComplex.boundaryTurn retain p)) = R.ray v t) :
    T.pairedComplex.boundaryBankLength p = (t - s) * ‖R.spatialDirection v‖ := by
  rw [T.pairedFolding.boundaryBankLength_eq_germDirection_norm,
    T.germDirection_eq_terminal_spatialDirection R M v p nonnegative (nonnegative.trans forward)
      first last, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr forward)]

end Unfoldings.SpatialEnvelope.Triangulation
