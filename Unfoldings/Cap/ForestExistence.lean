module

public import Unfoldings.Cap.ForestPaths
public import Unfoldings.Cap.AcuteProjection
public import Unfoldings.Cap.Roof
public import Unfoldings.Complex.SelectedCuts

/-!
# Uniform positive-tilt existence of an original-edge monotone forest

A positive acute margin gives uniform tilt and shear thresholds. All cap input
meshes within those thresholds have an actual boundary-rooted original-edge
forest, canonical acute-wedge paths to the rim, and an intrinsic cut disk.
Nonoverlap is a separate remaining assertion.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

/-- Both parameters are chosen before the cap; neither depends on its number of vertices. -/
theorem exists_tilt_monotoneForest {α : ℝ} (positive : 0 < α) (small : α < Real.pi / 2) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t > 0, ∀ K : ConvexCap C,
      AcuteMargin (C := C) α → K.TiltBound φ → Nonempty (K.MonotoneForest t) := by
  obtain ⟨φ, φbounds, project⟩ := exists_acute_projection_tilt (C := C) positive
  obtain ⟨t, tpos, shear⟩ := exists_shear_acute_triangles (half_pos positive)
    (by linarith [Real.pi_pos])
  exact ⟨φ, φbounds, t, tpos, fun K acute tilt =>
    ⟨K.monotoneForest t (fun f => shear (K.projectedTriangle f)
      (fun i => (project K acute tilt f i).le))⟩⟩

/-- A cap has a genuine triangle, so every feasible acute margin is strictly below pi/2. -/
theorem acuteMargin_lt_pi_div_two (K : ConvexCap C) {α : ℝ}
    (acute : AcuteMargin (C := C) α) : α < Real.pi / 2 := by
  obtain ⟨f⟩ := K.nonempty_face
  linarith [(C.triangle f).cornerAngle_pos 0, acute f 0]

/-- The useful statement needs only a positive acute margin; infeasible margins are vacuous. -/
theorem exists_tilt_monotoneForest_of_pos {α : ℝ} (positive : 0 < α) :
    ∃ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∃ t > 0, ∀ K : ConvexCap C,
      AcuteMargin (C := C) α → K.TiltBound φ → Nonempty (K.MonotoneForest t) := by
  by_cases small : α < Real.pi / 2
  · exact exists_tilt_monotoneForest positive small
  · refine ⟨Real.pi / 4, ⟨by positivity, by linarith [Real.pi_pos]⟩, 1, zero_lt_one, ?_⟩
    intro K acute _
    exact (small (acuteMargin_lt_pi_div_two K acute)).elim

namespace MonotoneForest

variable {K : ConvexCap C} {t : ℝ} (M : K.MonotoneForest t)

def retain : Set C.Seam := C.selectedRetain M.selection

theorem cut_rootedForest : (C.relativeCutGraph M.retain Set.univ).IsRootedForest
    (C.relativeCutRoots Set.univ) := C.selectedCut_rootedForest M.selection M.roots_eq

/-- The constructed original-edge cut forest yields the actual intrinsic cut disk. -/
def cutDisk : C.Realization M.retain ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  C.selectedCutDisk M.selection M.roots_eq K.folding K.diskHomeomorph

end MonotoneForest
end Unfoldings.ConvexCap
