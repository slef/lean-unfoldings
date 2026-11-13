module

public import Unfoldings.Geometry.AffineEnvelope
public import Unfoldings.Geometry.SupportedPlane

/-! Entire supported spatial roofs from finite families of actual Euclidean planes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope

variable {I : Type*} [Fintype I] [Nonempty I] (family : I → SpatialPlane)

/-- The actual height of the lower envelope of the supporting planes. -/
def height : Plane → ℝ := AffineEnvelope.height (fun i => (family i).height)

/-- A horizontal superlevel section of the supported roof. -/
def clip (Z : ℝ) : Set Plane := AffineEnvelope.clip (fun i => (family i).height) Z

/-- The actual spatial graph point of the envelope over a horizontal point. -/
def point (p : Plane) : Space := Cap.horizontalAtHeight p (height family p)

@[simp] theorem horizontal_point (p : Plane) : Cap.horizontal (point family p) = p :=
  Cap.horizontal_horizontalAtHeight _ _

@[simp] theorem height_point (p : Plane) : point family p 2 = height family p := rfl

theorem continuous_height : Continuous (height family) :=
  AffineEnvelope.continuous_height _

theorem continuous_point : Continuous (point family) := by
  change Continuous (fun p => WithLp.toLp 2 ![p 0, p 1, height family p])
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => by
    fin_cases i
    · exact (EuclideanSpace.proj 0).continuous
    · exact (EuclideanSpace.proj 1).continuous
    · exact continuous_height family))

/-- Every physical plane actually supports the entire completed graph. -/
theorem point_supporting (i : I) (p : Plane) :
    inner ℝ (family i).normal (point family p - (family i).place 0) ≤ 0 := by
  rw [(family i).supporting_iff, height_point, horizontal_point]
  exact AffineEnvelope.height_le _ p i

/-- An active support gives the exact original Euclidean placement of the graph point. -/
theorem point_eq_place (i : I) {p : Plane} (active : height family p = (family i).height p) :
    point family p = (family i).place ((family i).project.symm p) := by
  have horizontal : Cap.horizontal ((family i).place ((family i).project.symm p)) = p :=
    ((family i).horizontal_place _).trans ((family i).project.apply_symm_apply p)
  have vertical : (family i).place ((family i).project.symm p) 2 = height family p := by
    rw [(family i).height_place, (family i).project.apply_symm_apply]
    exact active.symm
  ext j
  fin_cases j
  · exact (congrArg (fun p : Plane => p 0) horizontal).symm
  · exact (congrArg (fun p : Plane => p 1) horizontal).symm
  · exact vertical.symm

/-- The actual spatial roof over a horizontal section. -/
def surface (Z : ℝ) : Set Space := point family '' clip family Z

/-- The whole spatial section is compact whenever its horizontal footprint is compact. -/
theorem isCompact_surface {Z : ℝ} (compact : IsCompact (clip family Z)) :
    IsCompact (surface family Z) := compact.image (continuous_point family)

end Unfoldings.SpatialEnvelope
