module

public import Unfoldings.Convex.PhysicalNormalCells
public import Unfoldings.Convex.CoerciveEnvelope

/-! Construct conforming physical meshes of nonempty horizontal sections of a finite slope model. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SlopeEnvelope.FiniteSlopeModel

variable {E : SlopeEnvelope} (M : E.FiniteSlopeModel)

theorem clip_eq_sublevel (Z : ℝ) :
    SpatialEnvelope.clip M.plane Z = {x | E.height x ≤ -Z} := by
  ext x
  change Z ≤ SpatialEnvelope.height M.plane x ↔ E.height x ≤ -Z
  rw [M.height_eq]
  constructor <;> intro h <;> linarith

theorem compact_clip {a : ℝ} (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes) (Z : ℝ) :
    IsCompact (SpatialEnvelope.clip M.plane Z) := by
  rw [M.clip_eq_sublevel]
  exact E.compact_sublevel positive inner_disk (-Z)

/-- Prescribed finite lines can include original edges and the already constructed cuts.
The construction refines the arrangement partition into a genuinely conforming physical mesh. -/
def mesh {J : Type} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ) (proper : ∀ j, extra j ≠ 0)
    {a : ℝ} (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes)
    {Z : ℝ} {q : Plane} (higher : Z < -E.height q) :
    SpatialEnvelope.ConstrainedTriangulation M.plane extra Z :=
  (SpatialEnvelope.constrainedTriangulation M.plane extra proper (q := q)
    (M.compact_clip positive inner_disk Z) (by rw [M.height_eq]; exact higher)).refined

theorem mesh_conforming {J : Type} [Finite J] (extra : J → Plane →ᵃ[ℝ] ℝ)
    (proper : ∀ j, extra j ≠ 0) {a : ℝ} (positive : 0 < a)
    (inner_disk : Metric.ball (0 : Plane) a ⊆ E.slopes) {Z : ℝ} {q : Plane}
    (higher : Z < -E.height q) :
    TriangleFamily.Conforming (M.mesh extra proper positive inner_disk higher).projectedTriangle :=
  SpatialEnvelope.ConstrainedTriangulation.refined_conforming
    (SpatialEnvelope.constrainedTriangulation M.plane extra proper (q := q)
      (M.compact_clip positive inner_disk Z) (by rw [M.height_eq]; exact higher))

end Unfoldings.SlopeEnvelope.FiniteSlopeModel
