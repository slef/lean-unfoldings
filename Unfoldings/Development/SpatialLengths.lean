module

public import Unfoldings.Development.GermRays
public import Unfoldings.Polyhedron.GermDirections

/-! Actual developed bank lengths match the original spatial edges, across distinct cut copies. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (F : SpatialFolding C)

theorem germRay_norm_eq_spatial {v : C.Vertex retain} (p : C.LinkGerm retain v) :
    ‖D.germRay p‖ = ‖F.germDirection p.val‖ := by
  rw [germRay, ← D.linkGerm_apex p]
  change ‖D.place p.val.1.1 ((C.triangle p.val.1.1).vertex (C.germFarCorner p.val).2) -
    D.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2)‖ =
      ‖F.place p.val.1.1 ((C.triangle p.val.1.1).vertex (C.germFarCorner p.val).2) -
        F.place p.val.1.1 ((C.triangle p.val.1.1).vertex p.val.1.2)‖
  rw [← dist_eq_norm, ← dist_eq_norm, (D.place p.val.1.1).isometry.dist_eq,
    (F.place p.val.1.1).isometry.dist_eq]

include F in
theorem germRay_norm_eq_of_original_mates {v w : C.Vertex retain}
    (p : C.LinkGerm retain v) (q : C.LinkGerm retain w)
    (mates : q.val = C.mateGerm Set.univ p.val) : ‖D.germRay p‖ = ‖D.germRay q‖ := by
  rw [D.germRay_norm_eq_spatial F, D.germRay_norm_eq_spatial F, mates, F.germDirection_mate]

end Unfoldings.FacewiseDevelopment
