module

public import Unfoldings.Cap.ClipBoundary
public import Unfoldings.Cap.RoofFlat

/-! The actual horizontally clipped roof is a compact topological disk with polygonal rim. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem clip_interior_nonempty {Z : ℝ} (lower : Z < 0) :
    (interior (K.clipFootprint Z)).Nonempty := by
  obtain ⟨p, member⟩ := K.interior_projection
  exact ⟨p, K.original_footprint_in_clip_interior lower (interior_subset member)⟩

theorem roofPoint_mem_clippedRoof {Z : ℝ} {p : Plane} (member : p ∈ K.clipFootprint Z) :
    K.roofPoint p ∈ K.clippedRoof Z := ⟨p, member, rfl⟩

theorem horizontal_mem_clip_of_mem_clippedRoof {Z : ℝ} {z : Space}
    (member : z ∈ K.clippedRoof Z) : Cap.horizontal z ∈ K.clipFootprint Z := by
  obtain ⟨p, inside, same⟩ := member
  have projected : p = Cap.horizontal z := by
    simpa only [K.horizontal_roofPoint] using congrArg Cap.horizontal same
  exact projected ▸ inside

theorem clippedRoof_subset_extendedRoof (Z : ℝ) : K.clippedRoof Z ⊆ K.extendedRoof := by
  rintro z ⟨p, _member, same⟩
  exact same ▸ K.roofPoint_mem p

/-- Projection identifies the actual finite roof clip, without a triangulation premise. -/
def clipProjectionHomeomorph (Z : ℝ) : K.clipFootprint Z ≃ₜ K.clippedRoof Z where
  toFun p := ⟨K.roofPoint p.val, K.roofPoint_mem_clippedRoof p.property⟩
  invFun z := ⟨Cap.horizontal z.val, K.horizontal_mem_clip_of_mem_clippedRoof z.property⟩
  left_inv p := Subtype.ext (K.horizontal_roofPoint p.val)
  right_inv z := Subtype.ext (K.roofPoint_horizontal
    ⟨z.val, K.clippedRoof_subset_extendedRoof Z z.property⟩)
  continuous_toFun := (K.continuous_roofPoint.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Cap.horizontalCLM.continuous.comp continuous_subtype_val).subtype_mk _

def clippedFootprintDisk {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z < 0) :
    K.clipFootprint Z ≃ₜ Metric.closedBall (0 : Plane) 1 := Classical.choice (by
  obtain ⟨h, _interior, closed, _boundary⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall (K.convex_clipFootprint Z)
      (K.clip_interior_nonempty lower)
      (K.isCompact_clipFootprint member positive lower.le).isBounded
  rw [(K.isClosed_clipFootprint Z).closure_eq] at closed
  exact ⟨(h.image (K.clipFootprint Z)).trans (Homeomorph.setCongr closed)⟩)

/-- A disk homeomorphism for the actual spatial roof clip. -/
def clippedRoofDisk {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z < 0) :
    K.clippedRoof Z ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  (K.clipProjectionHomeomorph Z).symm.trans (K.clippedFootprintDisk member positive lower)

/-- A geometric cap has an injective flat development or compact polygonal clips. -/
theorem flat_unfolding_or_compact_polygonal_clips :
    (∃ D : FacewiseDevelopment C Set.univ, D.Nonoverlapping ∧ Function.Injective D.toPlane) ∨
    (∃ q ∈ K.footprint, 0 < K.roofHeight q ∧ ∀ Z : ℝ, Z < 0 →
      IsCompact (K.clippedRoof Z) ∧
        Nonempty (K.clippedRoof Z ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
        ∃ edges : Set (Plane × Plane), edges.Finite ∧
          frontier (K.clipFootprint Z) = segmentCarrier edges) := by
  rcases K.flat_or_positive_roof with flat | ⟨q, member, positive⟩
  · exact Or.inl ⟨K.flatDevelopment flat, K.flatDevelopment_nonoverlapping flat,
      K.flatDevelopment_injective flat⟩
  · refine Or.inr ⟨q, member, positive, fun Z lower => ?_⟩
    exact ⟨K.isCompact_clippedRoof member positive lower.le,
      ⟨K.clippedRoofDisk member positive lower⟩,
      K.exists_finite_clip_boundary_segments member positive lower⟩

end Unfoldings.ConvexCap
