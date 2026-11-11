module

public import Unfoldings.Cap.RoofClips
public import Unfoldings.Geometry.CompactCollinear
public import Unfoldings.Geometry.SegmentVertices

/-!
# The actual clipped roof has a finite polygonal rim

Each original support plane cuts the horizontal clipping plane in a line.
Its intersection with the compact convex clip is a segment. These finitely
many actual segments cover exactly the clipped footprint's frontier.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

/-- A positive-height reference point rules out a plateau on the clipping level. -/
theorem mem_clip_frontier_iff {q : Plane} {Z : ℝ} (higher : Z < K.roofHeight q) (p : Plane) :
    p ∈ frontier (K.clipFootprint Z) ↔ K.roofHeight p = Z := by
  constructor
  · exact K.roofHeight_eq_level_of_clip_frontier
  · intro level
    refine ⟨subset_closure (show p ∈ K.clipFootprint Z from level.ge), ?_⟩
    intro interior_point
    obtain ⟨a, beyond, inside⟩ := exists_lineMap_beyond_one_mem (q := q) interior_point
    obtain ⟨f, active⟩ := K.exists_roofHeight_eq_supportHeight p
    have at_p : K.supportHeight f p = Z := active.symm.trans level
    have at_q : Z < K.supportHeight f q := higher.trans_le (K.roofHeight_le_supportHeight q f)
    have lower : Z ≤ K.supportHeight f (AffineMap.lineMap q p a) :=
      inside.trans (K.roofHeight_le_supportHeight _ f)
    rw [(K.supportHeight f).apply_lineMap, AffineMap.lineMap_apply_ring, at_p] at lower
    have product := mul_pos (sub_pos.mpr beyond) (sub_pos.mpr at_q)
    nlinarith

def clipRimCell (Z : ℝ) (f : Face) : Set Plane :=
  K.clipFootprint Z ∩ {p | K.supportHeight f p = Z}

theorem clipRimCell_subset_frontier {q : Plane} {Z : ℝ} (higher : Z < K.roofHeight q)
    (f : Face) : K.clipRimCell Z f ⊆ frontier (K.clipFootprint Z) := by
  intro p member
  apply (K.mem_clip_frontier_iff higher p).mpr
  exact le_antisymm ((K.roofHeight_le_supportHeight p f).trans_eq member.2) member.1

theorem clip_frontier_covered (Z : ℝ) :
    frontier (K.clipFootprint Z) ⊆ ⋃ f, K.clipRimCell Z f := by
  intro p boundary
  have level := K.roofHeight_eq_level_of_clip_frontier boundary
  obtain ⟨f, active⟩ := K.exists_roofHeight_eq_supportHeight p
  exact Set.mem_iUnion.mpr ⟨f, ⟨level.ge, active.symm.trans level⟩⟩

/-- Every nonempty support-plane rim cell is one actual closed segment, including degeneracies. -/
theorem clipRimCell_eq_segment {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z < 0)
    (f : Face) (nonempty : (K.clipRimCell Z f).Nonempty) :
    ∃ a ∈ K.clipRimCell Z f, ∃ b ∈ K.clipRimCell Z f,
      K.clipRimCell Z f = segment ℝ a b := by
  have compact : IsCompact (K.clipRimCell Z f) :=
    (K.isCompact_clipFootprint member positive lower.le).inter_right
    (isClosed_eq (K.supportHeight f).continuous_of_finiteDimensional continuous_const)
  have convex : Convex ℝ (K.clipRimCell Z f) :=
    (K.convex_clipFootprint Z).inter
      ((convex_singleton Z).affine_preimage (K.supportHeight f))
  let equation := K.supportHeight f - AffineMap.const ℝ Plane Z
  have nonzero : equation ≠ 0 := by
    intro zero
    have at_q := congrArg (fun A : Plane →ᵃ[ℝ] ℝ => A q) zero
    change K.supportHeight f q - Z = 0 at at_q
    linarith [K.roofHeight_le_supportHeight q f]
  have collinear : Collinear ℝ (K.clipRimCell Z f) :=
    collinear_of_affine_zero equation nonzero (fun _ h => sub_eq_zero.mpr h.2)
  exact exists_segment_of_compact_convex_collinear compact convex nonempty collinear

/-- Construct the entire exact finite segment rim from the original supporting planes. -/
theorem exists_finite_clip_boundary_segments {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z < 0) :
    ∃ edges : Set (Plane × Plane), edges.Finite ∧
      frontier (K.clipFootprint Z) = segmentCarrier edges := by
  classical
  let Active := {f : Face // (K.clipRimCell Z f).Nonempty}
  have segments (f : Active) := K.clipRimCell_eq_segment member positive lower f.val f.property
  choose first first_mem last last_mem equal using segments
  let edges := Set.range (fun f : Active => (first f, last f))
  refine ⟨edges, Set.finite_range _, ?_⟩
  ext p
  constructor
  · intro boundary
    obtain ⟨f, in_cell⟩ := Set.mem_iUnion.mp (K.clip_frontier_covered Z boundary)
    let active : Active := ⟨f, ⟨p, in_cell⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨(first active, last active), ⟨active, rfl⟩,
      (Set.ext_iff.mp (equal active) p).mp in_cell⟩
  · intro in_edge
    obtain ⟨edge, ⟨f, rfl⟩, in_segment⟩ := Set.mem_iUnion₂.mp in_edge
    exact K.clipRimCell_subset_frontier (lower.trans positive) f.val
      ((Set.ext_iff.mp (equal f) p).mpr in_segment)

end Unfoldings.ConvexCap
