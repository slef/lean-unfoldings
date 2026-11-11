module

public import Unfoldings.Cap.ClipSupportPolygons

/-!
# Actual distinct support polygons have disjoint interiors

Coplanar original triangles may have identical support maps. Indexing by the
actual finite set of support maps removes exactly those duplicates. Two
different remaining planes cannot share an open active region.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

theorem roofCell_interiors_disjoint {f g : Face}
    (different : K.supportHeight f ≠ K.supportHeight g) :
    Disjoint (interior (K.roofCell f)) (interior (K.roofCell g)) := by
  apply Set.disjoint_left.mpr
  intro x first last
  apply different
  have open_set : IsOpen (interior (K.roofCell f) ∩ interior (K.roofCell g)) :=
    isOpen_interior.inter isOpen_interior
  apply AffineMap.ext_on (open_set.affineSpan_eq_top ⟨x, first, last⟩)
  intro p member
  exact le_antisymm ((interior_subset member.1) g) ((interior_subset member.2) f)

abbrev SupportPlane := Set.range K.supportHeight

instance finite_supportPlane : Finite K.SupportPlane :=
  Set.finite_range K.supportHeight |>.to_subtype

def supportFace (plane : K.SupportPlane) : Face := plane.property.choose

theorem supportFace_eq (plane : K.SupportPlane) :
    K.supportHeight (K.supportFace plane) = plane.val :=
  plane.property.choose_spec

theorem supportFace_injective : Function.Injective K.supportFace := by
  intro a b equal
  apply Subtype.ext
  rw [← K.supportFace_eq a, ← K.supportFace_eq b, equal]

/-- The duplicate-free actual support polygons have pairwise disjoint interiors. -/
theorem distinct_clippedSupportCell_interiors_disjoint (Z : ℝ) :
    Pairwise (fun a b : K.SupportPlane =>
      Disjoint (interior (K.clippedSupportCell Z (K.supportFace a)))
        (interior (K.clippedSupportCell Z (K.supportFace b)))) := by
  intro a b different
  have planes : K.supportHeight (K.supportFace a) ≠ K.supportHeight (K.supportFace b) := by
    rw [K.supportFace_eq, K.supportFace_eq]
    exact fun same => different (Subtype.ext same)
  exact (K.roofCell_interiors_disjoint planes).mono
    (interior_mono (Set.inter_subset_right : K.clippedSupportCell Z (K.supportFace a) ⊆ _))
    (interior_mono (Set.inter_subset_right : K.clippedSupportCell Z (K.supportFace b) ⊆ _))

/-- The duplicate-free support polygons still cover the entire actual clipped footprint. -/
theorem clippedSupportCells_cover (Z : ℝ) :
    K.clipFootprint Z = ⋃ a : K.SupportPlane, K.clippedSupportCell Z (K.supportFace a) := by
  ext p
  constructor
  · intro member
    obtain ⟨f, active⟩ := K.roofCells_cover p
    let a : K.SupportPlane := ⟨K.supportHeight f, f, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨a, member, ?_⟩
    rw [K.mem_roofCell_iff, K.supportFace_eq]
    exact (K.mem_roofCell_iff f p).mp active
  · intro member
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp member
    exact member.1

end Unfoldings.ConvexCap
