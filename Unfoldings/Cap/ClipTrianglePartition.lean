module

public import Unfoldings.Cap.DistinctSupportCells

/-!
# A finite triangle partition of the entire actual roof clip

Partition each distinct active support polygon and assemble the partitions.
Different supports have disjoint interiors, including when original faces
share the same plane. Every whole new triangle lies on its actual supporting
plane. Conforming edge pairings and preservation of original cut edges remain
separate obligations.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

structure SupportTrianglePartition (Z : ℝ) (f : Face) where
  Index : Type
  finite : Finite Index
  triangle : Index → Triangle
  cover : K.clippedSupportCell Z f = ⋃ i, (triangle i).carrier
  separated : Pairwise (fun i j =>
    Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier))

def supportTrianglePartition {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) (f : Face) :
    K.SupportTrianglePartition Z f := Classical.choice (by
  obtain ⟨I, finite, triangle, cover, separated⟩ :=
    K.exists_clippedSupportCell_triangle_partition member positive lower f
  exact ⟨⟨I, finite, triangle, cover, separated⟩⟩)

namespace SupportTrianglePartition

variable {K} {Z : ℝ} {f : Face} (P : K.SupportTrianglePartition Z f)

theorem triangle_subset (i : P.Index) : (P.triangle i).carrier ⊆ K.clippedSupportCell Z f := by
  rw [P.cover]
  exact Set.subset_iUnion (fun j => (P.triangle j).carrier) i

end SupportTrianglePartition

/-- Exact disjoint-interior coverage, with an actual support label for each whole triangle. -/
theorem exists_clip_triangle_partition {q : Plane} (member : q ∈ K.footprint)
    (positive : 0 < K.roofHeight q) {Z : ℝ} (lower : Z ≤ 0) :
    ∃ (I : Type) (_ : Finite I) (triangle : I → Triangle) (face : I → Face),
      K.clipFootprint Z = ⋃ i, (triangle i).carrier ∧
      Pairwise (fun i j =>
        Disjoint (interior (triangle i).carrier) (interior (triangle j).carrier)) ∧
      ∀ i, ∀ p ∈ (triangle i).carrier,
        K.roofHeight p = K.supportHeight (face i) p := by
  classical
  let part (a : K.SupportPlane) :=
    K.supportTrianglePartition member positive lower (K.supportFace a)
  let finite_part (a : K.SupportPlane) : Finite (part a).Index := (part a).finite
  let I := (a : K.SupportPlane) × (part a).Index
  let triangle (i : I) := (part i.1).triangle i.2
  let face (i : I) := K.supportFace i.1
  have contained (i : I) : (triangle i).carrier ⊆ K.clippedSupportCell Z (face i) :=
    (part i.1).triangle_subset i.2
  refine ⟨I, inferInstance, triangle, face, ?_, ?_, ?_⟩
  · ext p
    constructor
    · intro clip
      obtain ⟨a, in_cell⟩ := Set.mem_iUnion.mp ((K.clippedSupportCells_cover Z) ▸ clip)
      rw [(part a).cover] at in_cell
      obtain ⟨i, in_triangle⟩ := Set.mem_iUnion.mp in_cell
      exact Set.mem_iUnion.mpr ⟨⟨a, i⟩, in_triangle⟩
    · intro covered
      obtain ⟨i, member⟩ := Set.mem_iUnion.mp covered
      exact (contained i member).1
  · intro i j different
    by_cases same_plane : i.1 = j.1
    · obtain ⟨a, i⟩ := i
      obtain ⟨b, j⟩ := j
      change a = b at same_plane
      subst b
      exact (part a).separated (fun same => different (congrArg (Sigma.mk a) same))
    · exact (K.distinct_clippedSupportCell_interiors_disjoint Z same_plane).mono
        (interior_mono (contained i)) (interior_mono (contained j))
  · intro i p member
    exact (K.mem_roofCell_iff _ _).mp (contained i member).2

end Unfoldings.ConvexCap
