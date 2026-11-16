module

public import Unfoldings.Geometry.SpatialGraphRefinement
public import Unfoldings.Geometry.FullConvexIntersectionCover

/-! Common physical refinements of graph patches with different original rigid frames. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialGraphPartition

universe u v

variable {height : Plane → ℝ} {region : Set Plane} {A : Type u} {B : Type v}
  (P : SpatialGraphPartition height region A) (Q : SpatialGraphPartition height region B)
  [Finite A] [Finite B]

abbrev CommonIndex := {p : A × B // (interior (P.footprint p.1 ∩ Q.footprint p.2)).Nonempty}

omit [Finite A] in
theorem full_intersections_cover (a : A) : P.footprint a =
    ⋃ b : {b // (interior (P.footprint a ∩ Q.footprint b)).Nonempty},
      P.footprint a ∩ Q.footprint b.val :=
  full_convex_intersections_cover_of_subset (P.footprint a) (P.closed a) (P.convex a) (P.full a)
    Q.footprint Q.closed Q.convex Q.full (fun x hx =>
      Eq.mp (congrArg (fun s : Set Plane => x ∈ s) Q.cover) (P.footprint_subset_region a hx))

/-- Construct a common physical patch partition from the actual full-dimensional intersections. -/
def commonPartition : SpatialGraphPartition height region (P.CommonIndex Q) where
  footprint i := P.footprint i.val.1 ∩ Q.footprint i.val.2
  plane i := P.plane i.val.1
  closed i := (P.closed i.val.1).inter (Q.closed i.val.2)
  convex i := (P.convex i.val.1).inter (Q.convex i.val.2)
  full i := i.property
  disjoint i j different := by
    apply Set.disjoint_left.mpr
    intro x first last
    by_cases same : i.val.1 = j.val.1
    · have other : i.val.2 ≠ j.val.2 :=
        fun equal => different (Subtype.ext (Prod.ext same equal))
      exact Set.disjoint_left.mp (Q.disjoint _ _ other)
        (interior_mono Set.inter_subset_right first) (interior_mono Set.inter_subset_right last)
    · exact Set.disjoint_left.mp (P.disjoint _ _ same)
        (interior_mono Set.inter_subset_left first) (interior_mono Set.inter_subset_left last)
  cover := by
    apply Set.Subset.antisymm
    · intro x member
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
        (Eq.mp (congrArg (fun s : Set Plane => x ∈ s) P.cover) member)
      have fine_member : x ∈ ⋃ b : {b // (interior (P.footprint a ∩ Q.footprint b)).Nonempty},
          P.footprint a ∩ Q.footprint b.val :=
        Eq.mp (congrArg (fun s : Set Plane => x ∈ s) (P.full_intersections_cover Q a)) ha
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp fine_member
      exact Set.mem_iUnion.mpr ⟨⟨(a, b.val), b.property⟩, hb⟩
    · intro x member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact P.footprint_subset_region i.val.1 hi.1
  active i p member := P.active i.val.1 p member.1

/-- The common physical partition covers each original left cell completely. -/
def commonRefinementLeft : P.Refinement (P.commonPartition Q) where
  parent i := i.val.1
  included _ := Set.inter_subset_left
  cover a := by
    apply Set.Subset.antisymm
    · intro x member
      have fine_member : x ∈ ⋃ b : {b // (interior (P.footprint a ∩ Q.footprint b)).Nonempty},
          P.footprint a ∩ Q.footprint b.val :=
        Eq.mp (congrArg (fun s : Set Plane => x ∈ s) (P.full_intersections_cover Q a)) member
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp fine_member
      exact Set.mem_iUnion.mpr ⟨⟨⟨(a, b.val), b.property⟩, rfl⟩, hb⟩
    · intro x member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact Eq.mp (congrArg (fun a => x ∈ P.footprint a) i.property) hi.1

/-- The same common physical partition covers every original right cell completely. -/
def commonRefinementRight : Q.Refinement (P.commonPartition Q) where
  parent i := i.val.2
  included _ := Set.inter_subset_right
  cover b := by
    apply Set.Subset.antisymm
    · intro x member
      have fine_member : x ∈ ⋃ a : {a // (interior (Q.footprint b ∩ P.footprint a)).Nonempty},
          Q.footprint b ∩ P.footprint a.val :=
        Eq.mp (congrArg (fun s : Set Plane => x ∈ s) (Q.full_intersections_cover P b)) member
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp fine_member
      have full : (interior (P.footprint a.val ∩ Q.footprint b)).Nonempty := by
        rw [Set.inter_comm]
        exact a.property
      exact Set.mem_iUnion.mpr ⟨⟨⟨(a.val, b), full⟩, rfl⟩, ha.2, ha.1⟩
    · intro x member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact Eq.mp (congrArg (fun b => x ∈ Q.footprint b) i.property) hi.2

end Unfoldings.SpatialGraphPartition
