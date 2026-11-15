module

public import Unfoldings.Geometry.SpatialEnvelopeRefinement
public import Unfoldings.Geometry.FullConvexIntersectionCover

/-! Construct common actual whole-roof partitions, retaining all original boundary points. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A B : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) (Q : WholePartition family B) [Finite A] [Finite B]

/-- Exactly the full-dimensional intersections of actual original roof cells. -/
abbrev CommonIndex := {p : A × B // (interior (P.footprint p.1 ∩ Q.footprint p.2)).Nonempty}

/-- Construct an actual common partition without lower-dimensional redundant pieces. -/
def commonPartition : WholePartition family (P.CommonIndex Q) where
  footprint i := P.footprint i.val.1 ∩ Q.footprint i.val.2
  support i := P.support i.val.1
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
    apply Set.eq_univ_of_forall
    intro x
    have covered : x ∈ ⋃ a, P.footprint a := P.cover.symm ▸ Set.mem_univ x
    obtain ⟨a, member⟩ := Set.mem_iUnion.mp covered
    have refined := full_convex_intersections_cover (P.footprint a) (P.closed a) (P.convex a)
      (P.full a) Q.footprint Q.closed Q.convex Q.full Q.cover
    have fine_member : x ∈ ⋃ b : {b // (interior (P.footprint a ∩ Q.footprint b)).Nonempty},
        P.footprint a ∩ Q.footprint b.val :=
      Eq.mp (congrArg (fun s : Set Plane => x ∈ s) refined) member
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp fine_member
    exact Set.mem_iUnion.mpr ⟨⟨(a, b.val), b.property⟩, hb⟩
  active i p member := P.active i.val.1 p member.1

/-- Every original left cell is covered by exactly its common-refinement pieces. -/
def commonRefinementLeft : P.Refinement (P.commonPartition Q) where
  parent i := i.val.1
  included _ := Set.inter_subset_left
  cover a := by
    apply Set.Subset.antisymm
    · intro x member
      have refined := full_convex_intersections_cover (P.footprint a) (P.closed a) (P.convex a)
        (P.full a) Q.footprint Q.closed Q.convex Q.full Q.cover
      have fine_member : x ∈ ⋃ b : {b // (interior (P.footprint a ∩ Q.footprint b)).Nonempty},
          P.footprint a ∩ Q.footprint b.val :=
        Eq.mp (congrArg (fun s : Set Plane => x ∈ s) refined) member
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp fine_member
      exact Set.mem_iUnion.mpr ⟨⟨⟨(a, b.val), b.property⟩, rfl⟩, hb⟩
    · intro x member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact Eq.mp (congrArg (fun a => x ∈ P.footprint a) i.property) hi.1

/-- Every original right cell is covered by exactly its common-refinement pieces. -/
def commonRefinementRight : Q.Refinement (P.commonPartition Q) where
  parent i := i.val.2
  included _ := Set.inter_subset_right
  cover b := by
    apply Set.Subset.antisymm
    · intro x member
      have refined := full_convex_intersections_cover (Q.footprint b) (Q.closed b) (Q.convex b)
        (Q.full b) P.footprint P.closed P.convex P.full P.cover
      have fine_member : x ∈ ⋃ a : {a // (interior (Q.footprint b ∩ P.footprint a)).Nonempty},
          Q.footprint b ∩ P.footprint a.val :=
        Eq.mp (congrArg (fun s : Set Plane => x ∈ s) refined) member
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp fine_member
      have full : (interior (P.footprint a.val ∩ Q.footprint b)).Nonempty := by
        rw [Set.inter_comm]
        exact a.property
      exact Set.mem_iUnion.mpr ⟨⟨⟨(a.val, b), full⟩, rfl⟩, ha.2, ha.1⟩
    · intro x member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact Eq.mp (congrArg (fun b => x ∈ Q.footprint b) i.property) hi.2

end Unfoldings.SpatialEnvelope.WholePartition
