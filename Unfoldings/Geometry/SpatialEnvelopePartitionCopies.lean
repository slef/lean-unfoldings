module

public import Unfoldings.Geometry.SpatialEnvelopePartitionIndependence
public import Unfoldings.Geometry.SpatialEnvelopeCutExcision

/-! Original physical copies and cut restoration commute with whole-roof partition changes. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A B : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) (Q : WholePartition family B) [Finite A] [Finite B]

/-- Every actual metric copy has a literal original footprint-cell representative. -/
theorem exists_liftCell (cuts : Set Plane) (x : P.Cut cuts) :
    ∃ a, ∃ p : P.footprint a, P.liftCell cuts a p = x := by
  obtain ⟨⟨a, y⟩, rfl⟩ := MetricGluing.point_surjective (fun a => P.planarCell a)
    (P.cutGlue cuts) x
  have inside : (family (P.support a)).project y.val ∈ P.footprint a := by
    obtain ⟨p, hp, equal⟩ := y.property
    rw [← equal, (family (P.support a)).project.apply_symm_apply]
    exact hp
  refine ⟨a, ⟨(family (P.support a)).project y.val, inside⟩, ?_⟩
  exact congrArg (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a)
    (Subtype.ext ((family (P.support a)).project.symm_apply_apply y.val))

/-- Every specified original cell copy has an actual target cell copy at the same point. -/
theorem cutPartitionEquiv_liftCell_exists (cuts : Set Plane) (cut_closed : IsClosed cuts)
    (outside_P : ∀ a, Disjoint (interior (P.footprint a)) cuts)
    (outside_Q : ∀ b, Disjoint (interior (Q.footprint b)) cuts)
    (a : A) (p : P.footprint a) :
    ∃ b : B, ∃ member : p.val ∈ Q.footprint b,
      P.cutPartitionEquiv Q cuts cut_closed outside_P outside_Q (P.liftCell cuts a p) =
        Q.liftCell cuts b ⟨p.val, member⟩ := by
  have refined := full_convex_intersections_cover (P.footprint a) (P.closed a) (P.convex a)
    (P.full a) Q.footprint Q.closed Q.convex Q.full Q.cover
  have covered : p.val ∈ ⋃ b : {b // (interior (P.footprint a ∩ Q.footprint b)).Nonempty},
      P.footprint a ∩ Q.footprint b.val :=
    Eq.mp (congrArg (fun s : Set Plane => p.val ∈ s) refined) p.property
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp covered
  exact ⟨b.val, hb.2, P.cutPartitionEquiv_liftCell Q cuts cut_closed outside_P outside_Q
    ⟨(a, b.val), b.property⟩ ⟨p.val, hb⟩⟩

/-- Restoration keeps the exact same named physical cell lift. -/
@[simp] theorem forgetCut_liftCell (cuts other : Set Plane) (included : other ⊆ cuts)
    (a : A) (p : P.footprint a) :
    P.forgetCut cuts other included (P.liftCell cuts a p) = P.liftCell other a p := rfl

/-- Restoring cuts commutes with the actual change of physical partition.
The retained original metric copies, rather than just their spatial points, agree. -/
theorem cutPartitionEquiv_forgetCut (cuts other : Set Plane) (included : other ⊆ cuts)
    (cut_closed : IsClosed cuts) (other_closed : IsClosed other)
    (outside_P : ∀ a, Disjoint (interior (P.footprint a)) cuts)
    (outside_Q : ∀ b, Disjoint (interior (Q.footprint b)) cuts) (x : P.Cut cuts) :
    Q.forgetCut cuts other included
      (P.cutPartitionEquiv Q cuts cut_closed outside_P outside_Q x) =
        P.cutPartitionEquiv Q other other_closed
          (fun a => (outside_P a).mono_right included)
          (fun b => (outside_Q b).mono_right included)
          (P.forgetCut cuts other included x) := by
  obtain ⟨a, p, rfl⟩ := P.exists_liftCell cuts x
  have refined := full_convex_intersections_cover (P.footprint a) (P.closed a) (P.convex a)
    (P.full a) Q.footprint Q.closed Q.convex Q.full Q.cover
  have covered : p.val ∈ ⋃ b : {b // (interior (P.footprint a ∩ Q.footprint b)).Nonempty},
      P.footprint a ∩ Q.footprint b.val :=
    Eq.mp (congrArg (fun s : Set Plane => p.val ∈ s) refined) p.property
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp covered
  have first := P.cutPartitionEquiv_liftCell Q cuts cut_closed outside_P outside_Q
    ⟨(a, b.val), b.property⟩ ⟨p.val, hb⟩
  have last := P.cutPartitionEquiv_liftCell Q other other_closed
    (fun a => (outside_P a).mono_right included) (fun b => (outside_Q b).mono_right included)
    ⟨(a, b.val), b.property⟩ ⟨p.val, hb⟩
  exact (congrArg (Q.forgetCut cuts other included) first).trans last.symm

end Unfoldings.SpatialEnvelope.WholePartition
