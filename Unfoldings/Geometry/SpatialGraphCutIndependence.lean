module

public import Unfoldings.Geometry.SpatialGraphCommonRefinement
public import Unfoldings.Metric.CommonModelTransport

/-! Physical patch cut metrics depend on the graph and cuts, not on the supporting mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialGraphPartition

universe u v

variable {height : Plane → ℝ} {region : Set Plane} {A : Type u} {B : Type v}
  (P : SpatialGraphPartition height region A) (Q : SpatialGraphPartition height region B)
  [Finite A] [Finite B] (cuts : Set Plane) (cut_closed : IsClosed cuts)
  (outside_P : ∀ a, Disjoint (interior (P.footprint a)) cuts)
  (outside_Q : ∀ b, Disjoint (interior (Q.footprint b)) cuts)

/-- Two actual rigid meshes of the same physical patch have identical complete cut metrics.
Support families and frames may differ; all original cell-bank copies are retained. -/
def cutPartitionEquiv : P.Cut cuts ≃ᵢ Q.Cut cuts :=
  ((P.commonRefinementLeft Q).cutEquiv cuts cut_closed outside_P).symm.trans
    ((P.commonRefinementRight Q).cutEquiv cuts cut_closed outside_Q)

theorem fold_cutPartitionEquiv (x : P.Cut cuts) :
    Q.fold cuts (P.cutPartitionEquiv Q cuts cut_closed outside_P outside_Q x) = P.fold cuts x :=
  map_common_model_isometry
    ((P.commonRefinementLeft Q).cutEquiv cuts cut_closed outside_P)
    ((P.commonRefinementRight Q).cutEquiv cuts cut_closed outside_Q)
    (P.fold cuts) (Q.fold cuts) ((P.commonPartition Q).fold cuts)
    ((P.commonRefinementLeft Q).fold_cutEquiv cuts cut_closed outside_P)
    ((P.commonRefinementRight Q).fold_cutEquiv cuts cut_closed outside_Q) x

/-- Every specified physical copy on a common piece matches the original copy in either mesh. -/
theorem cutPartitionEquiv_liftCell (i : P.CommonIndex Q)
    (p : ↥(P.footprint i.val.1 ∩ Q.footprint i.val.2)) :
    P.cutPartitionEquiv Q cuts cut_closed outside_P outside_Q
      (P.liftCell cuts i.val.1 ⟨p.val, p.property.1⟩) =
        Q.liftCell cuts i.val.2 ⟨p.val, p.property.2⟩ :=
  common_model_isometry_copy
    ((P.commonRefinementLeft Q).cutEquiv cuts cut_closed outside_P)
    ((P.commonRefinementRight Q).cutEquiv cuts cut_closed outside_Q)
    ((P.commonPartition Q).liftCell cuts i p)
    ((P.commonRefinementLeft Q).cutEquiv_liftCell cuts cut_closed outside_P i p)
    ((P.commonRefinementRight Q).cutEquiv_liftCell cuts cut_closed outside_Q i p)

/-- Every original cell-bank copy has a literal physical representative in the other mesh. -/
theorem cutPartitionEquiv_liftCell_exists (a : A) (p : P.footprint a) :
    ∃ b : B, ∃ member : p.val ∈ Q.footprint b,
      P.cutPartitionEquiv Q cuts cut_closed outside_P outside_Q (P.liftCell cuts a p) =
        Q.liftCell cuts b ⟨p.val, member⟩ := by
  have covered : p.val ∈ ⋃ b : {b // (interior (P.footprint a ∩ Q.footprint b)).Nonempty},
      P.footprint a ∩ Q.footprint b.val :=
    Eq.mp (congrArg (fun s : Set Plane => p.val ∈ s) (P.full_intersections_cover Q a)) p.property
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp covered
  exact ⟨b.val, hb.2, P.cutPartitionEquiv_liftCell Q cuts cut_closed outside_P outside_Q
    ⟨(a, b.val), b.property⟩ ⟨p.val, hb⟩⟩

end Unfoldings.SpatialGraphPartition
