module

public import Unfoldings.Roof.AffineFloorRoof
public import Unfoldings.Complex.BoundaryQuotient
public import Unfoldings.Complex.DiskBoundaryQuotient

/-! Removing a seam in the exact affine-floor problem exposes all copies over its physical edge. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.FloorMesh

universe u

variable {I J : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  {floor : Plane →ᵃ[ℝ] ℝ} {extra : J → Plane →ᵃ[ℝ] ℝ} {Z : ℝ}
  (T : FloorMesh family floor extra Z)

local instance affineFloorCutIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

local notation "D" => pairedComplex T
local notation "Fold" => pairedFolding T

/-- A geometric edge containing an interior section point has an incident seam. -/
theorem exists_seam_of_projected_edge_interior
    (nonempty : (interior (clipAbove family floor Z)).Nonempty)
    (a : EdgeRef T.Index) {p : Plane} (on_edge : p ∈ (T.projectedTriangle a.face).edge a.edge)
    (inside : p ∈ interior (clipAbove family floor Z)) :
    ∃ s : (D).Seam, (D).Incident s a := by
  classical
  by_contra absent
  have boundary : (D).IsBoundaryEdge Set.univ a := by
    rintro ⟨s, _, incident⟩
    exact absent ⟨s, incident⟩
  let bank : (D).BoundaryBank Set.univ := ⟨a, boundary⟩
  let x := (T.edgeProjection a.face a.edge).symm ⟨p, on_edge⟩
  have present : (D).bankMap Set.univ bank x ∈ (D).bankBoundary Set.univ :=
    (D).bankMap_mem_bankBoundary _ _ _
  let Q := T.roof nonempty
  have on_frontier := (Q.projected_mem_frontier_iff_bankBoundary _).mpr present
  change Cap.horizontal ((Fold).toSpace Set.univ ((D).bankMap Set.univ bank x)) ∈
    frontier Q.footprint at on_frontier
  have projected : Cap.horizontal ((Fold).toSpace Set.univ ((D).bankMap Set.univ bank x)) = p := by
    change Cap.horizontal ((family (T.support a.face)).place x.val) = p
    rw [(family (T.support a.face)).horizontal_place]
    exact (family (T.support a.face)).project.apply_symm_apply p
  have footprint : Q.footprint = clipAbove family floor Z := T.pairedFolding_footprint
  rw [projected, footprint] at on_frontier
  exact on_frontier.2 inside

/-- A point projected onto an actual removed seam is on the unfolded boundary
in every metric copy, even at a vertex incident to multiple removed seams. -/
theorem mem_bankBoundary_of_projected_cut_edge
    (retain : Set (D).Seam) (s : (D).Seam) (removed : s ∉ retain)
    (q : ((D).triangle ((D).left s).face).Edge ((D).left s).edge)
    (x : (D).Realization retain)
    (position : Cap.horizontal ((Fold).toSpace retain x) =
      Cap.horizontal ((Fold).place ((D).left s).face q.val)) :
    x ∈ (D).bankBoundary retain := by
  let included := Set.subset_univ retain
  let source := (D).bankMap retain ((D).leftBank retain s removed) q
  have on_boundary : source ∈ (D).bankBoundary retain := (D).bankMap_mem_bankBoundary _ _ _
  have projected : Cap.horizontal ((Fold).toSpace retain source) =
      Cap.horizontal ((Fold).toSpace retain x) := position.symm
  have same := T.pairedProjection_injective
    ((congrArg Cap.horizontal ((Fold).toSpace_forgetCuts included source)).trans
      (projected.trans (congrArg Cap.horizontal ((Fold).toSpace_forgetCuts included x)).symm))
  rcases (D).forgetCuts_fiber_eq_or_boundary included source x same with equal | both
  · exact equal ▸ on_boundary
  · exact both.2

/-- A original bank lies over the graph patch's boundary in horizontal coordinates. -/
theorem projected_original_bank_frontier (nonempty : (interior (clipAbove family floor Z)).Nonempty)
    (bank : (D).BoundaryBank Set.univ) (x : ((D).triangle bank.val.face).Edge bank.val.edge) :
    Cap.horizontal ((Fold).place bank.val.face x.val) ∈ frontier (clipAbove family floor Z) := by
  have present := (D).bankMap_mem_bankBoundary Set.univ bank x
  have result := ((T.roof nonempty).projected_mem_frontier_iff_bankBoundary _).mpr present
  change Cap.horizontal ((Fold).place bank.val.face x.val) ∈
    frontier (T.roof nonempty).footprint at result
  rwa [T.roof_footprint] at result

end Unfoldings.SpatialEnvelope.FloorMesh
