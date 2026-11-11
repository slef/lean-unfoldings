module

public import Unfoldings.Cap.ClipIntrinsicBoundary

/-! Geometric cut sets select actual whole-edge seams of the physical clip. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.ClipSpatialTriangles

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {Z : ℝ} (T : K.ClipSpatialTriangles Z)

local instance interiorSeamIndexFintype : Fintype T.Index := @Fintype.ofFinite _ T.finite

/-- A whole local edge meeting the interior of the actual clip has a genuine seam partner. -/
theorem exists_seam_of_projected_edge_interior
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (a : EdgeRef T.Index) {p : Plane} (on_edge : p ∈ (T.projectedTriangle a.face).edge a.edge)
    (inside : p ∈ interior (K.clipFootprint Z)) :
    ∃ s : T.pairedComplex.Seam, T.pairedComplex.Incident s a := by
  classical
  by_contra absent
  have boundary : T.pairedComplex.IsBoundaryEdge Set.univ a := by
    rintro ⟨s, _kept, incident⟩
    exact absent ⟨s, incident⟩
  let bank : T.pairedComplex.BoundaryBank Set.univ := ⟨a, boundary⟩
  let x := (T.edgeProjection a.face a.edge).symm ⟨p, on_edge⟩
  have present : T.pairedComplex.bankMap Set.univ bank x ∈
      T.pairedComplex.bankBoundary Set.univ := Set.mem_iUnion.mpr ⟨bank, x, rfl⟩
  have frontier := (T.projected_mem_frontier_iff_bankBoundary conforming lower _).mpr present
  have projected : Cap.horizontal (T.pairedFolding.toSpace Set.univ
      (T.pairedComplex.bankMap Set.univ bank x)) = p :=
    (K.projectFaceEquiv (T.face a.face)).apply_symm_apply p
  rw [projected] at frontier
  exact frontier.2 inside

/-- Keep precisely the actual seams whose whole projected edge is not selected for cutting. -/
def retainOutside (cuts : Set Plane) : Set T.pairedComplex.Seam :=
  {s | ¬ (T.projectedTriangle (T.pairedComplex.left s).face).edge
    (T.pairedComplex.left s).edge ⊆ cuts}

/-- A meshed cut edge meeting the clip interior is one of the actual removed seams. -/
theorem exists_cut_seam_of_projected_edge
    (conforming : TriangleFamily.Conforming T.projectedTriangle) (lower : Z < 0)
    (cuts : Set Plane) (a : EdgeRef T.Index)
    (selected : (T.projectedTriangle a.face).edge a.edge ⊆ cuts)
    {p : Plane} (on_edge : p ∈ (T.projectedTriangle a.face).edge a.edge)
    (inside : p ∈ interior (K.clipFootprint Z)) :
    ∃ s : T.pairedComplex.Seam, s ∉ T.retainOutside cuts ∧ T.pairedComplex.Incident s a := by
  obtain ⟨s, incident⟩ := T.exists_seam_of_projected_edge_interior conforming lower a on_edge inside
  refine ⟨s, fun kept => kept ?_, incident⟩
  rcases incident with first | last
  · simpa only [first] using selected
  · rw [T.paired_seam_projected_edge]
    simpa only [last] using selected

end Unfoldings.ConvexCap.ClipSpatialTriangles
