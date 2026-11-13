module

public import Unfoldings.Roof.FaceRestriction
public import Unfoldings.Roof.ProjectedFaces
public import Unfoldings.Complex.BoundaryCycles
public import Unfoldings.Topology.GraphVertexIdentifications

/-! Boundary cycles of whole-face roof restrictions contain actual planar Jordan curves. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
/-- A nonempty bank boundary of a whole-face roof restriction contains a planar Jordan
curve, even when distinct boundary vertex copies have coincident projections. -/
theorem exists_restricted_boundary_Jordan (U : Set Face)
    (bank : (C.restrictFaces U).BoundaryBank Set.univ) :
    ∃ J : Set Plane, Schoenflies.IsJordanCurve J ∧
      J ⊆ K.restrictProjection U '' (C.restrictFaces U).bankBoundary Set.univ := by
  let R := C.restrictFaces U
  let G := R.boundaryGraph Set.univ
  have cyclic : ¬ G.graph.IsAcyclic := by
    intro forest
    exact forest.not_liesOnCycle bank (R.boundaryGraph_bank_liesOnCycle Set.univ bank)
  have edge_injective : ∀ e, Function.Injective (K.restrictProjection U ∘ G.edge e) := by
    intro e s t same
    have cell : (R.bankParameter Set.univ e s).val = (R.bankParameter Set.univ e t).val :=
      K.projectFace_injective e.val.face.val same
    exact R.bankParameter_injective Set.univ e (Subtype.ext cell)
  have fibers : ∀ e t, 0 < t → t < 1 → ∀ y : R.Realization Set.univ,
      K.restrictProjection U (G.edge e t) = K.restrictProjection U y → G.edge e t = y := by
    intro e t positive small y same
    exact K.restrictProjection_fiber_regular U e.val.face
      ((R.triangle e.val.face).edgeMap e.val.edge (R.bankParameter Set.univ e t))
      (R.bankParameter_nonvertex Set.univ e t positive small) y same
  obtain ⟨J, jordan, subset⟩ :=
    G.exists_Jordan_subset_of_open_edge_fibers (K.restrictProjection U) edge_injective fibers cyclic
  rw [R.boundaryGraph_carrier Set.univ] at subset
  exact ⟨J, jordan, subset⟩

end Unfoldings.ConvexRoof
