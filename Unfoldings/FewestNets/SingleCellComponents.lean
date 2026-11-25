module

public import Unfoldings.FewestNets.SphericalPartition
public import Unfoldings.Polyhedron.SelectedComponentEuler
public import Unfoldings.Topology.CompactJordanDisk
public import Unfoldings.Topology.ConvexJordanBoundary

/-! Euler's formula for the actual original-face components in a single normal cell. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C)

include F in
open Classical in
/-- The whole restriction to one original triangle is an intrinsic disk. -/
theorem restrictionIsDisk_singleton (f : Face) : C.RestrictionIsDisk {f} := by
  let U : Set Face := {f}
  letI : Fintype U := Subtype.fintype (· ∈ U)
  let D := C.restrictFaces U
  let selected : U := ⟨f, rfl⟩
  let place := D.faceMap Set.univ selected
  have isometry : Isometry place := (F.restrictFaces U).faceMap_isometry Set.univ selected
  have onto : Function.Surjective place := by
    intro x
    obtain ⟨⟨g, p⟩, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue Set.univ) x
    obtain rfl : g = selected := Subtype.ext g.property
    exact ⟨p, rfl⟩
  let chart : D.Cell selected ≃ᵢ D.Realization Set.univ := ⟨
    Equiv.ofBijective place ⟨isometry.injective, onto⟩, isometry⟩
  let T := C.triangle f
  have jordan := PlanarTopology.isJordanCurve_frontier_of_convex
    T.convex_carrier T.interior_nonempty T.compact_carrier.isBounded
  obtain ⟨disk⟩ := PlanarTopology.exists_diskHomeomorph_of_compact_Jordan_frontier
    T.compact_carrier T.interior_nonempty jordan
  exact ⟨chart.toHomeomorph.symm.trans disk⟩

namespace ConvexBoundary

variable {F} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
open Classical in
/-- The selected components are normal-selection disks. An unselected original
face is isolated in the auxiliary graph and contributes its own triangular disk. -/
theorem restrictionIsDisk_of_single_normal_cell
    (center : Space) (unit : ‖center‖ = 1) (region : Set Space)
    (convex : SphericalConvex region) (closed : IsClosed region)
    (hemisphere : ∀ n ∈ region, 0 < inner ℝ center n)
    (c : (C.labeledSeamGraph (selectionLabel {f | N.normal f ∈ region})).ConnectedComponent) :
    C.RestrictionIsDisk c.supp := by
  let U := {f | N.normal f ∈ region}
  let G := C.labeledSeamGraph (selectionLabel U)
  obtain ⟨seed, rfl⟩ := c.exists_rep
  change C.RestrictionIsDisk (G.connectedComponentMk seed).supp
  by_cases chosen : N.normal seed ∈ region
  · have membership (f : Face) : N.normal f ∈ region ↔ selectionLabel U f = none := by
      by_cases hf : N.normal f ∈ region <;> simp [selectionLabel, U, hf]
    have image := P.normalSelectionFaces_image_eq_label N (selectionLabel U) center unit
      region hemisphere membership seed ((membership seed).mp chosen)
    rw [← image]
    obtain ⟨_, ⟨local_disk⟩, _⟩ := P.spherical_normal_selection_component N
      center unit region convex closed hemisphere seed chosen
    obtain ⟨flatten⟩ := C.nonempty_restrictFacesImageHomeomorph
      {g | 0 < (N.rotate (Cap.northFrame center)).normal g 2}
      (P.normalSelectionFaces N center unit region hemisphere seed chosen)
    exact ⟨flatten.trans local_disk⟩
  · have support : (G.connectedComponentMk seed).supp = {seed} := by
      ext f
      constructor
      · intro member
        have same : G.connectedComponentMk f = G.connectedComponentMk seed := member
        obtain ⟨walk⟩ := SimpleGraph.ConnectedComponent.exact same.symm
        cases walk with
        | nil => rfl
        | cons edge tail =>
          exact (chosen ((selectionLabel_eq_iff U edge.1).mp edge.2.1).1).elim
      · rintro rfl
        rfl
    rw [support]
    exact F.restrictionIsDisk_singleton seed

include P in
open Classical in
/-- Count the original components of one spherical convex selector through their
selected faces, interior seams, and full vertex links. -/
theorem normal_cell_components_eq_euler
    (center : Space) (unit : ‖center‖ = 1) (region : Set Space)
    (convex : SphericalConvex region) (closed : IsClosed region)
    (hemisphere : ∀ n ∈ region, 0 < inner ℝ center n) :
    let U := {f | N.normal f ∈ region}
    let graph := C.labeledSeamGraph (selectionLabel U)
    let selectedComponent (c : graph.ConnectedComponent) :=
      ∃ f ∈ U, graph.connectedComponentMk f = c
    (Nat.card {c // selectedComponent c} : ℤ) =
      ((Finset.univ.filter (· ∈ U)).card : ℤ) -
        (Finset.univ.filter fun s : C.Seam => (C.left s).face ∈ U ∧ (C.right s).face ∈ U).card +
        ((Finset.univ : Finset (C.Vertex Set.univ)).filter (fullSelectedLink U)).card :=
  P.selected_components_eq_euler _ (P.restrictionIsDisk_of_single_normal_cell N
    center unit region convex closed hemisphere)

end ConvexBoundary
end Unfoldings.SpatialFolding
