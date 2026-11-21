module

public import Unfoldings.FewestNets.SphericalPartition
public import Unfoldings.Polyhedron.LinkSeams
public import Unfoldings.FewestNets.SubdivisionCharge

/-! The exact component charge for the original triangles assigned to convex normal cells. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open scoped BigOperators

universe u v w

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)
  {Label : Type w} (cell : Label → Set Space) (center : Label → Space)
  (unit : ∀ i, ‖center i‖ = 1)
  (hemisphere : ∀ i, ∀ n ∈ cell i, 0 < inner ℝ (center i) n)
  (label : Face → Label) (assigned : ∀ f i, N.normal f ∈ cell i ↔ label f = i)

include P center unit hemisphere assigned in
/-- The original, fully retained triangle components for the normal labels are disks. -/
theorem restrictionIsDisk_of_normal_cells
    (convex : ∀ i, SphericalConvex (cell i)) (closed : ∀ i, IsClosed (cell i))
    (c : (C.labeledSeamGraph label).ConnectedComponent) : C.RestrictionIsDisk c.supp := by
  obtain ⟨f, rfl⟩ := c.exists_rep
  change C.RestrictionIsDisk ((C.labeledSeamGraph label).connectedComponentMk f).supp
  let i := label f
  let V := P.normalSelectionFaces N (center i) (unit i) (cell i) (hemisphere i) f
    ((assigned f i).mpr rfl)
  have image := P.normalSelectionFaces_image_eq_labeled_component N cell center unit
    hemisphere label assigned f
  change Subtype.val '' V = _ at image
  rw [← image]
  obtain ⟨_, ⟨local_disk⟩, _⟩ := P.spherical_normal_selection_component N
    (center i) (unit i) (cell i) (convex i) (closed i) (hemisphere i) f ((assigned f i).mpr rfl)
  obtain ⟨flatten⟩ := C.nonempty_restrictFacesImageHomeomorph
    {g | 0 < (N.rotate (Cap.northFrame (center i))).normal g 2} V
  exact ⟨flatten.trans local_disk⟩

include P center unit hemisphere assigned in
/-- Exact component counting for convex spherical labels, measured on the input
mesh with all seams and all subdivision vertices still present. -/
theorem normal_component_count_eq_two_add_sum_vertex_charges
    (convex : ∀ i, SphericalConvex (cell i)) (closed : ∀ i, IsClosed (cell i)) :
    (Nat.card (C.labeledSeamGraph label).ConnectedComponent : ℝ) =
      2 + ∑ p : C.Vertex Set.univ, componentCharge (labelCutDegree label p) :=
  P.labeled_component_count_eq_two_add_sum_vertex_charges label
    (P.restrictionIsDisk_of_normal_cells N cell center unit hemisphere label assigned convex closed)

include P in
/-- The input seam count gives zero charge at nonextreme vertices whenever
triangle labels depend only on their outward normals. -/
theorem normal_labelCutDegree_charge_eq_zero_of_nonextreme {L : Type*} (labelNormal : Space → L)
    (a : C.Vertex Set.univ)
    (not_extreme : F.toSpace Set.univ (C.vertexPoint Set.univ a) ∉ F.vertexHull.extremePoints ℝ) :
    componentCharge (labelCutDegree (labelNormal ∘ N.normal) a) = 0 := by
  obtain ⟨n, c, closes, covers⟩ := P.exists_cyclic_link a
  rw [P.labelCutDegree_eq_linkChanges _ c closes covers]
  exact P.componentCharge_eq_zero_of_nonextreme_link N labelNormal a not_extreme c closes

open Classical in
include P center unit hemisphere assigned in
/-- The charge sum may be restricted to the extreme physical vertices.
This uses the input mesh throughout, so coplanar subdivisions need no quotient. -/
theorem normal_component_count_eq_two_add_sum_extreme_charges
    (convex : ∀ i, SphericalConvex (cell i)) (closed : ∀ i, IsClosed (cell i))
    (labelNormal : Space → Label) (same_labels : label = labelNormal ∘ N.normal) :
    (Nat.card (C.labeledSeamGraph label).ConnectedComponent : ℝ) =
      2 + ∑ p ∈ (Finset.univ : Finset (C.Vertex Set.univ)).filter
          (fun p => F.toSpace Set.univ (C.vertexPoint Set.univ p) ∈ F.vertexHull.extremePoints ℝ),
        componentCharge (labelCutDegree label p) := by
  rw [P.normal_component_count_eq_two_add_sum_vertex_charges N cell center unit
    hemisphere label assigned convex closed, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  split
  · rfl
  · rename_i outside
    rw [same_labels]
    exact P.normal_labelCutDegree_charge_eq_zero_of_nonextreme N labelNormal p outside

end Unfoldings.SpatialFolding.ConvexBoundary
