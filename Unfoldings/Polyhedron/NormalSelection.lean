module

public import Unfoldings.Geometry.SphericalRotation
public import Unfoldings.Polyhedron.Rotation
public import Unfoldings.Polyhedron.UpperAdjacency
public import Unfoldings.Roof.SphericalSelection

/-! Spherical normal-selection disks on actual convex polyhedral boundaries. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

/-- The original upward triangles in coordinates centered on the chosen hemisphere. -/
def hemisphereRoof (center : Space) :
    ConvexRoof (N.rotate (Cap.northFrame center)).upperComplex :=
  (P.rotate (Cap.northFrame center)).upperRoof (N.rotate (Cap.northFrame center))

/-- Selection adjacency is exactly an original seam between two selected original faces. -/
theorem hemisphere_selectionGraph_adj_iff (center : Space) (region : Set Space)
    (f g : (N.rotate (Cap.northFrame center)).UpperFace) :
    ((P.hemisphereRoof N center).selectionGraph
      (Cap.gnomonicRegion (Cap.northFrame center '' region))).Adj f g ↔
      N.normal f.val ∈ region ∧ N.normal g.val ∈ region ∧ f ≠ g ∧
        ∃ s : C.Seam, ((C.left s).face = f.val ∧ (C.right s).face = g.val) ∨
          ((C.left s).face = g.val ∧ (C.right s).face = f.val) := by
  let K := P.hemisphereRoof N center
  have membership (f : (N.rotate (Cap.northFrame center)).UpperFace) :
      K.normalSlope f ∈ Cap.gnomonicRegion (Cap.northFrame center '' region) ↔
        N.normal f.val ∈ region := by
    rw [← K.normal_selected_iff]
    change Cap.northFrame center (N.normal f.val) ∈ Cap.northFrame center '' region ↔ _
    exact (Cap.northFrame center).injective.mem_set_image
  change _ ∧ _ ∧ TriangleFamily.EdgeAdjacent K.projectedTriangle f g ↔ _
  rw [membership, membership]
  have triangles : K.projectedTriangle = (N.rotate (Cap.northFrame center)).upperTriangle := by
    funext f
    apply Triangle.eq_of_vertex_eq
    intro i
    rfl
  rw [triangles, (N.rotate (Cap.northFrame center)).upper_edgeAdjacent_iff
    (P.rotate (Cap.northFrame center))]

/-- Every selected original face belongs to the upper roof of the containing hemisphere. -/
def normalSelectionSeed (_P : F.ConvexBoundary) (center : Space) (unit : ‖center‖ = 1)
    (region : Set Space)
    (hemisphere : ∀ n ∈ region, 0 < inner ℝ center n) (seed : Face)
    (selected : N.normal seed ∈ region) : (N.rotate (Cap.northFrame center)).UpperFace :=
  ⟨seed, by
    change 0 < Cap.northFrame center (N.normal seed) 2
    rw [Cap.northFrame_height center unit]
    exact hemisphere _ selected⟩

/-- A selected component uses whole original faces and inherited original seams.
The intermediate upward-face subtype only discards unselected lower faces. -/
def normalSelectionFaces (center : Space) (unit : ‖center‖ = 1) (region : Set Space)
    (hemisphere : ∀ n ∈ region, 0 < inner ℝ center n) (seed : Face)
    (selected : N.normal seed ∈ region) : Set (N.rotate (Cap.northFrame center)).UpperFace :=
  (P.hemisphereRoof N center).normalSelectionComponent (Cap.northFrame center '' region)
    (P.normalSelectionSeed N center unit region hemisphere seed selected)

/-- All faces in the component satisfy the original, unrotated normal selection. -/
theorem normalSelectionFaces_selected (center : Space) (unit : ‖center‖ = 1)
    (region : Set Space) (hemisphere : ∀ n ∈ region, 0 < inner ℝ center n)
    (seed : Face) (selected : N.normal seed ∈ region)
    {f : (N.rotate (Cap.northFrame center)).UpperFace}
    (member : f ∈ P.normalSelectionFaces N center unit region hemisphere seed selected) :
    N.normal f.val ∈ region := by
  have chosen : (P.hemisphereRoof N center).normal
      (P.normalSelectionSeed N center unit region hemisphere seed selected) ∈
        Cap.northFrame center '' region := ⟨N.normal seed, selected, rfl⟩
  obtain ⟨n, hn, equal⟩ :=
    (P.hemisphereRoof N center).normalSelectionComponent_selected chosen member
  exact (Cap.northFrame center).injective equal ▸ hn

open Classical in
/-- Every whole-edge component selected by a closed spherical convex region inside an open
hemisphere is an intrinsic disk. Projection is injective and the planar frontier is Jordan.
Neither a graph roof, a disk certificate, nor a triangulation refinement is input. -/
theorem spherical_normal_selection_component (center : Space) (unit : ‖center‖ = 1)
    (region : Set Space) (convex : SphericalConvex region) (closed : IsClosed region)
    (hemisphere : ∀ n ∈ region, 0 < inner ℝ center n) (seed : Face)
    (selected : N.normal seed ∈ region) :
    Function.Injective ((P.hemisphereRoof N center).restrictProjection
      (P.normalSelectionFaces N center unit region hemisphere seed selected)) ∧
    Nonempty (((N.rotate (Cap.northFrame center)).upperComplex.restrictFaces
      (P.normalSelectionFaces N center unit region hemisphere seed selected)).Realization
        Set.univ ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
    Schoenflies.IsJordanCurve (frontier ((P.hemisphereRoof N center).restrictedCarrier
      (P.normalSelectionFaces N center unit region hemisphere seed selected))) := by
  exact (P.hemisphereRoof N center).spherical_normal_selection_component
    (convex.image (Cap.northFrame center))
    ((Cap.northFrame center).toHomeomorph.isClosedMap region closed)
    (P.normalSelectionSeed N center unit region hemisphere seed selected)
    ⟨N.normal seed, selected, rfl⟩

end Unfoldings.SpatialFolding.ConvexBoundary
