module

public import Unfoldings.Geometry.Hinge
public import Unfoldings.Boundary
public import Mathlib.Tactic.NormNum

/-! A genuine joined hinge, boundary contact, and a development with interior overlap. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Examples

def upperTriangle : Triangle where
  vertex := ![0, EuclideanSpace.single 0 1, EuclideanSpace.single 1 1]
  nondegenerate := by norm_num [orient, EuclideanSpace.single, PiLp.single_apply]

def lowerTriangle : Triangle where
  vertex := ![0, EuclideanSpace.single 0 1, EuclideanSpace.single 1 (-1)]
  nondegenerate := by norm_num [orient, EuclideanSpace.single, PiLp.single_apply]

/-- Two cells with their entire common horizontal edge identified. -/
def hinge : TriangleComplex Bool where
  triangle := fun f => if f then lowerTriangle else upperTriangle
  Seam := Unit
  left := fun _ => ⟨false, 0⟩
  right := fun _ => ⟨true, 0⟩
  distinct := by
    intro s equal
    have impossible := congrArg EdgeRef.face equal
    cases impossible
  identify := fun _ => IsometryEquiv.refl _
  unique := fun _ _ _ => Subsingleton.elim _ _

def hingeDevelopment : FacewiseDevelopment hinge Set.univ where
  place := fun _ => AffineIsometryEquiv.refl ℝ Plane
  joined := by intro s hs x; rfl
  opposite := by
    intro s hs
    change orient 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) *
      orient 0 (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 (-1)) < 0
    norm_num [orient, EuclideanSpace.single, PiLp.single_apply]

theorem hinge_nonoverlapping : hingeDevelopment.Nonoverlapping := by
  intro f g different
  cases f <;> cases g
  · exact (different rfl).elim
  · exact hingeDevelopment.hinge_nonoverlap () (Set.mem_univ _)
  · exact (hingeDevelopment.hinge_nonoverlap () (Set.mem_univ _)).symm
  · exact (different rfl).elim

/-- The two closed developed cells touch; the nonoverlap predicate still holds. -/
theorem hinge_boundary_contact :
    ∃ x, x ∈ hingeDevelopment.faceImage false ∧ x ∈ hingeDevelopment.faceImage true := by
  have upper : (0 : Plane) ∈ upperTriangle.carrier := by
    simpa [upperTriangle] using upperTriangle.vertex_mem 0
  have lower : (0 : Plane) ∈ lowerTriangle.carrier := by
    simpa [lowerTriangle] using lowerTriangle.vertex_mem 0
  exact ⟨0, ⟨0, upper, rfl⟩, ⟨0, lower, rfl⟩⟩

/-- The actual metric gluing of the hinge keeps each original triangular cell isometric. -/
theorem hinge_face_isometry (f : Bool) : Isometry (hinge.faceMap Set.univ f) :=
  hingeDevelopment.faceMap_isometry f

/-- The common edge becomes two boundary banks exactly when its seam is cut. -/
theorem hinge_cut_banks :
    hinge.IsBoundaryEdge ∅ (hinge.left ()) ∧ hinge.IsBoundaryEdge ∅ (hinge.right ()) ∧
      ¬ hinge.IsBoundaryEdge Set.univ (hinge.left ()) := by
  refine ⟨hinge.isBoundaryEdge_empty _, hinge.isBoundaryEdge_empty _, ?_⟩
  intro boundary
  exact (hinge.isBoundaryEdge_left_iff Set.univ ()).mp boundary (Set.mem_univ _)

/-- The two hinge cells remain metrically separate after cutting, even at their bank endpoints. -/
theorem hinge_cut_cells_edist (x : hinge.Cell false) (y : hinge.Cell true) :
    edist (hinge.faceMap ∅ false x) (hinge.faceMap ∅ true y) = ⊤ :=
  hinge.edist_faceMap_empty_of_ne Bool.false_ne_true x y

/-- Restoring the hinge identifies its entire pair of banks. -/
theorem hinge_restore_banks (x : (hinge.triangle (hinge.left ()).face).Edge (hinge.left ()).edge) :
    hinge.forgetCuts (Set.empty_subset Set.univ)
        (hinge.bankMap ∅ (hinge.leftBank ∅ () (Set.notMem_empty _)) x) =
      hinge.forgetCuts (Set.empty_subset Set.univ)
        (hinge.bankMap ∅ (hinge.rightBank ∅ () (Set.notMem_empty _)) (hinge.identify () x)) :=
  hinge.forgetCuts_banks (Set.empty_subset Set.univ) () (Set.notMem_empty _) (Set.mem_univ _) x

/-- Two unjoined cells provide a simple example that overlap is representable. -/
def coincidentComplex (T : Triangle) : TriangleComplex Bool where
  triangle := fun _ => T
  Seam := Empty
  left := Empty.elim
  right := Empty.elim
  distinct := by intro s; cases s
  identify := by intro s; cases s
  unique := by intro s; cases s

def coincidentDevelopment (T : Triangle) :
    FacewiseDevelopment (coincidentComplex T) Set.univ where
  place := fun _ => AffineIsometryEquiv.refl ℝ Plane
  joined := by intro s; cases s
  opposite := by intro s; cases s

@[simp] theorem coincident_faceImage (T : Triangle) (f : Bool) :
    (coincidentDevelopment T).faceImage f = T.carrier := by
  simp [FacewiseDevelopment.faceImage, coincidentDevelopment, coincidentComplex]

theorem coincident_not_nonoverlapping (T : Triangle) :
    ¬ (coincidentDevelopment T).Nonoverlapping := by
  intro nonoverlap
  obtain ⟨x, hx⟩ := T.interior_nonempty
  have disjoint := nonoverlap false true Bool.false_ne_true
  rw [coincident_faceImage, coincident_faceImage] at disjoint
  exact Set.disjoint_left.mp disjoint hx hx

/-- Overlap is counted on genuine two-dimensional interiors. -/
theorem coincident_multiplicity_two (T : Triangle) :
    ∃ x, (coincidentDevelopment T).multiplicity x = 2 := by
  obtain ⟨x, hx⟩ := T.interior_nonempty
  exact ⟨x, by simp [FacewiseDevelopment.multiplicity, hx]⟩

end Unfoldings.Examples
