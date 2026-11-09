module

public import Unfoldings.Geometry.Placement
public import Unfoldings.Geometry.Hinge

/-! Every two-triangle full-edge hinge has a constructed nonoverlapping development. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Hinge

/-- A two-cell complex with one whole-edge seam. -/
def complex (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) :
    TriangleComplex Bool where
  triangle := fun side => if side then U else T
  Seam := Unit
  left := fun _ => ⟨false, e⟩
  right := fun _ => ⟨true, f⟩
  distinct := by
    intro s equal
    have impossible := congrArg EdgeRef.face equal
    cases impossible
  identify := fun _ => identify
  unique := fun _ _ _ => Subsingleton.elim _ _

/-- Develop a hinge by fixing the first triangle and constructing the outward second placement. -/
def development (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) :
    FacewiseDevelopment (complex T U e f identify) Set.univ where
  place := fun side => if side then (hingePlacement T U e f identify).place
    else AffineIsometryEquiv.refl ℝ Plane
  joined := by
    intro s hs x
    exact ((hingePlacement T U e f identify).joined x).symm
  opposite := by
    intro s hs
    exact (hingePlacement T U e f identify).opposite

/-- The construction has disjoint face interiors, with boundary contact allowed. -/
theorem nonoverlapping (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) :
    (development T U e f identify).Nonoverlapping := by
  intro a b different
  cases a <;> cases b
  · exact (different rfl).elim
  · exact (development T U e f identify).hinge_nonoverlap () (Set.mem_univ _)
  · exact ((development T U e f identify).hinge_nonoverlap () (Set.mem_univ _)).symm
  · exact (different rfl).elim

end Unfoldings.Hinge
