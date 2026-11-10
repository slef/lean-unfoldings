module

public import Unfoldings.Complex.ElementarySubdivision
public import Unfoldings.Development.SubdivisionNonoverlap

/-! Actual metric and development instances for every nondegenerate triangle split. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

variable (T : Triangle)

def singleDevelopment : FacewiseDevelopment T.singleComplex Set.univ where
  place _ := AffineIsometryEquiv.refl ℝ Plane
  joined s := s.elim
  opposite s := s.elim

theorem singleDevelopment_nonoverlapping : T.singleDevelopment.Nonoverlapping := by
  intro f g different
  exact (different (Subsingleton.elim f g)).elim

def singleCellMetricEquiv : T.Cell ≃ᵢ T.singleComplex.Realization Set.univ where
  toEquiv := Equiv.ofBijective (T.singleComplex.faceMap Set.univ ())
    ⟨(T.singleDevelopment.faceMap_isometry ()).injective, by
      intro p
      obtain ⟨⟨f, x⟩, rfl⟩ := MetricGluing.point_surjective T.singleComplex.Cell
        (T.singleComplex.glue Set.univ) p
      cases f
      exact ⟨x, rfl⟩⟩
  isometry_toFun := T.singleDevelopment.faceMap_isometry ()

variable (t : ℝ) (inside : t ∈ Set.Ioo 0 1)

/-- The two glued child cells recover the original triangle's actual Euclidean metric. -/
def splitCellMetricEquiv : (T.splitComplex t inside).Realization Set.univ ≃ᵢ T.Cell :=
  (T.splitMetricEquiv t inside).trans T.singleCellMetricEquiv.symm

/-- The elementary split has a constructed outward development. -/
def splitDevelopment : FacewiseDevelopment (T.splitComplex t inside) Set.univ :=
  T.singleDevelopment.subdivide (T.splitSubdivision t inside)
    (T.splitSubdivision_conforming t inside)

theorem splitDevelopment_nonoverlapping : (T.splitDevelopment t inside).Nonoverlapping :=
  FacewiseDevelopment.Nonoverlapping.subdivide T.singleDevelopment (T.splitSubdivision t inside)
    (T.splitSubdivision_conforming t inside) T.singleDevelopment_nonoverlapping

end Unfoldings.Triangle
