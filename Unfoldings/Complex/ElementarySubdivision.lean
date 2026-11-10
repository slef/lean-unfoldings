module

public import Unfoldings.Complex.SubdivisionComposition
public import Unfoldings.Geometry.TriangleSplitSides

/-! Construct the paired two-triangle split and its actual conforming subdivision certificate. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

variable (T : Triangle) (t : ℝ) (inside : t ∈ Set.Ioo 0 1)

abbrev singleComplex : TriangleComplex Unit where
  triangle _ := T
  Seam := Empty
  left := Empty.elim
  right := Empty.elim
  distinct s := s.elim
  identify s := s.elim
  unique s := s.elim

theorem splitEdge_eq : (T.splitTriangle t inside false).edge 1 =
    (T.splitTriangle t inside true).edge 2 :=
  segment_symm ℝ _ _

def splitIdentify : (T.splitTriangle t inside false).Edge 1 ≃ᵢ
    (T.splitTriangle t inside true).Edge 2 where
  toEquiv :=
    { toFun x := ⟨x.val, (T.splitEdge_eq t inside).subset x.property⟩
      invFun y := ⟨y.val, (T.splitEdge_eq t inside).symm.subset y.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  isometry_toFun _ _ := rfl

abbrev splitComplex : TriangleComplex Bool where
  triangle := T.splitTriangle t inside
  Seam := Unit
  left _ := ⟨false, 1⟩
  right _ := ⟨true, 2⟩
  distinct _ := by decide
  identify _ := T.splitIdentify t inside
  unique _ _ _ := Subsingleton.elim _ _

def splitSubdivision : (T.singleComplex).Subdivision (T.splitComplex t inside) where
  parent _ := ()
  place _ := AffineIsometryEquiv.refl ℝ Plane
  inside g x member := T.splitTriangle_subset t inside g member
  cover f x := by
    cases f
    have cover : x.val ∈ (T.splitTriangle t inside false).carrier ∪
        (T.splitTriangle t inside true).carrier :=
      (T.splitTriangle_cover t inside).symm.subset x.property
    rcases cover with first | last
    · exact ⟨false, ⟨x.val, first⟩, rfl, rfl⟩
    · exact ⟨true, ⟨x.val, last⟩, rfl, rfl⟩

theorem split_across_related (x : (T.splitTriangle t inside false).Cell)
    (y : (T.splitTriangle t inside true).Cell) (equal : x.val = y.val) :
    Relation.EqvGen ((T.splitComplex t inside).glue Set.univ) ⟨false, x⟩ ⟨true, y⟩ := by
  have on_edge := T.splitTriangle_intersection t inside x.property (equal.symm ▸ y.property)
  let edge : (T.splitTriangle t inside false).Edge 1 := ⟨x.val, on_edge⟩
  apply Relation.EqvGen.rel
  refine ⟨(), Set.mem_univ _, edge, rfl, ?_⟩
  exact congrArg (Sigma.mk true) (Subtype.ext equal.symm)

theorem split_points_related (a b : (T.splitComplex t inside).Total)
    (equal : a.2.val = b.2.val) :
    Relation.EqvGen ((T.splitComplex t inside).glue Set.univ) a b := by
  obtain ⟨f, x⟩ := a
  obtain ⟨g, y⟩ := b
  cases f <;> cases g
  · have cells : x = y := Subtype.ext equal
    subst y
    exact Relation.EqvGen.refl _
  · exact T.split_across_related t inside x y equal
  · exact (T.split_across_related t inside y x equal.symm).symm
  · have cells : x = y := Subtype.ext equal
    subst y
    exact Relation.EqvGen.refl _

theorem singleComplex_related_eq {a b : (T.singleComplex).Total}
    (related : Relation.EqvGen ((T.singleComplex).glue Set.univ) a b) : a = b := by
  induction related with
  | rel a b joined => obtain ⟨s, _⟩ := joined; exact s.elim
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ first last => exact first.trans last

theorem splitSubdivision_conforming :
    (T.splitSubdivision t inside).Conforming Set.univ Set.univ where
  respects a b joined := by
    obtain ⟨s, _kept, x, rfl, rfl⟩ := joined
    exact Relation.EqvGen.refl _
  lifts a b related := by
    have equal := T.singleComplex_related_eq related
    apply T.split_points_related t inside a b
    exact congrArg (fun p : (T.singleComplex).Total => p.2.val) equal

def splitMetricEquiv : (T.splitComplex t inside).Realization Set.univ ≃ᵢ
    (T.singleComplex).Realization Set.univ :=
  (T.splitSubdivision_conforming t inside).metricEquiv

end Unfoldings.Triangle
