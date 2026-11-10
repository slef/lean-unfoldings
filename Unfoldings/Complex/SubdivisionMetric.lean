module

public import Unfoldings.Complex.Subdivision

/-! Conforming finite subdivisions preserve the full intrinsic extended metric. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision.Conforming

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  {S : C.Subdivision D} {retain : Set C.Seam} {fineRetain : Set D.Seam}
  (H : S.Conforming retain fineRetain)

def equiv : D.Realization fineRetain ≃ C.Realization retain :=
  Equiv.ofBijective H.toCoarse ⟨H.toCoarse_injective, H.toCoarse_surjective⟩

def toFine : C.Realization retain → D.Realization fineRetain := H.equiv.symm

@[simp] theorem toFine_toCoarse (x : D.Realization fineRetain) :
    H.toFine (H.toCoarse x) = x := H.equiv.symm_apply_apply x

@[simp] theorem toCoarse_toFine (x : C.Realization retain) :
    H.toCoarse (H.toFine x) = x := H.equiv.apply_symm_apply x

theorem toFine_parentPoint (a : D.Total) :
    H.toFine (MetricGluing.point C.Cell (C.glue retain) (S.parentPoint a)) =
      MetricGluing.point D.Cell (D.glue fineRetain) a :=
  H.equiv.symm_apply_apply (MetricGluing.point D.Cell (D.glue fineRetain) a)

theorem toFine_faceMap_of_placement {g : Child} {f : Face} {a : D.Cell g} {x : C.Cell f}
    (parent : S.parent g = f) (point : S.place g a.val = x.val) :
    H.toFine (C.faceMap retain f x) = D.faceMap fineRetain g a := by
  have equal := H.toFine_parentPoint ⟨g, a⟩
  rw [S.parentPoint_eq parent point] at equal
  exact equal

private def pieces (f : Face) (g : Child) : Set (C.Cell f) :=
  {x | S.parent g = f ∧ x.val ∈ S.place g '' (D.triangle g).carrier}

private theorem closed_pieces (f : Face) (g : Child) : IsClosed (pieces (S := S) f g) := by
  by_cases parent : S.parent g = f
  · have closed := ((D.triangle g).compact_carrier.image (S.place g).continuous).isClosed
    simpa only [pieces, parent, true_and, Set.preimage] using closed.preimage
      (continuous_subtype_val : Continuous (Subtype.val : C.Cell f → Plane))
  · simpa only [pieces, parent, false_and, Set.ofPred_false] using
      (isClosed_empty : IsClosed (∅ : Set (C.Cell f)))

private theorem cover_pieces (f : Face) : ⋃ g, pieces (S := S) f g = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨g, y, parent, point⟩ := S.cover f x
  exact Set.mem_iUnion.mpr ⟨g, parent, y.val, y.property, point⟩

theorem toFine_faceMap_lipschitz (f : Face) :
    LipschitzWith 1 (H.toFine ∘ C.faceMap retain f) := by
  apply convex_subtype_emetric_lipschitzWith_of_finite_closed_cover
    (C.triangle f).carrier (C.triangle f).convex_carrier (pieces (S := S) f)
    (closed_pieces (S := S) f) (cover_pieces (S := S) f) _ 1
  intro g x hx y hy
  obtain ⟨parent, a, ha, ax⟩ := hx
  obtain ⟨_parent, b, hb, byPoint⟩ := hy
  have first := H.toFine_faceMap_of_placement (a := ⟨a, ha⟩) (x := x) parent ax
  have last := H.toFine_faceMap_of_placement (a := ⟨b, hb⟩) (x := y) parent byPoint
  change edist (H.toFine (C.faceMap retain f x)) (H.toFine (C.faceMap retain f y)) ≤
    (1 : ℝ≥0∞) * edist x y
  rw [first, last, one_mul]
  calc
    edist (D.faceMap fineRetain g ⟨a, ha⟩) (D.faceMap fineRetain g ⟨b, hb⟩) ≤
        edist (⟨a, ha⟩ : D.Cell g) ⟨b, hb⟩ := by
      simpa only [ENNReal.coe_one, one_mul] using
        (D.faceMap_lipschitz fineRetain g).edist_le_mul ⟨a, ha⟩ ⟨b, hb⟩
    _ = edist x y := by
      change edist a b = edist x.val y.val
      rw [← (S.place g).isometry a b, ax, byPoint]

theorem toFine_lipschitz : LipschitzWith 1 H.toFine := by
  have compatible (a b : C.Total) (joined : C.glue retain a b) :
      H.toFine (C.faceMap retain a.1 a.2) = H.toFine (C.faceMap retain b.1 b.2) :=
    congrArg H.toFine (MetricGluing.point_eq_of_glue C.Cell joined)
  have equal : H.toFine = MetricGluing.lift C.Cell (C.glue retain)
      (fun f x => H.toFine (C.faceMap retain f x)) H.toFine_faceMap_lipschitz compatible :=
    MetricGluing.lift_unique C.Cell (C.glue retain) _ H.toFine_faceMap_lipschitz compatible
      H.toFine (fun _ _ => rfl)
  rw [equal]
  exact MetricGluing.lift_lipschitz C.Cell (C.glue retain) _ H.toFine_faceMap_lipschitz compatible

theorem toCoarse_isometry : Isometry H.toCoarse := by
  intro x y
  apply le_antisymm
  · simpa only [ENNReal.coe_one, one_mul] using H.toCoarse_lipschitz.edist_le_mul x y
  · have bound := H.toFine_lipschitz.edist_le_mul (H.toCoarse x) (H.toCoarse y)
    simpa only [toFine_toCoarse, ENNReal.coe_one, one_mul] using bound

def metricEquiv : D.Realization fineRetain ≃ᵢ C.Realization retain :=
  ⟨H.equiv, H.toCoarse_isometry⟩

@[simp] theorem metricEquiv_faceMap (g : Child) (x : D.Cell g) :
    H.metricEquiv (D.faceMap fineRetain g x) =
      C.faceMap retain (S.parent g) (S.parentCell g x) := rfl

end Unfoldings.TriangleComplex.Subdivision.Conforming
