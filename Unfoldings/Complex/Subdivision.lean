module

public import Unfoldings.Complex.Exact
public import Unfoldings.Geometry.AffineEnd
public import Unfoldings.Metric.ConvexCover

/-!
# Geometric subdivisions and conforming seam systems

Every fine triangle lies isometrically in a specified old triangle, and these
images cover every old cell. Conformity is stated using finite declared seam
chains in both directions. No metric equivalence, development, disk topology,
or nonoverlap is assumed in the subdivision data.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]

structure Subdivision (C : TriangleComplex.{u, v} Face) (D : TriangleComplex.{w, z} Child) where
  parent : Child → Face
  place : Child → Plane ≃ᵃⁱ[ℝ] Plane
  inside : ∀ g x, x ∈ (D.triangle g).carrier → place g x ∈ (C.triangle (parent g)).carrier
  cover : ∀ f (x : C.Cell f), ∃ g, ∃ y : D.Cell g,
    parent g = f ∧ place g y.val = x.val

namespace Subdivision

variable {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  (S : Subdivision C D)

def parentCell (g : Child) (y : D.Cell g) : C.Cell (S.parent g) :=
  ⟨S.place g y.val, S.inside g y.val y.property⟩

def parentPoint (a : D.Total) : C.Total := ⟨S.parent a.1, S.parentCell a.1 a.2⟩

theorem parentCell_isometry (g : Child) : Isometry (S.parentCell g) :=
  (S.place g).isometry.comp isometry_subtype_coe

theorem parentPoint_eq {g : Child} {f : Face} {y : D.Cell g} {x : C.Cell f}
    (parent : S.parent g = f) (point : S.place g y.val = x.val) :
    S.parentPoint ⟨g, y⟩ = ⟨f, x⟩ := by
  subst f
  exact congrArg (Sigma.mk (S.parent g)) (Subtype.ext point)

theorem parentPoint_surjective : Function.Surjective S.parentPoint := by
  rintro ⟨f, x⟩
  obtain ⟨g, y, parent, point⟩ := S.cover f x
  exact ⟨⟨g, y⟩, S.parentPoint_eq parent point⟩

/-- The actual fine seam chains agree with the old seam chains under the placements. -/
structure Conforming (retain : Set C.Seam) (fineRetain : Set D.Seam) : Prop where
  respects : ∀ a b, D.glue fineRetain a b →
    Relation.EqvGen (C.glue retain) (S.parentPoint a) (S.parentPoint b)
  lifts : ∀ a b, Relation.EqvGen (C.glue retain) (S.parentPoint a) (S.parentPoint b) →
    Relation.EqvGen (D.glue fineRetain) a b

theorem cellMap_lipschitz (retain : Set C.Seam) (g : Child) :
    LipschitzWith 1 (fun y => C.faceMap retain (S.parent g) (S.parentCell g y)) := by
  intro x y
  have bound := (C.faceMap_lipschitz retain (S.parent g)).edist_le_mul
    (S.parentCell g x) (S.parentCell g y)
  simpa only [ENNReal.coe_one, one_mul, S.parentCell_isometry g x y] using bound

namespace Conforming

variable {S} {retain : Set C.Seam} {fineRetain : Set D.Seam}
  (H : S.Conforming retain fineRetain)

include H in
theorem related_iff (a b : D.Total) :
    Relation.EqvGen (D.glue fineRetain) a b ↔
      Relation.EqvGen (C.glue retain) (S.parentPoint a) (S.parentPoint b) := by
  refine ⟨?_, H.lifts a b⟩
  intro related
  induction related with
  | rel a b step => exact H.respects a b step
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ first last => exact Relation.EqvGen.trans _ _ _ first last

def toCoarse : D.Realization fineRetain → C.Realization retain :=
  MetricGluing.lift D.Cell (D.glue fineRetain)
    (fun g y => C.faceMap retain (S.parent g) (S.parentCell g y))
    (S.cellMap_lipschitz retain)
    (fun a b joined => (C.point_eq_iff retain _ _).mpr (H.respects a b joined))

@[simp] theorem toCoarse_faceMap (g : Child) (y : D.Cell g) :
    H.toCoarse (D.faceMap fineRetain g y) =
      C.faceMap retain (S.parent g) (S.parentCell g y) := rfl

theorem toCoarse_lipschitz : LipschitzWith 1 H.toCoarse :=
  MetricGluing.lift_lipschitz D.Cell (D.glue fineRetain) _
    (S.cellMap_lipschitz retain) _

theorem toCoarse_injective : Function.Injective H.toCoarse := by
  intro x y equal
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue fineRetain) x
  obtain ⟨b, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue fineRetain) y
  exact (D.point_eq_iff fineRetain a b).mpr
    (H.lifts a b ((C.point_eq_iff retain _ _).mp equal))

theorem toCoarse_surjective : Function.Surjective H.toCoarse := by
  intro x
  obtain ⟨a, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  obtain ⟨b, rfl⟩ := S.parentPoint_surjective a
  exact ⟨MetricGluing.point D.Cell (D.glue fineRetain) b, rfl⟩

end Conforming
end Subdivision
end Unfoldings.TriangleComplex
