module

public import Unfoldings.Complex.Classes
public import Unfoldings.Metric.ClosedSeams

/-!
# Exact metric realizations of finite triangle complexes

The constructed metric identifies exactly finite chains of retained seams.
In particular, its topology agrees with the quotient topology of the closed
triangular cells. These conclusions need no manifold or development hypothesis.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Retained whole-edge pairings form a finite closed isometric seam system. -/
def closedSeams (retain : Set C.Seam) : MetricGluing.ClosedSeams C.Cell where
  Seam := retain
  Domain := fun s => (C.triangle (C.left s.val).face).Edge (C.left s.val).edge
  left := fun s => (C.left s.val).face
  right := fun s => (C.right s.val).face
  toLeft := fun s => (C.triangle (C.left s.val).face).edgeMap (C.left s.val).edge
  toRight := fun s => (C.triangle (C.right s.val).face).edgeMap (C.right s.val).edge ∘
    C.identify s.val
  left_isometry := fun s => (C.triangle (C.left s.val).face).edgeMap_isometry _
  right_isometry := fun s => ((C.triangle (C.right s.val).face).edgeMap_isometry _).comp
    (C.identify s.val).isometry
  left_closed := fun s => (isCompact_range
    ((C.triangle (C.left s.val).face).edgeMap_isometry _).continuous).isClosed
  right_closed := fun s => (isCompact_range
    (((C.triangle (C.right s.val).face).edgeMap_isometry _).continuous.comp
      (C.identify s.val).continuous)).isClosed

theorem closedSeams_relation (retain : Set C.Seam) :
    (C.closedSeams retain).relation = C.glue retain := by
  funext a b
  apply propext
  constructor
  · rintro ⟨⟨s, hs⟩, x, ha, hb⟩
    exact ⟨s, hs, x, ha, hb⟩
  · rintro ⟨s, hs, x, ha, hb⟩
    exact ⟨⟨s, hs⟩, x, ha, hb⟩

/-- The separation quotient makes exactly the intended retained-seam identifications. -/
theorem exact (retain : Set C.Seam) : C.Exact retain := by
  have classes : ∀ a i,
      (MetricGluing.classIn C.Cell (C.closedSeams retain).relation a i).Finite := by
    simpa only [C.closedSeams_relation] using C.finite_classIn retain
  have result := (C.closedSeams retain).exact_of_finite_classes classes
  rw [C.closedSeams_relation] at result
  exact result

theorem point_eq_iff (retain : Set C.Seam) (a b : C.Total) :
    MetricGluing.point C.Cell (C.glue retain) a = MetricGluing.point C.Cell (C.glue retain) b ↔
      Relation.EqvGen (C.glue retain) a b :=
  MetricGluing.point_eq_iff_of_exact C.Cell (C.exact retain) a b

theorem faceMap_eq_iff (retain : Set C.Seam) (f g : Face) (x : C.Cell f) (y : C.Cell g) :
    C.faceMap retain f x = C.faceMap retain g y ↔
      Relation.EqvGen (C.glue retain) ⟨f, x⟩ ⟨g, y⟩ := C.point_eq_iff retain _ _

/-- An unconditional homeomorphism between the cell quotient and its route metric. -/
def realizationHomeomorph (retain : Set C.Seam) : C.SeamQuotient retain ≃ₜ C.Realization retain :=
  C.seamHomeomorph retain (C.exact retain)

@[simp] theorem realizationHomeomorph_seamPoint (retain : Set C.Seam) (a : C.Total) :
    C.realizationHomeomorph retain (MetricGluing.seamPoint C.Cell (C.glue retain) a) =
      MetricGluing.point C.Cell (C.glue retain) a := rfl

end Unfoldings.TriangleComplex
