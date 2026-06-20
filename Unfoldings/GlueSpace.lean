import Mathlib

/-!
# N-ary metric gluing scaffold

This file packages a family version of `Metric.GlueSpace`.

The genuinely hard part of a general n-ary metric gluing is constructing the
right pseudometric on the disjoint union.  Here we separate that concern from
the quotient API: `Data` records the pieces and their declared overlaps, while
`MetricData` records a pseudometric on the disjoint union with the expected
restriction and zero-identification properties.  The final `Space` is the
separation quotient of that pseudometric, hence a genuine metric space.
-/

noncomputable section

namespace Unfoldings
namespace GlueSpace

universe u v w z

/--
N-ary metric gluing data.

`I` indexes the spaces to be glued.  `J` indexes overlap charts.  For each
`j : J`, `Param j` is a common metric space that maps isometrically into two
pieces, at indices `left j` and `right j`.
-/
structure Data where
  /-- Index type for the spaces to be glued. -/
  I : Type u
  /-- The metric spaces to glue. -/
  E : I → Type v
  [metricSpace : ∀ i, MetricSpace (E i)]
  /-- Index type for declared overlap charts. -/
  J : Type w
  /-- First incident space of an overlap chart. -/
  left : J → I
  /-- Second incident space of an overlap chart. -/
  right : J → I
  /-- Common parameter space for an overlap chart. -/
  Param : J → Type z
  [paramMetricSpace : ∀ j, MetricSpace (Param j)]
  /-- Parametrization into the first incident space. -/
  leftMap : ∀ j, Param j → E (left j)
  /-- Parametrization into the second incident space. -/
  rightMap : ∀ j, Param j → E (right j)
  /-- The first parametrization is isometric. -/
  left_isometry : ∀ j, Isometry (leftMap j)
  /-- The second parametrization is isometric. -/
  right_isometry : ∀ j, Isometry (rightMap j)

attribute [instance] Data.metricSpace
attribute [instance] Data.paramMetricSpace

namespace Data

variable (D : Data.{u, v, w, z})

/-- The disjoint union of all spaces before quotienting by the gluing relation. -/
structure Total : Type (max u v) where
  /-- The component containing this point. -/
  index : D.I
  /-- The point inside its component. -/
  point : D.E index

end Data

/--
Metric realization data for an n-ary gluing datum.

This is the part that a future path-metric construction should produce
automatically.  The fields say that the pseudometric restricts to each original
piece and collapses each declared overlap chart.
-/
structure MetricData (D : Data.{u, v, w, z}) where
  /-- A pseudometric on the disjoint union before separation quotienting. -/
  [pseudoMetricSpaceTotal : PseudoMetricSpace D.Total]
  /-- Each original piece keeps its original metric inside the disjoint union. -/
  dist_mk_same : ∀ (i : D.I) (x y : D.E i),
    dist (Data.Total.mk i x : D.Total) (Data.Total.mk i y) = dist x y
  /-- Declared overlap points are at pseudodistance zero. -/
  dist_glued : ∀ (j : D.J) (z : D.Param j),
    dist (Data.Total.mk (D.left j) (D.leftMap j z) : D.Total)
      (Data.Total.mk (D.right j) (D.rightMap j z)) = 0

attribute [instance] MetricData.pseudoMetricSpaceTotal

/-- The metric space obtained by quotienting the glued pseudometric. -/
abbrev Space (D : Data.{u, v, w, z}) (_M : MetricData D) : Type (max u v) :=
  @SeparationQuotient D.Total _M.pseudoMetricSpaceTotal.toUniformSpace.toTopologicalSpace

instance (D : Data.{u, v, w, z}) (M : MetricData D) : MetricSpace (Space D M) := by
  infer_instance

/-- The canonical map from one piece into the glued metric space. -/
def of (D : Data.{u, v, w, z}) (M : MetricData D) (i : D.I) (x : D.E i) : Space D M :=
  Quotient.mk'' (Data.Total.mk i x : D.Total)

@[simp]
theorem dist_of_of (D : Data.{u, v, w, z}) (M : MetricData D) (i : D.I) (x y : D.E i) :
    dist (of D M i x) (of D M i y) = dist x y := by
  letI : PseudoMetricSpace D.Total := M.pseudoMetricSpaceTotal
  have h :
      dist ((SeparationQuotient.mk (Data.Total.mk i x : D.Total) : Space D M))
        (SeparationQuotient.mk (Data.Total.mk i y : D.Total)) =
          dist (Data.Total.mk i x : D.Total) (Data.Total.mk i y) :=
    SeparationQuotient.dist_mk (Data.Total.mk i x : D.Total) (Data.Total.mk i y)
  simpa [of, M.dist_mk_same i x y] using h

/-- Each original piece maps isometrically into the glued metric space. -/
theorem isometry_of (D : Data.{u, v, w, z}) (M : MetricData D) (i : D.I) :
    Isometry (of D M i) :=
  Isometry.of_dist_eq fun x y => dist_of_of D M i x y

/-- Declared overlap points become equal in the glued metric space. -/
theorem of_glued_eq (D : Data.{u, v, w, z}) (M : MetricData D) (j : D.J) (z : D.Param j) :
    of D M (D.left j) (D.leftMap j z) =
      of D M (D.right j) (D.rightMap j z) := by
  letI : PseudoMetricSpace D.Total := M.pseudoMetricSpaceTotal
  change (SeparationQuotient.mk
    (Data.Total.mk (D.left j) (D.leftMap j z) : D.Total) : Space D M) =
    SeparationQuotient.mk (Data.Total.mk (D.right j) (D.rightMap j z) : D.Total)
  refine SeparationQuotient.mk_eq_mk.2 (Metric.inseparable_iff.2 ?_)
  exact M.dist_glued j z

end GlueSpace
end Unfoldings
