module

public import Unfoldings.Complex.Paths
public import Unfoldings.Metric.Connected

/-!
# Connectivity and finite distances

Retained seams give a face-incidence relation, allowing loops and several
seams between the same pair of faces. Its equivalence closure expresses dual
connectivity, with no acyclicity requirement. Connected complexes have ordinary
intrinsic metrics and geodesics between all points.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Face incidence of the retained seams; only connectivity forgets their labels. -/
def FaceGlue (retain : Set C.Seam) (f g : Face) : Prop :=
  ∃ s ∈ retain, (C.left s).face = f ∧ (C.right s).face = g

/-- Retained face incidence is connected. Cycles and self-pairings are allowed. -/
def DuallyConnected (retain : Set C.Seam) : Prop :=
  ∀ f g, Relation.EqvGen (C.FaceGlue retain) f g

theorem faceRelated_of_glue {retain : Set C.Seam} {a b : C.Total}
    (joined : C.glue retain a b) : Relation.EqvGen (C.FaceGlue retain) a.1 b.1 := by
  obtain ⟨s, kept, x, rfl, rfl⟩ := joined
  exact Relation.EqvGen.rel _ _ ⟨s, kept, rfl, rfl⟩

theorem faceRelated_of_step_ne_top (retain : Set C.Seam) (a b : C.Total)
    (finite : MetricGluing.stepCost C.Cell (C.glue retain) a b ≠ ⊤) :
    Relation.EqvGen (C.FaceGlue retain) a.1 b.1 := by
  classical
  by_cases joined : C.glue retain a b ∨ C.glue retain b a
  · exact joined.elim (C.faceRelated_of_glue)
      (fun h => Relation.EqvGen.symm _ _ (C.faceRelated_of_glue h))
  · by_cases same : a.1 = b.1
    · rw [same]
      exact Relation.EqvGen.refl _
    · exact (finite (by simp [MetricGluing.stepCost, joined, MetricGluing.faceCost, same])).elim

theorem faceRelated_of_route_ne_top (retain : Set C.Seam) {a b : C.Total}
    (route : Route C.Total a b) (finite : route.length (MetricGluing.stepCost C.Cell
      (C.glue retain)) ≠ ⊤) : Relation.EqvGen (C.FaceGlue retain) a.1 b.1 := by
  induction route with
  | nil a => exact Relation.EqvGen.refl _
  | cons a b tail ih =>
    obtain ⟨first, rest⟩ := ENNReal.add_ne_top.mp finite
    exact Relation.EqvGen.trans _ _ _ (C.faceRelated_of_step_ne_top retain a b first) (ih rest)

/-- Finite metric distance cannot connect different retained face-incidence components. -/
theorem faceRelated_of_edist_ne_top (retain : Set C.Seam) (a b : C.Total)
    (finite : edist (MetricGluing.point C.Cell (C.glue retain) a)
      (MetricGluing.point C.Cell (C.glue retain) b) ≠ ⊤) :
    Relation.EqvGen (C.FaceGlue retain) a.1 b.1 := by
  have less : Route.distance (MetricGluing.stepCost C.Cell (C.glue retain)) a b < ⊤ :=
    lt_top_iff_ne_top.mpr finite
  obtain ⟨route, short⟩ := iInf_lt_iff.mp less
  exact C.faceRelated_of_route_ne_top retain route (ne_of_lt short)

theorem faceMap_edist_ne_top (retain : Set C.Seam) (f : Face) (x y : C.Cell f) :
    edist (C.faceMap retain f x) (C.faceMap retain f y) ≠ ⊤ := by
  have bound : edist (C.faceMap retain f x) (C.faceMap retain f y) ≤ edist x y := by
    simpa only [ENNReal.coe_one, one_mul] using (C.faceMap_lipschitz retain f).edist_le_mul x y
  exact ne_top_of_le_ne_top (edist_ne_top x y) bound

theorem finite_edist_of_faceGlue (retain : Set C.Seam) {f g : Face} (joined : C.FaceGlue retain f g)
    (x : C.Cell f) (y : C.Cell g) : edist (C.faceMap retain f x) (C.faceMap retain g y) ≠ ⊤ := by
  obtain ⟨s, kept, hf, hg⟩ := joined
  subst f
  subst g
  let z : (C.triangle (C.left s).face).Edge (C.left s).edge :=
    ⟨(C.triangle (C.left s).face).vertex (C.left s).edge, left_mem_segment ℝ _ _⟩
  let l := (C.triangle (C.left s).face).edgeMap (C.left s).edge z
  let r := (C.triangle (C.right s).face).edgeMap (C.right s).edge (C.identify s z)
  have same : C.faceMap retain (C.left s).face l = C.faceMap retain (C.right s).face r :=
    C.seam_identified retain s kept z
  apply finite_edist_trans (C.faceMap_edist_ne_top retain _ x l)
  rw [same]
  exact C.faceMap_edist_ne_top retain _ r y

theorem finite_edist_of_faceRelated (retain : Set C.Seam) {f g : Face}
    (related : Relation.EqvGen (C.FaceGlue retain) f g) : ∀ x : C.Cell f, ∀ y : C.Cell g,
      edist (C.faceMap retain f x) (C.faceMap retain g y) ≠ ⊤ := by
  induction related with
  | rel f g h => exact C.finite_edist_of_faceGlue retain h
  | refl f => exact C.faceMap_edist_ne_top retain f
  | symm f g h ih =>
    intro x y
    rw [edist_comm]
    exact ih y x
  | trans f g h hfg hgh ih₁ ih₂ =>
    intro x y
    let middle : C.Cell g := ⟨(C.triangle g).vertex 0, (C.triangle g).vertex_mem 0⟩
    exact finite_edist_trans (ih₁ x middle) (ih₂ middle y)

theorem edist_ne_top_of_duallyConnected (retain : Set C.Seam) (connected : C.DuallyConnected retain)
    (x y : C.Realization retain) : edist x y ≠ ⊤ := by
  obtain ⟨⟨f, x⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  obtain ⟨⟨g, y⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) y
  exact C.finite_edist_of_faceRelated retain (connected f g) x y

/-- The ordinary intrinsic metric on a connected complex, preserving its edistance and topology. -/
@[instance_reducible] def metricSpace (retain : Set C.Seam) (connected : C.DuallyConnected retain) :
    MetricSpace (C.Realization retain) :=
  EMetricSpace.toMetricSpace (C.edist_ne_top_of_duallyConnected retain connected)

theorem exists_geodesic_of_duallyConnected (retain : Set C.Seam)
    (connected : C.DuallyConnected retain)
    (x y : C.Realization retain) : ∃ p : Path x y, p.IsGeodesic :=
  C.exists_geodesic retain x y (C.edist_ne_top_of_duallyConnected retain connected x y)

theorem duallyConnected_iff_edist_ne_top (retain : Set C.Seam) : C.DuallyConnected retain ↔
    ∀ x y : C.Realization retain, edist x y ≠ ⊤ := by
  constructor
  · exact C.edist_ne_top_of_duallyConnected retain
  · intro finite f g
    let x : C.Cell f := ⟨(C.triangle f).vertex 0, (C.triangle f).vertex_mem 0⟩
    let y : C.Cell g := ⟨(C.triangle g).vertex 0, (C.triangle g).vertex_mem 0⟩
    exact C.faceRelated_of_edist_ne_top retain ⟨f, x⟩ ⟨g, y⟩ (finite _ _)

theorem duallyConnected_of_preconnected (retain : Set C.Seam)
    [PreconnectedSpace (C.Realization retain)] : C.DuallyConnected retain :=
  (C.duallyConnected_iff_edist_ne_top retain).mpr edist_ne_top_of_preconnected

end Unfoldings.TriangleComplex
