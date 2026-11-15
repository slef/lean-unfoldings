module

public import Unfoldings.Geometry.SpatialEnvelopeCut
public import Unfoldings.Geometry.EventualRayCell
public import Unfoldings.Metric.IsometricCells

/-! Exact lifts of complete terminal ray tails into the unbounded physical cut metric. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A]

/-- The actual retained cut metric has no shortcuts within a single rigid cell. -/
theorem cut_of_isometry (cuts : Set Plane) (a : A) :
    Isometry (MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a) := by
  apply MetricGluing.of_isometry_of_compatible (fun a => P.planarCell a) (P.cutGlue cuts)
    (fun a x => (family (P.support a)).place x.val)
  · intro b
    exact (family (P.support b)).place.isometry.comp isometry_subtype_coe
  · intro x y joined
    exact ((P.glue_iff x y).mp (P.cutGlue_subset cuts x y joined)).2

/-- A horizontal point in a specified physical cell gives its actual metric copy after cutting. -/
def liftCell (cuts : Set Plane) (a : A) (p : P.footprint a) : P.Cut cuts :=
  MetricGluing.of (fun a => P.planarCell a) (P.cutGlue cuts) a
    ⟨(family (P.support a)).project.symm p.val, p.val, p.property, rfl⟩

@[simp] theorem restoreCut_liftCell (cuts : Set Plane) (a : A) (p : P.footprint a) :
    (P.restoreCut cuts (P.liftCell cuts a p)).val = point family p.val := by
  exact (point_eq_place family (P.support a) (P.active a p.val p.property)).symm

/-- Distances between copies in one cell are exactly their spatial Euclidean distances. -/
theorem edist_liftCell (cuts : Set Plane) (a : A) (p q : P.footprint a) :
    edist (P.liftCell cuts a p) (P.liftCell cuts a q) =
      edist (point family p.val) (point family q.val) := by
  rw [point_eq_place family (P.support a) (P.active a p.val p.property),
    point_eq_place family (P.support a) (P.active a q.val q.property),
    (family (P.support a)).place.isometry.edist_eq]
  exact P.cut_of_isometry cuts a _ _

/-- Every whole horizontal ray eventually stays in an actual unbounded partition cell. -/
theorem exists_eventual_ray_cell (p d : Plane) :
    ∃ a : A, ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → p + t • d ∈ P.footprint a := by
  apply Unfoldings.exists_eventual_ray_cell P.footprint P.convex p d
  intro t _
  rw [P.cover]
  exact Set.mem_univ _

/-- The entire final ray tail, with no upper cutoff, lifted into its specified actual cut cell. -/
def liftRayTail (cuts : Set Plane) (a : A) (p d : Plane) (T : ℝ)
    (inside : ∀ t : ℝ, T ≤ t → p + t • d ∈ P.footprint a) :
    Set.Ici T → P.Cut cuts :=
  fun t => P.liftCell cuts a ⟨p + t.val • d, inside t.val t.property⟩

@[simp] theorem restoreCut_liftRayTail (cuts : Set Plane) (a : A) (p d : Plane) (T : ℝ)
    (inside : ∀ t : ℝ, T ≤ t → p + t • d ∈ P.footprint a) (t : Set.Ici T) :
    (P.restoreCut cuts (P.liftRayTail cuts a p d T inside t)).val =
      point family (p + t.val • d) :=
  P.restoreCut_liftCell cuts a _

/-- The cut does not shorten or stretch any pair of points on this whole spatial tail. -/
theorem edist_liftRayTail (cuts : Set Plane) (a : A) (p d : Plane) (T : ℝ)
    (inside : ∀ t : ℝ, T ≤ t → p + t • d ∈ P.footprint a) (s t : Set.Ici T) :
    edist (P.liftRayTail cuts a p d T inside s) (P.liftRayTail cuts a p d T inside t) =
      edist (point family (p + s.val • d)) (point family (p + t.val • d)) :=
  P.edist_liftCell cuts a _ _

end Unfoldings.SpatialEnvelope.WholePartition
