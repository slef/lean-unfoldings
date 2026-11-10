module

public import Unfoldings.Complex.RefinedCuts
public import Unfoldings.Complex.RelativeCutForest
public import Unfoldings.Development.FlatDisk

/-!
# Polygonal cut presentations carried by conforming refinements

New cuts may use internal subdivision edges of original faces. A presentation
specifies the actual retained fine seams and their uncut conforming surface.
Forest and flatness conditions are separate hypotheses, never conclusions
stored in the presentation. Developing maps may overlap.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex.Subdivision

universe u v w z

variable {Face : Type u} [Fintype Face] {Child : Type w} [Fintype Child]
  {C : TriangleComplex.{u, v} Face} {D : TriangleComplex.{w, z} Child}
  (S : C.Subdivision D)

/-- A cut through refined faces, with its original uncut metric identified by seam conformity. -/
structure CutPresentation (base : Set C.Seam) where
  uncut : Set D.Seam
  conforms : S.Conforming base uncut
  retain : Set D.Seam
  inclusion : retain ⊆ uncut

namespace CutPresentation

variable {S} {base : Set C.Seam} (P : S.CutPresentation base)

abbrev Surface := D.Realization P.retain

/-- Restoring only the new cuts projects to the original, possibly already cut surface. -/
def projection : P.Surface → C.Realization base :=
  fun x => P.conforms.metricEquiv (D.forgetCuts P.inclusion x)

@[simp] theorem projection_faceMap (g : Child) (x : D.Cell g) :
    P.projection (D.faceMap P.retain g x) =
      C.faceMap base (S.parent g) (S.parentCell g x) := rfl

theorem projection_lipschitz : LipschitzWith 1 P.projection := by
  intro x y
  change edist (P.conforms.metricEquiv _) (P.conforms.metricEquiv _) ≤ _
  rw [P.conforms.metricEquiv.isometry.edist_eq]
  exact (D.forgetCuts_lipschitz P.inclusion).edist_le_mul x y

theorem projection_surjective : Function.Surjective P.projection :=
  P.conforms.metricEquiv.surjective.comp (D.forgetCuts_surjective P.inclusion)

/-- The newly cut polygonal segments form a forest with exactly one old boundary root per tree. -/
def IsRootedForest : Prop :=
  (D.relativeCutGraph P.retain P.uncut).IsRootedForest (D.relativeCutRoots P.uncut)

/-- The old disk transported to the actual uncut fine metric. -/
def uncutDisk (disk : C.Realization base ≃ₜ Metric.closedBall (0 : Plane) 1) :
    D.Realization P.uncut ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  P.conforms.metricEquiv.toHomeomorph.trans disk

variable (F : SpatialFolding C) (H : S.Conforming Set.univ Set.univ)

include F H in
/-- The rooted-forest iff disk criterion applies to cuts through original face interiors. -/
theorem disk_iff_rootedForest (disk : C.Realization base ≃ₜ Metric.closedBall (0 : Plane) 1) :
    Nonempty (P.Surface ≃ₜ Metric.closedBall (0 : Plane) 1) ↔ P.IsRootedForest :=
  (F.subdivide S H).cutDisk_iff_rootedForest P.inclusion (P.uncutDisk disk)

/-- Construct the actual new cut disk from its polygonal rooted forest. -/
def diskOfRootedForest (disk : C.Realization base ≃ₜ Metric.closedBall (0 : Plane) 1)
    (forest : P.IsRootedForest) : P.Surface ≃ₜ Metric.closedBall (0 : Plane) 1 :=
  Classical.choice ((P.disk_iff_rootedForest F H disk).mpr forest)

theorem spatial_projection (x : P.Surface) :
    F.toSpace base (P.projection x) = (F.subdivide S H).toSpace P.retain x := by
  obtain ⟨⟨g, y⟩, rfl⟩ := MetricGluing.point_surjective D.Cell (D.glue P.retain) x
  rfl

include F H in
/-- Once the new interior is flat, prescribe one face and obtain exactly one outward development. -/
theorem existsUnique_development (disk : C.Realization base ≃ₜ Metric.closedBall (0 : Plane) 1)
    (forest : P.IsRootedForest)
    (flat : ∀ vertex : D.Vertex P.retain, ¬ D.IsBoundaryVertex P.retain vertex →
      D.totalAngle P.retain vertex = 2 * Real.pi)
    (root : Child) (target : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃! E : FacewiseDevelopment D P.retain, E.place root = target :=
  (F.subdivide S H).existsUnique_normalized_development_of_flat_disk P.retain
    (P.diskOfRootedForest F H disk forest) flat root target


include F H in
/-- The normalized map is locally isometric at flat interior vertices as well as on faces. -/
theorem existsUnique_isometric_development
    (disk : C.Realization base ≃ₜ Metric.closedBall (0 : Plane) 1)
    (forest : P.IsRootedForest)
    (flat : ∀ vertex : D.Vertex P.retain, ¬ D.IsBoundaryVertex P.retain vertex →
      D.totalAngle P.retain vertex = 2 * Real.pi)
    (root : Child) (target : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃! E : FacewiseDevelopment D P.retain, E.place root = target ∧
      ∀ x, ‖(P.diskOfRootedForest F H disk forest x).val‖ < 1 → ∃ r > 0,
        Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => E.toPlane y.val) :=
  (F.subdivide S H).existsUnique_normalized_isometric_development_of_flat_disk P.retain
    (P.diskOfRootedForest F H disk forest) flat root target

end CutPresentation
end Unfoldings.TriangleComplex.Subdivision
