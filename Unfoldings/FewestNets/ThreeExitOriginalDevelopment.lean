module

public import Unfoldings.FewestNets.ThreeExitOriginalFaceLift
public import Unfoldings.Roof.LabeledCutLayout
public import Unfoldings.Development.NetPartition

/-! A three-exit layout supplies an original-edge net with the exact retained seams. -/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)
  (M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel)

local notation "U" => K.selectionComponent slopes seed

open Classical in
set_option maxHeartbeats 1550000 in
-- Keep the original and restricted seam names definitionally synchronized.
/-- A faithful layout of the whole physical three-exit cut, locally rigid off
the cut, certifies a net of the unrefined input triangles. -/
theorem hasOriginalEdgeNet_of_whole_cut_layout (selected : K.normalSlope seed ∈ slopes)
    (W : R.WholeCutModel M) (layout : W.Cut → Plane) (continuous_layout : Continuous layout)
    (faithful : ∀ x y, layout x = layout y →
      (W.partition.restoreCut R.wholeCarrier x).val = (W.partition.restoreCut R.wholeCarrier y).val)
    (local_layout : ∀ x : W.Cut,
      Cap.horizontal (W.partition.restoreCut R.wholeCarrier x).val ∉ R.wholeCarrier →
        ∃ r > 0, Isometry (fun y : Metric.eball x (ENNReal.ofReal r) => layout y.val)) :
    C.HasOriginalEdgeNet U := by
  classical
  let retain : Set (C.restrictFaces U).Seam :=
    {s | s.val ∉ Set.range R.stems.toThreeExitComponentChoices.edge}
  refine ⟨retain, R.stems.toThreeExitComponentChoices.cut_disk B.convex compact.isClosed selected, ?_⟩
  refine K.exists_development_of_labeled_cut_layout U retain
    (fun x => (W.partition.restoreCut R.wholeCarrier x).val) R.wholeCarrier layout continuous_layout
    faithful ?_ local_layout ?_ ?_ ?_
  · intro x y equal outside
    exact W.partition.restoreCut_injective_at R.wholeCarrier (PolygonalPoint.ext equal) outside
  · intro f
    exact R.exists_original_face_lift M W f.val f.property selected
  · intro f x inside
    apply R.wholeCarrier_avoids_original_face_interior f.val f.property
    have image : (K.projectFaceHomeomorph f.val) '' (C.triangle f.val).carrier =
        (K.projectedTriangle f.val).carrier :=
      ((C.triangle f.val).affineImage_carrier (K.projectFace f.val) (K.projectFace_injective f.val)).symm
    rw [← image, ← Homeomorph.image_interior]
    exact ⟨x, inside, rfl⟩
  · intro s kept x nonvertex
    exact R.wholeCarrier_avoids_open_retained_seam s.val kept s.property.1 x nonvertex

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
