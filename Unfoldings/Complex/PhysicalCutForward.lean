module

public import Unfoldings.Complex.PhysicalCutMap
public import Mathlib.Analysis.Convex.Topology

/-! Original retained edges generate actual physical cut attachments, including endpoints. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

/-- The literal open spatial segment of an original paired edge. -/
def openSeamImage (s : C.Seam) : Set Space :=
  openSegment ℝ
    (F.place (C.left s).face ((C.triangle (C.left s).face).vertex (C.left s).edge))
    (F.place (C.left s).face ((C.triangle (C.left s).face).vertex (Triangle.next (C.left s).edge)))

/-- An uncut open original edge supplies its full separately closed physical attachment.
Endpoint copies are retained on their original sides by closure, not identified by coincidence. -/
theorem retained_edge_mem_physical_carrier (cuts : Set Space) (s : C.Seam)
    (uncut : Disjoint (F.openSeamImage s) cuts)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) :
    F.place (C.left s).face x.val ∈
      (F.physicalCutSeams cuts).carrier (C.left s).face (C.right s).face := by
  let f := (C.left s).face
  let e := (C.left s).edge
  let p := F.place f ((C.triangle f).vertex e)
  let q := F.place f ((C.triangle f).vertex (Triangle.next e))
  have image : F.place f '' (C.triangle f).edge e = segment ℝ p q :=
    image_segment ℝ (F.place f).toAffineMap _ _
  have both : F.place f '' (C.triangle f).edge e ⊆
      F.faceImage f ∩ F.faceImage (C.right s).face := by
    rintro z ⟨w, hw, rfl⟩
    refine ⟨⟨w, (C.triangle f).edge_subset e hw, rfl⟩, ?_⟩
    refine ⟨(C.identify s ⟨w, hw⟩).val,
      (C.triangle (C.right s).face).edge_subset _ (C.identify s ⟨w, hw⟩).property, ?_⟩
    exact (F.joined s ⟨w, hw⟩).symm
  have member : F.place f x.val ∈ segment ℝ p q :=
    Eq.mp (congrArg (fun t : Set Space => F.place f x.val ∈ t) image) ⟨x.val, x.property, rfl⟩
  have approached := segment_subset_closure_openSegment member
  change F.place f x.val ∈ closure ((F.faceImage f ∩ F.faceImage (C.right s).face) \ cuts)
  apply closure_mono ?_ approached
  intro z inside
  have in_segment : z ∈ segment ℝ p q := openSegment_subset_segment ℝ p q inside
  have in_edge : z ∈ F.place f '' (C.triangle f).edge e :=
    Eq.mpr (congrArg (fun t : Set Space => z ∈ t) image) in_segment
  exact ⟨both in_edge, fun cut => Set.disjoint_left.mp uncut inside cut⟩

/-- The specified original face copy in the actual physical cut metric. -/
@[macro_inline] def faceMapToPhysicalCut (cuts : Set Space) (f : Face) (x : C.Cell f) :
    F.PhysicalCut cuts :=
  MetricGluing.of (fun f => F.faceImage f) (F.physicalCutSeams cuts).relation f
    (F.faceImageIsometryEquiv f x)

theorem faceMapToPhysicalCut_isometry (cuts : Set Space) (f : Face) :
    Isometry (F.faceMapToPhysicalCut cuts f) :=
  ((F.physicalCutSeams cuts).of_isometry f).comp (F.faceImageIsometryEquiv f).isometry

/-- Actual retained original edge pairings agree in the physical cut. -/
theorem faceMapToPhysicalCut_compatible (retain : Set C.Seam) (cuts : Set Space)
    (retained : ∀ s ∈ retain, Disjoint (F.openSeamImage s) cuts)
    (a b : C.Total) (joined : C.glue retain a b) :
    F.faceMapToPhysicalCut cuts a.1 a.2 = F.faceMapToPhysicalCut cuts b.1 b.2 := by
  obtain ⟨s, hs, x, rfl, rfl⟩ := joined
  apply MetricGluing.point_eq_of_glue
  apply ((F.physicalCutSeams cuts).relation_iff _ _).mpr
  exact ⟨F.joined s x, F.retained_edge_mem_physical_carrier cuts s (retained s hs) x⟩

/-- Canonically send the original retained triangle complex to the actual physical cut. -/
def complexToPhysicalCut (retain : Set C.Seam) (cuts : Set Space)
    (retained : ∀ s ∈ retain, Disjoint (F.openSeamImage s) cuts) :
    C.Realization retain → F.PhysicalCut cuts :=
  MetricGluing.lift C.Cell (C.glue retain) (F.faceMapToPhysicalCut cuts)
    (fun f => (F.faceMapToPhysicalCut_isometry cuts f).lipschitzWith)
    (F.faceMapToPhysicalCut_compatible retain cuts retained)

theorem complexToPhysicalCut_lipschitz (retain : Set C.Seam) (cuts : Set Space)
    (retained : ∀ s ∈ retain, Disjoint (F.openSeamImage s) cuts) :
    LipschitzWith 1 (F.complexToPhysicalCut retain cuts retained) :=
  MetricGluing.lift_lipschitz _ _ _ _ _

@[simp] theorem complexToPhysicalCut_faceMap (retain : Set C.Seam) (cuts : Set Space)
    (retained : ∀ s ∈ retain, Disjoint (F.openSeamImage s) cuts) (f : Face) (x : C.Cell f) :
    F.complexToPhysicalCut retain cuts retained (C.faceMap retain f x) =
      F.faceMapToPhysicalCut cuts f x := rfl

end Unfoldings.SpatialFolding
