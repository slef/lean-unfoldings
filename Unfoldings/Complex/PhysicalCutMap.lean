module

public import Unfoldings.Complex.PhysicalCutClasses
public import Unfoldings.Metric.PolygonalCutIsometricImage

/-! Original triangle-complex copies recovered from actual closed physical cut attachments. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

/-- Each original rigid face and its literal spatial triangle have the same metric. -/
def faceImageIsometryEquiv (f : Face) : C.Cell f ≃ᵢ F.faceImage f :=
  MetricGluing.isometricImageCell (fun f => (C.triangle f).carrier)
    (F.place f) (F.place f).isometry f

/-- Recover the specified original cut face copy from its actual physical triangle. -/
@[macro_inline] def faceImageComplexMap (retain : Set C.Seam) (f : Face) (x : F.faceImage f) :
    C.Realization retain := C.faceMap retain f ((F.faceImageIsometryEquiv f).symm x)

theorem faceImageComplexMap_isometry (retain : Set C.Seam) (f : Face) :
    Isometry (F.faceImageComplexMap retain f) :=
  (F.faceMap_isometry retain f).comp (F.faceImageIsometryEquiv f).symm.isometry

theorem toSpace_faceImageComplexMap (retain : Set C.Seam) (f : Face) (x : F.faceImage f) :
    F.toSpace retain (F.faceImageComplexMap retain f x) = x.val :=
  congrArg Subtype.val ((F.faceImageIsometryEquiv f).apply_symm_apply x)

/-- The actual closed physical attachments of the original placed triangles. -/
def physicalCutSeams (cuts : Set Space) : MetricGluing.PhysicalSeams F.faceImage :=
  MetricGluing.cutSeams F.faceImage (fun f => (F.compact_faceImage f).isClosed) cuts

abbrev PhysicalCut (cuts : Set Space) :=
  MetricGluing.Realization (fun f => F.faceImage f) (F.physicalCutSeams cuts).relation

/-- Agreement at uncut physical points extends to each separately closed physical attachment. -/
theorem faceImageComplexMap_eq_on_carrier (embedded : F.IsEmbedded)
    (retain : Set C.Seam) (cuts : Set Space)
    (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      F.place (C.left s).face x.val ∈ cuts)
    (f g : Face) (z : Space) (member : z ∈ (F.physicalCutSeams cuts).carrier f g) :
    F.faceImageComplexMap retain f
      ⟨z, (F.physicalCutSeams cuts).subset_left f g member⟩ =
      F.faceImageComplexMap retain g
        ⟨z, (F.physicalCutSeams cuts).subset_right f g member⟩ := by
  let U := F.faceImage f ∩ F.faceImage g
  let left (p : U) := F.faceImageComplexMap retain f ⟨p.val, p.property.1⟩
  let right (p : U) := F.faceImageComplexMap retain g ⟨p.val, p.property.2⟩
  have left_bound : LipschitzWith 1 left := fun p q =>
    (F.faceImageComplexMap_isometry retain f).lipschitzWith _ _
  have right_bound : LipschitzWith 1 right := fun p q =>
    (F.faceImageComplexMap_isometry retain g).lipschitzWith _ _
  let uncut : Set U := {p | p.val ∉ cuts}
  have same : Set.EqOn left right uncut := by
    intro p outside
    apply F.faceMap_eq_of_spatial_eq_outside embedded retain cuts removed
    · exact (F.toSpace_faceImageComplexMap retain f ⟨p.val, p.property.1⟩).trans
        (F.toSpace_faceImageComplexMap retain g ⟨p.val, p.property.2⟩).symm
    · exact Eq.mpr (congrArg (fun z : Space => z ∉ cuts)
        (F.toSpace_faceImageComplexMap retain f ⟨p.val, p.property.1⟩)) outside
  let point : U := ⟨z, (F.physicalCutSeams cuts).subset_left f g member,
    (F.physicalCutSeams cuts).subset_right f g member⟩
  have image : Subtype.val '' uncut = (F.faceImage f ∩ F.faceImage g) \ cuts := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.property, hq⟩
    · intro hp
      exact ⟨⟨p, hp.1⟩, hp.2, rfl⟩
  have near : point ∈ closure uncut := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change z ∈ closure (Subtype.val '' uncut)
    rw [image]
    exact member
  exact same.closure left_bound.continuous right_bound.continuous near

/-- Recover original retained copies from the actual physical cut, without a seam certificate. -/
def physicalCutToComplex (embedded : F.IsEmbedded) (retain : Set C.Seam) (cuts : Set Space)
    (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      F.place (C.left s).face x.val ∈ cuts) : F.PhysicalCut cuts → C.Realization retain :=
  MetricGluing.lift (fun f => F.faceImage f) (F.physicalCutSeams cuts).relation
    (F.faceImageComplexMap retain)
    (fun f => (F.faceImageComplexMap_isometry retain f).lipschitzWith)
    (by
      rintro a b ⟨⟨f, g⟩, x, rfl, rfl⟩
      exact F.faceImageComplexMap_eq_on_carrier embedded retain cuts removed f g x.val x.property)

theorem physicalCutToComplex_lipschitz (embedded : F.IsEmbedded) (retain : Set C.Seam)
    (cuts : Set Space)
    (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      F.place (C.left s).face x.val ∈ cuts) :
    LipschitzWith 1 (F.physicalCutToComplex embedded retain cuts removed) :=
  MetricGluing.lift_lipschitz _ _ _ _ _

@[simp] theorem physicalCutToComplex_of (embedded : F.IsEmbedded) (retain : Set C.Seam)
    (cuts : Set Space)
    (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      F.place (C.left s).face x.val ∈ cuts) (f : Face) (x : F.faceImage f) :
    F.physicalCutToComplex embedded retain cuts removed
      (MetricGluing.of (fun f => F.faceImage f) (F.physicalCutSeams cuts).relation f x) =
        F.faceImageComplexMap retain f x := rfl

/-- The recovered original metric copy folds to exactly its original physical point. -/
theorem toSpace_physicalCutToComplex (embedded : F.IsEmbedded) (retain : Set C.Seam)
    (cuts : Set Space)
    (removed : ∀ s, s ∉ retain → ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      F.place (C.left s).face x.val ∈ cuts) (x : F.PhysicalCut cuts) :
    F.toSpace retain (F.physicalCutToComplex embedded retain cuts removed x) =
      (F.physicalCutSeams cuts).fold x := by
  obtain ⟨⟨f, p⟩, rfl⟩ := MetricGluing.point_surjective (fun f => F.faceImage f)
    (F.physicalCutSeams cuts).relation x
  exact F.toSpace_faceImageComplexMap retain f p

end Unfoldings.SpatialFolding
