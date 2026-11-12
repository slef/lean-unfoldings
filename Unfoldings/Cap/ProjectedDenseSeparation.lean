module

public import Unfoldings.Cap.ProjectedInteriorCoherence
public import Unfoldings.Cap.SectorWaterfallRegular
public import Unfoldings.Topology.DenseChartSeparation

/-! Injectivity away from waterfall walls separates actual developed face interiors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

/-- Actual affine face charts carry physical interiors to developed interiors. -/
theorem projectedPlacement_image_interior (f : Face) :
    D.projectedPlacement K f '' interior (K.projectedTriangle f).carrier =
      interior (D.faceImage f) := by
  let chart := (D.projectedPlacement K f).toContinuousAffineEquiv.toHomeomorph
  have carrier : chart '' (K.projectedTriangle f).carrier = D.faceImage f := by
    change D.projectedPlacement K f '' (K.projectedTriangle f).carrier = D.faceImage f
    simp only [ConvexCap.projectedTriangle, Triangle.affineImage_carrier,
      Set.image_image, D.projectedPlacement_apply, faceImage]
  exact (chart.image_interior _).trans (congrArg interior carrier)

/-- Open overlap cannot be confined to omitted physical walls, including
artificial subdivision walls passing through an original face. -/
theorem projected_face_interiors_disjoint_of_dense_injective {A U : Set Plane}
    (opened : IsOpen A) (dense : Dense A) (region_open : IsOpen U)
    (injective : Set.InjOn (D.projectedMap K) (A ∩ U)) {f g : Face} (different : f ≠ g) :
    Disjoint (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩ U))
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩ U)) := by
  let chart (f : Face) := (D.projectedPlacement K f).toContinuousAffineEquiv.toHomeomorph
  have restricted : Set.InjOn (D.projectedMap K)
      (A ∩ ((interior (K.projectedTriangle f).carrier ∩ U) ∪
        (interior (K.projectedTriangle g).carrier ∩ U))) := by
    intro p first q last equal
    exact injective ⟨first.1, first.2.elim And.right And.right⟩
      ⟨last.1, last.2.elim And.right And.right⟩ equal
  exact disjoint_homeomorph_images_of_dense_injective (chart f) (chart g) opened dense
    (isOpen_interior.inter region_open) (isOpen_interior.inter region_open)
    ((K.projectedTriangles_nonoverlapping different).mono
      Set.inter_subset_left Set.inter_subset_left)
    (fun _ member => D.projectedMap_eq_on_face_interior K member.1)
    (fun _ member => D.projectedMap_eq_on_face_interior K member.1) restricted

theorem nonoverlapping_of_projected_dense_injective {A : Set Plane}
    (opened : IsOpen A) (dense : Dense A) (injective : Set.InjOn (D.projectedMap K) A) :
    D.Nonoverlapping := by
  intro f g different
  have separate := D.projected_face_interiors_disjoint_of_dense_injective K opened dense
    isOpen_univ (injective.mono Set.inter_subset_left) different
  simpa only [Set.inter_univ, D.projectedPlacement_image_interior K] using separate

/-- It suffices to establish global injectivity on the actual regular waterfall
points in the controlled sweep. This does not assume nonoverlap of face images. -/
theorem projected_face_interiors_disjoint_of_waterfall_injective
    {t : ℝ} (positive : 0 < t) (small : t < 1) (source : Plane)
    (P : ∀ i : FiveSector, (fiveSectorFrame t positive small i).enclosingStrip.Subdivision)
    (cutoff : ℝ)
    (injective : Set.InjOn (D.projectedMap K)
      (sectorWaterfallRegular positive small source P ∩
        sectorSweepInterior positive small source cutoff))
    {f g : Face} (different : f ≠ g) :
    Disjoint (D.projectedPlacement K f '' (interior (K.projectedTriangle f).carrier ∩
      sectorSweepInterior positive small source cutoff))
      (D.projectedPlacement K g '' (interior (K.projectedTriangle g).carrier ∩
        sectorSweepInterior positive small source cutoff)) :=
  D.projected_face_interiors_disjoint_of_dense_injective K
    (isOpen_sectorWaterfallRegular positive small source P)
    (dense_sectorWaterfallRegular positive small source P)
    (isOpen_sectorSweepInterior positive small source cutoff) injective different

end Unfoldings.FacewiseDevelopment
