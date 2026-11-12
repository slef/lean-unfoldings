module

public import Unfoldings.Development.AdditionalCuts
public import Unfoldings.Complex.Folding
public import Unfoldings.Geometry.HingeConverse

/-! Restore coincident whole seam banks without changing any actual developed face placement. -/

@[expose] public section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain)

/-- Whole physical seam banks that already agree in the given development. -/
def coherentSeams : Set C.Seam :=
  {s | ∀ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
    D.place (C.left s).face x.val = D.place (C.right s).face (C.identify s x).val}

theorem retain_subset_coherentSeams : retain ⊆ D.coherentSeams := D.joined

/-- Nonoverlap supplies the strict opposite-side opening for every restored seam. -/
def restoreSeams (F : SpatialFolding C) (nonoverlap : D.Nonoverlapping)
    (large : Set C.Seam) (joined : large ⊆ D.coherentSeams) : FacewiseDevelopment C large where
  place := D.place
  joined := joined
  opposite s kept := (C.triangle (C.left s).face).placed_opposite_of_disjoint
    (C.triangle (C.right s).face) (C.left s).edge (C.right s).edge (C.identify s)
    (D.place (C.left s).face) (D.place (C.right s).face) (joined kept)
    (nonoverlap _ _ (F.incident_faces_ne s))

@[simp] theorem restoreSeams_place (F : SpatialFolding C) (nonoverlap : D.Nonoverlapping)
    (large : Set C.Seam) (joined : large ⊆ D.coherentSeams) (f : Face) :
    (D.restoreSeams F nonoverlap large joined).place f = D.place f := rfl

@[simp] theorem restoreSeams_nonoverlapping_iff (F : SpatialFolding C)
    (nonoverlap : D.Nonoverlapping) (large : Set C.Seam) (joined : large ⊆ D.coherentSeams) :
    (D.restoreSeams F nonoverlap large joined).Nonoverlapping ↔ D.Nonoverlapping := Iff.rfl

theorem restoreSeams_toPlane (F : SpatialFolding C) (nonoverlap : D.Nonoverlapping)
    (large : Set C.Seam) (joined : large ⊆ D.coherentSeams) (inclusion : retain ⊆ large)
    (x : C.Realization retain) :
    (D.restoreSeams F nonoverlap large joined).toPlane (C.forgetCuts inclusion x) =
      D.toPlane x := by
  obtain ⟨⟨f, y⟩, rfl⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) x
  change (D.restoreSeams F nonoverlap large joined).toPlane
    (C.forgetCuts inclusion (C.faceMap retain f y)) = D.toPlane (C.faceMap retain f y)
  rw [C.forgetCuts_faceMap, toPlane_faceMap, toPlane_faceMap, restoreSeams_place]

/-- Restore every coincident original seam bank; all placements remain the actual old ones. -/
def maximalRestoration (F : SpatialFolding C) (nonoverlap : D.Nonoverlapping) :
    FacewiseDevelopment C D.coherentSeams :=
  D.restoreSeams F nonoverlap D.coherentSeams Set.Subset.rfl

@[simp] theorem maximalRestoration_coherentSeams (F : SpatialFolding C)
    (nonoverlap : D.Nonoverlapping) :
    (D.maximalRestoration F nonoverlap).coherentSeams = D.coherentSeams := rfl

end Unfoldings.FacewiseDevelopment
