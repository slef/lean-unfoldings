module

public import Unfoldings.Cap.GeometricCutFlow
public import Unfoldings.Cap.GeometricLeafSweep
public import Unfoldings.Geometry.HeightSegmentNetwork

/-! Instantiate the forward-deterministic height network with actual geometric cut components. -/

@[expose] public section

noncomputable section

namespace Unfoldings

def centeredPlaneFrame (source : Plane) (frame : Plane ≃ₗᵢ[ℝ] ℂ) : Plane ≃ᵃ[ℝ] ℂ :=
  (AffineEquiv.constVAdd ℝ Plane (-source)).trans frame.toAffineIsometryEquiv.toAffineEquiv

@[simp] theorem centeredPlaneFrame_apply (source : Plane) (frame : Plane ≃ₗᵢ[ℝ] ℂ) (p : Plane) :
    centeredPlaneFrame source frame p = frame (p - source) := by
  change frame (-source + p) = frame (p - source)
  congr 1
  abel

namespace ConvexCap.SectorForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {t : ℝ} {origin : C.Vertex Set.univ} (M : K.SectorForest t origin)
  {Z : ℝ} (F : K.SkirtTailFamily Z (K.projectedVertex origin))
  (covered : ∀ w : C.Vertex Set.univ, C.IsBoundaryVertex Set.univ w →
    K.projectedVertex w ∈ ⋃ c : F.Component, (F.componentTail c).carrier)
  (positive : 0 < t) (small : t < 1) (lower : Z < 0)

abbrev GeometricComponentEdge (c : F.Component) := {w : F.GeometricVertex //
  w ∉ (M.geometricParents F covered positive small lower).roots ∧
    M.geometricComponent F covered w = c}

/-- The half-open uniqueness and positive height increment are proved from actual cut geometry. -/
def componentHeightNetwork (c : F.Component) (i : FiveSector)
    (directions : ∀ w : F.GeometricVertex,
      w ∉ (M.geometricParents F covered positive small lower).roots →
      M.geometricComponent F covered w = c →
        F.geometricPosition (M.geometricParent F covered w) - F.geometricPosition w ∈
          closedFiveSector t i) :
    HeightSegmentNetwork (M.GeometricComponentEdge F covered positive small lower c) where
  first e := centeredPlaneFrame (K.projectedVertex origin) (fiveSectorFrame t positive small
    i).place
    (F.geometricPosition e.val)
  last e := centeredPlaneFrame (K.projectedVertex origin) (fiveSectorFrame t positive small i).place
    (F.geometricPosition (M.geometricParent F covered e.val))
  ascending e := by
    have bound := M.geometricSweepHeight_parent_lt F covered positive small lower i e.val
      e.property.1 (directions e.val e.property.1 e.property.2)
    change (centeredPlaneFrame _ _ _).re + (centeredPlaneFrame _ _ _).im <
      (centeredPlaneFrame _ _ _).re + (centeredPlaneFrame _ _ _).im
    simpa only [centeredPlaneFrame_apply, geometricSweepHeight] using bound
  forward_unique := by
    intro a b x first first_not_end last last_not_end
    let A := centeredPlaneFrame (K.projectedVertex origin) (fiveSectorFrame t positive small
      i).place
    have pull {p q : Plane} (member : x ∈ segment ℝ (A p) (A q)) :
        A.symm x ∈ segment ℝ p q := by
      have image : A '' segment ℝ p q = segment ℝ (A p) (A q) :=
        image_segment ℝ A.toAffineMap p q
      obtain ⟨y, inside, equal⟩ := image.symm.subset member
      have inverse : y = A.symm x := (A.symm_apply_apply y).symm.trans (congrArg A.symm equal)
      exact inverse ▸ inside
    let ae : {w : F.GeometricVertex //
        w ∉ (M.geometricParents F covered positive small lower).roots} := ⟨a.val, a.property.1⟩
    let be : {w : F.GeometricVertex //
        w ∉ (M.geometricParents F covered positive small lower).roots} := ⟨b.val, b.property.1⟩
    have first_different : A.symm x ≠ F.geometricPosition (M.geometricParent F covered a.val) := by
      intro equal
      exact first_not_end (by simpa only [A.apply_symm_apply] using congrArg A equal)
    have last_different : A.symm x ≠ F.geometricPosition (M.geometricParent F covered b.val) := by
      intro equal
      exact last_not_end (by simpa only [A.apply_symm_apply] using congrArg A equal)
    have equal := M.geometric_halfOpen_parent_unique F covered positive small lower ae be
      (pull first) first_different (pull last) last_different
    have vertices : a.val = b.val :=
      congrArg (fun e : {w : F.GeometricVertex //
        w ∉ (M.geometricParents F covered positive small lower).roots} => e.val) equal
    exact Subtype.ext vertices

/-- Every actual geometric component supplies a finite network with a single forward edge.
The generic coalescence theorem can therefore be applied to its covered height graphs. -/
theorem exists_componentHeightNetwork (c : F.Component) :
    ∃ i : FiveSector, ∃ N : HeightSegmentNetwork
      (M.GeometricComponentEdge F covered positive small lower c),
      (∀ e, N.first e = centeredPlaneFrame (K.projectedVertex origin)
        (fiveSectorFrame t positive small i).place (F.geometricPosition e.val)) ∧
      ∀ e, N.last e = centeredPlaneFrame (K.projectedVertex origin)
        (fiveSectorFrame t positive small i).place
          (F.geometricPosition (M.geometricParent F covered e.val)) := by
  obtain ⟨i, directions⟩ := M.exists_geometric_component_sector F covered positive small lower c
  exact ⟨i, M.componentHeightNetwork F covered positive small lower c i directions,
    fun _ => rfl, fun _ => rfl⟩

end ConvexCap.SectorForest
end Unfoldings
