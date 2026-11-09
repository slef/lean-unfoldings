module

public import Unfoldings.Geometry.Triangle
public import Unfoldings.Path.Segment

/-! Straight paths in closed triangular cells, with exactly their Euclidean length. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

def cellPath (T : Triangle) (a b : T.Cell) : Path a b where
  toFun := fun t => ⟨Path.segment a.val b.val t,
    T.convex_carrier.segment_subset a.property b.property
    (by rw [← Path.range_segment]; exact ⟨t, rfl⟩)⟩
  continuous_toFun := (Path.segment a.val b.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment a.val b.val).source
  target' := Subtype.ext (Path.segment a.val b.val).target

@[simp] theorem cellPath_map_val (T : Triangle) (a b : T.Cell) :
    (T.cellPath a b).map continuous_subtype_val = Path.segment a.val b.val := by
  ext t
  rfl

@[simp] theorem eLength_cellPath (T : Triangle) (a b : T.Cell) :
    (T.cellPath a b).eLength = edist a b := by
  have inclusion : Isometry (Subtype.val : T.Cell → Plane) := fun _ _ => rfl
  have same := (T.cellPath a b).eLength_map_isometry inclusion
  rw [cellPath_map_val, Path.eLength_segment] at same
  exact same.symm

end Unfoldings.Triangle
