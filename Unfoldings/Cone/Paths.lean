module

public import Unfoldings.Cone.Proper
public import Unfoldings.Path.Segment
public import Unfoldings.Metric.Paths

/-! Continuous path distance and explicit radial geodesics of the constructed tangent fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

/-- Straight segments in the actual closed corner wedges. -/
def tangentCellPath (c : C.CornerAt retain v) (a b : C.TangentCell retain v c) : Path a b where
  toFun := fun t => ⟨Path.segment a.val b.val t,
    (C.triangle c.val.1).convex_cornerWedge c.val.2 |>.segment_subset a.property b.property
      (by rw [← Path.range_segment]; exact ⟨t, rfl⟩)⟩
  continuous_toFun := (Path.segment a.val b.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment a.val b.val).source
  target' := Subtype.ext (Path.segment a.val b.val).target

@[simp] theorem tangentCellPath_map_val (c : C.CornerAt retain v)
    (a b : C.TangentCell retain v c) :
    (C.tangentCellPath retain v c a b).map continuous_subtype_val = Path.segment a.val b.val := by
  ext t
  rfl

theorem tangentCellPath_lipschitz (c : C.CornerAt retain v) (a b : C.TangentCell retain v c) :
    LipschitzWith (nndist a b) (C.tangentCellPath retain v c a b) :=
  Path.segment_lipschitz a.val b.val

@[simp] theorem eLength_tangentCellPath (c : C.CornerAt retain v)
    (a b : C.TangentCell retain v c) :
    (C.tangentCellPath retain v c a b).eLength = edist a b := by
  have inclusion : Isometry (Subtype.val : C.TangentCell retain v c → Plane) := fun _ _ => rfl
  have same := (C.tangentCellPath retain v c a b).eLength_map_isometry inclusion
  rw [C.tangentCellPath_map_val, Path.eLength_segment] at same
  exact same.symm

/-- The tangent route metric is exactly the infimum of lengths of continuous paths. -/
theorem tangent_eDistance_eq_edist (x y : C.TangentFan retain v) :
    Path.eDistance x y = edist x y :=
  MetricGluing.eDistance_eq_edist (C.TangentCell retain v) (C.tangentCellPath retain v)
    (fun c a b => (C.eLength_tangentCellPath retain v c a b).le) (C.tangentGlue retain v) x y

/-- The explicit image of the straight radial segment in an original wedge. -/
def tangentRadialPath (c : C.CornerAt retain v) (x : C.TangentCell retain v c) :
    Path (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x) :=
  ((C.tangentCellPath retain v c (C.tangentApex retain v c) x).map
    (C.tangentFaceMap_lipschitz retain v c).continuous).cast (C.tangentOrigin_eq retain v c) rfl

@[simp] theorem tangentRadialPath_apply (c : C.CornerAt retain v)
    (x : C.TangentCell retain v c) (t : unitInterval) :
    C.tangentRadialPath retain v c x t = C.tangentFaceMap retain v c
      (C.tangentCellPath retain v c (C.tangentApex retain v c) x t) := rfl

theorem tangentRadialPath_lipschitz (c : C.CornerAt retain v) (x : C.TangentCell retain v c) :
    LipschitzWith (nndist (C.tangentApex retain v c) x) (C.tangentRadialPath retain v c x) := by
  change LipschitzWith (nndist (C.tangentApex retain v c) x)
    (C.tangentFaceMap retain v c ∘ C.tangentCellPath retain v c (C.tangentApex retain v c) x)
  simpa only [one_mul] using (C.tangentFaceMap_lipschitz retain v c).comp
    (C.tangentCellPath_lipschitz retain v c (C.tangentApex retain v c) x)

/-- A radial segment from the common apex is a genuine metric geodesic. -/
theorem tangentRadialPath_isGeodesic (c : C.CornerAt retain v) (x : C.TangentCell retain v c) :
    (C.tangentRadialPath retain v c x).IsGeodesic := by
  apply (C.tangentRadialPath retain v c x).isGeodesic_of_lipschitz
  have same_speed : nndist (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x) =
      nndist (C.tangentApex retain v c) x := NNReal.eq (C.tangent_dist_origin_faceMap retain v c x)
  rw [same_speed]
  exact C.tangentRadialPath_lipschitz retain v c x

@[simp] theorem eLength_tangentRadialPath (c : C.CornerAt retain v)
    (x : C.TangentCell retain v c) :
    (C.tangentRadialPath retain v c x).eLength = edist (C.tangentApex retain v c) x :=
  (C.tangentRadialPath_isGeodesic retain v c x).eLength_eq_edist.trans
    (C.tangent_edist_origin_faceMap retain v c x)

theorem exists_tangent_radial_geodesic (c : C.CornerAt retain v) (x : C.TangentCell retain v c) :
    ∃ p : Path (C.tangentOrigin retain v) (C.tangentFaceMap retain v c x), p.IsGeodesic :=
  ⟨C.tangentRadialPath retain v c x, C.tangentRadialPath_isGeodesic retain v c x⟩

end Unfoldings.TriangleComplex
