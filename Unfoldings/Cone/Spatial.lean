module

public import Unfoldings.Cone.Proper
public import Unfoldings.Complex.Folding

/-! Spatial face placements extend to the actual radially glued tangent fan. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

theorem place_lineMap (f : Face) (a b : Plane) (t : ℝ) :
    F.place f (AffineMap.lineMap a b t) =
      AffineMap.lineMap (F.place f a) (F.place f b) t :=
  (F.place f).toAffineMap.apply_lineMap a b t

/-- Every incident wedge apex folds to the original spatial vertex. -/
theorem tangentApex_spatial_eq (c : C.CornerAt retain v) :
    F.place c.val.1 (C.tangentApex retain v c).val =
      F.toSpace retain (C.vertexPoint retain v) :=
  congrArg (fun w : C.Vertex retain => F.toSpace retain (C.vertexPoint retain w)) c.property

theorem place_across (s : C.Seam) (side : Bool)
    (x : (C.triangle (C.seamSide s side).face).Edge (C.seamSide s side).edge) :
    F.place (C.seamSide s side).face x.val =
      F.place (C.seamSide s (!side)).face (C.across s side x).val := by
  cases side
  · exact F.joined s x
  · have joined := F.joined s ((C.identify s).symm x)
    exact (joined.trans (congrArg
      (fun y : (C.triangle (C.right s).face).Edge (C.right s).edge =>
        F.place (C.right s).face y.val)
      ((C.identify s).apply_symm_apply x))).symm

def tangentCellToSpace (c : C.CornerAt retain v) (x : C.TangentCell retain v c) : Space :=
  F.place c.val.1 x.val

theorem tangentCellToSpace_isometry (c : C.CornerAt retain v) :
    Isometry (F.tangentCellToSpace retain v c) :=
  (F.place c.val.1).isometry.comp isometry_subtype_coe

theorem tangentCellToSpace_compatible : ∀ a b, C.tangentGlue retain v a b →
    F.tangentCellToSpace retain v a.1 a.2 = F.tangentCellToSpace retain v b.1 b.2 := by
  rintro a b ⟨s, x, t, nonnegative, rfl, rfl⟩
  change F.place (C.seamSide s.val.1 s.val.2.1).face
      (AffineMap.lineMap (C.tangentApex retain v (C.tangentLeft retain v s)).val x.val t) =
    F.place (C.seamSide s.val.1 (!s.val.2.1)).face
      (AffineMap.lineMap (C.tangentApex retain v (C.tangentRight retain v s)).val
        (C.across s.val.1 s.val.2.1 x).val t)
  have apex : F.place (C.seamSide s.val.1 s.val.2.1).face
      (C.tangentApex retain v (C.tangentLeft retain v s)).val =
    F.place (C.seamSide s.val.1 (!s.val.2.1)).face
      (C.tangentApex retain v (C.tangentRight retain v s)).val :=
    (F.tangentApex_spatial_eq retain v (C.tangentLeft retain v s)).trans
      (F.tangentApex_spatial_eq retain v (C.tangentRight retain v s)).symm
  rw [F.place_lineMap, F.place_lineMap, apex, F.place_across]

/-- The spatial folding of the whole tangent metric fan. -/
def tangentToSpace : C.TangentFan retain v → Space :=
  MetricGluing.lift (C.TangentCell retain v) (C.tangentGlue retain v)
    (F.tangentCellToSpace retain v)
    (fun c => (F.tangentCellToSpace_isometry retain v c).lipschitzWith)
    (F.tangentCellToSpace_compatible retain v)

@[simp] theorem tangentToSpace_faceMap (c : C.CornerAt retain v) (x : C.TangentCell retain v c) :
    F.tangentToSpace retain v (C.tangentFaceMap retain v c x) = F.place c.val.1 x.val := rfl

theorem tangentToSpace_lipschitz : LipschitzWith 1 (F.tangentToSpace retain v) :=
  MetricGluing.lift_lipschitz (C.TangentCell retain v) (C.tangentGlue retain v)
    (F.tangentCellToSpace retain v)
    (fun c => (F.tangentCellToSpace_isometry retain v c).lipschitzWith)
    (F.tangentCellToSpace_compatible retain v)

/-- Spatial compatibility rules out shortcuts within any single tangent wedge. -/
theorem tangentFaceMap_isometry (c : C.CornerAt retain v) :
    Isometry (C.tangentFaceMap retain v c) :=
  MetricGluing.of_isometry_of_compatible (C.TangentCell retain v) (C.tangentGlue retain v)
    (F.tangentCellToSpace retain v) (F.tangentCellToSpace_isometry retain v)
    (F.tangentCellToSpace_compatible retain v) c

@[simp] theorem tangentToSpace_origin :
    F.tangentToSpace retain v (C.tangentOrigin retain v) =
      F.toSpace retain (C.vertexPoint retain v) := by
  obtain ⟨p⟩ := C.nonempty_linkGerm retain v
  let c : C.CornerAt retain v := ⟨p.val.1, p.property⟩
  rw [C.tangentOrigin_eq retain v c, F.tangentToSpace_faceMap]
  exact F.tangentApex_spatial_eq retain v c

end Unfoldings.SpatialFolding
