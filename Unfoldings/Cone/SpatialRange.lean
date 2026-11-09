module

public import Unfoldings.Cone.SpatialEmbedding
public import Unfoldings.Geometry.RadialLocality

/-!
# Radial homogeneity of the actual spatial tangent image

Positive scaling about the physical vertex preserves exactly the spatial
image of the tangent fan. Every witness is constructed in an actual corner
wedge; no angular or planar-development hypothesis is used.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

theorem tangent_range_lineMap {z : Space} (member : z ∈ Set.range (F.tangentToSpace retain v))
    {t : ℝ} (nonnegative : 0 ≤ t) :
    AffineMap.lineMap (F.toSpace retain (C.vertexPoint retain v)) z t ∈
      Set.range (F.tangentToSpace retain v) := by
  obtain ⟨w, image⟩ := member
  obtain ⟨⟨c, p⟩, rfl⟩ := MetricGluing.point_surjective
    (C.TangentCell retain v) (C.tangentGlue retain v) w
  let q : C.TangentCell retain v c :=
    ⟨AffineMap.lineMap ((C.triangle c.val.1).vertex c.val.2) p.val t,
      (C.triangle c.val.1).lineMap_mem_cornerWedge c.val.2 p.property nonnegative⟩
  refine ⟨C.tangentFaceMap retain v c q, ?_⟩
  change F.place c.val.1 (AffineMap.lineMap
    ((C.triangle c.val.1).vertex c.val.2) p.val t) = _
  have apex : F.place c.val.1 ((C.triangle c.val.1).vertex c.val.2) =
      F.toSpace retain (C.vertexPoint retain v) := F.tangentApex_spatial_eq retain v c
  rw [F.place_lineMap, apex]
  exact congrArg (fun y : Space => AffineMap.lineMap
    (F.toSpace retain (C.vertexPoint retain v)) y t) image

theorem tangent_range_lineMap_iff (z : Space) {t : ℝ} (positive : 0 < t) :
    AffineMap.lineMap (F.toSpace retain (C.vertexPoint retain v)) z t ∈
        Set.range (F.tangentToSpace retain v) ↔ z ∈ Set.range (F.tangentToSpace retain v) := by
  constructor
  · intro member
    have expanded := F.tangent_range_lineMap retain v member (inv_nonneg.mpr positive.le)
    rwa [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ positive.ne',
      AffineMap.lineMap_apply_one] at expanded
  · intro member
    exact F.tangent_range_lineMap retain v member positive.le

end Unfoldings.SpatialFolding
