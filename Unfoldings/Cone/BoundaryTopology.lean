module

public import Unfoldings.Cone.AngularHomeomorph
public import Unfoldings.Cone.IntervalIsometry
public import Unfoldings.Cone.Charts

/-!
# Half-plane models at actual boundary vertices

The actual interval-link tangent fan is homeomorphic to a half-plane, with
its common apex on the boundary line. For spatially folded complexes the
constructed local metric comparison transfers this to whole intrinsic
neighborhoods. No bound on total angle or nonoverlap is assumed.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)
  (retain : Set C.Seam) (v : C.Vertex retain)

def intervalTangentHalfPlaneHomeomorph {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) :
    C.TangentFan retain v ≃ₜ PlanarTopology.closedHalfPlane :=
  (C.intervalFanIsometry retain v chain covers start finish).symm.toHomeomorph.trans
    (C.linkAngularFan retain v chain).halfPlaneHomeomorph

@[simp] theorem intervalTangentHalfPlaneHomeomorph_origin {n : ℕ}
    (chain : (C.linkSystem retain v).Chain n) (covers : ∀ p, chain.Visited p)
    (start : C.linkMate retain v chain.first = chain.first)
    (finish : C.linkMate retain v (C.linkTurn retain v chain.last) =
      C.linkTurn retain v chain.last) :
    C.intervalTangentHalfPlaneHomeomorph retain v chain covers start finish
      (C.tangentOrigin retain v) =
      ⟨(0, 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  have center : (C.intervalFanIsometry retain v chain covers start finish).symm
      (C.tangentOrigin retain v) = (C.linkAngularFan retain v chain).origin := by
    apply (C.intervalFanIsometry retain v chain covers start finish).injective
    rw [IsometryEquiv.apply_symm_apply, C.intervalFanIsometry_apply,
      C.angularToTangent_origin]
  change (C.linkAngularFan retain v chain).halfPlaneHomeomorph
    ((C.intervalFanIsometry retain v chain covers start finish).symm
      (C.tangentOrigin retain v)) = _
  rw [center, AngularFan.halfPlaneHomeomorph_origin]

theorem exists_boundaryTangentHalfPlaneHomeomorph (boundary : C.IsBoundaryVertex retain v) :
    ∃ e : C.TangentFan retain v ≃ₜ PlanarTopology.closedHalfPlane,
      e (C.tangentOrigin retain v) = ⟨(0, 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  obtain ⟨n, chain, start, finish, covers⟩ := C.exists_interval_link retain v boundary
  exact ⟨C.intervalTangentHalfPlaneHomeomorph retain v chain covers start finish,
    C.intervalTangentHalfPlaneHomeomorph_origin retain v chain covers start finish⟩

theorem tangentSurfaceTag_apex (c : C.CornerAt retain v) :
    C.tangentSurfaceTag retain v ⟨c, C.tangentApex retain v c⟩ = C.vertexPoint retain v := by
  rw [C.tangentSurfaceTag_of_mem retain v _ ((C.triangle c.val.1).vertex_mem c.val.2)]
  exact (C.vertexPoint_eq_cornerAt retain v c).symm

theorem TangentChart.center (N : C.TangentChart retain v) :
    (N.chart ⟨C.tangentOrigin retain v, by
      rw [Metric.mem_eball, edist_self]
      exact ENNReal.ofReal_pos.mpr N.positive⟩).val = C.vertexPoint retain v := by
  let p := Classical.choice (C.nonempty_linkGerm retain v)
  let c : C.CornerAt retain v := ⟨p.val.1, p.property⟩
  have value := N.agrees ⟨c, C.tangentApex retain v c⟩ (by
    change edist (C.tangentFaceMap retain v c (C.tangentApex retain v c))
      (C.tangentOrigin retain v) < _
    rw [← C.tangentOrigin_eq retain v c, edist_self]
    exact ENNReal.ofReal_pos.mpr N.positive)
  rw [C.tangentSurfaceTag_apex retain v c] at value
  convert value using 1
  congr 2

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  (F : SpatialFolding C) (retain : Set C.Seam) (v : C.Vertex retain)

include F

/-- A whole surface ball has an actual half-plane chart at every boundary vertex. -/
theorem exists_boundaryVertexHalfPlaneChart (boundary : C.IsBoundaryVertex retain v) :
    ∃ r : ℝ, ∃ positive : 0 < r,
      ∃ U : Set PlanarTopology.closedHalfPlane, IsOpen U ∧
        ∃ e : Metric.eball (C.vertexPoint retain v) (ENNReal.ofReal r) ≃ₜ U,
          (e ⟨C.vertexPoint retain v, by
            rw [Metric.mem_eball, edist_self]
            exact ENNReal.ofReal_pos.mpr positive⟩).val =
            ⟨(0, 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  obtain ⟨N⟩ := F.exists_tangentChart retain v
  obtain ⟨h, center⟩ := C.exists_boundaryTangentHalfPlaneHomeomorph retain v boundary
  let B := Metric.eball (C.tangentOrigin retain v) (ENNReal.ofReal N.radius)
  refine ⟨N.radius, N.positive, h '' B, h.isOpenMap _ Metric.isOpen_eball,
    N.chart.symm.toHomeomorph.trans (h.image B), ?_⟩
  change h ((N.chart.symm _).val) = _
  rw [← center]
  congr 1
  have back : N.chart.symm
      ⟨C.vertexPoint retain v, by
        rw [Metric.mem_eball, edist_self]
        exact ENNReal.ofReal_pos.mpr N.positive⟩ =
      ⟨C.tangentOrigin retain v, by
        rw [Metric.mem_eball, edist_self]
        exact ENNReal.ofReal_pos.mpr N.positive⟩ := by
    apply N.chart.injective
    rw [IsometryEquiv.apply_symm_apply]
    exact Subtype.ext (TriangleComplex.TangentChart.center C retain v N).symm
  exact congrArg Subtype.val back

end Unfoldings.SpatialFolding
