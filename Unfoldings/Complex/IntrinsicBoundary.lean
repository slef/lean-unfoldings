module

public import Unfoldings.Complex.BoundaryRegular
public import Unfoldings.Boundary.Charts
public import Unfoldings.Geometry.EdgePerfect
public import Unfoldings.Geometry.PlaneSphere
public import Unfoldings.Topology.PlanarOpenMapping
public import Unfoldings.Topology.PerfectProjection

/-!
# Intrinsic bank boundaries are preserved by disk homeomorphisms

Planar openness distinguishes Euclidean charts from one-sided bank charts at
nonvertex points. Closedness and the perfect boundary circle extend the
identification across the finite vertex set. No cone-angle restrictions or
boundary-preservation hypotheses are imposed on the disk homeomorphism.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings

variable {X : Type*} [EMetricSpace X]

theorem HasMetricBallChart.disk_image_norm_lt_one {x : X}
    (regular : HasMetricBallChart Plane x)
    (disk : X ≃ₜ Metric.closedBall (0 : Plane) 1) : ‖(disk x).val‖ < 1 := by
  obtain ⟨D, U, _, member, open_U, ⟨chart⟩⟩ := regular.exists_open_chart
  let f : C(U, Plane) := ⟨fun z => (disk (chart.symm z).val).val,
    continuous_subtype_val.comp (disk.continuous.comp
      (continuous_subtype_val.comp chart.symm.continuous))⟩
  have injective : Function.Injective f := by
    intro a b equal
    apply chart.symm.injective
    apply Subtype.ext
    apply disk.injective
    exact Subtype.ext equal
  have open_range := PlanarTopology.isOpen_range_of_continuous_injective open_U f injective
  have included : Set.range f ⊆ Metric.closedBall (0 : Plane) 1 := by
    rintro _ ⟨z, rfl⟩
    exact (disk (chart.symm z).val).property
  have center : (disk x).val ∈ Set.range f := by
    refine ⟨chart ⟨x, member⟩, ?_⟩
    change (disk (chart.symm (chart ⟨x, member⟩)).val).val = (disk x).val
    rw [chart.symm_apply_apply]
  have inside := interior_mono included (open_range.interior_eq.symm ▸ center)
  rw [interior_closedBall (0 : Plane) one_ne_zero, Metric.mem_ball, dist_zero_right] at inside
  exact inside

end Unfoldings

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem BoundaryChart.center_coordinates {retain : Set C.Seam} {bank : C.BoundaryBank retain}
    {x : (C.triangle bank.val.face).Edge bank.val.edge} (N : C.BoundaryChart retain bank x) :
    (N.chart.symm ⟨C.bankMap retain bank x,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive)⟩).val = x.val := by
  have center_ball : x.val ∈ Metric.ball x.val N.radius := Metric.mem_ball_self N.positive
  have halfplane := (N.halfplane x.val center_ball).mp
    ((C.triangle bank.val.face).edge_subset bank.val.edge x.property)
  let center : (C.triangle bank.val.face).edgeHalfBall bank.val.edge x N.radius :=
    ⟨x.val, center_ball, halfplane⟩
  have image : N.chart center = ⟨C.bankMap retain bank x,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive)⟩ := Subtype.ext (N.agrees center)
  rw [← image, N.chart.symm_apply_apply]

theorem bankMap_disk_norm_eq_one_of_nonvertex (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (bank : C.BoundaryBank retain) (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ (C.triangle bank.val.face).IsVertex x) :
    ‖(disk (C.bankMap retain bank x)).val‖ = 1 := by
  have bound : ‖(disk (C.bankMap retain bank x)).val‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (disk (C.bankMap retain bank x)).property
  by_contra different
  have inside : ‖(disk (C.bankMap retain bank x)).val‖ < 1 := lt_of_le_of_ne bound different
  obtain ⟨N⟩ := C.exists_boundaryChart retain bank x regular
  let U := Metric.eball (C.bankMap retain bank x) (ENNReal.ofReal N.radius)
  let fromDisk : C(Metric.ball (0 : Plane) 1, C.Realization retain) :=
    ⟨disk.symm ∘ openBallDiskInclusion,
      disk.symm.continuous.comp openBallDiskInclusion.continuous⟩
  let V : Set (Metric.ball (0 : Plane) 1) := fromDisk ⁻¹' U
  have open_V : IsOpen V := Metric.isOpen_eball.preimage fromDisk.continuous
  let into : C(V, U) :=
    ⟨fun z => ⟨fromDisk z.val, z.property⟩,
      (fromDisk.continuous.comp continuous_subtype_val).subtype_mk (fun z => z.property)⟩
  have into_injective : Function.Injective into := by
    intro a b equal
    have original := congrArg Subtype.val equal
    have points := disk.symm.injective original
    exact Subtype.ext (Subtype.ext
      (congrArg (fun p : Metric.closedBall (0 : Plane) 1 => p.val) points))
  let f : C(V, Plane) := ⟨fun z => (N.chart.symm (into z)).val,
    continuous_subtype_val.comp (N.chart.symm.continuous.comp into.continuous)⟩
  have injective : Function.Injective f := by
    intro a b equal
    exact into_injective (N.chart.symm.injective (Subtype.ext equal))
  have embedding : Topology.IsOpenEmbedding (fun z : V => z.val.val) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp open_V.isOpenEmbedding_subtypeVal
  have open_range := PlanarTopology.isOpen_range_of_openEmbedding _ embedding f injective
  have included : Set.range f ⊆ (C.triangle bank.val.face).carrier := by
    rintro _ ⟨z, rfl⟩
    exact (N.halfplane _ (N.chart.symm (into z)).property.1).mpr
      (N.chart.symm (into z)).property.2
  let z : Metric.ball (0 : Plane) 1 := ⟨(disk (C.bankMap retain bank x)).val, by
    simpa only [Metric.mem_ball, dist_zero_right] using inside⟩
  have from_center : fromDisk z = C.bankMap retain bank x := by
    change disk.symm (disk (C.bankMap retain bank x)) = C.bankMap retain bank x
    exact disk.symm_apply_apply _
  let a : V := ⟨z, by
    change fromDisk z ∈ U
    rw [from_center]
    exact Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive)⟩
  have into_center : into a = ⟨C.bankMap retain bank x,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive)⟩ := Subtype.ext from_center
  have center : x.val ∈ Set.range f := by
    refine ⟨a, ?_⟩
    change (N.chart.symm (into a)).val = x.val
    rw [into_center]
    exact BoundaryChart.center_coordinates C N
  exact (C.triangle bank.val.face).not_mem_interior_of_mem_edge bank.val.edge x.property
    (interior_mono included (open_range.interior_eq.symm ▸ center))

theorem bankMap_disk_norm_eq_one (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (bank : C.BoundaryBank retain) (x : (C.triangle bank.val.face).Edge bank.val.edge) :
    ‖(disk (C.bankMap retain bank x)).val‖ = 1 := by
  let T := C.triangle bank.val.face
  let := T.edgePerfectSpace bank.val.edge
  let U : Set (T.Edge bank.val.edge) := {y | ‖(disk (C.bankMap retain bank y)).val‖ ≠ 1}
  have continuous_norm : Continuous
      (fun y : T.Edge bank.val.edge => ‖(disk (C.bankMap retain bank y)).val‖) :=
    (continuous_subtype_val.comp
      (disk.continuous.comp (C.bankMap_lipschitz retain bank).continuous)).norm
  have open_U : IsOpen U := (isClosed_eq continuous_norm continuous_const).isOpen_compl
  have finite : {y : T.Edge bank.val.edge | T.IsVertex y}.Finite :=
    (Set.finite_range T.vertex).of_injOn (f := fun y : T.Edge bank.val.edge => y.val)
      (fun _ hy => hy) Subtype.val_injective.injOn
  have finite_U : U.Finite := finite.subset (by
    intro y hy
    by_contra nonvertex
    exact hy (C.bankMap_disk_norm_eq_one_of_nonvertex retain disk bank y nonvertex))
  by_contra different
  exact infinite_of_mem_nhds x (open_U.mem_nhds different) finite_U

theorem bankBoundary_subset_disk_boundary (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    {x : C.Realization retain} (member : x ∈ C.bankBoundary retain) : ‖(disk x).val‖ = 1 := by
  obtain ⟨bank, y, rfl⟩ := Set.mem_iUnion.mp member
  exact C.bankMap_disk_norm_eq_one retain disk bank y

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F in
theorem bankBoundary_iff_disk_norm_eq_one (retain : Set C.Seam)
    (disk : C.Realization retain ≃ₜ Metric.closedBall (0 : Plane) 1)
    (x : C.Realization retain) : x ∈ C.bankBoundary retain ↔ ‖(disk x).val‖ = 1 := by
  let := plane_unit_sphere_perfect
  let f : Metric.sphere (0 : Plane) 1 → C.Realization retain :=
    disk.symm ∘ unitSphereDiskInclusion
  have continuous_f : Continuous f :=
    disk.symm.continuous.comp unitSphereDiskInclusion.continuous
  have sphere_norm (z : Metric.sphere (0 : Plane) 1) : ‖(disk (f z)).val‖ = 1 := by
    change ‖(disk (disk.symm (unitSphereDiskInclusion z))).val‖ = 1
    rw [disk.apply_symm_apply]
    exact mem_sphere_zero_iff_norm.mp z.property
  have images : Set.range f ⊆ C.bankBoundary retain ∪ Set.range (C.vertexPoint retain) := by
    rintro _ ⟨z, rfl⟩
    by_cases bank : f z ∈ C.bankBoundary retain
    · exact Or.inl bank
    · right
      by_contra nonvertex
      have regular := F.isRegularPoint_of_not_bankBoundary_of_not_vertex retain (f z) bank nonvertex
      have small := regular.disk_image_norm_lt_one disk
      rw [sphere_norm] at small
      exact (lt_irrefl (1 : ℝ)) small
  have injective : Function.Injective f := by
    intro a b equal
    have points := disk.symm.injective equal
    exact Subtype.ext (congrArg (fun p : Metric.closedBall (0 : Plane) 1 => p.val) points)
  have boundary := range_subset_closed_of_perfect f continuous_f (C.isClosed_bankBoundary retain)
    (Set.finite_range (C.vertexPoint retain)) images (fun _ _ _ equal => injective equal)
  constructor
  · exact C.bankBoundary_subset_disk_boundary retain disk
  · intro norm
    let z : Metric.sphere (0 : Plane) 1 := ⟨(disk x).val, mem_sphere_zero_iff_norm.mpr norm⟩
    apply boundary
    refine ⟨z, ?_⟩
    change disk.symm (disk x) = x
    exact disk.symm_apply_apply x

end Unfoldings.SpatialFolding
