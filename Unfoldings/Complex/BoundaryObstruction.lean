module

public import Unfoldings.Complex.IntrinsicBoundary

/-!
# Open planar patches cannot hit an unpaired bank

The inverse one-sided metric chart would turn such a patch into an open subset
of a triangle containing an edge point. Planar invariance of domain rules this
out. The domain may be any space with an open planar embedding.
-/

@[expose] public section

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v w

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem bankMap_not_mem_range_of_planar_injection (retain : Set C.Seam)
    (bank : C.BoundaryBank retain) (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (nonvertex : ¬ (C.triangle bank.val.face).IsVertex x)
    {A : Type w} [TopologicalSpace A] (i : A → Plane)
    (embedding : Topology.IsOpenEmbedding i) (f : C(A, C.Realization retain))
    (injective : Function.Injective f) : C.bankMap retain bank x ∉ Set.range f := by
  rintro ⟨a, equal⟩
  obtain ⟨N⟩ := C.exists_boundaryChart retain bank x nonvertex
  let U := Metric.eball (C.bankMap retain bank x) (ENNReal.ofReal N.radius)
  let D : Set A := f ⁻¹' U
  have open_D : IsOpen D := Metric.isOpen_eball.preimage f.continuous
  let into : C(D, U) := ⟨fun p => ⟨f p.val, p.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have into_injective : Function.Injective into := by
    intro p q same
    exact Subtype.ext (injective (congrArg Subtype.val same))
  let g : C(D, Plane) := ⟨fun p => (N.chart.symm (into p)).val,
    continuous_subtype_val.comp (N.chart.symm.continuous.comp into.continuous)⟩
  have inj : Function.Injective g := fun _ _ same =>
    into_injective (N.chart.symm.injective (Subtype.ext same))
  have source_embedding : Topology.IsOpenEmbedding (fun p : D => i p.val) :=
    embedding.comp open_D.isOpenEmbedding_subtypeVal
  have open_range := PlanarTopology.isOpen_range_of_openEmbedding _ source_embedding g inj
  have included : Set.range g ⊆ (C.triangle bank.val.face).carrier := by
    rintro _ ⟨p, rfl⟩
    exact (N.halfplane _ (N.chart.symm (into p)).property.1).mpr
      (N.chart.symm (into p)).property.2
  let p : D := ⟨a, by
    change f a ∈ U
    rw [equal]
    exact Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive)⟩
  have center : into p = ⟨C.bankMap retain bank x,
      Metric.mem_eball_self (ENNReal.ofReal_pos.mpr N.positive)⟩ := Subtype.ext equal
  have in_range : x.val ∈ Set.range g := by
    refine ⟨p, ?_⟩
    change (N.chart.symm (into p)).val = x.val
    rw [center]
    exact BoundaryChart.center_coordinates C N
  exact (C.triangle bank.val.face).not_mem_interior_of_mem_edge bank.val.edge x.property
    (interior_mono included (open_range.interior_eq.symm ▸ in_range))

theorem not_isRegularPoint_bankMap_of_nonvertex (retain : Set C.Seam)
    (bank : C.BoundaryBank retain) (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (nonvertex : ¬ (C.triangle bank.val.face).IsVertex x) :
    ¬ C.IsRegularPoint retain (C.bankMap retain bank x) := by
  intro regular
  obtain ⟨D, U, _, member, open_U, ⟨chart⟩⟩ := regular.exists_open_chart
  let f : C(U, C.Realization retain) := ⟨fun z => (chart.symm z).val,
    continuous_subtype_val.comp chart.symm.continuous⟩
  have injective : Function.Injective f := fun _ _ equal =>
    chart.symm.injective (Subtype.ext equal)
  apply C.bankMap_not_mem_range_of_planar_injection retain bank x nonvertex
    Subtype.val open_U.isOpenEmbedding_subtypeVal f injective
  exact ⟨chart ⟨C.bankMap retain bank x, member⟩,
    congrArg Subtype.val (chart.symm_apply_apply _)⟩

end Unfoldings.TriangleComplex
