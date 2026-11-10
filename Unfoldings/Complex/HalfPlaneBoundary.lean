module

public import Unfoldings.Complex.BoundaryObstruction
public import Unfoldings.Topology.PlanarHalfPlane
public import Unfoldings.Topology.BoundaryAtlas

/-! Intrinsic cut banks in arbitrary local half-plane coordinates. -/

@[expose] public section

noncomputable section

namespace Unfoldings

open PlanarTopology

variable {X : Type*} [EMetricSpace X]

theorem HasMetricBallChart.halfPlane_image_positive {x : X}
    (regular : HasMetricBallChart Plane x)
    {U : Set X} (open_U : IsOpen U) {V : Set closedHalfPlane}
    (e : U ≃ₜ V) (inside : x ∈ U) : 0 < (e ⟨x, inside⟩).val.val.2 := by
  obtain ⟨D, W, _, member, open_W, ⟨chart⟩⟩ := regular.exists_open_chart
  let S : Set W := {z | (chart.symm z).val ∈ U}
  have open_S : IsOpen S := open_U.preimage
    (continuous_subtype_val.comp chart.symm.continuous)
  let into : C(S, U) := ⟨fun z => ⟨(chart.symm z.val).val, z.property⟩,
    (continuous_subtype_val.comp (chart.symm.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  let f : C(S, closedHalfPlane) := ⟨fun z => (e (into z)).val,
    continuous_subtype_val.comp (e.continuous.comp into.continuous)⟩
  have inj : Function.Injective f := by
    intro a b equal
    have points := e.injective (Subtype.ext equal)
    have originals := congrArg Subtype.val points
    exact Subtype.ext (chart.symm.injective (Subtype.ext originals))
  have embedding : Topology.IsOpenEmbedding (fun z : S => z.val.val) :=
    open_W.isOpenEmbedding_subtypeVal.comp open_S.isOpenEmbedding_subtypeVal
  let a : S := ⟨chart ⟨x, member⟩, by
    change (chart.symm (chart ⟨x, member⟩)).val ∈ U
    rwa [IsometryEquiv.symm_apply_apply]⟩
  have center : into a = ⟨x, inside⟩ := by
    apply Subtype.ext
    change (chart.symm (chart ⟨x, member⟩)).val = x
    exact congrArg (fun z : D => z.val) (chart.symm_apply_apply _)
  have positive := positive_snd_of_planar_injection _ embedding f inj a
  change 0 < (e (into a)).val.val.2 at positive
  rwa [center] at positive

end Unfoldings

namespace Unfoldings.TriangleComplex

open PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

theorem bankMap_halfPlane_snd_eq_zero_of_nonvertex (retain : Set C.Seam)
    {U : Set (C.Realization retain)} {V : Set closedHalfPlane} (open_V : IsOpen V)
    (e : U ≃ₜ V) (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (nonvertex : ¬ (C.triangle bank.val.face).IsVertex x)
    (inside : C.bankMap retain bank x ∈ U) :
    (e ⟨C.bankMap retain bank x, inside⟩).val.val.2 = 0 := by
  let a := e ⟨C.bankMap retain bank x, inside⟩
  have nonnegative : 0 ≤ a.val.val.2 := a.val.property
  by_contra different
  have positive : 0 < a.val.val.2 := lt_of_le_of_ne nonnegative (Ne.symm different)
  let D : Set halfPlaneInterior := {z | z.val ∈ V}
  have open_D : IsOpen D := open_V.preimage continuous_subtype_val
  let into : C(D, V) := ⟨fun z => ⟨z.val.val, z.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let f : C(D, C.Realization retain) := ⟨fun z => (e.symm (into z)).val,
    continuous_subtype_val.comp (e.symm.continuous.comp into.continuous)⟩
  have inj : Function.Injective f := by
    intro p q equal
    have points := e.symm.injective (Subtype.ext equal)
    have values := congrArg (fun z : V => z.val) points
    change p.val.val = q.val.val at values
    exact Subtype.ext (Subtype.ext values)
  have embedding : Topology.IsOpenEmbedding
      (fun z : D => pairHomeomorph z.val.val.val) :=
    halfPlaneInterior_openEmbedding.comp open_D.isOpenEmbedding_subtypeVal
  apply C.bankMap_not_mem_range_of_planar_injection retain bank x nonvertex _ embedding f inj
  let z : D := ⟨⟨a.val, positive⟩, a.property⟩
  refine ⟨z, ?_⟩
  change (e.symm a).val = C.bankMap retain bank x
  exact congrArg Subtype.val (e.symm_apply_apply _)

theorem bankMap_halfPlane_snd_eq_zero (retain : Set C.Seam)
    {U : Set (C.Realization retain)} (open_U : IsOpen U)
    {V : Set closedHalfPlane} (open_V : IsOpen V) (e : U ≃ₜ V)
    (bank : C.BoundaryBank retain) (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (inside : C.bankMap retain bank x ∈ U) :
    (e ⟨C.bankMap retain bank x, inside⟩).val.val.2 = 0 := by
  let T := C.triangle bank.val.face
  let := T.edgePerfectSpace bank.val.edge
  let E : Set (T.Edge bank.val.edge) := C.bankMap retain bank ⁻¹' U
  have open_E : IsOpen E := open_U.preimage (C.bankMap_lipschitz retain bank).continuous
  let into : C(E, U) := ⟨fun z => ⟨C.bankMap retain bank z.val, z.property⟩,
    ((C.bankMap_lipschitz retain bank).continuous.comp continuous_subtype_val).subtype_mk _⟩
  let f : C(E, ℝ) := ⟨fun z => (e (into z)).val.val.2, by fun_prop⟩
  let bad : Set E := {z | f z ≠ 0}
  have open_bad : IsOpen bad := (isClosed_eq f.continuous continuous_const).isOpen_compl
  have finite_vertices : {z : E | T.IsVertex z.val}.Finite :=
    (Set.finite_range T.vertex).of_injOn (f := fun z : E => z.val.val)
      (fun _ hz => hz) (fun _ _ _ _ equal => Subtype.ext (Subtype.ext equal))
  have finite_bad : bad.Finite := finite_vertices.subset (by
    intro z hz
    by_contra nonvertex
    exact hz (C.bankMap_halfPlane_snd_eq_zero_of_nonvertex retain open_V e bank z.val
      nonvertex z.property))
  by_contra different
  let z : E := ⟨x, inside⟩
  have member : z ∈ bad := different
  have ambient_open : IsOpen (Subtype.val '' bad) := open_E.isOpenMap_subtype_val _ open_bad
  exact infinite_of_mem_nhds x (ambient_open.mem_nhds ⟨z, member, rfl⟩)
    (finite_bad.image Subtype.val)

end Unfoldings.TriangleComplex

namespace Unfoldings.SpatialFolding

open PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (F : SpatialFolding C)

include F in
theorem bankBoundary_iff_halfPlane_snd_eq_zero (retain : Set C.Seam)
    {U : Set (C.Realization retain)} (open_U : IsOpen U)
    {V : Set closedHalfPlane} (open_V : IsOpen V) (e : U ≃ₜ V) (p : U) :
    p.val ∈ C.bankBoundary retain ↔ (e p).val.val.2 = 0 := by
  let line : C(ℝ, closedHalfPlane) := ⟨fun t => ⟨(t, 0), by change (0 : ℝ) ≤ 0; rfl⟩,
    by fun_prop⟩
  let E : Set ℝ := line ⁻¹' V
  have open_E : IsOpen E := open_V.preimage line.continuous
  let into : C(E, V) := ⟨fun z => ⟨line z.val, z.property⟩,
    (line.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let f : C(E, C.Realization retain) := ⟨fun z => (e.symm (into z)).val,
    continuous_subtype_val.comp (e.symm.continuous.comp into.continuous)⟩
  have coordinates (z : E) : (e ⟨f z, (e.symm (into z)).property⟩).val.val.2 = 0 := by
    change (e (e.symm (into z))).val.val.2 = 0
    rw [e.apply_symm_apply]
    rfl
  have images : Set.range f ⊆ C.bankBoundary retain ∪ Set.range (C.vertexPoint retain) := by
    rintro _ ⟨z, rfl⟩
    by_cases bank : f z ∈ C.bankBoundary retain
    · exact Or.inl bank
    · right
      by_contra nonvertex
      have regular := F.isRegularPoint_of_not_bankBoundary_of_not_vertex retain (f z) bank nonvertex
      have positive := regular.halfPlane_image_positive open_U e (e.symm (into z)).property
      rw [coordinates] at positive
      exact lt_irrefl 0 positive
  have injective : Function.Injective f := by
    intro a b equal
    have points := e.symm.injective (Subtype.ext equal)
    have values : a.val = b.val := congrArg (fun z : V => z.val.val.1) points
    exact Subtype.ext values
  have all_bank : Set.range f ⊆ C.bankBoundary retain :=
    range_subset_closed_of_open_subset_perfect open_E f f.continuous
    (C.isClosed_bankBoundary retain) (Set.finite_range (C.vertexPoint retain)) images injective
  constructor
  · intro bank
    obtain ⟨b, y, equal⟩ := Set.mem_iUnion.mp bank
    have inside : C.bankMap retain b y ∈ U := equal.symm ▸ p.property
    have value := C.bankMap_halfPlane_snd_eq_zero retain open_U open_V e b y inside
    have same : (⟨C.bankMap retain b y, inside⟩ : U) = p := Subtype.ext equal
    rwa [same] at value
  · intro boundary
    have line_equal : line (e p).val.val.1 = (e p).val := by
      apply Subtype.ext
      exact Prod.ext rfl boundary.symm
    let z : E := ⟨(e p).val.val.1, by
      change line (e p).val.val.1 ∈ V
      rw [line_equal]
      exact (e p).property⟩
    apply all_bank
    refine ⟨z, ?_⟩
    have into_equal : into z = e p := Subtype.ext line_equal
    change (e.symm (into z)).val = p.val
    rw [into_equal, e.symm_apply_apply]

end Unfoldings.SpatialFolding
