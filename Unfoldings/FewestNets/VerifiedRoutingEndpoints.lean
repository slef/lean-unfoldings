module

public import Unfoldings.FewestNets.VerifiedRoutingCellNet
public import Unfoldings.FewestNets.IcosahedronEndpointBounds
public import Unfoldings.FewestNets.IcosahedronFrequency400Endpoint

/-! Exact finite routing-table coverage discharges both endpoint development obligations. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FewestNets.Icosahedron

open MeshStar InnerProductGeometry Real

universe u v

/-- Every canonical local star has a geometric witness and checked scalar data. -/
def HasVerifiedRoutingTable (q : ℕ) (target : ℚ) : Prop :=
  ∀ key ∈ meshRecordKeys q, ∃ record : MeshRoutingRecord q key, record.Verified target

theorem hasVerifiedRoutingTable_of_keys {q : ℕ} {target : ℚ}
    (table : List (Σ key, {row : MeshRoutingRecord q key // row.Verified target}))
    (keys : table.map Sigma.fst = meshRecordKeys q) : HasVerifiedRoutingTable q target := by
  intro key present
  rw [← keys] at present
  obtain ⟨⟨other, record, verified⟩, _, equal⟩ := List.mem_map.mp present
  change other = key at equal
  subst other
  exact ⟨record, verified⟩

/-- Cover the canonical key list by separately verified consecutive slices. -/
theorem hasVerifiedRoutingTable_of_sliceProviders {q batches size : ℕ} {target : ℚ}
    (positive : 0 < size) (capacity : (meshRecordKeys q).length ≤ batches * size)
    (verify : ∀ (i : Fin batches) key,
      key ∈ ((meshRecordKeys q).drop (size * i.val)).take size →
      ∃ row : MeshRoutingRecord q key, row.Verified target) :
    HasVerifiedRoutingTable q target := by
  intro key member
  obtain ⟨j, at_key⟩ := List.mem_iff_get.mp member
  let i : Fin batches := ⟨j.val / size, (Nat.div_lt_iff_lt_mul positive).mpr
    (j.isLt.trans_le capacity)⟩
  let t := j.val % size
  have idx : size * i.val + t = j.val := Nat.div_add_mod _ _
  have t_small : t < size := Nat.mod_lt _ positive
  have fits : t < (((meshRecordKeys q).drop (size * i.val)).take size).length := by
    rw [List.length_take, List.length_drop]
    exact lt_min t_small (by have lt := j.isLt; omega)
  have same : (((meshRecordKeys q).drop (size * i.val)).take size)[t]'fits = key := by
    rw [List.getElem_take, List.getElem_drop]
    exact (congrArg (meshRecordKeys q).get (Fin.ext idx)).trans at_key
  exact verify i key (same ▸ List.getElem_mem fits)

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

include P in
theorem component_nets_of_verified_routingTable {q : ℕ} (qbig : 100 ≤ q)
    (outward : ∀ key ∈ meshRecordKeys q, ∀ k,
      0 < inner ℝ (key.model q).direction ((key.model q).dual k))
    {target : ℚ} (target_nonneg : 0 ≤ target)
    (table : HasVerifiedRoutingTable q target)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ (target : ℝ) * π / 180)
    (g : SpatialRotation) (label : Face → meshSites q)
    (chosen : ∀ f, N.normal f ∈ strictVoronoiCone (fun b : meshSites q =>
      SpatialRotation.linear g (b : Space)) (label f))
    (c : (C.labeledSeamGraph label).ConnectedComponent) :
    C.HasOriginalEdgeNet c.supp := by
  have hq : 0 < q := by omega
  obtain ⟨seed, rfl⟩ := c.exists_rep
  let a := label seed
  obtain ⟨site, _, realized⟩ := exists_perimeterIndex_realizing hq a
  let key := perimeterIndexRecordKey site
  have present : key ∈ meshRecordKeys q := perimeterIndexRecordKey_mem site
  obtain ⟨row, verified⟩ := table key present
  obtain ⟨R⟩ : Nonempty (MeshStarRealization a (key.model q)) := by
    rcases site with branch | (branch | branch) <;> exact realized
  exact hasOriginalEdgeNet_of_verified_routing_record hq qbig R (outward key present)
    target_nonneg row verified P N g label chosen angles seed rfl

theorem q100_model_outward (key : MeshRecordKey) (member : key ∈ meshRecordKeys 100)
    (k : Fin (key.sidePred + 1)) : 0 < inner ℝ (key.model 100).direction ((key.model 100).dual k) := by
  cases key with
  | face i j =>
    exact (q100_face_corner_bounds (by simpa [meshRecordKeys] using member) k).1
  | seam i =>
    exact (q100_seam_corner_bounds (by simpa [meshRecordKeys] using member) k).1
  | vertex => exact (q100_pentagon_corner_bounds k).1

theorem q400_model_outward (key : MeshRecordKey) (member : key ∈ meshRecordKeys 400)
    (k : Fin (key.sidePred + 1)) : 0 < inner ℝ (key.model 400).direction ((key.model 400).dual k) := by
  cases key with
  | face i j =>
    exact (q400_face_corner_bounds (by simpa [meshRecordKeys] using member) k).1
  | seam i =>
    exact (q400_seam_corner_bounds (by simpa [meshRecordKeys] using member) k).1
  | vertex => exact (q400_pentagon_corner_bounds k).1

include P N in
/-- The first endpoint follows from exact geometric routing-table coverage. -/
theorem exists_netPartition_lt_q100_of_verified_routingTable
    (table : HasVerifiedRoutingTable 100 81)
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ 81 * π / 180) :
    ∃ n < 11300000, C.HasNetPartition n := by
  apply P.exists_netPartition_lt_q100_of_component_nets N angles
  exact component_nets_of_verified_routingTable P N (by decide) q100_model_outward (by norm_num)
    table (by simpa using angles)

include P N in
/-- The second endpoint follows from exact geometric routing-table coverage. -/
theorem exists_netPartition_lt_q400_of_verified_routingTable
    (table : HasVerifiedRoutingTable 400 (832067 / 10000))
    (angles : ∀ f i, (C.triangle f).cornerAngle i ≤ 83.2067 * π / 180) :
    ∃ n < 200700000, C.HasNetPartition n := by
  apply P.exists_netPartition_lt_q400_of_component_nets N angles
  exact component_nets_of_verified_routingTable P N (by decide) q400_model_outward (by norm_num)
    table (fun f i => by
      have exact_degrees : (((832067 / 10000 : ℚ) : ℝ)) = 83.2067 := by norm_num
      rw [exact_degrees]
      exact angles f i)

end Unfoldings.FewestNets.Icosahedron
