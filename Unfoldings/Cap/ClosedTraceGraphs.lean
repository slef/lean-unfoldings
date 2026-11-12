module

public import Unfoldings.Cap.RadialStripPhysicalMap
public import Unfoldings.Cap.ProjectedDenseSeparation

/-! Compact approached trace graphs cover every actual closed face over the controlled region. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {source : Plane} {cuts : Set Plane} {N : K.RadialCutForest source cuts}
  {D : FacewiseDevelopment C N.retain} {t : ℝ} {positive : 0 < t} {small : t < 1}
  {calibration : Plane ≃ₗᵢ[ℝ] ℂ} {i : FiveSector} {S : MonotoneStrip} {ε cutoff : ℝ}

namespace RadialStripTraceData

variable (data : N.RadialStripTraceData positive small D calibration i S ε cutoff)

def closedGraph : Set (Plane × Plane) :=
  (fun z : ℂ => (source + (fiveSectorFrame t positive small i).place.symm z,
    data.outputFrame.symm (data.value z))) '' closure (S.openSlab 0 cutoff)

theorem isCompact_closedGraph : IsCompact data.closedGraph :=
  (S.isCompact_closure_openSlab 0 cutoff).image
    ((continuous_const.add (fiveSectorFrame t positive small i).place.symm.continuous).prodMk
      (data.outputFrame.symm.continuous.comp data.continuous))

theorem graph_mem_of_physicalDomain {p : Plane} (member : p ∈ data.physicalDomain) :
    (p, D.projectedMap K p) ∈ data.closedGraph := by
  let frame := (fiveSectorFrame t positive small i).place
  refine ⟨frame (p - source), subset_closure member, ?_⟩
  apply Prod.ext
  · change source + frame.symm (frame (p - source)) = p
    rw [frame.symm_apply_apply]
    abel
  · change data.outputFrame.symm (data.value
      ((fiveSectorFrame t positive small i).place (p - source))) = D.projectedMap K p
    rw [data.physical_value member, data.outputFrame.symm_apply_apply]

end RadialStripTraceData

/-- The two coordinates retain both the physical point and its actual containing-face copy.
A finite closed cover and density remove every omitted waterfall wall and face edge. -/
theorem exists_closed_trace_of_face_point
    (P : ∀ a : FiveSector, (fiveSectorFrame t positive small a).enclosingStrip.Subdivision)
    (traces : ∀ a : FiveSector, ∀ cell : {S : MonotoneStrip // S ∈ (P a).cells},
      N.RadialStripTraceData positive small D calibration a cell.val ε cutoff)
    {U : Set Plane} (opened : IsOpen U)
    (inside : U ⊆ sectorSweepInterior positive small source cutoff)
    (f : Face) {p : Plane} (member : p ∈ (K.projectedTriangle f).carrier ∩ U) :
    ∃ a : FiveSector, ∃ cell : {S : MonotoneStrip // S ∈ (P a).cells}, ∃ z : ℂ,
      z ∈ closure (cell.val.openSlab 0 cutoff) ∧
      p = source + (fiveSectorFrame t positive small a).place.symm z ∧
      D.projectedPlacement K f p = (traces a cell).outputFrame.symm ((traces a cell).value z) := by
  let : ∀ a : FiveSector, Finite {S : MonotoneStrip // S ∈ (P a).cells} :=
    fun a => (P a).cells.finite_toSet.to_subtype
  let graphs := ⋃ a : FiveSector, ⋃ cell : {S : MonotoneStrip // S ∈ (P a).cells},
    (traces a cell).closedGraph
  have graphs_closed : IsClosed graphs := isClosed_iUnion_of_finite fun a =>
    isClosed_iUnion_of_finite fun cell => (traces a cell).isCompact_closedGraph.isClosed
  let graph := fun q : Plane => (q, D.projectedPlacement K f q)
  have graph_continuous : Continuous graph :=
    continuous_id.prodMk
      (D.projectedPlacement K f).toContinuousAffineEquiv.toHomeomorph.continuous
  have closed_preimage : IsClosed (graph ⁻¹' graphs) := graphs_closed.preimage graph_continuous
  let A := sectorWaterfallRegular positive small source P
  let V := interior (K.projectedTriangle f).carrier ∩ U
  have cover_dense : A ∩ V ⊆ graph ⁻¹' graphs := by
    rintro q ⟨regular, face, in_region⟩
    obtain ⟨a, S, cell, in_strip⟩ := sectorWaterfallRegular_mem_openSlab positive small source P
      regular (inside in_region)
    have actual := (traces a ⟨S, cell⟩).graph_mem_of_physicalDomain in_strip
    rw [D.projectedMap_eq_on_face_interior K face] at actual
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨⟨S, cell⟩, actual⟩⟩
  have cover_interior : V ⊆ graph ⁻¹' graphs := by
    intro q local_member
    have approached : q ∈ closure (A ∩ V) :=
      (isOpen_interior.inter opened).closure_inter
        ⟨dense_sectorWaterfallRegular positive small source P q, local_member⟩
    exact closure_minimal cover_dense closed_preimage approached
  have regular_closed : closure (interior (K.projectedTriangle f).carrier) =
      (K.projectedTriangle f).carrier :=
    ((K.projectedTriangle f).convex_carrier.closure_interior_eq_closure_of_nonempty_interior
      (K.projectedTriangle f).interior_nonempty).trans
      (K.projectedTriangle f).compact_carrier.isClosed.closure_eq
  have approached : p ∈ closure V :=
    opened.closure_inter ⟨regular_closed.symm ▸ member.1, member.2⟩
  have in_graph := closure_minimal cover_interior closed_preimage approached
  obtain ⟨a, in_graph⟩ := Set.mem_iUnion.mp in_graph
  obtain ⟨cell, z, closed, equal⟩ := Set.mem_iUnion.mp in_graph
  exact ⟨a, cell, z, closed, (congrArg Prod.fst equal).symm, (congrArg Prod.snd equal).symm⟩

end Unfoldings.ConvexCap.RadialCutForest
