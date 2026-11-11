module

public import Unfoldings.Cap.ProjectedDevelopedMap
public import Unfoldings.Cap.RadialSourceCopy

/-! The actual developed map also extends continuously over points with coincident bank values. -/

@[expose] public section

noncomputable section

namespace Unfoldings.FacewiseDevelopment

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {retain : Set C.Seam} (D : FacewiseDevelopment C retain) (K : ConvexCap C)

def ProjectedCoherentAt (p : Plane) : Prop :=
  ∀ f g, p ∈ (K.projectedTriangle f).carrier → p ∈ (K.projectedTriangle g).carrier →
    D.projectedPlacement K f p = D.projectedPlacement K g p

theorem projected_coherentAt_of_not_cut {p : Plane} (outside : p ∉ K.projectedCutSet retain) :
    D.ProjectedCoherentAt K p :=
  fun _ _ first last => D.projectedPlacement_eq_away_cuts K first last outside

theorem projectedMap_eq_of_coherent {p : Plane} {f : Face}
    (coherent : D.ProjectedCoherentAt K p) (member : p ∈ (K.projectedTriangle f).carrier) :
    D.projectedMap K p = D.projectedPlacement K f p := by
  have footprint : p ∈ K.footprint :=
    K.footprint_eq_union_projectedTriangles.symm.subset (Set.mem_iUnion.mpr ⟨f, member⟩)
  simp only [projectedMap, dite_eq_left footprint]
  exact coherent _ _
    (Set.mem_iUnion.mp (K.footprint_eq_union_projectedTriangles.subset footprint)).choose_spec
    member

/-- The domain includes uncut points and every cut endpoint whose placed copies agree. -/
theorem projectedMap_continuousOn_coherent :
    ContinuousOn (D.projectedMap K) {p | p ∈ K.footprint ∧ D.ProjectedCoherentAt K p} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let S := {p | p ∈ K.footprint ∧ D.ProjectedCoherentAt K p}
  let piece : Face → Set S := fun f => {x | x.val ∈ (K.projectedTriangle f).carrier}
  have cover : ⋃ f, piece f = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨f, member⟩ := Set.mem_iUnion.mp
      (K.footprint_eq_union_projectedTriangles.subset x.property.1)
    exact Set.mem_iUnion.mpr ⟨f, member⟩
  apply (locallyFinite_of_finite piece).continuous cover
    (fun f => (K.projectedTriangle f).compact_carrier.isClosed.preimage continuous_subtype_val)
  intro f
  have continuous : Continuous (fun x : S => D.projectedPlacement K f x.val) :=
    (D.projectedPlacement K f).continuous_of_finiteDimensional.comp continuous_subtype_val
  exact continuous.continuousOn.congr
    (fun x member => D.projectedMap_eq_of_coherent K x.property.2 member)

/-- Coherence at an original vertex follows from equality of its actual developed copies. -/
theorem projected_coherentAt_vertex (v : C.Vertex Set.univ)
    (copies : ∀ a b : C.Vertex retain,
      C.vertexForgetCuts (Set.subset_univ retain) a = v →
      C.vertexForgetCuts (Set.subset_univ retain) b = v →
      D.toPlane (C.vertexPoint retain a) = D.toPlane (C.vertexPoint retain b)) :
    D.ProjectedCoherentAt K (K.projectedVertex v) := by
  intro f g first last
  obtain ⟨i, at_first⟩ := K.projected_corner_of_vertex_mem v f first
  obtain ⟨j, at_last⟩ := K.projected_corner_of_vertex_mem v g last
  have original_first : C.vertexForgetCuts (Set.subset_univ retain)
      (C.vertexOfCorner retain (f, i)) = v := by
    rw [C.vertexForgetCuts_vertexOfCorner]
    exact K.projectedVertex_injective at_first
  have original_last : C.vertexForgetCuts (Set.subset_univ retain)
      (C.vertexOfCorner retain (g, j)) = v := by
    rw [C.vertexForgetCuts_vertexOfCorner]
    exact K.projectedVertex_injective at_last
  have values := copies _ _ original_first original_last
  have first_value : D.projectedPlacement K f (K.projectedVertex v) =
      D.toPlane (C.vertexPoint retain (C.vertexOfCorner retain (f, i))) := by
    rw [← at_first]
    exact D.projectedPlacement_apply K f ((C.triangle f).vertex i)
  have last_value : D.projectedPlacement K g (K.projectedVertex v) =
      D.toPlane (C.vertexPoint retain (C.vertexOfCorner retain (g, j))) := by
    rw [← at_last]
    exact D.projectedPlacement_apply K g ((C.triangle g).vertex j)
  exact first_value.trans (values.trans last_value.symm)

end FacewiseDevelopment

namespace ConvexCap.RadialCutForest

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexCap C} {q : Plane} {cuts : Set Plane} (R : K.RadialCutForest q cuts)

theorem completed_source_projected_coherent (D : FacewiseDevelopment C R.completedRetain)
    (source : C.Vertex Set.univ) (at_source : K.projectedVertex source = q)
    (internal : ¬ C.IsBoundaryVertex Set.univ source) : D.ProjectedCoherentAt K q := by
  suffices coherent : D.ProjectedCoherentAt K (K.projectedVertex source) by
    simpa only [at_source] using coherent
  apply D.projected_coherentAt_vertex K source
  intro a b first last
  exact congrArg (fun v => D.toPlane (C.vertexPoint R.completedRetain v))
    (R.completed_source_copy_unique at_source internal a b first last)

end ConvexCap.RadialCutForest
end Unfoldings
