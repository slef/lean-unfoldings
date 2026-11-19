module

public import Unfoldings.Geometry.SourceGapBankRetraction
public import Unfoldings.Geometry.PolygonalRayMapContinuity
public import Unfoldings.Geometry.BankGapBoundaryMap

/-! A continuous collapse of the whole source-only gap to its original physical path. -/

@[expose] public section

noncomputable section

open scoped NNReal

namespace Unfoldings.OrientedBankGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {n : ℕ} {B : PolygonalRay ℂ n} {θ : ℝ} (G : OrientedBankGap B (B.rotateSuffix 0 θ))
  (Q : PolygonalRay F n)

/-- Map the whole gap to the original physical ray, keeping the literal boundary addresses. -/
def collapseTo (x : PolygonalPoint G.model.region) : Q.carrier :=
  B.mapCarrier Q (G.projectFirstBank x)

variable (genuine : ∀ i, B.chain.edge i ≠ 0)

include genuine in
theorem continuous_collapseTo : Continuous (G.collapseTo Q) :=
  (B.continuous_mapCarrier G.first_outward genuine G.first_nonzero Q).comp
    G.continuous_projectFirstBank

include genuine in
/-- The gap collapse has compact inverse images of compact portions of the physical path. -/
theorem isProperMap_collapseTo (target_nonzero : Q.direction ≠ 0) :
    IsProperMap (G.collapseTo Q) :=
  (B.isProperMap_mapCarrier G.first_outward genuine G.first_nonzero Q target_nonzero).comp
    G.isProperMap_projectFirstBank

include genuine in
@[simp] theorem collapseTo_edgePoint (side : Bool) (i : Fin n) (t : unitInterval) :
    G.collapseTo Q (G.model.edgePoint side i t) =
      ⟨Q.addressPoint (.inl (i, t)), Q.addressPoint_mem (.inl (i, t))⟩ := by
  rw [collapseTo, G.projectFirstBank_edgePoint]
  exact B.mapCarrier_address G.first_outward genuine G.first_nonzero Q (.inl (i, t))

include genuine in
@[simp] theorem collapseTo_tailPoint (side : Bool) (t : ℝ≥0) :
    G.collapseTo Q (G.model.tailPoint side t) =
      ⟨Q.addressPoint (.inr t), Q.addressPoint_mem (.inr t)⟩ := by
  rw [collapseTo, G.projectFirstBank_tailPoint]
  exact B.mapCarrier_address G.first_outward genuine G.first_nonzero Q (.inr t)

include genuine in
/-- The continuous collapse extends the already-defined original physical frontier map. -/
theorem collapseTo_eq_frontierMap
    (moved_genuine : ∀ i, (B.rotateSuffix 0 θ).chain.edge i ≠ 0)
    (x : PolygonalPoint G.model.region) (boundary : x.val ∈ frontier G.model.region) :
    G.collapseTo Q x = G.model.frontierMap Q ⟨x.val, boundary⟩ := by
  have member : x.val ∈ B.carrier ∪ (B.rotateSuffix 0 θ).carrier :=
    G.model.frontier_eq ▸ boundary
  have address : ∃ (side : Bool) (a : PolygonalRay.Address n),
      (G.model.bank side).addressPoint a = x.val := by
    rcases member with h | h
    · obtain ⟨a, ha⟩ := B.exists_address h
      exact ⟨false, a, ha⟩
    · obtain ⟨a, ha⟩ := (B.rotateSuffix 0 θ).exists_address h
      exact ⟨true, a, ha⟩
  obtain ⟨side, a, equal⟩ := address
  have label : G.model.addressFrontier side a = ⟨x.val, boundary⟩ := Subtype.ext equal
  refine Eq.trans ?_ ((G.model.frontierMap_address G.first_outward genuine G.first_nonzero
    G.second_outward moved_genuine G.second_nonzero G.common Q side a).symm.trans
      (congrArg (G.model.frontierMap Q) label))
  cases a with
  | inl p =>
    have marked : G.model.edgePoint side p.1 p.2 = x := PolygonalPoint.ext equal
    exact (congrArg (G.collapseTo Q) marked).symm.trans
      (G.collapseTo_edgePoint Q genuine side p.1 p.2)
  | inr t =>
    have marked : G.model.tailPoint side t = x := PolygonalPoint.ext equal
    exact (congrArg (G.collapseTo Q) marked).symm.trans
      (G.collapseTo_tailPoint Q genuine side t)

end Unfoldings.OrientedBankGap
