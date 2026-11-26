module

public import Unfoldings.Roof.PotentialContourGapAddress
public import Unfoldings.Geometry.BankGapBendAddresses
public import Unfoldings.Cap.ContourLeafFans

/-! Literal marks at source corners and saved bank bends. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.PotentialCutForest

universe u v

set_option maxHeartbeats 2000000

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {f : Plane → ℝ} {cuts : Set Plane} (F : K.PotentialCutForest f cuts)
  (contour : C.BoundaryContour F.retain)

local notation "Event" => TriangleComplex.PositiveContourSource C F.selection contour
local notation "Stack" => contourAttachmentStack F contour
local notation "Param" => contourAttachmentParameter F
local notation "Length[" e "]" => TriangleComplex.positiveContourBankLength C F.selection contour e

variable (starts : C.contourOriginalVertex F.selection contour 0 ∈ F.parents.roots)
  (gaps : ∀ e : C.PositiveContourSource F.selection contour, OrientedBankGap (F.contourSourceRay contour starts e)
    (F.contourSourceOpenedRay contour starts e))

local notation "Attachment" => PotentialCutForest.ContourAttachment F
local notation "BankAt[" e "]" => F.contourSourceRay contour starts e
local notation "MovedAt[" e "]" => F.contourSourceOpenedRay contour starts e
local notation "Model[" e "]" => OrientedBankGap.model (gaps e)
local notation "Gap" => PotentialCutForest.contourGapMark F contour starts
  (fun e : Event => Model[e])
local notation "AddressAt[" b "," e "," h "," t "]" =>
  PotentialCutForest.contourGapAddress F contour b e h t

theorem contourGapBank_genuine (e : Event) (side : Bool) (i : Fin (Length[e] + 1)) :
    ((Model[e]).bank side).chain.edge i ≠ 0 := by
  let θ := C.interiorAngularDefect Set.univ (C.positiveContourVertex F.selection contour e)
  have genuine : (BankAt[e]).chain.edge i ≠ 0 :=
    C.boundaryChainRoll_edge_ne_zero (F.contourSourceBankChain contour starts e) i
  cases side
  · exact genuine
  · change ((BankAt[e]).rotateSuffix 0 θ).chain.edge i ≠ 0
    rw [(BankAt[e]).rotateSuffix_zero_edge]
    simpa only [map_zero] using (complexRotation θ).injective.ne genuine

/-- A bend is reached only by the two adjacent finite parameters on its original bank. -/
theorem contourGapMark_eq_bend (event : Event)
    (k : Fin Length[event]) (side : Bool)
    (bank : Attachment) (member : event ∈ Stack bank) (other : Bool) (t : Param bank)
    (same : Gap bank event member other t = (Model[event]).edgePoint side k.succ 0) :
    (!other) = side ∧
      (AddressAt[bank,event,member,t] = .inl (k.castSucc, 1) ∨
        AddressAt[bank,event,member,t] = .inl (k.succ, 0)) := by
  have coordinate : (Model[event]).addressFrontier (!other) AddressAt[bank,event,member,t] =
      (Model[event]).addressFrontier side (.inl (k.succ, 0)) := by
    apply Subtype.ext
    cases bank <;> cases other <;> exact congrArg PolygonalPoint.val same
  exact (Model[event]).addressFrontier_eq_bend (gaps event)
    (contourGapBank_genuine F contour starts gaps event) side (!other) k _ coordinate

/-- The common source is reached only by the two original bank starts. -/
theorem contourGapMark_eq_source (event : Event)
    (bank : Attachment) (member : event ∈ Stack bank) (side : Bool) (t : Param bank)
    (same : Gap bank event member side t = (Model[event]).edgePoint false 0 0) :
    AddressAt[bank,event,member,t] = .inl (0, 0) := by
  have coordinate : (Model[event]).addressFrontier (!side) AddressAt[bank,event,member,t] =
      (Model[event]).addressFrontier false (.inl (0, 0)) := by
    apply Subtype.ext
    cases bank <;> cases side <;> exact congrArg PolygonalPoint.val same
  exact (Model[event]).address_eq_source (gaps event)
    (contourGapBank_genuine F contour starts gaps event) (!side) _ coordinate

local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)

/-- On a single gap side, the child edge's endpoint and its parent edge's start are
the same actual bend. Both parameters keep their original attachment labels. -/
theorem contourGapMark_parent_join
    (v : C.Vertex Set.univ) (nonroot : v ∉ F.parents.roots)
    (parent_nonroot : F.parents.parent v ∉ F.parents.roots) (event : Event)
    (here : event ∈ Stack FiniteBank[v,nonroot])
    (above : event ∈ Stack FiniteBank[F.parents.parent v,parent_nonroot])
    (side : Bool) :
    Gap FiniteBank[v,nonroot] event here side 1 =
      Gap FiniteBank[F.parents.parent v,parent_nonroot] event above side 0 := by
  let parent := F.parents.parent v
  have edge_member (u : C.Vertex Set.univ) (h : u ∉ F.parents.roots)
      (member : event ∈ Stack FiniteBank[u,h]) :
      event ∈ C.contourEdgeGapStack F.selection contour u :=
    (C.mem_contourEdgeGapStack F.selection contour u event).mpr
      ((C.mem_contourSavedGapStack F.selection contour u event).mp member)
  let i := C.contourGapBankIndex F.selection contour v nonroot event (edge_member v nonroot here)
  let j := C.contourGapBankIndex F.selection contour parent parent_nonroot event
    (edge_member parent parent_nonroot above)
  have next : j.val = i.val + 1 :=
    C.contourGapBankIndex_parent F.selection contour v nonroot parent_nonroot event
      (edge_member v nonroot here) (edge_member parent parent_nonroot above)
  have vertex : i.succ = j.castSucc := Fin.ext next.symm
  apply PolygonalPoint.ext
  change ((Model[event]).bank (!side)).chain.point i 1 =
    ((Model[event]).bank (!side)).chain.point j 0
  rw [PolygonalChain.point_one, PolygonalChain.point_zero, vertex]

/-- An interior parent bend has exactly its incoming and outgoing parameters
on the same original bank side. -/
theorem contourGapMark_parent_bend_address
    (v : C.Vertex Set.univ) (nonroot : v ∉ F.parents.roots)
    (parent_nonroot : F.parents.parent v ∉ F.parents.roots) (event : Event)
    (here : event ∈ Stack FiniteBank[v,nonroot])
    (above : event ∈ Stack FiniteBank[F.parents.parent v,parent_nonroot])
    (side : Bool) (bank : Attachment) (member : event ∈ Stack bank)
    (other : Bool) (t : Param bank)
    (same : Gap bank event member other t =
      Gap FiniteBank[F.parents.parent v,parent_nonroot] event above side 0) :
    other = side ∧ ((⟨bank, t⟩ : Σ b : Attachment, Param b) = ⟨FiniteBank[v,nonroot], 1⟩ ∨
      (⟨bank, t⟩ : Σ b : Attachment, Param b) =
        ⟨FiniteBank[F.parents.parent v,parent_nonroot], 0⟩) := by
  let parent := F.parents.parent v
  let child_bank := FiniteBank[v,nonroot]
  let parent_bank := FiniteBank[parent,parent_nonroot]
  let edge_member (u : C.Vertex Set.univ) (h : u ∉ F.parents.roots)
      (mem : event ∈ Stack FiniteBank[u,h]) : event ∈ C.contourEdgeGapStack F.selection contour u :=
    (C.mem_contourEdgeGapStack F.selection contour u event).mpr
      ((C.mem_contourSavedGapStack F.selection contour u event).mp mem)
  let i := C.contourGapBankIndex F.selection contour v nonroot event (edge_member v nonroot here)
  let j := C.contourGapBankIndex F.selection contour parent parent_nonroot event
    (edge_member parent parent_nonroot above)
  have next : j.val = i.val + 1 :=
    C.contourGapBankIndex_parent F.selection contour v nonroot parent_nonroot event
      (edge_member v nonroot here) (edge_member parent parent_nonroot above)
  let k : Fin Length[event] := ⟨i.val, by have top := j.isLt; omega⟩
  have first : k.castSucc = i := Fin.ext rfl
  have last : k.succ = j := Fin.ext next.symm
  have bind : Gap bank event member other t = (Model[event]).edgePoint (!side) k.succ 0 :=
    same.trans (congrArg (fun l => (Model[event]).edgePoint (!side) l 0) last.symm)
  have named := F.contourGapMark_eq_bend contour starts gaps event k (!side)
    bank member other t bind
  refine ⟨?_, ?_⟩
  · simpa only [Bool.not_not] using congrArg Bool.not named.1
  rcases named.2 with h | h
  · have addr : AddressAt[child_bank,event,here,1] = .inl (k.castSucc, 1) :=
      congrArg (fun l => Sum.inl (l, (1 : unitInterval))) first.symm
    exact Or.inl (F.contourGapAddress_eq contour event child_bank bank here member 1 t
      (h.trans addr.symm))
  · have addr : AddressAt[parent_bank,event,above,0] = .inl (k.succ, 0) :=
      congrArg (fun l => Sum.inl (l, (0 : unitInterval))) last.symm
    exact Or.inr (F.contourGapAddress_eq contour event parent_bank bank above member 0 t
      (h.trans addr.symm))

local notation "SourceAt[" e "]" => TriangleComplex.positiveContourVertex C F.selection contour e
local notation "FirstEdge[" e "]" => (Sum.inl
  (Subtype.mk SourceAt[e] (TriangleComplex.positiveContourVertex_nonroot C F.selection contour e)) :
    Attachment)

/-- The literal source attachment uses the first finite edge for its entire parameter interval. -/
theorem contourGapMark_source_edge (event : Event)
    (member : event ∈ Stack FirstEdge[event]) (side : Bool) (t : unitInterval) :
    Gap FirstEdge[event] event member side t = (Model[event]).edgePoint (!side) 0 t := by
  let v := SourceAt[event]
  let nonroot := C.positiveContourVertex_nonroot F.selection contour event
  have at_edge : event ∈ C.contourEdgeGapStack F.selection contour v :=
    (C.mem_contourEdgeGapStack F.selection contour v event).mpr
      ((C.mem_contourSavedGapStack F.selection contour v event).mp member)
  have index := C.contourGapBankIndex_source F.selection contour event at_edge
  change (Model[event]).edgePoint (!side)
    (C.contourGapBankIndex F.selection contour v nonroot event at_edge) t = _
  exact congrArg (fun i => (Model[event]).edgePoint (!side) i t) index

/-- Both literal source attachment sides give the same intrinsic tip of the actual gap. -/
theorem contourGapMark_at_source (event : Event)
    (member : event ∈ Stack FirstEdge[event]) (side : Bool) :
    Gap FirstEdge[event] event member side 0 = (Model[event]).edgePoint false 0 0 := by
  refine (F.contourGapMark_source_edge contour starts gaps event member side 0).trans ?_
  cases side
  · apply PolygonalPoint.ext
    have tip : ((Model[event]).edgePoint true 0 0).val = (MovedAt[event]).start := by
      rw [BankGapModel.edgePoint_val, PolygonalChain.point_zero, Fin.castSucc_zero]
      rfl
    have old : ((Model[event]).edgePoint false 0 0).val = (BankAt[event]).start := by
      rw [BankGapModel.edgePoint_val, PolygonalChain.point_zero, Fin.castSucc_zero]
      rfl
    exact tip.trans ((gaps event).common.trans old.symm)
  · rfl

/-- Every mark incident to the common source uses exactly its original first finite attachment. -/
theorem contourGapMark_eq_source_attachment (event : Event)
    (member : event ∈ Stack FirstEdge[event]) (bank : Attachment)
    (other_member : event ∈ Stack bank) (side : Bool) (t : Param bank)
    (same : Gap bank event other_member side t = (Model[event]).edgePoint false 0 0) :
    (⟨bank, t⟩ : Σ b : Attachment, Param b) = ⟨FirstEdge[event], 0⟩ := by
  have source_index := F.contourGapMark_eq_source contour starts gaps event bank other_member side t same
  have named : AddressAt[FirstEdge[event],event,member,0] = .inl (0, 0) :=
    congrArg (fun i => Sum.inl (i, (0 : unitInterval)))
      (C.contourGapBankIndex_source F.selection contour event _)
  exact F.contourGapAddress_eq contour event FirstEdge[event] bank member other_member 0 t
    (source_index.trans named.symm)

end Unfoldings.ConvexRoof.PotentialCutForest
