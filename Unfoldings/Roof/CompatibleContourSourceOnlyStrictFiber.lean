module

public import Unfoldings.Roof.CompatibleContourSourceOnlyCollapseNames
public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofAddressCoverage
public import Unfoldings.Metric.BankStackArcFiber
public import Unfoldings.Metric.BankStackAddressPredicate
public import Unfoldings.Roof.CompatibleContourSourceOnlySmoothMarks

/-! The collapse fiber over any physical point with a single strict bank address is a chain of arcs. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)
  {slopes : Set Plane} (compact : IsCompact slopes) (nonempty : slopes.Nonempty)
  {boundary : (frontier slopes).Nonempty} {a β : ℝ}
  (R : K.CompatiblePotentialRouting {f | K.normalSlope f ∈ slopes}
    (K.clippedExtension slopes compact nonempty) boundary a β)
  (no_boundary : ∀ f, K.normalSlope f ∉ frontier slopes)
  (level : ℝ)
  (higher : ∀ v, (K.clippedExtension slopes compact nonempty).height (K.projectedVertex v) < level)
  (M : (K.clippedExtension slopes compact nonempty).FiniteSlopeModel)
  (positive : 0 < a) (inner_disk : Metric.ball (0 : Plane) a ⊆ slopes)
  (beta : 0 ≤ β) (acute : β < Real.pi / 2)

local notation "T" => K.compatibleCutMesh compact nonempty R no_boundary level higher M
  positive inner_disk
local notation "Fcut" => K.compatibleMeshForest compact nonempty R no_boundary level higher
  M positive inner_disk beta acute

local instance sourceOnlyStrictFiberIndexFintype : Fintype (T).Index :=
  @Fintype.ofFinite _ (T).finite

include beta acute

local notation "D" => SpatialEnvelope.Triangulation.pairedComplex
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T)
local notation "Selection" => PotentialCutForest.selection Fcut
variable (contour :
    (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.BoundaryContour
    ((K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.selectedRetain
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection))
  (starts : (K.compatibleCutMesh compact nonempty R no_boundary level higher M positive
      inner_disk).pairedComplex.contourOriginalVertex
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour 0 ∈
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).parents.roots)
  (W : R.WholeCutModel M)
  (models : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    BankGapModel
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyStrictFiberWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "Stack" => K.compatibleContourBankStack compact nonempty R no_boundary level higher
  M positive inner_disk beta acute contour
local notation "Pieces" => polygonalBankStackPiece W.Cut
  (fun event : Event => BankGapModel.region (models event))
local notation "Base" => K.compatibleContourSourceOnlyBaseMark compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Gap" => K.compatibleContourSourceOnlyGapMark compact nonempty R no_boundary level
  higher M positive inner_disk beta acute contour starts models

local notation "Attachment" => K.compatibleContourBankAttachment compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "ParamAt" => K.compatibleContourBankParameter compact nonempty R no_boundary
  level higher M positive inner_disk beta acute
local notation "BankAt[" e "]" => K.compatibleContourSourceBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "MovedAt[" e "]" => K.compatibleContourSourceOnlyBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "SpatialAt[" e "]" => K.compatibleContourPhysicalBank compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts e
local notation "Index" => K.compatibleContourSourceOnlyCellIndex compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models

local notation "Graft" => K.compatibleContourSourceOnlyGraft compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W models
local notation "FoldAt[" e "]" => K.compatibleContourSourceOnlyFrontierMap compact nonempty R
  no_boundary level higher M positive inner_disk beta acute contour starts models e
local notation "L" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Rgt" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams L Rgt

local notation "Surface" => SpatialEnvelope.wholeSurface M.plane

local notation "Point" => MetricGluing.point Pieces Banks
local notation "Phys" => K.compatibleContourPhysicalAttachmentPoint compact nonempty R no_boundary
  level higher M positive inner_disk beta acute contour starts W
local notation "Addr" => MetricGluing.BankStackAddress (G := Event) (Parameter := ParamAt)
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "AddressAt[" b "," e "," h "," t "]" => K.compatibleContourGapAddress compact
  nonempty R no_boundary level higher M positive inner_disk beta acute contour b e h t

local notation "Height" => SlopeEnvelope.height (K.clippedExtension slopes compact nonempty)
local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := ParamAt) Stack
local notation "Regular" => K.compatibleContourBankParameterInterior compact nonempty R no_boundary
  level higher M positive inner_disk beta acute

set_option maxHeartbeats 2950000 in
-- The arc endpoints and the marked seam coordinates belong to dependent original bank types.
/-- A canonical stack represents the full fiber if all physical addresses reduce
to its roof marks, gap list and consecutive seam pairs. -/
theorem compatibleContourSourceOnlyCollapse_fiber_of_address_pairs
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (f : Graft → Space) (image : Set.range f ⊆ Surface)
    (roof : ∀ x : W.Cut, f (Point ⟨none, x⟩) = (W.partition.restoreCut R.carrier x).val)
    (boundary_gap : ∀ (e : Event) (x : PolygonalPoint (models e).region)
      (h : x.val ∈ frontier (models e).region),
      f (Point ⟨some e, x⟩) = (FoldAt[e] ⟨x.val, h⟩).val)
    (marked : ∀ e : Event, (models e).HasMarkedCollapseFibers (SpatialAt[e])
      (fun y => f (Point ⟨some e, y⟩)))
    (b : Attachment) (t : ParamAt b)
    (stack_at : ∀ a (u : ParamAt a), Phys a u = Phys b t → Stack a = Stack b)
    (base_at : ∀ a (u : ParamAt a), Phys a u = Phys b t →
      ∀ side, Base a side u = Base b side t)
    (seam_at : ∀ (slot : MetricGluing.BankStackSlot Stack) (u : ParamAt slot.1),
      Phys slot.1 u = Phys b t → ∃ i : Fin ((Stack b).length + 1),
        L slot u = L ⟨b, i⟩ t ∧ Rgt slot u = Rgt ⟨b, i⟩ t)
    (pair_class : ∀ (i : Fin ((Stack b).length + 1)) (x : MetricGluing.Total Pieces),
      Relation.EqvGen Banks (L ⟨b, i⟩ t) x ↔ x = L ⟨b, i⟩ t ∨ x = Rgt ⟨b, i⟩ t)
    (avoids_source : ∀ (e : Event) (mem : e ∈ Stack b),
      AddressAt[b,e,mem,t] ≠ .inl (0, 0))
    (p : Space) (hp : p ∈ Surface) (position : Cap.horizontal p = Phys b t) :
    ContractibleSpace {x : Graft | f x = p} := by
  let tag (e : Event) (x : PolygonalPoint (models e).region) : MetricGluing.Total Pieces :=
    ⟨some e, x⟩
  have physical_injective (x : Graft) (equal : Cap.horizontal (f x) = Cap.horizontal p) :
      f x = p := by
    let H := SpatialEnvelope.wholeSurfaceHomeomorph M.plane
    have eq : H ⟨f x, image (Set.mem_range_self x)⟩ = H ⟨p, hp⟩ := equal
    exact congrArg Subtype.val (H.injective eq)
  have marked_phys (a : Addr) (ha : Valid a) :
      Cap.horizontal (f (Point (Mark a ha))) = Phys a.1 a.2.2.2 :=
    K.compatibleContourSourceOnlyCollapse_mark_horizontal compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W models geometry f roof boundary_gap
      a ha
  have tag_phys (a : Attachment) (e : Event) (h : e ∈ Stack a) (flag : Bool) (u : ParamAt a) :
      Cap.horizontal (f (Point (tag e (Gap a e h flag u)))) = Phys a u :=
    marked_phys ⟨a, some e, flag, u⟩ h
  have physical_slot (slot : MetricGluing.BankStackSlot Stack) (u : ParamAt slot.1) :
      Cap.horizontal (f (Point (L slot u))) = Phys slot.1 u := by
    let a := Named false slot u
    have key := marked_phys a (MetricGluing.bankStackEndpointAddress_valid Stack false slot u)
    rw [MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap false slot u] at key
    exact key.trans (congrArg (fun p : Σ a : Attachment, ParamAt a => Phys p.1 p.2)
      (MetricGluing.bankStackEndpointAddress_parameter Stack false slot u))
  have on_cut : Phys b t ∈ R.carrier := by
    cases b with
    | inl e =>
      exact K.compatibleContourParentMark_carrier compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W e.val e.property false t
    | inr e =>
      exact K.compatibleContourTerminalMark_carrier compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W e false t
  have roof_names (x : W.Cut) (h : f (Point ⟨none, x⟩) = p) : ∃ flag, x = Base b flag t := by
    let x_pos := Cap.horizontal (W.partition.restoreCut R.carrier x).val
    have restored : x_pos = Phys b t :=
      (congrArg Cap.horizontal ((roof x).symm.trans h)).trans position
    have at_cut : x_pos ∈ R.carrier := restored.symm ▸ on_cut
    have names : ∃ (a : Attachment) (side : Bool) (u : ParamAt a), Base a side u = x := by
      by_cases below : Height x_pos < level
      · obtain ⟨a, flag, u, eq⟩ := K.compatibleContourParentMark_exists_of_mem_cut_below
          compact nonempty R no_boundary level higher M positive inner_disk beta acute contour
          starts W x at_cut below
        exact ⟨.inl a, flag, u, eq⟩
      · obtain ⟨a, flag, u, eq⟩ := K.compatibleContourTailMark_exists_of_mem_cut_above
          compact nonempty R no_boundary level higher M positive inner_disk beta acute contour
          starts W x at_cut (le_of_not_gt below)
        exact ⟨.inr a, flag, u, eq⟩
    obtain ⟨a, flag, u, eq⟩ := names
    have a_phys : Phys a u = Phys b t := (marked_phys ⟨a, none, flag, u⟩ trivial).symm.trans
      ((congrArg (fun x => Cap.horizontal (f (Point ⟨none, x⟩))) eq).trans
        ((congrArg Cap.horizontal h).trans position))
    exact ⟨flag, eq.symm.trans (base_at a u a_phys flag)⟩
  have address_value (a : Attachment) (e : Event) (h : e ∈ Stack a) (u : ParamAt a) :
      f (Point (tag e (Gap a e h true u))) = (SpatialAt[e]).addressPoint AddressAt[a,e,h,u] := by
    let y := Gap a e h true u
    let mark := (models e).addressFrontier false AddressAt[a,e,h,u]
    have same_val : y.val = mark.val :=
      K.compatibleContourSourceOnlyGapMark_address compact nonempty R no_boundary level
        higher M positive inner_disk beta acute contour starts models a e h true u
    have boundary : y.val ∈ frontier (models e).region := same_val.symm ▸ mark.property
    have same_mark : (⟨y.val, boundary⟩ : frontier (models e).region) = mark :=
      Subtype.ext same_val
    have loc := K.compatibleContourSourceOnlyFrontierMap_address compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models e (geometry e) false
      AddressAt[a,e,h,u]
    exact (boundary_gap e y boundary).trans
      ((congrArg (fun q : frontier (models e).region => (FoldAt[e] q).val) same_mark).trans
        (congrArg Subtype.val loc))
  have gap_names (e : Event) (x : PolygonalPoint (models e).region)
      (h : f (Point (tag e x)) = p) : e ∈ Stack b := by
    have address_exists : p ∈ (SpatialAt[e]).carrier := (marked e).1 ⟨x, h⟩
    obtain ⟨addr, located⟩ := (SpatialAt[e]).exists_address address_exists
    obtain ⟨a, ha, u, named⟩ := K.exists_compatibleContourGapAddress_eq compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour e addr
    have at_p := (address_value a e ha u).trans ((congrArg ((SpatialAt[e]).addressPoint) named).trans located)
    have spatial := (tag_phys a e ha true u).symm.trans ((congrArg Cap.horizontal at_p).trans position)
    exact stack_at a u spatial ▸ ha
  have non_source (e : Event) (mem : e ∈ Stack b) :
      (BankAt[e]).addressPoint AddressAt[b,e,mem,t] ≠ (BankAt[e]).start := by
    intro at_start
    let a := AddressAt[b,e,mem,t]
    have source_mark : (models e).addressFrontier false a =
        (models e).addressFrontier false (.inl (0, 0)) := by
      apply Subtype.ext
      change (BankAt[e]).addressPoint a = (BankAt[e]).chain.point 0 0
      rw [PolygonalChain.point_zero, Fin.castSucc_zero]
      exact at_start
    have genuine := K.compatibleContourSourceOnlyBank_edge_ne_zero compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models e
    have is_source := (models e).address_eq_source (geometry e) genuine false a source_mark
    exact avoids_source e mem is_source
  have fiber_arc (i : Fin (Stack b).length) :
      let e := (Stack b).get i
      let mem := List.get_mem (Stack b) i
      ∃ P : Path (Gap b e mem false t) (Gap b e mem true t),
        Function.Injective P ∧ {x | f (Point (tag e x)) = p} = Set.range P := by
    let e := (Stack b).get i
    let mem := List.get_mem (Stack b) i
    let a := AddressAt[b,e,mem,t]
    obtain ⟨⟨original, values, injective, _⟩, _⟩ := (marked e).2 a
    have first : Gap b e mem false t = (models e).intrinsicAddressPoint true a :=
      K.compatibleContourSourceOnlyGapMark_eq_intrinsicAddress compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts models b e mem false t
    have last : Gap b e mem true t = (models e).intrinsicAddressPoint false a :=
      K.compatibleContourSourceOnlyGapMark_eq_intrinsicAddress compact nonempty R no_boundary
        level higher M positive inner_disk beta acute contour starts models b e mem true t
    let P := original.symm.cast first last
    have map_p : f (Point (tag e (Gap b e mem true t))) = p :=
      physical_injective _ ((tag_phys b e mem true t).trans position.symm)
    have value : (SpatialAt[e]).addressPoint a = p :=
      (address_value b e mem t).symm.trans map_p
    have path_range : Set.range P = Set.range original := original.symm_range
    refine ⟨P, ?_, ?_⟩
    · exact (injective (non_source e mem)).comp unitInterval.symm_involutive.injective
    · rw [path_range, ← values, value]
  exact MetricGluing.contractibleSpace_fiber_of_bank_stack_pairs Pieces Stack Base Gap b t f p
    (K.compatibleContourSourceOnlyGraft_exact compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry)
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour)
    pair_class
    (by
      intro x y joined inside
      obtain ⟨slot, u, rfl, rfl⟩ := joined
      exact seam_at slot u ((physical_slot slot u).symm.trans
        ((congrArg Cap.horizontal inside).trans position)))
    (fun i => physical_injective _ ((physical_slot ⟨b, i⟩ t).trans position.symm))
    roof_names gap_names fiber_arc

set_option maxHeartbeats 2950000 in
-- The arc endpoints and the marked seam coordinates belong to dependent original bank types.
/-- A single strict physical bank address gives the whole collapse fiber, with
the two roof copies and all the original gap arcs in their original order. -/
theorem compatibleContourSourceOnlyCollapse_fiber_of_strict_address
    (geometry : ∀ e : Event, OrientedBankGap BankAt[e] MovedAt[e])
    (f : Graft → Space) (image : Set.range f ⊆ Surface)
    (roof : ∀ x : W.Cut, f (Point ⟨none, x⟩) = (W.partition.restoreCut R.carrier x).val)
    (boundary_gap : ∀ (e : Event) (x : PolygonalPoint (models e).region)
      (h : x.val ∈ frontier (models e).region),
      f (Point ⟨some e, x⟩) = (FoldAt[e] ⟨x.val, h⟩).val)
    (marked : ∀ e : Event, (models e).HasMarkedCollapseFibers (SpatialAt[e])
      (fun y => f (Point ⟨some e, y⟩)))
    (b : Attachment) (t : ParamAt b) (regular : Regular b t)
    (unique : ∀ a (u : ParamAt a), Phys a u = Phys b t →
      (⟨a, u⟩ : Σ a : Attachment, ParamAt a) = ⟨b, t⟩)
    (p : Space) (hp : p ∈ Surface) (position : Cap.horizontal p = Phys b t) :
    ContractibleSpace {x : Graft | f x = p} := by
  have nodup := K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M
    positive inner_disk beta acute contour
  have named := K.compatibleContourSourceOnlyMarks_unique compact nonempty R no_boundary level
    higher M positive inner_disk beta acute contour starts W models geometry b t regular
  apply K.compatibleContourSourceOnlyCollapse_fiber_of_address_pairs compact nonempty R no_boundary
    level higher M positive inner_disk beta acute contour starts W models geometry f image roof
    boundary_gap marked b t ?_ ?_ ?_ ?_ ?_ p hp position
  · intro a u h
    exact congrArg (fun q : Σ a : Attachment, ParamAt a => Stack q.1) (unique a u h)
  · intro a u h side
    exact congrArg (fun q : Σ a : Attachment, ParamAt a => Base q.1 side q.2) (unique a u h)
  · rintro ⟨a, i⟩ u h
    have address := unique a u h
    have bank : a = b := congrArg Sigma.fst address
    subst a
    have time : u = t := eq_of_heq (Sigma.mk.inj address).2
    subst u
    exact ⟨i, rfl, rfl⟩
  · intro i
    exact MetricGluing.bankStack_eqvGen_pair_iff Stack Pieces Base Gap nodup ⟨b, i⟩ t named
  · intro e mem is_source
    cases b with
    | inl v =>
      have zero : t = 0 := congrArg Prod.snd (Sum.inl.inj is_source)
      exact regular.1.ne' zero
    | inr v =>
      change Sum.inr t = Sum.inl (0, 0) at is_source
      cases is_source

end Unfoldings.ConvexRoof
