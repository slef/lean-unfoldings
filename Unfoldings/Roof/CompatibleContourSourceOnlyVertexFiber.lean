module

public import Unfoldings.Metric.BankStackTrimmedFiber
public import Unfoldings.Roof.CompatibleContourSourceOnlyOffCutFiber
public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofAddressCoverage
public import Unfoldings.Roof.CompatibleContourSourceOnlyRoofVertexBall
public import Unfoldings.Roof.CompatibleContourSourceOnlyVertexSeparation
public import Unfoldings.Roof.CompatibleContourPhysicalVertexAttachments

/-! Full collapse fibers over fine vertices of the original cut forest. -/

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

local instance sourceOnlyVertexFiberIndexFintype : Fintype (T).Index :=
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
  (geometry : ∀ event : (K.compatibleCutMesh compact nonempty R no_boundary level higher M
      positive inner_disk).pairedComplex.PositiveContourSource
      (K.compatibleMeshForest compact nonempty R no_boundary level higher M positive
        inner_disk beta acute).selection contour,
    OrientedBankGap
      (K.compatibleContourSourceBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event)
      (K.compatibleContourSourceOnlyBank compact nonempty R no_boundary level higher M positive
        inner_disk beta acute contour starts event))

local instance sourceOnlyVertexFiberWholeFintype : Fintype W.Index := W.finiteIndex

local notation "Event" => TriangleComplex.PositiveContourSource D Selection contour
local notation "models" => (fun event : Event => OrientedBankGap.model (geometry event))
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

local notation "Conforming" => K.compatibleCutMesh_conforming compact nonempty R no_boundary
  level higher M positive inner_disk
local notation "Inside" => K.compatible_section_interior compact nonempty R level higher M
local notation "Q" => SpatialEnvelope.Triangulation.roof
  (SpatialEnvelope.ConstrainedTriangulation.toTriangulation T) Conforming Inside
local notation "VertexAt[" v "]" => ConvexRoof.projectedVertex Q v
local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection contour e
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "RoofTime" => MetricGluing.bankStackRoofTime (Parameter := ParamAt) Stack

set_option maxHeartbeats 5600000 in
/-- The full fiber at a fine nonroot vertex is its outgoing stack of marked
arcs, with the possible final source tip identified as one point. -/
theorem compatibleContourSourceOnlyCollapse_fiber_of_vertex
    (f : Graft → Space) (image : Set.range f ⊆ Surface)
    (roof : ∀ x : W.Cut, f (Point ⟨none, x⟩) = (W.partition.restoreCut R.carrier x).val)
    (boundary_gap : ∀ (e : Event) (x : PolygonalPoint (models e).region)
      (h : x.val ∈ frontier (models e).region),
      f (Point ⟨some e, x⟩) = (FoldAt[e] ⟨x.val, h⟩).val)
    (marked : ∀ e : Event, (models e).HasMarkedCollapseFibers (SpatialAt[e])
      (fun y => f (Point ⟨some e, y⟩)))
    (v : Edge) (p : Space) (hp : p ∈ Surface)
    (position : Cap.horizontal p = VertexAt[v.val]) :
    ContractibleSpace {x : Graft | f x = p} := by
  classical
  let b : Attachment := .inl v
  let xs := Stack b
  let vertex (i : Fin (xs.length + 1)) := Point (L ⟨b, i⟩ 0)
  let tag (e : Event) (x : PolygonalPoint (models e).region) : MetricGluing.Total Pieces :=
    ⟨some e, x⟩
  have at_vertex : Phys b 0 = Cap.horizontal p := (K.compatibleContourPhysicalAttachmentPoint_finite
    compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W v 0
    ).trans ((AffineMap.lineMap_apply_zero ..).trans position.symm)
  have below : Height VertexAt[v.val] < level :=
    K.compatibleMesh_nonroot_height_lt compact nonempty R no_boundary level higher M positive
      inner_disk beta acute v.val v.property
  have locations (a : Attachment) (u : ParamAt a) (at_p : Phys a u = Cap.horizontal p) :=
    K.compatibleContourPhysicalAttachmentPoint_at_vertex compact nonempty R no_boundary level
      higher M positive inner_disk beta acute contour starts W v.val below a u (at_p.trans position)
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
  have joined (a : Attachment) (i : Fin ((Stack a).length + 1)) (u : ParamAt a) :
      Point (L ⟨a, i⟩ u) = Point (Rgt ⟨a, i⟩ u) :=
    MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨⟨a, i⟩, u, rfl, rfl⟩
  have vertex_fiber (i : Fin (xs.length + 1)) : f (vertex i) = p :=
    physical_injective _ ((physical_slot ⟨b, i⟩ 0).trans at_vertex)
  have named_value (a : Attachment) (e : Event) (mem : e ∈ Stack a) (u : ParamAt a) :
      Cap.horizontal ((SpatialAt[e]).addressPoint AddressAt[a,e,mem,u]) = Phys a u :=
    congrArg Cap.horizontal (K.compatibleContourPhysicalBank_addressPoint_eq_restore compact
      nonempty R no_boundary level higher M positive inner_disk beta acute contour starts W e a mem u)
  have all_gaps (e : Event) (x : PolygonalPoint (models e).region)
      (hx : f (Point (tag e x)) = p) : e ∈ xs := by
    obtain ⟨addr, located⟩ := (SpatialAt[e]).exists_address ((marked e).1 ⟨x, hx⟩)
    obtain ⟨a, mem, u, named⟩ := K.exists_compatibleContourGapAddress_eq compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour e addr
    have at_p : (SpatialAt[e]).addressPoint AddressAt[a,e,mem,u] = p :=
      (congrArg ((SpatialAt[e]).addressPoint) named).trans located
    have phys := (named_value a e mem u).symm.trans (congrArg Cap.horizontal at_p)
    obtain ⟨child, ⟨address, at_v⟩ | ⟨address, at_v⟩⟩ := locations a u phys
    · have same : a = b := (congrArg Sigma.fst address).trans
        (congrArg Sum.inl (Subtype.ext at_v))
      exact Eq.mp (congrArg (fun a => e ∈ Stack a) same) mem
    · have same : a = .inl child := congrArg Sigma.fst address
      have here : e ∈ Stack (.inl child) := same ▸ mem
      have path := ((D).mem_contourSavedGapStack Selection contour child.val e).mp here
      exact ((D).mem_contourSavedGapStack Selection contour v.val e).mpr
        (at_v ▸ AscendingParents.Ancestor.trans (Fcut).parents path ((Fcut).parents.ancestor_parent child.val))
  have roof_at_slot (a : Attachment) (flag : Bool) (u : ParamAt a) :
      let time := RoofTime a flag u
      Point ⟨none, Base a flag u⟩ = Point (L time.1 time.2) := by
    let time := RoofTime a flag u
    have eq := MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap flag time
      a flag u (MetricGluing.bankStackRoofTime_address Stack a flag u)
    change Point ⟨none, Base a flag u⟩ = Point (L time.1 time.2)
    cases flag
    · exact congrArg Point eq.symm
    · exact (congrArg Point eq.symm).trans (joined _ _ _).symm
  have all_roof (x : W.Cut) (hx : f (Point ⟨none, x⟩) = p) :
      ∃ i, Point ⟨none, x⟩ = vertex i := by
    let x_pos := Cap.horizontal (W.partition.restoreCut R.carrier x).val
    have x_loc : x_pos = Cap.horizontal p := congrArg Cap.horizontal ((roof x).symm.trans hx)
    have on_cut : Phys b 0 ∈ R.carrier :=
      K.compatibleContourParentMark_carrier compact nonempty R no_boundary level higher M
        positive inner_disk beta acute contour starts W v.val v.property false 0
    have on_cut_x : x_pos ∈ R.carrier := (x_loc.trans at_vertex.symm).symm ▸ on_cut
    have below_x : Height x_pos < level := (x_loc.trans position).symm ▸ below
    obtain ⟨child, flag, u, label⟩ := K.compatibleContourParentMark_exists_of_mem_cut_below
      compact nonempty R no_boundary level higher M positive inner_disk beta acute contour starts
      W x on_cut_x below_x
    have h := (marked_phys ⟨.inl child, none, flag, u⟩ trivial).symm.trans
      (congrArg Cap.horizontal ((congrArg (fun y => f (Point ⟨none, y⟩)) label).trans hx))
    obtain ⟨a, ⟨address, root⟩ | ⟨address, root⟩⟩ := locations (.inl child) u h
    · have same : child = v := (Sum.inl.inj (congrArg Sigma.fst address)).trans (Subtype.ext root)
      subst child
      have time : u = 0 := eq_of_heq (Sigma.mk.inj address).2
      subst u
      exact ⟨(RoofTime b flag 0).1.2,
        (congrArg (fun y => Point ⟨none, y⟩) label.symm).trans (roof_at_slot b flag 0)⟩
    · have same : child = a := Sum.inl.inj (congrArg Sigma.fst address)
      subst child
      have time : u = 1 := eq_of_heq (Sigma.mk.inj address).2
      subst u
      let bank : Attachment := .inl a
      let k := (RoofTime bank flag 1).1.2
      have nonroot : (Fcut).parents.parent a.val ∉ (Fcut).parents.roots := root.symm ▸ v.property
      have incoming : ∃ i : Fin ((Stack (.inl ⟨(Fcut).parents.parent a.val, nonroot⟩)).length + 1),
          Point (L ⟨bank, k⟩ 1) =
            Point (Rgt ⟨.inl ⟨(Fcut).parents.parent a.val, nonroot⟩, i⟩ 0) := by
        by_cases empty : Stack bank = []
        · exact K.compatibleContourSourceOnlyFiniteEnd_empty_eq_outgoing compact nonempty R
            no_boundary level higher M positive inner_disk beta acute contour starts W geometry
            a nonroot empty k
        · exact K.compatibleContourSourceOnlyFiniteEnd_nonempty_eq_outgoing compact nonempty R
            no_boundary level higher M positive inner_disk beta acute contour starts W geometry
            a nonroot empty k
      let P (v' : Edge) := ∃ i : Fin ((Stack (.inl v')).length + 1),
        Point (L ⟨bank, k⟩ 1) = Point (Rgt ⟨.inl v', i⟩ 0)
      obtain ⟨i, hi⟩ := Eq.mp (congrArg P (Subtype.ext root)) incoming
      exact ⟨i, (congrArg (fun y => Point ⟨none, y⟩) label.symm).trans
        ((roof_at_slot bank flag 1).trans (hi.trans (joined b i 0).symm))⟩
  have in_frontier (e : Event) (x : PolygonalPoint (models e).region) (a : Addr) (ha : Valid a)
      (eq : tag e x = Mark a ha) : x.val ∈ frontier (models e).region := by
    rcases a with ⟨bank, g, flag, time⟩
    cases g with
    | none =>
      have contra : some e = none := congrArg Sigma.fst eq
      cases contra
    | some g =>
      have same : e = g := Option.some.inj (congrArg Sigma.fst eq)
      subst g
      have xx : x = Gap bank e ha flag time := eq_of_heq (Sigma.mk.inj eq).2
      let address := AddressAt[bank,e,ha,time]
      have coord := K.compatibleContourSourceOnlyGapMark_address compact nonempty R
        no_boundary level higher M positive inner_disk beta acute contour starts models bank
        e ha flag time
      exact (congrArg PolygonalPoint.val xx).symm ▸
        (coord.symm ▸ ((models e).addressFrontier (!flag) address).property)
  have on_seam (e : Event) (x : PolygonalPoint (models e).region)
      (seam : ∃ y, Banks (tag e x) y ∨ Banks y (tag e x)) :
      x.val ∈ frontier (models e).region := by
    have at_endpoint (side : Bool) (slot : MetricGluing.BankStackSlot Stack)
        (u : ParamAt slot.1) (h : tag e x = EndAt side slot u) :
        x.val ∈ frontier (models e).region := by
      let a := Named side slot u
      let ha := MetricGluing.bankStackEndpointAddress_valid Stack side slot u
      exact in_frontier e x a ha
        (h.trans (MetricGluing.bankStackAddressPoint_endpoint Stack Pieces Base Gap side slot u).symm)
    obtain ⟨y, join | join⟩ := seam
    · obtain ⟨slot, u, named, _⟩ := join
      exact at_endpoint false slot u named
    · obtain ⟨slot, u, _, named⟩ := join
      exact at_endpoint true slot u named
  let event (i : Fin xs.length) := xs.get i
  let mark (i : Fin xs.length) (flag : Bool) :=
    Gap b (event i) (List.get_mem xs i) flag 0
  have first (i : Fin xs.length) : vertex i.castSucc = Point (tag (event i) (mark i false)) :=
    (joined b i.castSucc 0).trans
      (congrArg Point (MetricGluing.bankStackRight_at Pieces Stack Base Gap b i 0))
  have last (i : Fin xs.length) : vertex i.succ = Point (tag (event i) (mark i true)) :=
    congrArg Point (MetricGluing.bankStackLeft_after Pieces Stack Base Gap b i 0)
  have gap_value (i : Fin xs.length) :
      (SpatialAt[event i]).addressPoint AddressAt[b,event i,List.get_mem xs i,0] = p := by
    have restored := K.compatibleContourPhysicalBank_addressPoint_eq_restore compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W (event i) b
      (List.get_mem xs i) 0
    have at_p := physical_injective (Point ⟨none, Base b false 0⟩)
      ((marked_phys ⟨b, none, false, 0⟩ trivial).trans at_vertex)
    exact restored.trans ((roof _).symm.trans at_p)
  have gap_mark (i : Fin xs.length) (flag : Bool) :
      mark i flag = (models (event i)).intrinsicAddressPoint (!flag)
        AddressAt[b,event i,List.get_mem xs i,0] :=
    K.compatibleContourSourceOnlyGapMark_eq_intrinsicAddress compact nonempty R no_boundary
      level higher M positive inner_disk beta acute contour starts models b (event i)
      (List.get_mem xs i) flag 0
  have endpoint (i : Fin xs.length) (x : PolygonalPoint (models (event i)).region)
      (hx : f (Point (tag (event i) x)) = p)
      (seam : ∃ y, Banks (tag (event i) x) y ∨ Banks y (tag (event i) x)) :
      x = mark i false ∨ x = mark i true := by
    let a := AddressAt[b,event i,List.get_mem xs i,0]
    obtain ⟨side, h⟩ := ((marked (event i)).2 a).2 x
      (on_seam (event i) x seam) (hx.trans (gap_value i).symm)
    cases side
    · exact Or.inr (h.trans (gap_mark i true).symm)
    · exact Or.inl (h.trans (gap_mark i false).symm)
  have gap_arc (i : Fin xs.length) : ∃ P : Path (mark i false) (mark i true),
      {x | f (Point (tag (event i) x)) = p} = Set.range P ∧
      (Function.Injective P ∨ ∀ s t : unitInterval, P s = P t) := by
    let e := event i
    let a := AddressAt[b,e,List.get_mem xs i,0]
    obtain ⟨⟨P, range, injective, constant⟩, _⟩ := (marked e).2 a
    let path := P.symm.cast (gap_mark i false) (gap_mark i true)
    have same_range : Set.range path = Set.range P := P.symm_range
    refine ⟨path, ?_, ?_⟩
    · rw [same_range, ← range, gap_value i]
    · by_cases at_start : (BankAt[e]).addressPoint a = (BankAt[e]).start
      · exact Or.inr (fun s t => constant at_start (unitInterval.symm s) (unitInterval.symm t))
      · exact Or.inl ((injective at_start).comp unitInterval.symm_involutive.injective)
  choose arc arc_range arc_cases using gap_arc
  let own := ∃ e : Event, SourceOf[e] = v.val
  let n := if own then xs.length - 1 else xs.length
  have bound : n ≤ xs.length := by
    by_cases at_source : own
    · simpa only [n, ite_eq_left at_source] using Nat.sub_le xs.length 1
    · exact Nat.le_of_eq (ite_eq_right at_source)
  let keep (i : Fin n) := Fin.castLE bound i
  let kept_vertex (i : Fin (n + 1)) := Fin.castLE (Nat.succ_le_succ bound) i
  have kept_live (i : Fin (n + 1)) (e : Event) (at_v : SourceOf[e] = v.val) :
      kept_vertex i ≠ Fin.last xs.length := by
    have hn : n = xs.length - 1 := ite_eq_left (show own from ⟨e, at_v⟩)
    intro equal
    have val : i.val = xs.length := congrArg Fin.val equal
    have member : e ∈ xs := ((D).mem_contourSavedGapStack Selection contour v.val e).mpr
      (at_v ▸ (Fcut).parents.ancestor_refl SourceOf[e])
    have length_pos : 0 < xs.length := List.length_pos_iff.mpr (List.ne_nil_of_mem member)
    have rank := i.isLt
    omega
  have distinct : Function.Injective (fun i : Fin (n + 1) => vertex (kept_vertex i)) := by
    intro i j h
    have through := (joined b (kept_vertex i) 0).symm.trans
      (h.trans (joined b (kept_vertex j) 0))
    have slots := K.compatibleContourSourceOnly_outgoingVertex_eq_of_live_slots compact nonempty R
      no_boundary level higher M positive inner_disk beta acute contour starts W geometry v
      (kept_vertex i) (kept_vertex j) (kept_live i) (kept_live j) through
    exact Fin.ext (congrArg (fun k : Fin (xs.length + 1) => k.val) slots)
  have source_shape (e : Event) (at_v : SourceOf[e] = v.val) :
      ∃ earlier, xs = earlier ++ [e] := by
    obtain ⟨earlier, shape⟩ := (D).contourSavedGapStack_source_last Selection contour
      (Fcut).boundary_roots starts e
    refine ⟨earlier, ?_⟩
    change (D).contourSavedGapStack Selection contour v.val = _
    rw [← at_v]
    exact shape
  have removed (i : Fin xs.length) (rest : n ≤ i.val) :
      i.val = n ∧ i.val + 1 = xs.length ∧ SourceOf[event i] = v.val := by
    have at_source : own := by
      by_contra hn
      have eq : n = xs.length := ite_eq_right hn
      exact (not_le_of_gt i.isLt) (Eq.mp (congrArg (fun m => m ≤ i.val) eq) rest)
    have hn : n = xs.length - 1 := ite_eq_left at_source
    have val : i.val = n := by have rank := i.isLt; omega
    have size : i.val + 1 = xs.length := by have rank := i.isLt; omega
    obtain ⟨e, at_v⟩ := at_source
    obtain ⟨earlier, shape⟩ := source_shape e at_v
    have nonempty_list : xs ≠ [] := shape.symm ▸ List.append_ne_nil_of_right_ne_nil _ (by simp)
    have at_last : xs.getLast? = some e := by
      rw [shape, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
      rfl
    have last_eq : xs.getLast nonempty_list = e := Option.some.inj
      ((List.getLast?_eq_getLast_of_ne_nil nonempty_list).symm.trans at_last)
    have get_eq : event i = xs.getLast nonempty_list := by
      rw [List.getLast_eq_getElem]
      change xs[i.val] = xs[xs.length - 1]
      congr 1
      omega
    exact ⟨val, size, (congrArg (fun e => SourceOf[e]) (get_eq.trans last_eq)).trans at_v⟩
  have source_marks (i : Fin xs.length) (at_v : SourceOf[event i] = v.val) :
      mark i false = mark i true := by
    let e := event i
    let s : Edge := ⟨SourceOf[e], (D).positiveContourVertex_nonroot Selection contour e⟩
    let P (a : Edge) :=
      ∀ mem : e ∈ Stack (.inl a), Gap (.inl a) e mem false 0 = Gap (.inl a) e mem true 0
    have at_source : P s := by
      intro mem
      have at_side (side : Bool) :=
        K.compatibleContourSourceOnlyGapMark_at_source compact nonempty R no_boundary level
          higher M positive inner_disk beta acute contour starts models e (geometry e) mem side
      exact (at_side false).trans (at_side true).symm
    exact (Eq.mp (congrArg P (Subtype.ext at_v)) at_source) (List.get_mem xs i)
  have trim_vertex (i : Fin (xs.length + 1)) :
      ∃ k : Fin (n + 1), vertex i = vertex (kept_vertex k) := by
    by_cases live : i.val ≤ n
    · exact ⟨⟨i.val, Nat.lt_succ_of_le live⟩, rfl⟩
    have short : n < xs.length := by have rank := i.isLt; omega
    let j : Fin xs.length := ⟨n, short⟩
    obtain ⟨_, size, tip⟩ := removed j (Nat.le_refl n)
    have eq : i = j.succ := by
      apply Fin.ext
      change i.val = n + 1
      change n + 1 = xs.length at size
      have rank := i.isLt
      omega
    refine ⟨Fin.last n, ?_⟩
    rw [eq]
    change vertex j.succ = vertex j.castSucc
    exact (last j).trans
      ((congrArg (fun x => Point (tag (event j) x)) (source_marks j tip).symm).trans (first j).symm)
  have trim_roof (x : W.Cut) (hx : f (Point ⟨none, x⟩) = p) :
      ∃ k : Fin (n + 1), Point ⟨none, x⟩ = vertex (kept_vertex k) := by
    obtain ⟨i, same⟩ := all_roof x hx
    obtain ⟨k, at_k⟩ := trim_vertex i
    exact ⟨k, same.trans at_k⟩
  have trim_gap (e : Event) (x : PolygonalPoint (models e).region) (hx : f (Point (tag e x)) = p) :
      (∃ i : Fin n, event (keep i) = e) ∨
        (∃ k : Fin (n + 1), Point (tag e x) = vertex (kept_vertex k)) := by
    obtain ⟨j, eq⟩ := List.get_of_mem (all_gaps e x hx)
    change event j = e at eq
    subst e
    by_cases live : j.val < n
    · exact Or.inl ⟨⟨j.val, live⟩, rfl⟩
    obtain ⟨at_n, _, tip⟩ := removed j (Nat.le_of_not_gt live)
    have same_mark := source_marks j tip
    have ends_equal : arc j 0 = arc j 1 :=
      (arc j).source.trans (same_mark.trans (arc j).target.symm)
    have const := (arc_cases j).resolve_left (fun h => zero_ne_one (h ends_equal))
    have mem : x ∈ {y | f (Point (tag (event j) y)) = p} := hx
    rw [arc_range j] at mem
    obtain ⟨s, rfl⟩ := mem
    have at_start : arc j s = mark j false := (const s 0).trans (arc j).source
    have at_last : j.castSucc = kept_vertex (Fin.last n) := Fin.ext at_n
    exact Or.inr ⟨Fin.last n,
      (congrArg (fun y => Point (tag (event j) y)) at_start).trans
        ((first j).symm.trans (congrArg vertex at_last))⟩
  have kept_arcs (i : Fin n) : Function.Injective (arc (keep i)) := by
    apply (arc_cases (keep i)).resolve_right
    intro flat
    have at_start : mark (keep i) false = mark (keep i) true :=
      (arc (keep i)).source.symm.trans ((flat 0 1).trans (arc (keep i)).target)
    have same : vertex (kept_vertex i.castSucc) = vertex (kept_vertex i.succ) :=
      (first (keep i)).trans ((congrArg (fun x => Point (tag (event (keep i)) x)) at_start).trans
        (last (keep i)).symm)
    exact Nat.ne_of_lt (Nat.lt_succ_self i.val) (congrArg Fin.val (distinct same))
  exact _root_.Unfoldings.MetricGluing.contractibleSpace_fiber_of_trimmed_bank_stack Pieces Stack Base Gap b 0 bound
    f p (K.compatibleContourSourceOnlyGraft_exact compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour starts W models geometry)
    (K.compatibleContourBankStack_nodup compact nonempty R no_boundary level higher M
      positive inner_disk beta acute contour b)
    distinct (fun i => vertex_fiber (kept_vertex i)) trim_roof trim_gap
    (fun i => endpoint (keep i))
    (fun i => ⟨arc (keep i), kept_arcs i, arc_range (keep i)⟩)

end Unfoldings.ConvexRoof
