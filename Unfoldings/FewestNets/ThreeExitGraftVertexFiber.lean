module

public import Unfoldings.FewestNets.ThreeExitGraftVertexAttachments
public import Unfoldings.FewestNets.ThreeExitGraftVertexSeparation
public import Unfoldings.Metric.BankStackTrimmedFiber





/-! The full collapse at a finite nonroot vertex has a contractible fiber. -/

@[expose] public section

noncomputable section

open scoped NNReal ENNReal

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel

open MetricGluing

universe u v

set_option maxHeartbeats 2800000

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : FewestNets.ThreeExitStemWindows}
  {R : K.ThreeExitComponentRouting seed B compact nonempty H}

local notation "U" => K.selectionComponent slopes seed
local notation "V" => {v : C.Vertex Set.univ // K.projectedVertex v ∈ K.restrictedCarrier U}
local notation "G" => SlopeEnvelope.recenter
  (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty) B.reference
local notation "pointOf" => (fun v : V => K.projectedVertex (Subtype.val v))

variable {level : ℝ}
  {M : (K.componentClippedExtension
    (Set.nonempty_of_mem (K.seed_mem_selectionComponent slopes seed)) compact nonempty).FiniteSlopeModel}
  (L : R.FloorWindowModel level M)

local notation "T[" h "]" => R.fineMesh level M h
local notation "D[" h "]" => SpatialEnvelope.FloorMesh.pairedComplex T[h]
local notation "F[" h "]" => R.fineMeshForest level M h
local notation "Sel[" h "]" => PotentialCutForest.selection F[h]

local instance graftVertexFiberIndexFintype (h : ∀ v : V, (G).height (pointOf v) < level) :
    Fintype (T[h]).Index := @Fintype.ofFinite _ (T[h]).finite

variable (S : SourceContour (R := R) (M := M) (level := level))

local notation "T" => T[S.higher]
local notation "D" => D[S.higher]
local notation "Fcut" => F[S.higher]
local notation "Selection" => Sel[S.higher]
local notation "Event" => TriangleComplex.PositiveContourSource D Selection S.contour
local notation "Model[" e "]" => OrientedBankGap.model (S.gaps e)
local notation "Pieces" => polygonalBankStackPiece L.whole.Cut (fun e : Event => BankGapModel.region (Model[e]))
local notation "Stack" => PotentialCutForest.contourAttachmentStack Fcut S.contour
local notation "Base" => contourBaseMark L S
local notation "Gap" => PotentialCutForest.contourGapMark Fcut S.contour S.starts
  (fun e : Event => Model[e])
local notation "Attachment" => PotentialCutForest.ContourAttachment Fcut
local notation "Param" => PotentialCutForest.contourAttachmentParameter Fcut

local notation "Edge" => {v : TriangleComplex.Vertex D Set.univ //
  v ∉ AscendingParents.roots (PotentialCutForest.parents Fcut)}
local notation "FiniteBank[" v "," h "]" => (Sum.inl (Subtype.mk v h) : Attachment)
local notation "Retain" => PotentialCutForest.retain Fcut
local notation "Map" => L.fineMeshWholeMap S.higher
local notation "RoofPoint[" j "]" => (Sigma.mk none (Map
  (TriangleComplex.vertexPoint D Retain (TriangleComplex.boundaryEndVertex D Retain
    (PairedInvolutions.System.Chain.point (TriangleComplex.BoundaryContour.cycle S.contour) j)))) :
      MetricGluing.Total Pieces)
local notation "Interval[" v "," h "]" => TriangleComplex.contourParentInterval
  D Selection S.contour (PotentialCutForest.boundary_roots Fcut) S.starts v h
local notation "RoofTime" => MetricGluing.bankStackRoofTime (Parameter := Param) Stack
local notation "Germ" => contourFiniteRoofGerm S
local notation "EndAt" => MetricGluing.bankStackEndpoint Stack Pieces Base Gap
local notation "Time" => (Σ s : MetricGluing.BankStackSlot Stack, Param (Sigma.fst s))

local notation "Named" => MetricGluing.bankStackEndpointAddress (Parameter := Param) Stack
local notation "Addr" => MetricGluing.BankStackAddress («G» := Event) (Parameter := Param)
local notation "Valid" => MetricGluing.BankStackAddressValid Stack
local notation "Mark" => MetricGluing.bankStackAddressPoint Stack Pieces Base Gap
local notation "SourceOf[" e "]" => TriangleComplex.positiveContourVertex D Selection S.contour e
local notation "SourceEdge[" e "]" => (Sum.inl (Subtype.mk SourceOf[e]
  (TriangleComplex.positiveContourVertex_nonroot D Selection S.contour e)) : Attachment)
local notation "BankAt[" e "]" => PotentialCutForest.contourSourceRay Fcut S.contour S.starts e
local notation "MovedAt[" e "]" => PotentialCutForest.contourSourceOpenedRay Fcut S.contour S.starts e
local notation "models" => (fun e : Event => Model[e])
local notation "Left" => MetricGluing.bankStackLeft Pieces Stack Base Gap
local notation "Right" => MetricGluing.bankStackRight Pieces Stack Base Gap
local notation "Banks" => MetricGluing.bankSeams Left Right
local notation "Point" => MetricGluing.point Pieces Banks
local notation "geometry" => S.gaps

local notation "Visit[" j "]" => TriangleComplex.contourOriginalVertex D Selection S.contour j
local notation "SiteTime" => contourGraftRoofSiteTime S


local notation "Graft" => contourGraft L S
local notation "Fold" => contourGraftPieceCollapse L S
local notation "restore" => SpatialEnvelope.WholePartition.restoreCut L.whole.partition R.wholeCarrier
local notation "Phys" => contourPhysicalAddress L S
local notation "Q" => SpatialEnvelope.FloorMesh.roof T
  (meshSection_nonempty (K := K) (slopes := slopes) (seed := seed) level M S.higher)
local notation "VertexAt[" v "]" => ConvexRoof.projectedVertex Q v
local notation "SpatialAt[" e "]" => PotentialCutForest.contourSourceSpatialRay Fcut S.contour S.starts e
local notation "AddressAt[" a "," e "," mem "," t "]" =>
  PotentialCutForest.contourGapAddress Fcut S.contour a e mem t

set_option maxHeartbeats 5600000 in
/-- The only possibly constant arc is the vertex's own source tip. The live
outgoing slots and the other gap arcs form its entire contractible fiber. -/
theorem contourGraftCollapse_fiber_of_vertex
    (f : Graft → Space) (on_piece : ∀ y : MetricGluing.Total Pieces, f (Point y) = Fold y.1 y.2)
    (v : Edge) :
    ContractibleSpace {x : Graft | f x = (restore (Base (.inl v) false 0)).val} := by
  classical
  let b : Attachment := .inl v
  let p := (restore (Base b false 0)).val
  let xs := Stack b
  let vertex (i : Fin (xs.length + 1)) := Point (Left ⟨b, i⟩ 0)
  let tag (e : Event) (x : PolygonalPoint (models e).region) : MetricGluing.Total Pieces :=
    ⟨some e, x⟩
  have at_vertex : Phys b 0 = VertexAt[v.val] :=
    (L.contourPhysicalAddress_finite S v 0).trans (AffineMap.lineMap_apply_zero ..)
  have below : (G).height VertexAt[v.val] < level := contourParentStart_below S v
  have locations (a : Attachment) (u : Param a) (at_p : Phys a u = Cap.horizontal p) :=
    L.contourPhysicalAddress_at_vertex S v.val below a u (at_p.trans at_vertex)
  have roof (x : L.whole.Cut) : f (Point ⟨none, x⟩) = (restore x).val := on_piece ⟨none, x⟩
  have marked (e : Event) := L.hasMarkedCollapseFibers_contourGraft S f on_piece e
  have joined (a : Attachment) (i : Fin ((Stack a).length + 1)) (u : Param a) :
      Point (Left ⟨a, i⟩ u) = Point (Right ⟨a, i⟩ u) :=
    MetricGluing.point_eq_of_glue Pieces (glue := Banks) ⟨⟨a, i⟩, u, rfl, rfl⟩
  have vertex_fiber (i : Fin (xs.length + 1)) : f (vertex i) = p :=
    (on_piece (Left ⟨b, i⟩ 0)).trans (L.contourGraft_left_physical S ⟨b, i⟩ 0)
  have named_value (a : Attachment) (e : Event) (mem : e ∈ Stack a) (u : Param a) :
      (SpatialAt[e]).addressPoint AddressAt[a,e,mem,u] = (restore (Base a false u)).val :=
    (L.contourGraftGapMark_spatial_eq_address S a e mem false u).symm.trans
      (L.contourGraftPieceCollapse_gap_eq S a e mem false u)
  have all_gaps (e : Event) (x : PolygonalPoint (models e).region)
      (hx : f (Point (tag e x)) = p) : e ∈ xs := by
    obtain ⟨addr, located⟩ := (SpatialAt[e]).exists_address ((marked e).1 ⟨x, hx⟩)
    obtain ⟨a, mem, u, named⟩ := (Fcut).exists_contourGapAddress_eq S.contour e addr
    have at_p : (SpatialAt[e]).addressPoint AddressAt[a,e,mem,u] = p :=
      (congrArg ((SpatialAt[e]).addressPoint) named).trans located
    have phys := congrArg Cap.horizontal ((named_value a e mem u).symm.trans at_p)
    obtain ⟨child, ⟨address, at_v⟩ | ⟨address, at_v⟩⟩ := locations a u phys
    · have same : a = b := (congrArg Sigma.fst address).trans
        (congrArg Sum.inl (Subtype.ext at_v))
      exact Eq.mp (congrArg (fun a => e ∈ Stack a) same) mem
    · have same : a = .inl child := congrArg Sigma.fst address
      have here : e ∈ Stack (.inl child) := same ▸ mem
      have path := ((D).mem_contourSavedGapStack Selection S.contour child.val e).mp here
      exact ((D).mem_contourSavedGapStack Selection S.contour v.val e).mpr
        (at_v ▸ AscendingParents.Ancestor.trans (Fcut).parents path ((Fcut).parents.ancestor_parent child.val))
  have roof_at_slot (a : Attachment) (flag : Bool) (u : Param a) :
      let time := RoofTime a flag u
      Point ⟨none, Base a flag u⟩ = Point (Left time.1 time.2) := by
    let time := RoofTime a flag u
    have eq := MetricGluing.bankStackEndpoint_eq_of_base_address Stack Pieces Base Gap flag time
      a flag u (MetricGluing.bankStackRoofTime_address Stack a flag u)
    change Point ⟨none, Base a flag u⟩ = Point (Left time.1 time.2)
    cases flag
    · exact congrArg Point eq.symm
    · exact (congrArg Point eq.symm).trans (joined _ _ _).symm
  have all_roof (x : L.whole.Cut) (hx : f (Point ⟨none, x⟩) = p) :
      ∃ i, Point ⟨none, x⟩ = vertex i := by
    let x_pos := Cap.horizontal (restore x).val
    have x_loc : x_pos = Cap.horizontal p := congrArg Cap.horizontal ((roof x).symm.trans hx)
    have on_cut_x : x_pos ∈ R.wholeCarrier :=
      x_loc.symm ▸ L.contourGraftBaseMark_horizontal_mem_cut S b false 0
    have below_x : (G).height x_pos < level := (x_loc.trans at_vertex).symm ▸ below
    obtain ⟨child, flag, u, label⟩ :=
      L.exists_contourParentMark_of_cut_below S x on_cut_x below_x
    have h := (L.contourPhysicalAddress_side S (.inl child) flag u).symm.trans
      ((congrArg (fun y : L.whole.Cut => Cap.horizontal (restore y).val) label).trans x_loc)
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
          Point (Left ⟨bank, k⟩ 1) =
            Point (Right ⟨.inl ⟨(Fcut).parents.parent a.val, nonroot⟩, i⟩ 0) := by
        by_cases empty : Stack bank = []
        · exact L.contourGraftFiniteEnd_empty_eq_outgoing S
            a nonroot empty k
        · exact L.contourGraftFiniteEnd_nonempty_eq_outgoing S
            a nonroot empty k
      let P (v' : Edge) := ∃ i : Fin ((Stack (.inl v')).length + 1),
        Point (Left ⟨bank, k⟩ 1) = Point (Right ⟨.inl v', i⟩ 0)
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
      have coord := contourGraftGapMark_eq_intrinsicAddressPoint S bank e ha flag time
      exact (congrArg PolygonalPoint.val xx).symm ▸
        (coord.symm ▸ ((models e).addressFrontier (!flag) address).property)
  have on_seam (e : Event) (x : PolygonalPoint (models e).region)
      (seam : ∃ y, Banks (tag e x) y ∨ Banks y (tag e x)) :
      x.val ∈ frontier (models e).region := by
    have at_endpoint (side : Bool) (slot : MetricGluing.BankStackSlot Stack)
        (u : Param slot.1) (h : tag e x = EndAt side slot u) :
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
    exact named_value b (event i) (List.get_mem xs i) 0
  have gap_mark (i : Fin xs.length) (flag : Bool) :
      mark i flag = (models (event i)).intrinsicAddressPoint (!flag)
        AddressAt[b,event i,List.get_mem xs i,0] :=
    contourGraftGapMark_eq_intrinsicAddressPoint S b (event i)
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
    have member : e ∈ xs := ((D).mem_contourSavedGapStack Selection S.contour v.val e).mpr
      (at_v ▸ (Fcut).parents.ancestor_refl SourceOf[e])
    have length_pos : 0 < xs.length := List.length_pos_iff.mpr (List.ne_nil_of_mem member)
    have rank := i.isLt
    omega
  have distinct : Function.Injective (fun i : Fin (n + 1) => vertex (kept_vertex i)) := by
    intro i j h
    have through := (joined b (kept_vertex i) 0).symm.trans
      (h.trans (joined b (kept_vertex j) 0))
    have slots := L.contourGraft_outgoingVertex_eq_of_live_slots S v
      (kept_vertex i) (kept_vertex j) (kept_live i) (kept_live j) through
    exact Fin.ext (congrArg (fun k : Fin (xs.length + 1) => k.val) slots)
  have source_shape (e : Event) (at_v : SourceOf[e] = v.val) :
      ∃ earlier, xs = earlier ++ [e] := by
    obtain ⟨earlier, shape⟩ := (D).contourSavedGapStack_source_last Selection S.contour
      (Fcut).boundary_roots S.starts e
    refine ⟨earlier, ?_⟩
    change (D).contourSavedGapStack Selection S.contour v.val = _
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
    let s : Edge := ⟨SourceOf[e], (D).positiveContourVertex_nonroot Selection S.contour e⟩
    let P (a : Edge) :=
      ∀ mem : e ∈ Stack (.inl a), Gap (.inl a) e mem false 0 = Gap (.inl a) e mem true 0
    have at_source : P s := by
      intro mem
      have at_side (side : Bool) :=
        (Fcut).contourGapMark_at_source S.contour S.starts S.gaps e mem side
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
  have trim_roof (x : L.whole.Cut) (hx : f (Point ⟨none, x⟩) = p) :
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
    f p (L.contourGraft_exact S)
    (contourGraft_stack_nodup S b)
    distinct (fun i => vertex_fiber (kept_vertex i)) trim_roof trim_gap
    (fun i => endpoint (keep i))
    (fun i => ⟨arc (keep i), kept_arcs i, arc_range (keep i)⟩)

end Unfoldings.ConvexRoof.ThreeExitComponentRouting.FloorWindowModel
