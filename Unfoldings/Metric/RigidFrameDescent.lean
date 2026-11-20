module

public import Unfoldings.Metric.RigidFrameActions
public import Unfoldings.Metric.EuclideanDevelopment
public import Unfoldings.Topology.CoveringNearFiber

/-! A proper collapse with contractible fibers descends the local frame choices. -/

@[expose] public section

noncomputable section

open Set Topology Filter

namespace Unfoldings.EuclideanAtlas

variable {X : Type*} [MetricSpace X] (A : EuclideanAtlas X)
  {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y]
  (f : X → Y) (proper : IsProperMap f) (onto : Function.Surjective f)
  (fiber : ∀ y : Y, ContractibleSpace (f ⁻¹' {y}))

local notation "FrameSpace" => FiberBundleCore.TotalSpace (EuclideanAtlas.frameCore A)

include f proper onto fiber

set_option maxHeartbeats 1900000 in
-- Local frames lie over saturated open sets, while their relative motions use the quotient base.
/-- A proper map with contractible fibers to a contractible space supplies a continuous
global frame section. The construction descends relative motions to the target. -/
theorem exists_frameSection_of_proper_contractible_fibers :
    ∃ S : C(X, FrameSpace), A.frameCore.proj ∘ S = id := by
  classical
  let frames := A.frameCore
  let unit : RigidFrame := ⟨AffineIsometryEquiv.refl ℝ Plane⟩
  have frames_onto : Function.Surjective frames.proj := fun x => ⟨⟨x, unit⟩, rfl⟩
  have local_section (y : Y) : ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      ∃ s : C(f ⁻¹' U, FrameSpace), ∀ x, (s x).1 = x.val :=
    exists_covering_section_near_proper_fiber f proper frames.proj A.frameCore_isCoveringMap
      frames_onto y (fiber y)
  choose U openU covers s project using local_section
  let overlap (i j : Y) := U i ∩ U j
  have q : IsQuotientMap f := proper.isClosedMap.isQuotientMap proper.continuous onto
  let onLeft (i j : Y) : C(f ⁻¹' overlap i j, f ⁻¹' U i) :=
    ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  let onRight (i j : Y) : C(f ⁻¹' overlap i j, f ⁻¹' U j) :=
    ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩
  let relativeAt (i j : Y) : C(f ⁻¹' overlap i j, RigidFrame) :=
    ⟨fun x => (s j (onRight i j x)).2.relative (s i (onLeft i j x)).2,
      A.continuous_relativeFrames ((s j).comp (onRight i j)) ((s i).comp (onLeft i j))
        (fun x => (project j (onRight i j x)).trans (project i (onLeft i j x)).symm)⟩
  have restricted_fiber (i j : Y) (y : overlap i j) :
      IsPreconnected ((overlap i j).restrictPreimage f ⁻¹' {y}) := by
    let : ContractibleSpace (f ⁻¹' {y.val}) := fiber y.val
    let embed (x : f ⁻¹' {y.val}) : f ⁻¹' overlap i j :=
      ⟨x.val, Eq.mpr (congrArg (fun z : Y => z ∈ overlap i j)
        (show f x.val = y.val from x.property)) y.property⟩
    have continuous : Continuous embed := continuous_subtype_val.subtype_mk _
    have image : embed '' (univ : Set (f ⁻¹' {y.val})) =
        (overlap i j).restrictPreimage f ⁻¹' {y} := by
      ext x
      constructor
      · rintro ⟨a, _, rfl⟩
        exact mem_singleton_iff.mpr (Subtype.ext a.property)
      · intro h
        have eq : f x.val = y.val := congrArg Subtype.val (mem_singleton_iff.mp h)
        exact ⟨⟨x.val, eq⟩, mem_univ _, Subtype.ext rfl⟩
    exact image ▸ isPreconnected_univ.image embed continuous.continuousOn
  have descended (i j : Y) :
      ∃ d : C(overlap i j, RigidFrame), d ∘ (overlap i j).restrictPreimage f = relativeAt i j :=
    exists_descend_continuous_of_preconnected_fibers ((overlap i j).restrictPreimage f)
      (q.restrictPreimage_isOpen ((openU i).inter (openU j))) (restricted_fiber i j) (relativeAt i j)
  choose d agrees using descended
  have read (i j : Y) (x : X) (hi : f x ∈ U i) (hj : f x ∈ U j) :
      d i j ⟨f x, ⟨hi, hj⟩⟩ =
        (s j ⟨x, hj⟩).2.relative (s i ⟨x, hi⟩).2 :=
    congrFun (agrees i j) (⟨x, ⟨hi, hj⟩⟩ : f ⁻¹' overlap i j)
  have comparison (i j : Y) (x : X) (hi : f x ∈ U i) (hj : f x ∈ U j) :
      (s j ⟨x, hj⟩).2.postcompose (d i j ⟨f x, ⟨hi, hj⟩⟩) = (s i ⟨x, hi⟩).2 :=
    (congrArg (RigidFrame.postcompose (s j ⟨x, hj⟩).2) (read i j x hi hj)).trans
      (RigidFrame.postcompose_relative _ _)
  let transport (i j : Y) (y : Y) (u : RigidFrame) : RigidFrame :=
    if h : y ∈ overlap i j then (d i j ⟨y, h⟩).postcompose u else u
  have continuous_change (i j : Y) :
      ContinuousOn (fun p : Y × RigidFrame => transport i j p.1 p.2) (overlap i j ×ˢ univ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let B := overlap i j ×ˢ (univ : Set RigidFrame)
    let base : B → overlap i j := fun p => ⟨p.val.1, p.property.1⟩
    have continuous_base : Continuous base := (continuous_fst.comp continuous_subtype_val).subtype_mk _
    have continuous_second : Continuous (fun p : B => p.val.2) :=
      continuous_snd.comp continuous_subtype_val
    have operation : Continuous (fun p : RigidFrame × RigidFrame => p.1.postcompose p.2) :=
      continuous_of_discreteTopology
    have c := operation.comp (((d i j).continuous.comp continuous_base).prodMk continuous_second)
    apply c.congr
    intro p
    change (d i j (base p)).postcompose p.val.2 = transport i j p.val.1 p.val.2
    dsimp only [transport]
    rw [dite_eq_left p.property.1]
  have compute (i j : Y) (y : Y) (h : y ∈ overlap i j) (u : RigidFrame) :
      transport i j y u = (d i j ⟨y, h⟩).postcompose u := by
    dsimp only [transport]
    rw [dite_eq_left h]
  have compatible_at (i j : Y) (x : X) (hi : f x ∈ U i) (hj : f x ∈ U j) (u : RigidFrame) :
      (s j ⟨x, hj⟩).2.postcompose (transport i j (f x) u) =
        (s i ⟨x, hi⟩).2.postcompose u := by
    let frame : RigidFrame := (s j ⟨x, hj⟩).2
    let motion := d i j ⟨f x, ⟨hi, hj⟩⟩
    exact (congrArg (RigidFrame.postcompose frame) (compute i j _ ⟨hi, hj⟩ u)).trans
      ((RigidFrame.postcompose_assoc frame motion u).symm.trans
        (congrArg (fun w : RigidFrame => w.postcompose u) (comparison i j x hi hj)))
  let downstairs : FiberBundleCore Y Y RigidFrame := {
    baseSet := U
    isOpen_baseSet := openU
    indexAt := id
    mem_baseSet_at := covers
    coordChange := transport
    continuousOn_coordChange := continuous_change
    coordChange_self i y hy u := by
      obtain ⟨x, rfl⟩ := onto y
      exact (RigidFrame.postcompose_injective (s i ⟨x, hy⟩).2)
        (compatible_at i i x hy hy u)
    coordChange_comp i j k y hy u := by
      obtain ⟨x, rfl⟩ := onto y
      have hi : f x ∈ U i := hy.1.1
      have hj : f x ∈ U j := hy.1.2
      have hk : f x ∈ U k := hy.2
      apply RigidFrame.postcompose_injective (s k ⟨x, hk⟩).2
      exact (compatible_at j k x hj hk (transport i j (f x) u)).trans
        ((compatible_at i j x hi hj u).trans (compatible_at i k x hi hk u).symm) }
  have covering : IsCoveringMap downstairs.proj := FiberBundle.isCoveringMap
  have down_onto : Function.Surjective downstairs.proj := fun y => ⟨⟨y, unit⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_covering_lift_of_contractible downstairs.proj covering down_onto
    (ContinuousMap.id Y)
  have proj_g (y : Y) : (g y).1 = y := congrFun hg y
  let S (x : X) : FrameSpace :=
    ⟨x, (s (f x) ⟨x, covers (f x)⟩).2.postcompose (g (f x)).2⟩
  have continuousOnS (i : Y) : ContinuousOn S (f ⁻¹' U i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let V := f ⁻¹' U i
    let triv := downstairs.localTriv i
    let lift (x : V) := g (f x.val)
    have lift_continuous : Continuous lift := g.continuous.comp
      (proper.continuous.comp continuous_subtype_val)
    have source : ∀ x : V, lift x ∈ triv.source := by
      intro x
      apply (FiberBundleCore.mem_localTriv_source downstairs i (lift x)).mpr
      change (g (f x.val)).1 ∈ U i
      rw [proj_g]
      exact x.property
    let coordinate : C(V, RigidFrame) :=
      ⟨fun x => (triv (lift x)).2, (continuous_iff_continuousAt.mpr fun x =>
        ((triv.toOpenPartialHomeomorph.continuousAt (source x)).comp
          lift_continuous.continuousAt).snd)⟩
    have shifted := A.continuous_postcomposeFrames (s i) coordinate
    have equal (x : V) : (⟨(s i x).1, (s i x).2.postcompose (coordinate x)⟩ : FrameSpace) = S x.val := by
      have gauge : coordinate x = transport (f x.val) i (f x.val) (g (f x.val)).2 := by
        change transport (g (f x.val)).1 i (g (f x.val)).1 (g (f x.val)).2 = _
        have eq := proj_g (f x.val)
        exact congrArg (fun y => transport y i y (g (f x.val)).2) eq
      have then_agree : (s i x).2.postcompose (coordinate x) =
          (s (f x.val) ⟨x.val, covers (f x.val)⟩).2.postcompose (g (f x.val)).2 :=
        (congrArg (RigidFrame.postcompose (s i x).2) gauge).trans
          (compatible_at (f x.val) i x.val (covers (f x.val)) x.property (g (f x.val)).2)
      dsimp only [S]
      exact (congrArg (fun y => (⟨y, (s i x).2.postcompose (coordinate x)⟩ : FrameSpace))
        (project i x)).trans (congrArg (fun m => (⟨x.val, m⟩ : FrameSpace)) then_agree)
    exact shifted.congr equal
  have continuousS : Continuous S := continuous_iff_continuousAt.mpr fun x =>
    (continuousOnS (f x) x (covers (f x))).continuousAt
      (((openU (f x)).preimage proper.continuous).mem_nhds (covers (f x)))
  exact ⟨⟨S, continuousS⟩, rfl⟩

include A in
/-- Evaluating the descended frame gives a Euclidean local isometry on the whole domain. -/
theorem exists_local_isometry_of_proper_contractible_fibers :
    ∃ F : X → Plane, ∀ x, ∃ r > 0, Isometry (fun y : Metric.ball x r => F y.val) := by
  obtain ⟨S, h⟩ := A.exists_frameSection_of_proper_contractible_fibers f proper onto fiber
  exact ⟨fun x => A.frameValue (S x), A.frameValue_section_local_isometry S h⟩

end Unfoldings.EuclideanAtlas
