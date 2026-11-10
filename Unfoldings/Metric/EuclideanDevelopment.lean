module

public import Unfoldings.Metric.RigidFrameBundle
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Developing simply connected Euclidean metric spaces

Continue one rigid frame through the actual discrete frame covering. Its
section gives a global locally isometric map into the plane. Injectivity is
not assumed or concluded.
-/

@[expose] public section

open Filter Topology

noncomputable section

namespace Unfoldings.EuclideanAtlas

variable {X : Type*} [MetricSpace X] (A : EuclideanAtlas X)

theorem transition_at (i j x : X) (member : x ∈ (A i).domain ∩ (A j).domain) :
    A.transition i j x ((A i).chart ⟨x, member.1⟩).val =
      ((A j).chart ⟨x, member.2⟩).val := by
  rw [A.transition_eq i j x member]
  exact (A.transitionPatch i j x member).agrees
    ⟨x, Metric.mem_ball_self (A.transitionPatch i j x member).positive⟩

def frameValue (p : A.frameCore.TotalSpace) : Plane :=
  p.2.motion ((A p.1).chart ⟨p.1, (A p.1).center_mem⟩).val

theorem frameValue_in_chart (p : A.frameCore.TotalSpace) (i : X) (member : p.1 ∈ (A i).domain) :
    A.frameValue p = ((A.frameCore.localTriv i p).2).motion ((A i).chart ⟨p.1, member⟩).val := by
  rw [FiberBundleCore.localTriv_apply]
  change p.2.motion _ = p.2.motion ((A.transition p.1 i p.1).symm _)
  apply congrArg p.2.motion
  apply (A.transition p.1 i p.1).injective
  rw [AffineIsometryEquiv.apply_symm_apply]
  exact A.transition_at p.1 i p.1 ⟨(A p.1).center_mem, member⟩

/-- A continuous section of the frame covering evaluates to a local Euclidean isometry. -/
theorem frameValue_section_local_isometry (sectionMap : C(X, A.frameCore.TotalSpace))
    (projects : A.frameCore.proj ∘ sectionMap = id) (x : X) :
    ∃ r > 0, Isometry (fun y : Metric.ball x r => A.frameValue (sectionMap y.val)) := by
  have projection (y : X) : (sectionMap y).1 = y := congrFun projects y
  let t := A.frameCore.localTriv x
  have source : sectionMap x ∈ t.source := by
    rw [FiberBundleCore.mem_localTriv_source, ← FiberBundleCore.baseSet_at]
    change (sectionMap x).1 ∈ (A x).domain
    rw [projection]
    exact (A x).center_mem
  have coords_continuous : ContinuousAt (fun y => (t (sectionMap y)).2) x :=
    ((t.toOpenPartialHomeomorph.continuousAt source).comp
      sectionMap.continuous.continuousAt).snd
  have constant : ∀ᶠ y in 𝓝 x, (t (sectionMap y)).2 = (t (sectionMap x)).2 :=
    coords_continuous (isOpen_discrete {((t (sectionMap x)).2)} |>.mem_nhds rfl)
  obtain ⟨r, positive, fixed⟩ := Metric.eventually_nhds_iff.mp constant
  obtain ⟨a, apos, inside⟩ := Metric.isOpen_iff.mp (A x).open_domain x (A x).center_mem
  refine ⟨min r a, lt_min positive apos, ?_⟩
  have member (y : Metric.ball x (min r a)) : (sectionMap y.val).1 ∈ (A x).domain := by
    rw [projection]
    exact inside ((Metric.ball_subset_ball (min_le_right _ _)) y.property)
  have formula (y : Metric.ball x (min r a)) : A.frameValue (sectionMap y.val) =
      ((t (sectionMap x)).2).motion
        ((A x).chart ⟨y.val, by simpa only [projection] using member y⟩).val := by
    rw [A.frameValue_in_chart (sectionMap y.val) x (member y)]
    change ((t (sectionMap y.val)).2).motion _ = _
    rw [fixed ((Metric.mem_ball.mp y.property).trans_le (min_le_left _ _))]
    exact congrArg (fun q : (A x).domain => ((t (sectionMap x)).2).motion ((A x).chart q).val)
      (Subtype.ext (projection y.val))
  intro y z
  change edist (A.frameValue (sectionMap y.val)) (A.frameValue (sectionMap z.val)) = edist y z
  rw [formula y, formula z, ((t (sectionMap x)).2).motion.isometry.edist_eq]
  exact (A x).chart.isometry _ _

include A in
/-- Simply connected flat metric spaces admit global developments, which may overlap. -/
theorem exists_local_isometry [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (root : X) (frame : RigidFrame) :
    ∃ f : X → Plane, ∀ x, ∃ r > 0, Isometry (fun y : Metric.ball x r => f y.val) := by
  obtain ⟨sectionMap, initial, _unique⟩ :=
    (A.frameCore_isCoveringMap).existsUnique_continuousMap_lifts (ContinuousMap.id X) root
      (⟨root, frame⟩ : A.frameCore.TotalSpace) rfl
  exact ⟨fun x => A.frameValue (sectionMap x),
    A.frameValue_section_local_isometry sectionMap initial.2⟩

end Unfoldings.EuclideanAtlas
