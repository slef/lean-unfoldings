module

public import Unfoldings.Roof.GraphWindowFaces
public import Unfoldings.Complex.RestrictedFanAgreement

/-! The selected scalar graph region recovers the actual coarse saved fan between its two banks. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open Filter Topology PlanarTopology

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

open Classical in
private theorem exists_restricted_boundaryEnd_of_face_side (U : Set Face) (p : C.Germ)
    (kept : p.1.1 ∈ U) (other : (C.mateGerm Set.univ p).1.1 ∉ U) :
    ∃ q : (C.restrictFaces U).BoundaryEnd Set.univ, C.includeRestrictedGerm U q.val = p := by
  let R := C.restrictFaces U
  let g : R.Germ := ((⟨p.1.1, kept⟩, p.1.2), p.2)
  have boundary : R.IsBoundaryEdge Set.univ (R.germEdge g) := by
    by_contra has_mate
    obtain ⟨r, crosses⟩ := (R.exists_germCrosses_iff Set.univ g).mpr has_mate
    have across := C.includeRestrictedGerm_crossing U crosses
    have equal : C.mateGerm Set.univ p = C.includeRestrictedGerm U r :=
      C.mateGerm_of_crossing across
    have face_eq : (C.mateGerm Set.univ p).1.1 = r.1.1.val :=
      congrArg (fun k : C.Germ => k.1.1) equal
    exact other (face_eq.symm ▸ r.1.1.property)
  exact ⟨⟨g, boundary⟩, rfl⟩

variable {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
  (aligned : ∀ j, Disjoint (interior (K.projectedTriangle j).carrier) (graphPoint f '' Set.Icc a b))

local notation "U" => K.graphWindowFaces f a b
include hf aligned in

open Classical in
set_option maxHeartbeats 1300000 in
/-- The entire original selected fan gives exactly the saved intrinsic and
projected fan angle difference when the two named banks face the upper region. -/
theorem regionalAngleExcess_graphWindow_eq_original_fan {retain : Set C.Seam}
    (p : C.BoundaryEnd retain)
    (kept : p.val.1.1 ∈ (U)) (other : (C.mateGerm Set.univ p.val).1.1 ∉ (U))
    (kept_mate : (C.boundaryMate retain p).val.1.1 ∈ (U))
    (other_mate : (C.mateGerm Set.univ (C.boundaryMate retain p).val).1.1 ∉ (U))
    (w : C.Vertex Set.univ)
    (original : C.vertexForgetCuts (Set.subset_univ retain) (C.boundaryEndVertex retain p) = w)
    (inside : K.projectedVertex w ∈ interior K.footprint)
    (window : K.projectedVertex w 0 ∈ Set.Ioo a b)
    (graph : K.projectedVertex w 1 = f (K.projectedVertex w 0)) :
    K.regionalAngleExcess (U) w =
      C.totalAngle retain (C.boundaryEndVertex retain p) -
        K.projectedTotalAngle retain (C.boundaryEndVertex retain p) := by
  let R := C.restrictFaces (U)
  let back := C.boundaryMate retain p
  obtain ⟨q, named⟩ := exists_restricted_boundaryEnd_of_face_side (U) p.val kept other
  obtain ⟨r, named_back⟩ := exists_restricted_boundaryEnd_of_face_side (U) back.val kept_mate other_mate
  let v := R.boundaryEndVertex Set.univ q
  let u := R.boundaryEndVertex Set.univ r
  have q_at : C.includeRestrictedVertexUniv (U) v = w := by
    change C.vertexOfCorner Set.univ (C.includeRestrictedGerm (U) q.val).1 = w
    rw [named]
    exact original
  have r_at : C.includeRestrictedVertexUniv (U) u = w := by
    change C.vertexOfCorner Set.univ (C.includeRestrictedGerm (U) r.val).1 = w
    rw [named_back]
    change C.vertexForgetCuts (Set.subset_univ retain) (C.boundaryEndVertex retain back) = w
    rw [(C.boundaryMate_spec retain p).2]
    exact original
  have unique (x : R.Vertex Set.univ)
      (equal : C.includeRestrictedVertexUniv (U) x = w) : x = v :=
    K.graphWindow_vertex_unique hf aligned inside window graph x v
      (congrArg K.projectedVertex equal) (congrArg K.projectedVertex q_at)
  have different : r ≠ q := by
    intro equal
    have raw : back.val = p.val := named_back.symm.trans ((congrArg
      (fun e : R.BoundaryEnd Set.univ => C.includeRestrictedGerm (U) e.val) equal).trans named)
    exact (C.boundaryMate_spec retain p).1 (Subtype.ext raw)
  have mate : r = R.boundaryMate Set.univ q :=
    ((R.boundaryEnd_vertex_eq_iff Set.univ r q).mp (unique u r_at)).resolve_left different
  let weight (d : C.Corner) :=
    (C.triangle d.1).cornerAngle d.2 - (K.projectedTriangle d.1).cornerAngle d.2
  have weights := C.sum_fan_weights_eq_restricted_of_terminal_germs (U) p q named.symm
    (named_back.symm.trans (congrArg
      (fun e : R.BoundaryEnd Set.univ => C.includeRestrictedGerm (U) e.val) mate)) weight
  have fibers := C.regionalCornerSum_restricted_vertex_fiber (U) weight w
  have only_v (x : R.Vertex Set.univ) : C.includeRestrictedVertexUniv (U) x = w ↔ x = v :=
    ⟨unique x, fun equal => equal.symm ▸ q_at⟩
  simp only [only_v, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at fibers
  change C.regionalCornerSum (U) weight w = _
  rw [← fibers]
  have restricted_sum :
      R.regionalCornerSum Set.univ (fun d => weight (d.1.val, d.2)) v =
        ∑ d : R.Corner, if R.vertexOfCorner Set.univ d = v then weight (d.1.val, d.2) else 0 := by
    simp only [TriangleComplex.regionalCornerSum, Set.mem_univ, true_and]
  rw [restricted_sum, ← weights, TriangleComplex.totalAngle, projectedTotalAngle, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hit : C.vertexOfCorner retain d = C.boundaryEndVertex retain p <;>
    simp only [hit, weight, ite_true, ite_false, sub_self]

end Unfoldings.ConvexRoof
