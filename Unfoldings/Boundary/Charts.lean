module

public import Unfoldings.Boundary.Exact
public import Unfoldings.Complex.Charts
public import Unfoldings.Geometry.Barycentric

/-! Constructed metric half-ball charts at nonvertex boundary-bank points. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Every seam attachment occurs on an edge whose pairing is retained. -/
theorem seamSupport_on_attachingEdge (retain : Set C.Seam) (f : Face) (x : C.Cell f)
    (attached : x ∈ MetricGluing.seamSupport C.Cell (C.glue retain) f) :
    ∃ e, C.OnEdge e ⟨f, x⟩ ∧ ¬ C.IsBoundaryEdge retain e := by
  rcases attached with ⟨y, s, hs, p, ha, hb⟩ | ⟨y, s, hs, p, ha, hb⟩
  · refine ⟨C.left s, ?_, ?_⟩
    · rw [ha]
      exact C.edgePoint_onEdge (C.left s) p
    · intro boundary
      exact boundary ⟨s, hs, Or.inl rfl⟩
  · refine ⟨C.right s, ?_, ?_⟩
    · rw [hb]
      exact C.edgePoint_onEdge (C.right s) (C.identify s p)
    · intro boundary
      exact boundary ⟨s, hs, Or.inr rfl⟩

/-- Unpaired edge interiors have positive metric clearance from all retained attachments. -/
theorem exists_boundary_clearance (retain : Set C.Seam) (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ (C.triangle bank.val.face).IsVertex x) : ∃ ε > 0,
      ∀ z ∈ MetricGluing.seamSupport C.Cell (C.glue retain) bank.val.face,
        ε ≤ dist z ((C.triangle bank.val.face).edgeMap bank.val.edge x) := by
  obtain ⟨ε, positive, bound⟩ :=
    (C.triangle bank.val.face).exists_radius_clear_other_edges bank.val.edge x regular
  refine ⟨ε, positive, ?_⟩
  intro z hz
  obtain ⟨e, on_edge, not_boundary⟩ := C.seamSupport_on_attachingEdge retain bank.val.face z hz
  have face : e.face = bank.val.face := on_edge.1.symm
  have different : e.edge ≠ bank.val.edge := by
    intro equal
    have same : e = bank.val := congrArg₂ (EdgeRef.mk : Face → Fin 3 → EdgeRef Face) face equal
    exact not_boundary (same.symm ▸ bank.property)
  have member := on_edge.2
  rw [face] at member
  exact bound e.edge different z.val member

/-- A boundary chart is a Euclidean half-ball isometric to an entire intrinsic open ball. -/
structure BoundaryChart (retain : Set C.Seam) (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge) where
  radius : ℝ
  positive : 0 < radius
  halfplane : ∀ p ∈ Metric.ball x.val radius,
    (p ∈ (C.triangle bank.val.face).carrier ↔
      0 ≤ (C.triangle bank.val.face).coord (Triangle.next (Triangle.next bank.val.edge)) p)
  chart : (C.triangle bank.val.face).edgeHalfBall bank.val.edge x radius ≃ᵢ
    Metric.eball (C.bankMap retain bank x) (ENNReal.ofReal radius)
  agrees : ∀ p, (chart p).val = C.faceMap retain bank.val.face
    ⟨p.val, (halfplane p.val p.property.1).mpr p.property.2⟩

/-- Every nonvertex bank point has a metric half-disk chart, regardless of other cuts. -/
theorem exists_boundaryChart (retain : Set C.Seam) (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ (C.triangle bank.val.face).IsVertex x) :
    Nonempty (C.BoundaryChart retain bank x) := by
  obtain ⟨δ, δpos, geometry⟩ :=
    (C.triangle bank.val.face).exists_ball_halfplane_edge bank.val.edge x regular
  obtain ⟨ε, εpos, clearance⟩ := C.exists_boundary_clearance retain bank x regular
  let r := min δ (ε / 3)
  have positive : 0 < r := lt_min δpos (div_pos εpos (by norm_num))
  have halfplane : ∀ p ∈ Metric.ball x.val r,
      (p ∈ (C.triangle bank.val.face).carrier ↔
        0 ≤ (C.triangle bank.val.face).coord (Triangle.next (Triangle.next bank.val.edge)) p) :=
    fun p hp => geometry p (Metric.ball_subset_ball (min_le_left _ _) hp)
  have support_clear : ∀ z ∈ MetricGluing.seamSupport C.Cell (C.glue retain) bank.val.face,
      3 * r ≤ dist z ((C.triangle bank.val.face).edgeMap bank.val.edge x) := by
    intro z hz
    have lower := clearance z hz
    have small : r ≤ ε / 3 := min_le_right _ _
    linarith
  let chart := ((C.triangle bank.val.face).edgeHalfBallIsometry bank.val.edge x r halfplane).trans
    (MetricGluing.ballIsometry C.Cell (C.glue retain) bank.val.face
      ((C.triangle bank.val.face).edgeMap bank.val.edge x) positive.le support_clear)
  exact ⟨⟨r, positive, halfplane, chart, fun _ => rfl⟩⟩

def boundaryChart (retain : Set C.Seam) (bank : C.BoundaryBank retain)
    (x : (C.triangle bank.val.face).Edge bank.val.edge)
    (regular : ¬ (C.triangle bank.val.face).IsVertex x) : C.BoundaryChart retain bank x :=
  Classical.choice (C.exists_boundaryChart retain bank x regular)

end Unfoldings.TriangleComplex
