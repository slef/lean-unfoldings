module

public import Unfoldings.Complex.Exact
public import Unfoldings.Geometry.Interior
public import Unfoldings.Metric.Local

/-! Constructed Euclidean metric-ball charts at face-interior points. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- A seam attachment point lies on one of the three original cell edges. -/
theorem seamSupport_subset_edges (retain : Set C.Seam) (f : Face) :
    MetricGluing.seamSupport C.Cell (C.glue retain) f ⊆
      {x | ∃ e, x.val ∈ (C.triangle f).edge e} := by
  intro x attached
  rcases attached with ⟨y, s, hs, p, ha, hb⟩ | ⟨y, s, hs, p, ha, hb⟩
  · have face := congrArg Sigma.fst ha
    have coord := congrArg (fun q : C.Total => q.2.val) ha
    change f = (C.left s).face at face
    change x.val = p.val at coord
    refine ⟨(C.left s).edge, ?_⟩
    rw [coord, face]
    exact p.property
  · have face := congrArg Sigma.fst hb
    have coord := congrArg (fun q : C.Total => q.2.val) hb
    change f = (C.right s).face at face
    change x.val = (C.identify s p).val at coord
    refine ⟨(C.right s).edge, ?_⟩
    rw [coord, face]
    exact (C.identify s p).property

/-- An actual Euclidean ball chart with its radius and compatibility with the original face. -/
structure FaceChart (retain : Set C.Seam) (f : Face) (p : C.Cell f) where
  radius : ℝ
  positive : 0 < radius
  included : Metric.ball p.val radius ⊆ (C.triangle f).carrier
  chart : Metric.ball p.val radius ≃ᵢ Metric.eball (C.faceMap retain f p) (ENNReal.ofReal radius)
  agrees : ∀ x, (chart x).val = C.faceMap retain f ⟨x.val, included x.property⟩

/-- Face-interior points have Euclidean charts for the constructed intrinsic metric. -/
theorem exists_faceChart (retain : Set C.Seam) (f : Face) (p : C.Cell f)
    (inside : p.val ∈ interior (C.triangle f).carrier) : Nonempty (C.FaceChart retain f p) := by
  obtain ⟨r, positive, included, clearance⟩ := (C.triangle f).exists_radius_clear_edges p inside
  have clear_support : ∀ x ∈ MetricGluing.seamSupport C.Cell (C.glue retain) f,
      3 * r ≤ dist x p := by
    intro x hx
    obtain ⟨e, he⟩ := C.seamSupport_subset_edges retain f hx
    exact clearance e x.val he
  let chart := ((C.triangle f).cellBallIsometry p r included).trans
    (MetricGluing.ballIsometry C.Cell (C.glue retain) f p positive.le clear_support)
  exact ⟨⟨r, positive, included, chart, fun _ => rfl⟩⟩

/-- Choose a chart only after its existence has been proved from the triangle geometry. -/
def faceChart (retain : Set C.Seam) (f : Face) (p : C.Cell f)
    (inside : p.val ∈ interior (C.triangle f).carrier) : C.FaceChart retain f p :=
  Classical.choice (C.exists_faceChart retain f p inside)

end Unfoldings.TriangleComplex
