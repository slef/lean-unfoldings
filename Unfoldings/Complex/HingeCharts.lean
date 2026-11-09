module

public import Unfoldings.Complex.HingeCoordinates

/-! Constructed Euclidean metric-ball charts at nonvertex retained-seam points. -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace Unfoldings.TriangleComplex

universe u v

variable {Face : Type u} [Fintype Face] (C : TriangleComplex.{u, v} Face)

/-- Quantitative local geometry, proved from the finite seam system below. -/
structure HingeNeighborhood (retain : Set C.Seam) (s : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) where
  radius : ℝ
  positive : 0 < radius
  cover : Metric.ball x.val radius ⊆ (C.triangle (C.left s).face).carrier ∪
    (C.seamHinge s).place '' (C.triangle (C.right s).face).carrier
  faces : ∀ a : C.Total,
    edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
      (MetricGluing.point C.Cell (C.glue retain) a) < ENNReal.ofReal radius →
        a.1 = (C.left s).face ∨ a.1 = (C.right s).face
  coordinates : ∀ a : C.Total,
    edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
      (MetricGluing.point C.Cell (C.glue retain) a) < ENNReal.ofReal radius →
        C.hingeCoordinates s a ∈ Metric.ball x.val radius
  exact_distance : ∀ a b : C.Total,
    edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
      (MetricGluing.point C.Cell (C.glue retain) a) < ENNReal.ofReal radius →
    edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
      (MetricGluing.point C.Cell (C.glue retain) b) < ENNReal.ofReal radius →
    edist (MetricGluing.point C.Cell (C.glue retain) a)
      (MetricGluing.point C.Cell (C.glue retain) b) =
        edist (C.hingeCoordinates s a) (C.hingeCoordinates s b)

theorem exists_hingeNeighborhood (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x) :
    Nonempty (C.HingeNeighborhood retain s x) := by
  obtain ⟨δ, δpos, step⟩ := C.exists_radius_hinge_step retain s kept different x regular
  obtain ⟨ε, εpos, transport⟩ := C.exists_class_transport retain (C.edgePoint (C.left s) x)
  obtain ⟨R, Rpos, cover⟩ := (C.seamHinge s).exists_ball_cover x regular
  let r := min (δ / 4) (min ε R)
  have rpos : 0 < r := lt_min (div_pos δpos (by norm_num)) (lt_min εpos Rpos)
  have small : r ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have covered : r ≤ R := (min_le_right _ _).trans (min_le_right _ _)
  have budget_radius : 3 * r ≤ δ := by
    have bound : r ≤ δ / 4 := min_le_left _ _
    linarith
  have crossing : C.Crosses retain (C.edgePoint (C.left s) x)
      (C.edgePoint (C.right s) (C.identify s x)) := ⟨s, kept, false, x, rfl, rfl⟩
  have regular' : ¬ C.IsVertex (C.edgePoint (C.left s) x) := regular
  have faces (a : C.Total)
      (near : edist (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
        (MetricGluing.point C.Cell (C.glue retain) a) < ENNReal.ofReal r) :
      a.1 = (C.left s).face ∨ a.1 = (C.right s).face :=
    C.face_eq_or_of_near_class regular' crossing εpos transport
      (near.trans_le (ENNReal.ofReal_le_ofReal small))
  have coordinates := C.hingeCoordinates_mem_ball retain s kept different x regular
    εpos small transport
  refine ⟨⟨r, rpos, (Metric.ball_subset_ball covered).trans cover, faces, coordinates, ?_⟩⟩
  intro a b ha hb
  apply le_antisymm
  · exact C.edist_le_hinge_coordinates retain s kept different
      ((Metric.ball_subset_ball covered).trans cover) a b (faces a ha) (faces b hb)
      (coordinates a ha) (coordinates b hb)
  · have ca : edist (C.hingeCoordinates s a) x.val < ENNReal.ofReal r := by
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr
        (Metric.mem_ball.mp (coordinates a ha))
    have cb : edist x.val (C.hingeCoordinates s b) < ENNReal.ofReal r := by
      rw [edist_comm, edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr
        (Metric.mem_ball.mp (coordinates b hb))
    have chord := (edist_triangle (C.hingeCoordinates s a) x.val (C.hingeCoordinates s b)).trans_lt
      (ENNReal.add_lt_add ca cb)
    have total := ENNReal.add_lt_add ha chord
    have radius_sum : ENNReal.ofReal r + (ENNReal.ofReal r + ENNReal.ofReal r) =
        ENNReal.ofReal (3 * r) := by
      rw [← ENNReal.ofReal_add rpos.le rpos.le,
        ← ENNReal.ofReal_add rpos.le (add_nonneg rpos.le rpos.le)]
      congr 1
      ring
    rw [radius_sum] at total
    exact MetricGluing.map_edist_le_edist_of_budget C.Cell (C.glue retain)
      (C.hingeCoordinates s) _ (ENNReal.ofReal δ) step a b
      (total.trans_le (ENNReal.ofReal_le_ofReal budget_radius))

/-- A Euclidean ball chart, with compatibility on both original incident faces. -/
structure HingeChart (retain : Set C.Seam) (s : C.Seam)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge) where
  radius : ℝ
  positive : 0 < radius
  chart : Metric.ball x.val radius ≃ᵢ
    Metric.eball (MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x))
      (ENNReal.ofReal radius)
  agrees : ∀ (a : C.Total)
    (_faces : a.1 = (C.left s).face ∨ a.1 = (C.right s).face)
    (near : C.hingeCoordinates s a ∈ Metric.ball x.val radius),
    (chart ⟨C.hingeCoordinates s a, near⟩).val = MetricGluing.point C.Cell (C.glue retain) a

/-- Every nonvertex seam point with distinct incident faces has an actual Euclidean metric chart. -/
theorem exists_hingeChart (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x) :
    Nonempty (C.HingeChart retain s x) := by
  classical
  obtain ⟨N⟩ := C.exists_hingeNeighborhood retain s kept different x regular
  let center := MetricGluing.point C.Cell (C.glue retain) (C.edgePoint (C.left s) x)
  have lifts (z : Metric.ball x.val N.radius) := C.exists_hinge_lift s different N.cover z.property
  choose lift lift_faces lift_coordinates using lifts
  have coordinate_near (z : Metric.ball x.val N.radius) :
      edist x.val z.val < ENNReal.ofReal N.radius := by
    rw [edist_comm, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr
      (Metric.mem_ball.mp z.property)
  have lift_near (z : Metric.ball x.val N.radius) :
      edist center (MetricGluing.point C.Cell (C.glue retain) (lift z)) <
        ENNReal.ofReal N.radius := by
    have bound := C.edist_center_le_hingeCoordinates retain s kept different x
      (lift z) (lift_faces z)
    rw [lift_coordinates z] at bound
    exact bound.trans_lt (coordinate_near z)
  let f : Metric.ball x.val N.radius → Metric.eball center (ENNReal.ofReal N.radius) :=
    fun z => ⟨MetricGluing.point C.Cell (C.glue retain) (lift z), by
      rw [Metric.mem_eball, edist_comm]
      exact lift_near z⟩
  have isometry : Isometry f := by
    intro z w
    change edist (MetricGluing.point C.Cell (C.glue retain) (lift z))
      (MetricGluing.point C.Cell (C.glue retain) (lift w)) = edist z.val w.val
    rw [N.exact_distance _ _ (lift_near z) (lift_near w), lift_coordinates z, lift_coordinates w]
  have surjective : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := MetricGluing.point_surjective C.Cell (C.glue retain) y.val
    have near : edist center (MetricGluing.point C.Cell (C.glue retain) a) <
        ENNReal.ofReal N.radius := by
      rw [ha, edist_comm]
      exact y.property
    let z : Metric.ball x.val N.radius := ⟨C.hingeCoordinates s a, N.coordinates a near⟩
    refine ⟨z, Subtype.ext ?_⟩
    apply edist_eq_zero.mp
    change edist (MetricGluing.point C.Cell (C.glue retain) (lift z)) y.val = 0
    rw [← ha, N.exact_distance _ _ (lift_near z) near, lift_coordinates z]
    exact edist_self _
  let chart : Metric.ball x.val N.radius ≃ᵢ Metric.eball center (ENNReal.ofReal N.radius) :=
    ⟨Equiv.ofBijective f ⟨isometry.injective, surjective⟩, isometry⟩
  refine ⟨⟨N.radius, N.positive, chart, ?_⟩⟩
  intro a faces near
  let z : Metric.ball x.val N.radius := ⟨C.hingeCoordinates s a, near⟩
  have a_near : edist center (MetricGluing.point C.Cell (C.glue retain) a) <
      ENNReal.ofReal N.radius :=
    (C.edist_center_le_hingeCoordinates retain s kept different x a faces).trans_lt
      (coordinate_near z)
  apply edist_eq_zero.mp
  change edist (MetricGluing.point C.Cell (C.glue retain) (lift z))
    (MetricGluing.point C.Cell (C.glue retain) a) = 0
  rw [N.exact_distance _ _ (lift_near z) a_near, lift_coordinates z]
  exact edist_self _

/-- Choose a chart after proving its existence from the actual triangle gluing. -/
def hingeChart (retain : Set C.Seam) (s : C.Seam) (kept : s ∈ retain)
    (different : (C.left s).face ≠ (C.right s).face)
    (x : (C.triangle (C.left s).face).Edge (C.left s).edge)
    (regular : ¬ (C.triangle (C.left s).face).IsVertex x) : C.HingeChart retain s x :=
  Classical.choice (C.exists_hingeChart retain s kept different x regular)

end Unfoldings.TriangleComplex
