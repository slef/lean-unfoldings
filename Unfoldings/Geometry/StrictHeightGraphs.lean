module

public import Unfoldings.Geometry.RayStrip
public import Mathlib.Order.Monotone.Union

/-! Strict progress in both coordinates survives the operations used for waterfall walls. -/

@[expose] public section

namespace Unfoldings.MonotoneHeightGraph

variable (G H : MonotoneHeightGraph)

/-- Both physical coordinates increase strictly on the specified height domain. -/
def StrictCoordinatesOn (s : Set ℝ) : Prop :=
  StrictMonoOn G.coordinate s ∧ StrictMonoOn (fun h => h - G.coordinate h) s

variable {G} in
theorem StrictCoordinatesOn.mono {s t : Set ℝ} (strict : G.StrictCoordinatesOn s)
    (subset : t ⊆ s) : G.StrictCoordinatesOn t :=
  ⟨strict.1.mono subset, strict.2.mono subset⟩

theorem strictCoordinatesOn_min {s : Set ℝ}
    (first : G.StrictCoordinatesOn s) (last : H.StrictCoordinatesOn s) :
    (G.min H).StrictCoordinatesOn s := by
  constructor
  · intro a ha b hb ordered
    exact min_lt_min (first.1 ha hb ordered) (last.1 ha hb ordered)
  · intro a ha b hb ordered
    change a - Min.min (G.coordinate a) (H.coordinate a) <
      b - Min.min (G.coordinate b) (H.coordinate b)
    rw [← max_sub_sub_left, ← max_sub_sub_left]
    exact max_lt_max (first.2 ha hb ordered) (last.2 ha hb ordered)

theorem strictCoordinatesOn_max {s : Set ℝ}
    (first : G.StrictCoordinatesOn s) (last : H.StrictCoordinatesOn s) :
    (G.max H).StrictCoordinatesOn s := by
  constructor
  · intro a ha b hb ordered
    exact max_lt_max (first.1 ha hb ordered) (last.1 ha hb ordered)
  · intro a ha b hb ordered
    change a - Max.max (G.coordinate a) (H.coordinate a) <
      b - Max.max (G.coordinate b) (H.coordinate b)
    rw [← min_sub_sub_left, ← min_sub_sub_left]
    exact min_lt_min (first.2 ha hb ordered) (last.2 ha hb ordered)

theorem strictCoordinatesOn_affine (height x slope : ℝ)
    (positive : 0 < slope) (small : slope < 1) (s : Set ℝ) :
    (affine height x slope positive.le small.le).StrictCoordinatesOn s := by
  constructor
  · intro a _ b _ ordered
    change x + slope * (a - height) < x + slope * (b - height)
    nlinarith [mul_pos positive (sub_pos.mpr ordered)]
  · intro a _ b _ ordered
    change a - (x + slope * (a - height)) < b - (x + slope * (b - height))
    nlinarith [mul_pos (sub_pos.mpr small) (sub_pos.mpr ordered)]

theorem strictCoordinatesOn_ray (p : ℂ) (horizontal : 0 < p.re) (vertical : 0 < p.im)
    (s : Set ℝ) : (ray p horizontal vertical).StrictCoordinatesOn s :=
  strictCoordinatesOn_affine 0 0 _ (div_pos horizontal (add_pos horizontal vertical))
    ((div_lt_one (add_pos horizontal vertical)).mpr (by linarith)) s

/-- Splicing genuinely increasing pieces preserves strict progress across the joining height. -/
theorem strictCoordinatesOn_splice {a c b : ℝ}
    (joined : G.coordinate c = H.coordinate c)
    (first : G.StrictCoordinatesOn (Set.Icc a c))
    (last : H.StrictCoordinatesOn (Set.Icc c b)) (ac : a ≤ c) (cb : c ≤ b) :
    (G.splice H c joined).StrictCoordinatesOn (Set.Icc a b) := by
  have first_eq : Set.EqOn (G.splice H c joined).coordinate G.coordinate (Set.Icc a c) :=
    fun _ member => G.splice_coordinate_left H c joined member.2
  have last_eq : Set.EqOn (G.splice H c joined).coordinate H.coordinate (Set.Icc c b) :=
    fun _ member => G.splice_coordinate_right H c joined member.1
  have cover : Set.Icc a c ∪ Set.Icc c b = Set.Icc a b := Set.Icc_union_Icc_eq_Icc ac cb
  constructor
  · rw [← cover]
    exact (first.1.congr first_eq.symm).union (last.1.congr last_eq.symm)
      (isGreatest_Icc ac) (isLeast_Icc cb)
  · rw [← cover]
    have first_complement : StrictMonoOn
        (fun h => h - (G.splice H c joined).coordinate h) (Set.Icc a c) :=
      first.2.congr (fun _ member => congrArg (fun r => _ - r) (first_eq member).symm)
    have last_complement : StrictMonoOn
        (fun h => h - (G.splice H c joined).coordinate h) (Set.Icc c b) :=
      last.2.congr (fun _ member => congrArg (fun r => _ - r) (last_eq member).symm)
    exact first_complement.union last_complement (isGreatest_Icc ac) (isLeast_Icc cb)

end Unfoldings.MonotoneHeightGraph

namespace Unfoldings.MonotoneStrip

theorem rayStrip_strictCoordinatesOn (p q : ℂ) (px : 0 < p.re) (py : 0 < p.im)
    (qx : 0 < q.re) (qy : 0 < q.im) (s : Set ℝ) :
    (rayStrip p q px py qx qy).lower.StrictCoordinatesOn s ∧
      (rayStrip p q px py qx qy).upper.StrictCoordinatesOn s :=
  ⟨MonotoneHeightGraph.strictCoordinatesOn_min _ _
      (MonotoneHeightGraph.strictCoordinatesOn_ray p px py s)
      (MonotoneHeightGraph.strictCoordinatesOn_ray q qx qy s),
    MonotoneHeightGraph.strictCoordinatesOn_max _ _
      (MonotoneHeightGraph.strictCoordinatesOn_ray p px py s)
      (MonotoneHeightGraph.strictCoordinatesOn_ray q qx qy s)⟩

end Unfoldings.MonotoneStrip
