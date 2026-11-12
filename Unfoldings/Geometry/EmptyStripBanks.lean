module

public import Unfoldings.Geometry.MonotoneStripTopology
public import Unfoldings.Geometry.SubdivisionWallContacts

/-! A physically empty open slab identifies its actual banks on the whole closed height interval. -/

@[expose] public section

namespace Unfoldings.MonotoneStrip

variable (S : MonotoneStrip)

theorem exists_openSlab_point_at_height {a h b : ℝ} (height : h ∈ Set.Ioo a b)
    (width : S.lower.coordinate h < S.upper.coordinate h) :
    ∃ z ∈ S.openSlab a b, z.re + z.im = h := by
  let x := (S.lower.coordinate h + S.upper.coordinate h) / 2
  let z : ℂ := ⟨x, h - x⟩
  have at_height : z.re + z.im = h := by change x + (h - x) = h; ring
  refine ⟨z, ⟨?_, at_height ▸ height⟩, at_height⟩
  change S.lower.coordinate (z.re + z.im) < x ∧ x < S.upper.coordinate (z.re + z.im)
  rw [at_height]
  dsimp only [x]
  constructor <;> linarith

theorem banks_coordinate_eqOn_of_empty_openSlab {a b : ℝ} (ordered : a < b)
    (empty : S.openSlab a b = ∅) :
    Set.EqOn S.lower.coordinate S.upper.coordinate (Set.Icc a b) := by
  have closed : IsClosed {h : ℝ | S.lower.coordinate h = S.upper.coordinate h} :=
    isClosed_eq S.lower.continuous S.upper.continuous
  have zero_width : Set.Ioo a b ⊆ {h : ℝ | S.lower.coordinate h = S.upper.coordinate h} := by
    intro h member
    by_contra different
    have width : S.lower.coordinate h < S.upper.coordinate h :=
      lt_of_le_of_ne (S.ordered h) different
    obtain ⟨z, inside, _⟩ := S.exists_openSlab_point_at_height member width
    rw [empty] at inside
    exact inside
  have all : Set.Icc a b ⊆ {h : ℝ | S.lower.coordinate h = S.upper.coordinate h} := by
    rw [← closure_Ioo ordered.ne]
    exact closure_minimal zero_width closed
  exact all

theorem banks_point_eqOn_of_empty_openSlab {a b : ℝ} (ordered : a < b)
    (empty : S.openSlab a b = ∅) : Set.EqOn S.lower.point S.upper.point (Set.Icc a b) := by
  intro h member
  exact S.lower.point_eq_of_same_coordinate S.upper
    (S.banks_coordinate_eqOn_of_empty_openSlab ordered empty member)

end Unfoldings.MonotoneStrip
