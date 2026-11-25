module

public import Unfoldings.FewestNets.ThreeExitRoots
public import Mathlib.Tactic.FinCases

/-! Every actual compatible root uses one of its two certified exit headings. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof.ThreeExitComponentRouting

open FewestNets Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {K : ConvexRoof C} {slopes : Set Plane} {seed : Face}
  {B : PolygonSideDirections (Fin 3) slopes}
  {compact : IsCompact slopes} {nonempty : slopes.Nonempty} {H : ThreeExitStemWindows}
  (R : K.ThreeExitComponentRouting seed B compact nonempty H)

local notation "Root" => {r // r ∈ R.stems.choice.parents.roots}

private theorem east_choice (i : Fin 3) (allowed : i ≠ 1) : i = 0 ∨ i = 2 := by
  fin_cases i <;> simp_all

private theorem west_choice (i : Fin 3) (allowed : i ≠ 0) : i = 1 ∨ i = 2 := by
  fin_cases i <;> simp_all

private theorem north_span {lo stem width : ℝ} (nonnegative : 0 ≤ width)
    (upper : lo + stem < π / 2) (allowed : π / 2 - lo ≤ width) :
    max (lo + stem) (π / 2) - min lo (π / 2) ≤ width := by
  rw [max_eq_right upper.le]
  rcases le_total lo (π / 2) with low | high
  · rwa [min_eq_left low]
  · rw [min_eq_right high, sub_self]
    exact nonnegative

/-- The compatible root chooses an east or north exit for an east history,
and a west or north exit for a west history. Its entire cone has the specified width. -/
theorem root_span_of_signed_headings {e w width : ℝ} (nonnegative : 0 ≤ width)
    (east : (exitHeadingChart false (B.normal 0)).arg = e)
    (west : (exitHeadingChart true (B.normal 1)).arg = -w)
    (north : ∀ side, (exitHeadingChart side (B.normal 2)).arg = π / 2)
    (span_e : max (H.eastStart + H.width) e - min H.eastStart e ≤ width)
    (span_w : max (H.westStart + H.width) (-w) - min H.westStart (-w) ≤ width)
    (north_e : π / 2 - H.eastStart ≤ width) (north_w : π / 2 - H.westStart ≤ width)
    (r : Root) :
    let exit := (R.rootHeadingChart r (R.rootExitDirection r)).arg
    let lo := R.rootWindowStart r
    max (lo + H.width) exit - min lo exit ≤ width := by
  classical
  let i := B.sideIndex (R.exits.slope (R.exitRoot r) + B.reference)
  have direction : R.rootExitDirection r = B.normal i := R.direction_eq (R.exitRoot r)
  have compatible := R.compatible r.val (R.root_frontier r)
  change (R.stems.choice.choosesEast r.val → i ≠ 1) ∧
    (¬ R.stems.choice.choosesEast r.val → i ≠ 0) at compatible
  dsimp only
  by_cases eastward : R.stems.choice.choosesEast r.val
  · simp only [rootHeadingChart, rootWindowStart, ite_eq_left eastward, direction]
    rcases east_choice i (compatible.1 eastward) with horizontal | vertical
    · rw [horizontal, east]
      exact span_e
    · rw [vertical, north]
      exact north_span nonnegative H.east_upper north_e
  · simp only [rootHeadingChart, rootWindowStart, ite_eq_right eastward, direction]
    rcases west_choice i (compatible.2 eastward) with horizontal | vertical
    · rw [horizontal, west]
      exact span_w
    · rw [vertical, north]
      exact north_span nonnegative H.west_upper north_w

/-- The exact north unit vector has heading `π/2` in both exit charts. -/
theorem north_arg (side : Bool) :
    (exitHeadingChart side (WithLp.toLp 2 ![0, 1] : Plane)).arg = π / 2 := by
  have eq : exitHeadingChart side (WithLp.toLp 2 ![0, 1] : Plane) = Complex.I := by
    apply Complex.ext
    · cases side <;> simp [exitHeadingChart_re]
    · simp [exitHeadingChart_im]
  rw [eq, Complex.arg_I]

end Unfoldings.ConvexRoof.ThreeExitComponentRouting
