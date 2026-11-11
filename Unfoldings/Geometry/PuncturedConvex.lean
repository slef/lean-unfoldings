module

public import Unfoldings.Geometry.RayAvoidance
public import Mathlib.Analysis.Convex.PathConnected

/-! Removing one point preserves path connectivity of a full-dimensional convex planar set. -/

@[expose] public section

noncomputable section

namespace Unfoldings

/-- A full-dimensional convex planar region remains path connected after removing one point. -/
theorem convex_isPathConnected_sdiff_singleton {S : Set Plane} (convex : Convex ℝ S)
    (nonempty : (interior S).Nonempty) (p : Plane) : IsPathConnected (S \ {p}) := by
  classical
  have choose_pivot {x y : Plane} (xp : x ≠ p) (yp : y ≠ p) :
      ∃ z ∈ interior S, orient x p z ≠ 0 ∧ orient y p z ≠ 0 := by
    let equation (b : Bool) := if b then orientMap x p else orientMap y p
    have proper (b : Bool) : equation b ≠ 0 := by
      cases b
      · exact orientMap_ne_zero yp
      · exact orientMap_ne_zero xp
    obtain ⟨z, regular, member⟩ :=
      (AffineArrangement.dense_regular equation proper).exists_mem_open isOpen_interior nonempty
    exact ⟨z, member, by simpa [equation, orientMap_apply] using regular true,
      by simpa [equation, orientMap_apply] using regular false⟩
  have segment_avoids {x z : Plane} (regular : orient x p z ≠ 0) :
      p ∉ segment ℝ x z := by
    intro member
    rw [segment_eq_image_lineMap] at member
    obtain ⟨t, _bounds, equal⟩ := member
    exact lineMap_ne_of_orient_ne_zero regular t equal
  have connected (x y : Plane) (hx : x ∈ S \ {p}) (hy : y ∈ S \ {p}) :
      JoinedIn (S \ {p}) x y := by
    obtain ⟨z, member, first, last⟩ := choose_pivot hx.2 hy.2
    have first_path : JoinedIn (S \ {p}) x z := JoinedIn.of_segment_subset (fun w hw =>
      ⟨convex.segment_subset hx.1 (interior_subset member) hw,
        fun equal => segment_avoids first (Set.mem_singleton_iff.mp equal ▸ hw)⟩)
    have last_path : JoinedIn (S \ {p}) y z := JoinedIn.of_segment_subset (fun w hw =>
      ⟨convex.segment_subset hy.1 (interior_subset member) hw,
        fun equal => segment_avoids last (Set.mem_singleton_iff.mp equal ▸ hw)⟩)
    exact first_path.trans last_path.symm
  obtain ⟨x, different, hx⟩ :=
    (dense_compl_singleton p).exists_mem_open isOpen_interior nonempty
  exact ⟨x, ⟨interior_subset hx, different⟩, fun y hy => connected x y
    ⟨interior_subset hx, different⟩ hy⟩

end Unfoldings
