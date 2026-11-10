module

public import Unfoldings.Cap.ThreeSectorProgress

/-! Construct an original-edge forest with preserved source-centered acute sectors. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexCap

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexCap C)

def sourceSectorLabel (t : ℝ) (origin vertex : C.Vertex Set.univ) : Fin 3 :=
  threeSectorLabel t (K.projectedVertex vertex - K.projectedVertex origin)

/-- A constructed forest with actual seam names and source-centered sector directions. -/
structure SectorForest (t : ℝ) (origin : C.Vertex Set.univ) where
  maximal : ∀ v, ¬ C.IsBoundaryVertex Set.univ v →
    K.projectedVertex v 0 ≤ K.projectedVertex origin 0
  parents : AscendingParents (C.Vertex Set.univ)
  roots_eq : parents.roots = {v | C.IsBoundaryVertex Set.univ v}
  selection : parents.EdgeSelection C.seamGraph
  direction : ∀ v ∉ parents.roots,
    K.projectedVertex (parents.parent v) - K.projectedVertex v ∈
      strictThreeSector t (K.sourceSectorLabel t origin v)

/-- Positions on a sector bank are allowed; each outgoing edge moves into the sector interior. -/
def sectorForest {t : ℝ} (nonnegative : 0 ≤ t) (small : t < 1)
    (origin : C.Vertex Set.univ)
    (maximal : ∀ v, ¬ C.IsBoundaryVertex Set.univ v →
      K.projectedVertex v 0 ≤ K.projectedVertex origin 0)
    (acute : ∀ i f j, ((K.projectedTriangle f).affineImage
      (threeSectorCoordinates t i).toAffineMap
        (threeSectorCoordinates_affine_injective nonnegative small i)).cornerAngle j <
          Real.pi / 2) :
    K.SectorForest t origin := by
  classical
  let roots : Set (C.Vertex Set.univ) := {v | C.IsBoundaryVertex Set.univ v}
  let label := K.sourceSectorLabel t origin
  have step (v : {v : C.Vertex Set.univ // v ∉ roots}) : ∃ w s,
      C.seamGraph.IsLink s v.val w ∧
      K.projectedVertex w - K.projectedVertex v.val ∈ strictThreeSector t (label v.val) ∧
      label w = label v.val := by
    obtain ⟨w, s, link, direction⟩ := K.exists_threeSector_seam_step nonnegative small
      (label v.val) (acute (label v.val)) v.val v.property
    refine ⟨w, s, link, direction, ?_⟩
    have backward : (K.projectedVertex v.val - K.projectedVertex origin) 0 ≤ 0 :=
      sub_nonpos.mpr (maximal v.val v.property)
    have position := mem_closedThreeSector_label_of_backward nonnegative small backward
    have preserved := threeSectorLabel_add nonnegative small position direction
    have sum : (K.projectedVertex v.val - K.projectedVertex origin) +
        (K.projectedVertex w - K.projectedVertex v.val) =
          K.projectedVertex w - K.projectedVertex origin := by abel
    rw [sum] at preserved
    exact preserved
  choose next edge linked directions labels using step
  let potential (i : Fin 3) (v : C.Vertex Set.univ) : ℝ :=
    threeSectorCoordinates t i (K.projectedVertex v) 0 +
      threeSectorCoordinates t i (K.projectedVertex v) 1
  let P : AscendingParents (C.Vertex Set.univ) :=
    { roots := roots
      parent v := if h : v ∈ roots then v else next ⟨v, h⟩
      height v := potential (label v) v
      fixed_root v root := dite_eq_left root
      ascending v nonroot := by
        rw [dite_eq_right nonroot, labels ⟨v, nonroot⟩]
        have pair := directions ⟨v, nonroot⟩
        change 0 < threeSectorCoordinates t (label v)
          (K.projectedVertex (next ⟨v, nonroot⟩) - K.projectedVertex v) 0 ∧
          0 < threeSectorCoordinates t (label v)
            (K.projectedVertex (next ⟨v, nonroot⟩) - K.projectedVertex v) 1 at pair
        simp only [map_sub, PiLp.sub_apply] at pair
        dsimp only [potential]
        linarith }
  let S : P.EdgeSelection C.seamGraph :=
    { edge v := edge ⟨v.val, v.property⟩
      link v := by
        change C.seamGraph.IsLink (edge ⟨v.val, v.property⟩) v.val
          (if h : v.val ∈ roots then v.val else next ⟨v.val, h⟩)
        rw [dite_eq_right v.property]
        exact linked ⟨v.val, v.property⟩ }
  refine ⟨maximal, P, rfl, S, ?_⟩
  intro v nonroot
  change K.projectedVertex (if h : v ∈ roots then v else next ⟨v, h⟩) -
    K.projectedVertex v ∈ strictThreeSector t (label v)
  rw [dite_eq_right nonroot]
  exact directions ⟨v, nonroot⟩

end Unfoldings.ConvexCap
