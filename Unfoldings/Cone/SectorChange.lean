module

public import Unfoldings.Cone.SectorCoordinates
public import Unfoldings.Topology.Quadrant
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Linear changes between convex sectors

Boundary-ray coordinates identify any two genuine convex sectors by a bounded
linear equivalence. Both boundary rays retain their radius parameter. These
maps can therefore be glued across angular-fan seams, even when the full fan
has more than one turn and its planar development overlaps.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

def sectorCombinationLinearMap (α : ℝ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (polarRay α)

def sectorCombinationLinearEquiv (α : ℝ) (nonzero : Real.sin α ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] ℂ where
  toLinearEquiv :=
    { toEquiv := (sectorCombinationHomeomorph α nonzero).toEquiv
      map_add' := (sectorCombinationLinearMap α).map_add
      map_smul' := (sectorCombinationLinearMap α).map_smul }
  continuous_toFun := (sectorCombinationHomeomorph α nonzero).continuous
  continuous_invFun := (sectorCombinationHomeomorph α nonzero).symm.continuous

@[simp] theorem sectorCombinationLinearEquiv_apply (α : ℝ) (nonzero : Real.sin α ≠ 0)
    (p : ℝ × ℝ) : sectorCombinationLinearEquiv α nonzero p = sectorCombination α p := rfl

def sectorChangeLinearEquiv (α β : ℝ) (first : Real.sin α ≠ 0) (second : Real.sin β ≠ 0) :
    ℂ ≃L[ℝ] ℂ :=
  (sectorCombinationLinearEquiv α first).symm.trans (sectorCombinationLinearEquiv β second)

theorem sectorChangeLinearEquiv_combination (α β : ℝ)
    (first : Real.sin α ≠ 0) (second : Real.sin β ≠ 0) (p : ℝ × ℝ) :
    sectorChangeLinearEquiv α β first second (sectorCombination α p) = sectorCombination β p := by
  change sectorCombinationLinearEquiv β second
    ((sectorCombinationLinearEquiv α first).symm (sectorCombinationLinearEquiv α first p)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem sectorChangeLinearEquiv_mem_iff (α β : ℝ)
    (first : Real.sin α ≠ 0) (second : Real.sin β ≠ 0) (z : ℂ) :
    sectorChangeLinearEquiv α β first second z ∈ planarSector β ↔ z ∈ planarSector α := by
  constructor
  · rintro ⟨c, hc, d, hd, equal⟩
    have value : sectorChangeLinearEquiv α β first second z = sectorCombination β (c, d) := equal
    have point : z = sectorCombination α (c, d) :=
      (sectorChangeLinearEquiv α β first second).injective
        (value.trans (sectorChangeLinearEquiv_combination α β first second (c, d)).symm)
    exact ⟨c, hc, d, hd, point⟩
  · rintro ⟨c, hc, d, hd, rfl⟩
    exact ⟨c, hc, d, hd, sectorChangeLinearEquiv_combination α β first second (c, d)⟩

def sectorChangeHomeomorph (α β : ℝ) (first : Real.sin α ≠ 0) (second : Real.sin β ≠ 0) :
    planarSector α ≃ₜ planarSector β :=
  (sectorChangeLinearEquiv α β first second).toHomeomorph.subtype
    (fun z => (sectorChangeLinearEquiv_mem_iff α β first second z).symm)

theorem sectorChangeHomeomorph_lipschitz (α β : ℝ)
    (first : Real.sin α ≠ 0) (second : Real.sin β ≠ 0) :
    LipschitzWith ‖(sectorChangeLinearEquiv α β first second).toContinuousLinearMap‖₊
      (sectorChangeHomeomorph α β first second) := by
  intro x y
  exact (sectorChangeLinearEquiv α β first second).toContinuousLinearMap.lipschitzWith.edist_le_mul
    x.val y.val

@[simp] theorem sectorChangeHomeomorph_reverse (α β : ℝ)
    (first : Real.sin α ≠ 0) (second : Real.sin β ≠ 0) (x : planarSector α) :
    sectorChangeHomeomorph β α second first (sectorChangeHomeomorph α β first second x) = x := by
  apply Subtype.ext
  change sectorCombinationLinearEquiv α first
    ((sectorCombinationLinearEquiv β second).symm
      (sectorCombinationLinearEquiv β second
        ((sectorCombinationLinearEquiv α first).symm x.val))) = x.val
  rw [ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- Nonnegative coefficients identify a genuine sector with the closed quadrant. -/
def quadrantSectorHomeomorph (α : ℝ) (nonzero : Real.sin α ≠ 0) :
    PlanarTopology.closedQuadrant ≃ₜ planarSector α where
  toFun p := ⟨sectorCombination α p.val,
    p.val.1, p.property.1, p.val.2, p.property.2, rfl⟩
  invFun z := ⟨(sectorCombinationHomeomorph α nonzero).symm z.val, by
    obtain ⟨c, hc, d, hd, equal⟩ := z.property
    have value : z.val = sectorCombinationHomeomorph α nonzero (c, d) := equal
    rw [value, Homeomorph.symm_apply_apply]
    exact ⟨hc, hd⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact (sectorCombinationHomeomorph α nonzero).symm_apply_apply p.val
  right_inv z := by
    apply Subtype.ext
    exact (sectorCombinationHomeomorph α nonzero).apply_symm_apply z.val
  continuous_toFun := by
    exact ((sectorCombinationHomeomorph α nonzero).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact ((sectorCombinationHomeomorph α nonzero).symm.continuous.comp
      continuous_subtype_val).subtype_mk _

@[simp] theorem quadrantSectorHomeomorph_apply (α : ℝ) (nonzero : Real.sin α ≠ 0)
    (p : PlanarTopology.closedQuadrant) :
    (quadrantSectorHomeomorph α nonzero p).val = sectorCombination α p.val := rfl

def sectorHalfPlaneHomeomorph (α : ℝ) (nonzero : Real.sin α ≠ 0) :
    planarSector α ≃ₜ PlanarTopology.closedHalfPlane :=
  (quadrantSectorHomeomorph α nonzero).symm.trans
    PlanarTopology.quadrantHalfPlaneHomeomorph

@[simp] theorem sectorHalfPlaneHomeomorph_zero (α : ℝ) (nonzero : Real.sin α ≠ 0) :
    sectorHalfPlaneHomeomorph α nonzero
      ⟨0, 0, le_refl 0, 0, le_refl 0, by simp⟩ =
      ⟨(0, 0), by change (0 : ℝ) ≤ 0; rfl⟩ := by
  have source : (⟨0, 0, le_refl 0, 0, le_refl 0, by simp⟩ : planarSector α) =
      quadrantSectorHomeomorph α nonzero
        ⟨(0, 0), by exact ⟨le_refl 0, le_refl 0⟩⟩ := by
    apply Subtype.ext
    simp [sectorCombination]
  rw [source]
  change PlanarTopology.quadrantHalfPlaneHomeomorph
    ((quadrantSectorHomeomorph α nonzero).symm
      (quadrantSectorHomeomorph α nonzero _)) = _
  rw [Homeomorph.symm_apply_apply, PlanarTopology.quadrantHalfPlaneHomeomorph_zero]

@[simp] theorem sectorHalfPlaneHomeomorph_quadrant (α : ℝ) (nonzero : Real.sin α ≠ 0)
    (p : PlanarTopology.closedQuadrant) :
    sectorHalfPlaneHomeomorph α nonzero (quadrantSectorHomeomorph α nonzero p) =
      PlanarTopology.quadrantHalfPlaneHomeomorph p := by
  change PlanarTopology.quadrantHalfPlaneHomeomorph
    ((quadrantSectorHomeomorph α nonzero).symm (quadrantSectorHomeomorph α nonzero p)) = _
  rw [Homeomorph.symm_apply_apply]

end Unfoldings
