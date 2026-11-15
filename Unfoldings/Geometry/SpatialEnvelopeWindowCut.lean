module

public import Unfoldings.Geometry.SpatialEnvelopeFaceSideBall
public import Unfoldings.Metric.CutSubfamilyBall
public import Unfoldings.Metric.BallIsometry

/-! Actual polygonal-window cut patches, retaining all original metric copies in interior balls. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialEnvelope.WholePartition

universe u

variable {I A : Type u} [Fintype I] [Nonempty I] {family : I → SpatialPlane}
  (P : WholePartition family A) [Finite A] {J : Type*}

/-- The cells on all the specified positive window sides. -/
def WindowSelected (signs : A → J → Bool) (a : A) : Prop := ∀ j, signs a j = true

/-- The actual original physical cut inside the selected polygonal window cells. -/
abbrev WindowCut (signs : A → J → Bool) (cuts : Set Plane) :=
  MetricGluing.CutSubfamily P.spatialCell P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts)
    (WindowSelected signs)

/-- Include the actual window patch into the same original full-roof cut. -/
@[macro_inline] def windowCutMap (signs : A → J → Bool) (cuts : Set Plane)
    (source : P.WindowCut signs cuts) : P.Cut cuts :=
  (P.cutIsometryEquiv cuts).symm (MetricGluing.cutSubfamilyMap P.spatialCell
    P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts) (WindowSelected signs) source)

theorem windowCutMap_lipschitz (signs : A → J → Bool) (cuts : Set Plane) :
    LipschitzWith 1 (P.windowCutMap signs cuts) := by
  intro x y
  exact ((P.cutIsometryEquiv cuts).symm.isometry.edist_eq _ _).trans_le
    (MetricGluing.cutSubfamilyMap_lipschitz P.spatialCell P.isClosed_spatialCell
      (Cap.horizontal ⁻¹' cuts) (WindowSelected signs) x y)

/-- The patch inclusion retains every original spatial roof point. -/
theorem restoreCut_windowCutMap (signs : A → J → Bool) (cuts : Set Plane)
    (x : P.WindowCut signs cuts) :
    (P.restoreCut cuts (P.windowCutMap signs cuts x)).val =
      (MetricGluing.cutSeams (fun a : {a // WindowSelected signs a} => P.spatialCell a.val)
        (fun a => P.isClosed_spatialCell a.val) (Cap.horizontal ⁻¹' cuts)).fold x := by
  exact (P.fold_cutIsometryEquiv cuts _).symm.trans
    ((congrArg (P.cutPhysicalSeams cuts).fold
      ((P.cutIsometryEquiv cuts).apply_symm_apply _)).trans
        (MetricGluing.fold_cutSubfamilyMap P.spatialCell P.isClosed_spatialCell
          (Cap.horizontal ⁻¹' cuts) (WindowSelected signs) x))

omit [Finite A] in
/-- Strict physical window membership forces every cell at that point onto all window sides. -/
theorem windowSelected_of_spatial_mem (equations : J → Plane →ᵃ[ℝ] ℝ) (signs : A → J → Bool)
    (aligned : ∀ a z, z ∈ P.footprint a → ∀ j,
      0 ≤ AffineArrangement.signed (equations j) (signs a j) z)
    (p : Space) (positive : ∀ j, 0 < equations j (Cap.horizontal p))
    (a : A) (member : p ∈ P.spatialCell a) : WindowSelected signs a := by
  intro j
  have bound := aligned a (Cap.horizontal p)
    (P.horizontal_mem_footprint_of_spatial a ⟨p, member⟩) j
  cases value : signs a j
  · have nonpositive : equations j (Cap.horizontal p) ≤ 0 := by
      simpa only [AffineArrangement.signed_apply, value, Bool.false_eq_true,
        ↓reduceIte, neg_nonneg] using bound
    exact False.elim ((not_lt_of_ge nonpositive) (positive j))
  · rfl

/-- Every actual cut copy over the strict window interior has a whole original window-patch ball.
Neither convexity nor a global isometry of the intrinsic window patch is required. -/
theorem exists_windowCut_ball_chart (equations : J → Plane →ᵃ[ℝ] ℝ) (signs : A → J → Bool)
    (aligned : ∀ a z, z ∈ P.footprint a → ∀ j,
      0 ≤ AffineArrangement.signed (equations j) (signs a j) z)
    (cuts : Set Plane) (x : P.Cut cuts)
    (positive : ∀ j, 0 < equations j (Cap.horizontal (P.restoreCut cuts x).val)) :
    ∃ source : P.WindowCut signs cuts, P.windowCutMap signs cuts source = x ∧
      ∃ r : ℝ, 0 < r ∧ ∃ B : Metric.eball source (ENNReal.ofReal r) ≃ᵢ
        Metric.eball x (ENNReal.ofReal r), ∀ z, (B z).val = P.windowCutMap signs cuts z.val := by
  let S := P.cutPhysicalSeams cuts
  obtain ⟨a, represents⟩ := MetricGluing.point_surjective (fun a => P.spatialCell a) S.relation
    (P.cutIsometryEquiv cuts x)
  have physical : a.2.val = (P.restoreCut cuts x).val :=
    (congrArg S.fold represents).trans (P.fold_cutIsometryEquiv cuts x)
  have selected_at_point : ∀ c, a.2.val ∈ P.spatialCell c → WindowSelected signs c :=
    fun c member => P.windowSelected_of_spatial_mem equations signs aligned a.2.val
      (fun j => Eq.mpr (congrArg (fun p : Space =>
        0 < equations j (Cap.horizontal p)) physical) (positive j)) c member
  have chosen : WindowSelected signs a.1 := selected_at_point a.1 a.2.property
  let root : MetricGluing.Total
      (fun a : {a // WindowSelected signs a} => P.spatialCell a.val) := ⟨⟨a.1, chosen⟩, a.2⟩
  let source := MetricGluing.point
    (fun a : {a // WindowSelected signs a} => P.spatialCell a.val)
    (MetricGluing.cutSeams (fun a : {a // WindowSelected signs a} => P.spatialCell a.val)
      (fun a => P.isClosed_spatialCell a.val) (Cap.horizontal ⁻¹' cuts)).relation root
  have center : P.windowCutMap signs cuts source = x :=
    (congrArg (P.cutIsometryEquiv cuts).symm represents).trans
      ((P.cutIsometryEquiv cuts).symm_apply_apply x)
  obtain ⟨r, rpos, B, agrees⟩ := MetricGluing.exists_cutSubfamily_ball_chart_of_cells_at_point
    P.spatialCell P.isClosed_spatialCell (Cap.horizontal ⁻¹' cuts) (WindowSelected signs)
    root selected_at_point
  let move := basedEBallIsometry (P.cutIsometryEquiv cuts).symm
    (MetricGluing.point (fun a => P.spatialCell a) S.relation a) x center (ENNReal.ofReal r)
  refine ⟨source, center, r, rpos, B.trans move, ?_⟩
  intro z
  exact congrArg (P.cutIsometryEquiv cuts).symm (agrees z)

end Unfoldings.SpatialEnvelope.WholePartition
