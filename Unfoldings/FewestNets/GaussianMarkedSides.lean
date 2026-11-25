module

public import Unfoldings.FewestNets.NormalComponentCharges
public import Unfoldings.FewestNets.SingleCellCharge
public import Unfoldings.Polyhedron.GaussianTwoSideBound
public import Unfoldings.Polyhedron.SelectedComponentEuler

/-! Choose two actual marked seams at each vertex of the original mesh. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets.SingleCellCharge InnerProductGeometry MeasureTheory

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

private theorem labelCutDegree_normal (a : C.Vertex Set.univ) :
    labelCutDegree N.normal a = (gaussianArcSeams N a).card := by
  unfold labelCutDegree gaussianArcSeams
  congr 1
  ext s
  simp only [Finset.mem_filter]

include P in
/-- A vertex of the original closed triangulation has two distinct incident seams. -/
theorem two_le_incidentSeams_card (a : C.Vertex Set.univ) : 2 ≤ (incidentSeams a).card := by
  classical
  obtain ⟨p⟩ := C.nonempty_linkGerm Set.univ a
  let q := C.linkTurn Set.univ a p
  let s := P.germSeam p.val
  let t := P.germSeam q.val
  have distinct : s ≠ t := by
    intro same
    rcases P.eq_or_mate_of_germSeam_eq p q same with equal | equal
    · exact C.linkTurn_ne Set.univ a p equal.symm
    · obtain ⟨b, original⟩ := P.exists_germSeam_side p.val
      have crossing : C.GermCrosses Set.univ p.val
          (C.germOfEndpoint (C.seamSide s (!b)) (C.acrossEndpoint s b p.val.2)) :=
        ⟨s, Set.mem_univ _, b, p.val.2, original, rfl⟩
      have first := congrArg (fun z : C.Germ => z.1.1) original
      have paired := (C.mateGerm_of_crossing crossing).symm.trans
        (congrArg Subtype.val equal)
      have last := congrArg (fun z : C.Germ => z.1.1) paired
      change p.val.1.1 = (C.seamSide s b).face at first
      change (C.seamSide s (!b)).face = p.val.1.1 at last
      have same_face := last.trans first
      cases b
      · exact F.incident_faces_ne s same_face.symm
      · exact F.incident_faces_ne s same_face
  calc
    2 = ({s, t} : Finset C.Seam).card := (Finset.card_pair distinct).symm
    _ ≤ _ := Finset.card_le_card (by
      intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact P.germSeam_mem_incidentSeams p
      · rw [Finset.mem_singleton.mp he]
        exact P.germSeam_mem_incidentSeams q)

include P in
/-- All genuine seams at a flat or crease subdivision vertex fit among two marks. -/
theorem gaussianArcSeams_card_le_two_of_nonextreme (a : C.Vertex Set.univ)
    (outside : (F.gaussianSiteOfVertex a : Space) ∉ F.vertexHull.extremePoints ℝ) :
    (gaussianArcSeams N a).card ≤ 2 := by
  have zero := P.normal_labelCutDegree_charge_eq_zero_of_nonextreme N id a outside
  change componentCharge (labelCutDegree N.normal a) = 0 at zero
  rw [labelCutDegree_normal N] at zero
  unfold componentCharge at zero
  split at zero
  · omega
  · exact_mod_cast (show ((gaussianArcSeams N a).card : ℝ) ≤ 2 by linarith only [zero])

include P in
/-- The genuine normal polygon of an extreme vertex has at least two sides. -/
theorem two_le_gaussianArcSeams_card_of_extreme (a : C.Vertex Set.univ)
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ) :
    2 ≤ (gaussianArcSeams N a).card := by
  classical
  obtain ⟨n, c, closes, covers⟩ := P.exists_cyclic_link a
  obtain ⟨i, hi⟩ := P.nonempty_cyclicRunStarts_of_extreme N c covers extreme
  have some := (P.runStart_iff_genuine_seam N c closes i).mp hi
  have positive := Finset.card_pos.mpr ⟨_, some⟩
  have not_one := P.labelCutDegree_ne_one N.normal a
  rw [labelCutDegree_normal N] at not_one
  omega

/-- The endpoints used for the signed charge are the actual incident normals. -/
def seamMembership (N : F.SupportingNormals) (label : Space → Bool) (s : C.Seam) : Bool × Bool :=
  (label (N.normal (C.left s).face), label (N.normal (C.right s).face))

/-- The signed charge on an original vertex includes the full selected link. -/
def gaussianSignedCharge (N : F.SupportingNormals) (label : Space → Bool)
    (a : C.Vertex Set.univ) (first second : C.Seam) : ℝ := by
  classical
  let side := seamMembership N label
  exact charge (∑ s ∈ incidentSeams a, crossing (side s)) (side first) (side second)
    (decide (fullSelectedLink {f | label (N.normal f) = true} a))

open Classical in
/-- The pointwise upper bound only charges genuine changes outside the marks. -/
theorem gaussianSignedCharge_le_unmarked (label : Space → Bool) (a : C.Vertex Set.univ)
    {first second : C.Seam} (first_in : first ∈ incidentSeams a) (second_in : second ∈ incidentSeams a)
    (distinct : first ≠ second) :
    gaussianSignedCharge N label a first second ≤
      (∑ s ∈ gaussianArcSeams N a \ {first, second}, crossing (seamMembership N label s)) / 4 := by
  let side := seamMembership N label
  let cost := crossing ∘ side
  let incident := incidentSeams a
  let remaining := incident \ {first, second}
  let U : Set Face := {f | label (N.normal f) = true}
  have equality : (∑ s ∈ remaining, cost s) =
      ∑ s ∈ gaussianArcSeams N a \ {first, second}, cost s := by
    symm
    apply Finset.sum_subset
    · intro s hs
      obtain ⟨genuine, outside⟩ := Finset.mem_sdiff.mp hs
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp genuine).1, outside⟩
    · intro s hs outside
      obtain ⟨at_a, not_marked⟩ := Finset.mem_sdiff.mp hs
      have same : N.normal (C.left s).face = N.normal (C.right s).face := by
        by_contra diff
        exact outside (Finset.mem_sdiff.mpr
          ⟨Finset.mem_filter.mpr ⟨at_a, diff⟩, not_marked⟩)
      simp only [cost, Function.comp_apply, side, seamMembership, crossing, same, ite_true]
  change charge (∑ s ∈ incident, cost s) (side first) (side second)
      (decide (fullSelectedLink U a)) ≤
      (∑ s ∈ gaussianArcSeams N a \ {first, second}, cost s) / 4
  rw [← equality]
  have marks : {first, second} ⊆ incident := Finset.insert_subset_iff.mpr
    ⟨first_in, Finset.singleton_subset_iff.mpr second_in⟩
  have sum_marks : (∑ s ∈ ({first, second} : Finset C.Seam), cost s) = cost first + cost second := by
    rw [Finset.sum_pair distinct]
  have split := Finset.sum_sdiff (f := cost) marks
  change (∑ s ∈ remaining, cost s) + _ = _ at split
  rw [sum_marks, ← add_assoc] at split
  by_cases full : fullSelectedLink U a
  · have both (s : C.Seam) (hs : s ∈ incident) : side s = (true, true) :=
      Prod.ext (full s hs).1 (full s hs).2
    have zero : (∑ s ∈ incident, cost s) = 0 := Finset.sum_eq_zero fun s hs => by
      change crossing (side s) = 0
      rw [both s hs]
      rfl
    rw [zero, both first first_in, both second second_in, decide_eq_true full, charge_homogeneous]
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg
    intro s _
    simp only [cost, Function.comp_apply, crossing]
    split <;> norm_num
  · rw [decide_eq_false full, ← split]
    exact charge_le_unmarked _ _ _

open Classical in
include P in
/-- At a subdivision vertex the two chosen marks can cover all genuine
changes for every placement of the selector at once. -/
theorem exists_gaussian_marks_of_nonextreme (a : C.Vertex Set.univ)
    (outside : (F.gaussianSiteOfVertex a : Space) ∉ F.vertexHull.extremePoints ℝ) :
    ∃ first second : C.Seam, first ≠ second ∧ {first, second} ⊆ incidentSeams a ∧
      gaussianArcSeams N a ⊆ {first, second} := by
  obtain ⟨marks, cover, incident, size⟩ := Finset.exists_subsuperset_card_eq
    (Finset.filter_subset _ _) (P.gaussianArcSeams_card_le_two_of_nonextreme N a outside)
    (P.two_le_incidentSeams_card a)
  obtain ⟨first, second, distinct, rfl⟩ := Finset.card_eq_two.mp size
  exact ⟨first, second, distinct, incident, cover⟩

open Classical in
/-- Covering all genuine seams gives a nonpositive signed charge, including
the case where the two marked seams are distinct coplanar subdivisions. -/
theorem gaussianSignedCharge_nonpos_of_covered (label : Space → Bool) (a : C.Vertex Set.univ)
    {first second : C.Seam} (distinct : first ≠ second) (incident : {first, second} ⊆ incidentSeams a)
    (cover : gaussianArcSeams N a ⊆ {first, second}) :
    gaussianSignedCharge N label a first second ≤ 0 := by
  have bound := gaussianSignedCharge_le_unmarked N label a
    (incident (by simp : first ∈ ({first, second} : Finset C.Seam)))
    (incident (by simp : second ∈ ({first, second} : Finset C.Seam))) distinct
  simpa only [Finset.sdiff_eq_empty_iff_subset.mpr cover, Finset.sum_empty, zero_div] using bound

open Classical in
include P in
/-- The Gaussian perimeter estimate can always use two distinct actual
genuine marks while simultaneously controlling both diameter regimes. -/
theorem exists_gaussian_marks_of_extreme (a : C.Vertex Set.univ)
    (extreme : (F.gaussianSiteOfVertex a : Space) ∈ F.vertexHull.extremePoints ℝ)
    {eta : ℝ} (eta_pos : 0 < eta) (eta_small : eta ≤ Real.pi / 2)
    (min_angle : ∀ f i, eta ≤ (C.triangle f).cornerAngle i) :
    let cell := F.gaussianCell (F.gaussianSiteOfVertex a)
    let A := solidAngleMeasure.real cell
    ∃ (d : ℝ) (first second : C.Seam), 0 ≤ d ∧
      (∀ u ∈ cell, ∀ v ∈ cell, angle u v ≤ d) ∧
      first ≠ second ∧ {first, second} ⊆ gaussianArcSeams N a ∧
      let S := ∑ s ∈ gaussianArcSeams N a \ {first, second},
        angle (N.normal (C.left s).face) (N.normal (C.right s).face)
      S * d ≤ 8 / Real.sin eta * A ∧
      (d ≤ 1 → S * d ≤ 4 / (Real.cos (d / 2) ^ 2 * Real.sin eta) * A) := by
  obtain ⟨d, removed, nonneg, diameter, subset, few, big, small⟩ :=
    P.exists_omit_two_gaussian_sides_of_small_minimum N a extreme eta_pos eta_small min_angle
  obtain ⟨marks, includes, genuine, count⟩ :=
    Finset.exists_subsuperset_card_eq subset few (P.two_le_gaussianArcSeams_card_of_extreme N a extreme)
  obtain ⟨first, second, distinct, rfl⟩ := Finset.card_eq_two.mp count
  let side (s : C.Seam) := angle (N.normal (C.left s).face) (N.normal (C.right s).face)
  let S := ∑ s ∈ gaussianArcSeams N a \ {first, second}, side s
  let T := ∑ s ∈ gaussianArcSeams N a \ removed, side s
  have compare : S ≤ T := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.sdiff_subset_sdiff Finset.Subset.rfl includes) (fun s _ _ => angle_nonneg _ _)
  have sine : 0 < Real.sin eta :=
    Real.sin_pos_of_pos_of_lt_pi eta_pos (by linarith only [eta_small, Real.pi_pos])
  have compare' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right compare nonneg) sine.le
  refine ⟨d, first, second, nonneg, diameter, distinct, genuine, ?_, ?_⟩
  · change S * d ≤ _
    rw [div_mul_eq_mul_div, le_div_iff₀ sine]
    exact compare'.trans big
  · intro hd
    change S * d ≤ _
    have cosine : 0 < Real.cos (d / 2) := Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [nonneg, Real.pi_pos], by linarith only [hd, Real.pi_gt_three]⟩
    rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos (pow_pos cosine _) sine)]
    calc
      _ = Real.cos (d / 2) ^ 2 * (S * d * Real.sin eta) := by ring
      _ ≤ Real.cos (d / 2) ^ 2 * (T * d * Real.sin eta) :=
        mul_le_mul_of_nonneg_left compare' (sq_nonneg _)
      _ ≤ _ := small hd

end Unfoldings.SpatialFolding.ConvexBoundary
