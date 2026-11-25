module

public import Unfoldings.FewestNets.GaussianMarkedSides
public import Unfoldings.FewestNets.SingleCellComponents
public import Unfoldings.FewestNets.OrthogonalSiteFlags
public import Unfoldings.Geometry.SphericalRotation
public import Unfoldings.Polyhedron.LabeledSelectionCount

/-! The signed Gaussian charges give the exact expected component count. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SpatialFolding.ConvexBoundary

open FewestNets.SingleCellCharge SpatialRotation MeasureTheory InnerProductGeometry

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}
  {F : SpatialFolding C} (P : F.ConvexBoundary) (N : F.SupportingNormals)

/-- The original triangle components whose normals, in the placed frame,
fall in one spherical selector. -/
def gaussianSelectedCount (N : F.SupportingNormals) (region : Set Space)
    (reversed : Bool) (g : SpatialRotation) : ℝ :=
  Nat.card (C.SelectedComponents {f | siteFlag region reversed (N.normal f) g = true})

open Classical in
private def fullFlag (N : F.SupportingNormals) (region : Set Space) (reversed : Bool)
    (g : SpatialRotation) (a : C.Vertex Set.univ) : Bool :=
  decide (fullSelectedLink {f | siteFlag region reversed (N.normal f) g = true} a)

private theorem indicator_eq_decide (x : Bool) :
    membershipValue x = (if x = true then (1 : ℝ) else 0) := by
  cases x <;> rfl

private theorem card_filter_eq_sum_membership {ι : Type*} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (flag : ι → Bool) (correct : ∀ i, flag i = true ↔ p i) :
    ((Finset.univ.filter p).card : ℝ) = ∑ i, membershipValue (flag i) := by
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i _
  by_cases member : p i <;> simp [indicator_eq_decide, correct i, member]

private theorem measurableSet_bool_and {X : Type*} [MeasurableSpace X] {a b : X → Bool}
    (left : MeasurableSet {x | a x = true}) (right : MeasurableSet {x | b x = true}) :
    MeasurableSet {x | (a x && b x) = true} := by
  convert left.inter right using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Bool.and_eq_true]

open Classical in
include P in
private theorem gaussianSelectedCount_eq_euler (region : Set Space) (convex : SphericalConvex region)
    (closed : IsClosed region) (q : Space) (unit : ‖q‖ = 1)
    (hemisphere : ∀ n ∈ region, 0 < inner ℝ q n) (reversed : Bool) (g : SpatialRotation) :
    let inside (f : Face) := siteFlag region reversed (N.normal f) g
    gaussianSelectedCount N region reversed g =
      (∑ f : Face, membershipValue (inside f)) -
        (∑ s : C.Seam, membershipValue (inside (C.left s).face && inside (C.right s).face)) +
        ∑ a : C.Vertex Set.univ, membershipValue (fullFlag N region reversed g a) := by
  let T := orthogonalIsometry g reversed
  let K := T.symm '' region
  have mem (x : Space) : x ∈ K ↔ T x ∈ region := by
    constructor
    · rintro ⟨y, inside, rfl⟩
      rwa [T.apply_symm_apply]
    · exact fun inside => ⟨T x, inside, T.symm_apply_apply x⟩
  have K_closed : IsClosed K := T.symm.toHomeomorph.isClosedMap _ closed
  have K_up (n : Space) (hn : n ∈ K) : 0 < inner ℝ (T.symm q) n := by
    rw [← T.inner_map_map, T.apply_symm_apply]
    exact hemisphere _ ((mem _).mp hn)
  have flags (f : Face) : N.normal f ∈ K ↔ siteFlag region reversed (N.normal f) g = true := by
    rw [mem, orthogonalIsometry_apply, siteFlag_eq_true_iff]
  have selected : {f | N.normal f ∈ K} = {f | siteFlag region reversed (N.normal f) g = true} :=
    Set.ext flags
  have euler := P.normal_cell_components_eq_euler N (T.symm q) (by rwa [T.symm.norm_map])
    K (convex.image T.symm) K_closed K_up
  dsimp only at euler
  change (Nat.card (C.SelectedComponents {f | N.normal f ∈ K}) : ℤ) = _ at euler
  have real_euler := congrArg (fun z : ℤ => (z : ℝ)) euler
  simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast] at real_euler
  let inside (f : Face) := siteFlag region reversed (N.normal f) g
  let U : Set Face := {f | N.normal f ∈ K}
  change (Nat.card (C.SelectedComponents {f | inside f = true}) : ℝ) = _
  rw [← selected]
  have left (f : Face) : inside f = true ↔ f ∈ U := (flags f).symm
  have faces := card_filter_eq_sum_membership (· ∈ U) inside left
  have seams := card_filter_eq_sum_membership
    (fun s : C.Seam => (C.left s).face ∈ U ∧ (C.right s).face ∈ U)
    (fun s => inside (C.left s).face && inside (C.right s).face)
    (fun s => by simp only [Bool.and_eq_true, left])
  have vertices := card_filter_eq_sum_membership (fullSelectedLink U)
    (fullFlag N region reversed g) (fun a => by
      change decide (fullSelectedLink {f | inside f = true} a) = true ↔ _
      rw [decide_eq_true_eq]
      change fullSelectedLink _ _ ↔ fullSelectedLink {f | N.normal f ∈ K} _
      rw [selected])
  change (Nat.card (C.SelectedComponents U) : ℝ) = _ at real_euler
  exact real_euler.trans (by rw [faces, seams, vertices])

private theorem measurable_fullFlag {region : Set Space} (measurable : MeasurableSet region)
    (reversed : Bool) (a : C.Vertex Set.univ) :
    MeasurableSet {g | fullFlag N region reversed g a = true} := by
  classical
  have eq : {g | fullFlag N region reversed g a = true} =
      ⋂ s : ↑(incidentSeams a), {g | siteFlag region reversed (N.normal (C.left s.val).face) g = true} ∩
        {g | siteFlag region reversed (N.normal (C.right s.val).face) g = true} := by
    ext g
    simp only [Set.mem_ofPred_eq, fullFlag, fullSelectedLink,
      Set.mem_iInter, Set.mem_inter_iff, Subtype.forall]
    let p := fullSelectedLink {f | siteFlag region reversed (N.normal f) g = true} a
    change @decide p (Classical.propDecidable p) = true ↔ p
    exact Iff.of_eq (@decide_eq_true_eq p (Classical.propDecidable p))
  rw [eq]
  exact MeasurableSet.iInter fun s => (measurableSet_siteFlag measurable reversed _).inter
    (measurableSet_siteFlag measurable reversed _)

/-- The signed charge is integrable for every fixed choice of the marked seams. -/
theorem integrable_gaussianSignedCharge {region : Set Space} (measurable : MeasurableSet region)
    (reversed : Bool) (a : C.Vertex Set.univ) (first second : C.Seam) :
    Integrable (fun g => gaussianSignedCharge N (fun x => siteFlag region reversed x g)
      a first second) probability := by
  let flag (f : Face) (g : SpatialRotation) := siteFlag region reversed (N.normal f) g
  have measurable_flag (f : Face) : MeasurableSet {g | flag f g = true} :=
    measurableSet_siteFlag measurable reversed _
  have both_integrable (s : C.Seam) : Integrable
      (fun g => membershipValue (flag (C.left s).face g && flag (C.right s).face g)) probability := by
    apply integrable_membershipValue
    exact measurableSet_bool_and (measurable_flag (C.left s).face)
      (measurable_flag (C.right s).face)
  have ends (s : C.Seam) : Integrable
      (fun g => endpoints (flag (C.left s).face g, flag (C.right s).face g)) probability :=
    (integrable_membershipValue _ (measurable_flag (C.left s).face)).add
      (integrable_membershipValue _ (measurable_flag (C.right s).face))
  have crossing_formula (a b : Bool) :
      crossing (a, b) = endpoints (a, b) - 2 * membershipValue (a && b) := by
    cases a <;> cases b <;> norm_num [crossing, endpoints, membershipValue]
  have cross (s : C.Seam) : Integrable
      (fun g => crossing (flag (C.left s).face g, flag (C.right s).face g)) probability := by
    simp only [crossing_formula]
    exact (ends s).sub ((both_integrable s).const_mul 2)
  have changes : Integrable (fun g => ∑ s ∈ incidentSeams a,
      crossing (flag (C.left s).face g, flag (C.right s).face g)) probability :=
    integrable_finsetSum _ fun s _ => cross s
  change Integrable (fun g => ((∑ s ∈ incidentSeams a,
      crossing (flag (C.left s).face g, flag (C.right s).face g)) -
        endpoints (flag (C.left first).face g, flag (C.right first).face g) -
        endpoints (flag (C.left second).face g, flag (C.right second).face g)) / 4 +
        membershipValue (fullFlag N region reversed g a)) probability
  exact (((changes.sub (ends first)).sub (ends second)).div_const 4).add
    (integrable_membershipValue _ (measurable_fullFlag N measurable reversed a))

open Classical in
include P in
/-- Each orientation class has the same linear area term. Its remaining
expected component count is exactly the sum of the signed charges. -/
theorem integral_gaussianSelectedCount_eq (region : Set Space) (convex : SphericalConvex region)
    (closed : IsClosed region) (q : Space) (unit : ‖q‖ = 1)
    (hemisphere : ∀ n ∈ region, 0 < inner ℝ q n)
    (reversed : Bool) (first second : C.Vertex Set.univ → C.Seam) :
    (∫ g, gaussianSelectedCount N region reversed g ∂probability) =
      2 * uniformSphere.real region +
        ∑ a : C.Vertex Set.univ, ∫ g, gaussianSignedCharge N
          (fun x => siteFlag region reversed x g) a (first a) (second a) ∂probability := by
  let flag (g : SpatialRotation) (f : Face) := siteFlag region reversed (N.normal f) g
  have twice (s : C.Seam) :
      (Finset.univ.filter fun a : C.Vertex Set.univ => s ∈ incidentSeams a).card = 2 := by
    have endpoints :
        (Finset.univ.filter fun a : C.Vertex Set.univ => s ∈ incidentSeams a) =
          {C.seamVertex s false, C.seamVertex s true} := by
      ext a
      simp [incidentSeams]
    rw [endpoints, Finset.card_pair]
    exact fun h => gaussianSiteOfVertex_seam_ne (F := F) s
      (congrArg (fun a => (F.gaussianSiteOfVertex a : Space)) h)
  simp_rw [P.gaussianSelectedCount_eq_euler N region convex closed q unit hemisphere reversed]
  have estimate := integral_binary_euler_of_equal_marginals (μ := probability)
    (fun s : C.Seam => (C.left s).face) (fun s => (C.right s).face) incidentSeams first second twice
    flag (fun g => fullFlag N region reversed g) (uniformSphere.real region)
    (fun f => measurableSet_siteFlag closed.measurableSet reversed (N.normal f))
    (fun f => integral_siteFlag closed.measurableSet reversed (N.unit f))
    (fun a => integrable_gaussianSignedCharge N closed.measurableSet reversed a (first a) (second a))
  have euler : (Fintype.card Face : ℝ) - Fintype.card C.Seam +
      Fintype.card (C.Vertex Set.univ) = 2 := by
    have real_euler : (Fintype.card (C.Vertex Set.univ) : ℝ) - Fintype.card C.Seam +
        Fintype.card Face = 2 := by exact_mod_cast P.triangulation_euler
    linarith only [real_euler]
  rw [euler] at estimate
  exact estimate

open Classical in
include P in
/-- The count itself is integrable in each orientation class. -/
theorem integrable_gaussianSelectedCount (region : Set Space) (convex : SphericalConvex region)
    (closed : IsClosed region) (q : Space) (unit : ‖q‖ = 1)
    (hemisphere : ∀ n ∈ region, 0 < inner ℝ q n) (reversed : Bool) :
    Integrable (gaussianSelectedCount N region reversed) probability := by
  let flag (f : Face) (g : SpatialRotation) := siteFlag region reversed (N.normal f) g
  have face (f : Face) : Integrable (fun g => membershipValue (flag f g)) probability :=
    integrable_membershipValue _ (measurableSet_siteFlag closed.measurableSet reversed _)
  have edge (s : C.Seam) : Integrable (fun g =>
      membershipValue (flag (C.left s).face g && flag (C.right s).face g)) probability := by
    apply integrable_membershipValue
    exact measurableSet_bool_and
      (measurableSet_siteFlag closed.measurableSet reversed (N.normal (C.left s).face))
      (measurableSet_siteFlag closed.measurableSet reversed (N.normal (C.right s).face))
  have full (a : C.Vertex Set.univ) :
      Integrable (fun g => membershipValue (fullFlag N region reversed g a)) probability :=
    integrable_membershipValue _ (measurable_fullFlag N closed.measurableSet reversed a)
  have eq : gaussianSelectedCount N region reversed = fun g =>
      (∑ f, membershipValue (flag f g)) -
        (∑ s : C.Seam, membershipValue (flag (C.left s).face g && flag (C.right s).face g)) +
        ∑ a, membershipValue (fullFlag N region reversed g a) :=
    funext (P.gaussianSelectedCount_eq_euler N region convex closed q unit hemisphere reversed)
  rw [eq]
  exact ((integrable_finsetSum _ (fun f _ => face f)).sub
    (integrable_finsetSum _ (fun s _ => edge s))).add (integrable_finsetSum _ (fun a _ => full a))

include P in
/-- The Gaussian areas indexed by the original vertices sum to the full sphere. -/
theorem sum_original_gaussianCellArea :
    (∑ a : C.Vertex Set.univ,
      solidAngleMeasure.real (F.gaussianCell (F.gaussianSiteOfVertex a))) = 4 * Real.pi := by
  have area := (Equiv.sum_comp P.vertexEquivGaussianSite
    (fun i => (solidAngleMeasure (F.gaussianCone i)).toReal)).trans (F.sum_gaussianArea P)
  change (∑ a : C.Vertex Set.univ,
    (solidAngleMeasure (F.gaussianCone (F.gaussianSiteOfVertex a))).toReal) = _ at area
  simpa only [Measure.real, F.solidAngle_gaussianCell] using area

end Unfoldings.SpatialFolding.ConvexBoundary
