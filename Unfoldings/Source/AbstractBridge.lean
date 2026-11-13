module

public import Unfoldings.Source.Unfolding
public import Unfoldings.Cap.AbstractBridge

/-! Proof translations for the independent source-unfolding abstract. -/

@[expose] public section

noncomputable section

namespace Unfoldings.SourceAbstractBridge

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face}

/-- The intrinsic gluing metric is the greatest extended pseudometric bounded by
Euclidean distance on each face. This characterizes it without a route representation. -/
theorem maximal_edist (x y : C.SeamQuotient Set.univ) :
    (⨆ d : C.SeamQuotient Set.univ → C.SeamQuotient Set.univ → ENNReal,
      ⨆ (_ : (∀ a, d a a = 0) ∧ (∀ a b, d a b = d b a) ∧
        (∀ a b c, d a c ≤ d a b + d b c) ∧
        (∀ f (a b : C.Cell f),
          d (MetricGluing.seamPoint C.Cell (C.glue Set.univ) ⟨f, a⟩)
            (MetricGluing.seamPoint C.Cell (C.glue Set.univ) ⟨f, b⟩) ≤ edist a b)), d x y) =
      edist (C.realizationHomeomorph Set.univ x) (C.realizationHomeomorph Set.univ y) := by
  let H := C.realizationHomeomorph Set.univ
  apply le_antisymm
  · refine iSup_le fun d => iSup_le fun admissible => ?_
    obtain ⟨a, rfl⟩ := Quot.exists_rep x
    obtain ⟨b, rfl⟩ := Quot.exists_rep y
    apply Route.le_distance (MetricGluing.stepCost C.Cell (C.glue Set.univ))
      (fun a b => d (MetricGluing.seamPoint C.Cell (C.glue Set.univ) a)
        (MetricGluing.seamPoint C.Cell (C.glue Set.univ) b))
      (fun a => admissible.1 _) (fun a b c => admissible.2.2.1 _ _ _) ?_ a b
    intro a b
    classical
    by_cases joined : C.glue Set.univ a b ∨ C.glue Set.univ b a
    · have equal : MetricGluing.seamPoint C.Cell (C.glue Set.univ) a =
          MetricGluing.seamPoint C.Cell (C.glue Set.univ) b := by
        rcases joined with h | h
        · exact Quot.sound h
        · exact (Quot.sound h).symm
      simp only [MetricGluing.stepCost, ite_eq_left joined, equal, admissible.1, le_refl]
    · obtain ⟨f, a⟩ := a
      obtain ⟨g, b⟩ := b
      by_cases same : f = g
      · subst g
        simpa [MetricGluing.stepCost, joined, MetricGluing.faceCost] using
          admissible.2.2.2 f a b
      · simp only [MetricGluing.stepCost, ite_eq_right joined, MetricGluing.faceCost,
          dite_eq_right same, le_top]
  · let d (a b : C.SeamQuotient Set.univ) := edist (H a) (H b)
    apply le_iSup_of_le d
    apply le_iSup_of_le
      (show (∀ a, d a a = 0) ∧ (∀ a b, d a b = d b a) ∧
        (∀ a b c, d a c ≤ d a b + d b c) ∧
        (∀ f (a b : C.Cell f),
          d (MetricGluing.seamPoint C.Cell (C.glue Set.univ) ⟨f, a⟩)
            (MetricGluing.seamPoint C.Cell (C.glue Set.univ) ⟨f, b⟩) ≤ edist a b) from
        ⟨fun _ => edist_self _, fun _ _ => edist_comm _ _,
          fun _ _ _ => edist_triangle _ _ _, fun f a b =>
            MetricGluing.edist_of_le C.Cell (C.glue Set.univ) f a b⟩)
    exact le_rfl

/-- Change a quotient relation by a proved equality, preserving the original quotient topology. -/
def quotientHomeomorph {X : Type*} [TopologicalSpace X] {R S : X → X → Prop}
    (equal : R = S) : Quot R ≃ₜ Quot S := by
  subst S
  exact Homeomorph.refl _

@[simp] theorem quotientHomeomorph_mk {X : Type*} [TopologicalSpace X]
    {R S : X → X → Prop} (equal : R = S) (x : X) :
    quotientHomeomorph equal (Quot.mk R x) = Quot.mk S x := by
  subst S
  rfl

/-- The public statement expands this predicate using only its independent distance. -/
def Shortest {X : Type*} [TopologicalSpace X] (d : X → X → ENNReal)
    {a b : X} (p : Path a b) : Prop :=
  ∀ s t : unitInterval, d (p s) (p t) = d a b * edist s t

def cutLocus {X : Type*} [TopologicalSpace X] (d : X → X → ENNReal)
    (source : X) : Set X :=
  closure {x | ∃ p q : Path source x, Shortest d p ∧ Shortest d q ∧ p ≠ q}

def Polygon (s : Set Plane) : Prop :=
  IsCompact s ∧ (interior s).Nonempty ∧
    ∃ n : ℕ, ∃ halfplane : Fin n → Plane →ᵃ[ℝ] ℝ,
      s = {x | ∀ i, 0 ≤ halfplane i x}

/-- Internal transfer data; the public abstract has its own geometric definitions. -/
structure NetData (X : Type*) [TopologicalSpace X] (d : X → X → ENNReal)
    (point : ∀ f, C.Cell f → X) (source : X) where
  region : Set Plane
  zero_interior : (0 : Plane) ∈ interior region
  disk : Nonempty (region ≃ₜ Metric.closedBall (0 : Plane) 1)
  fold : region → X
  continuous_fold : Continuous fold
  surjective_fold : Function.Surjective fold
  radial : ∀ (z : region) (t : unitInterval), (t : ℝ) • z.val ∈ region
  source_image : fold ⟨0, interior_subset zero_interior⟩ = source
  pieces : ∃ n : ℕ, ∃ piece : Fin n → Set Plane,
    (∀ i, Polygon (piece i)) ∧
    Pairwise (fun i j => Disjoint (interior (piece i)) (interior (piece j))) ∧
    (⋃ i, piece i) = region ∧
    ∃ face : Fin n → Face, ∃ motion : Fin n → Plane ≃ᵃⁱ[ℝ] Plane,
      ∀ i (x : piece i), ∃ h : motion i x.val ∈ (C.triangle (face i)).carrier,
        ∃ hz : x.val ∈ region, fold ⟨x.val, hz⟩ = point (face i) ⟨motion i x.val, h⟩
  polygonal_boundary : ∃ n : ℕ, ∃ a b : Fin n → Plane,
    frontier region = ⋃ i, segment ℝ (a i) (b i)
  cut_complement : ∃ H : interior region ≃ₜ ↥((cutLocus d source)ᶜ),
    ∀ z, (H z).val = fold ⟨z.val, interior_subset z.property⟩
  local_isometry : ∀ x : interior region,
    ∃ T : Set (interior region), IsOpen T ∧ x ∈ T ∧
      ∀ y z : T, d (fold ⟨y.val.val, interior_subset y.val.property⟩)
        (fold ⟨z.val.val, interior_subset z.val.property⟩) = edist y.val.val z.val.val
  boundary_projection : fold '' {z : region | z.val ∈ frontier region} = cutLocus d source
  source_distance : ∀ z : region, d source (fold z) = ENNReal.ofReal ‖z.val‖
  radial_geodesic : ∀ (z : region) (s t : unitInterval),
    d (fold ⟨(s : ℝ) • z.val, radial z s⟩)
      (fold ⟨(t : ℝ) • z.val, radial z t⟩) = ENNReal.ofReal ‖z.val‖ * edist s t
  all_shortest_paths : ∀ x (p : Path source x), Shortest d p →
    ∃! z : region, ∀ t : unitInterval, fold ⟨(t : ℝ) • z.val, radial z t⟩ = p t

theorem maximal_edist_of_glue_eq (R : C.Total → C.Total → Prop)
    (equal : R = C.glue Set.univ) (x y : Quot R) :
    (⨆ d : Quot R → Quot R → ENNReal,
      ⨆ (_ : (∀ a, d a a = 0) ∧ (∀ a b, d a b = d b a) ∧
        (∀ a b c, d a c ≤ d a b + d b c) ∧
        (∀ f (a b : C.Cell f), d (Quot.mk R ⟨f, a⟩) (Quot.mk R ⟨f, b⟩) ≤ edist a b)),
      d x y) =
      edist ((C.realizationHomeomorph Set.univ) (quotientHomeomorph equal x))
        ((C.realizationHomeomorph Set.univ) (quotientHomeomorph equal y)) := by
  subst R
  exact maximal_edist x y

/-- Transport normalized paths without changing their parameters. -/
def pathEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) (a b : X) : Path a b ≃ Path (H a) (H b) where
  toFun p := p.map H.continuous
  invFun p := (p.map H.symm.continuous).cast
    (H.symm_apply_apply a).symm (H.symm_apply_apply b).symm
  left_inv p := by ext t; exact H.symm_apply_apply (p t)
  right_inv p := by ext t; exact H.apply_symm_apply (p t)

theorem shortest_iff {X Y : Type*} [TopologicalSpace X] [PseudoEMetricSpace Y]
    (d : X → X → ENNReal) (H : X ≃ₜ Y)
    (distance : ∀ a b, d a b = edist (H a) (H b)) {a b : X} (p : Path a b) :
    Shortest d p ↔ (pathEquiv H a b p).IsGeodesic := by
  simp only [Shortest, Path.IsGeodesic, distance]
  rfl

theorem cutLocus_eq_preimage {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (d : X → X → ENNReal) (H : X ≃ₜ Y)
    (distance : ∀ a b, d a b = edist (H a) (H b)) (source : X) :
    cutLocus d source = H ⁻¹' sourceCutLocus (H source) := by
  rw [cutLocus, sourceCutLocus, H.preimage_closure]
  congr 1
  ext x
  change (∃ p q : Path source x, Shortest d p ∧ Shortest d q ∧ p ≠ q) ↔
    ∃ p q : Path (H source) (H x), p.IsGeodesic ∧ q.IsGeodesic ∧ p ≠ q
  let E := pathEquiv H source x
  constructor
  · rintro ⟨p, q, hp, hq, different⟩
    exact ⟨E p, E q, (shortest_iff d H distance p).mp hp,
      (shortest_iff d H distance q).mp hq, fun equal => different (E.injective equal)⟩
  · rintro ⟨p, q, hp, hq, different⟩
    refine ⟨E.symm p, E.symm q, ?_, ?_, fun equal => different (E.symm.injective equal)⟩
    · apply (shortest_iff d H distance _).mpr
      change (E (E.symm p)).IsGeodesic
      simpa only [E.apply_symm_apply] using hp
    · apply (shortest_iff d H distance _).mpr
      change (E (E.symm q)).IsGeodesic
      simpa only [E.apply_symm_apply] using hq

/-- A layout's finite halfplane specification is an ordinary finite polygon description. -/
theorem layout_polygon {Piece : Type*} (D : FacePolygonalLayout C Piece) (i : Piece) :
    Polygon (D.region i) := by
  classical
  let := (D.finite_halfplanes i).fintype
  let e := Fintype.equivFin (D.halfplanes i)
  refine ⟨D.compact_region i, D.interior_nonempty i,
    Fintype.card (D.halfplanes i), fun j => (e.symm j).val, ?_⟩
  rw [D.region_eq i]
  ext x
  constructor
  · intro h j
    exact h (e.symm j).val (e.symm j).property
  · intro h l member
    simpa only [e.symm_apply_apply] using h (e ⟨l, member⟩)

/-- Transfer the constructed net through a homeomorphism that preserves the intrinsic distance. -/
def source_net (F : SpatialFolding C) (P : F.ConvexBoundary)
    {X : Type*} [TopologicalSpace X] (d : X → X → ENNReal)
    (H : X ≃ₜ C.Realization Set.univ)
    (distance : ∀ a b, d a b = edist (H a) (H b))
    (point : ∀ f, C.Cell f → X)
    (point_eq : ∀ f x, H (point f x) = C.faceMap Set.univ f x)
    (source : X) (outside : F.toSpace Set.univ (H source) ∉ F.vertexHull.extremePoints ℝ) :
    NetData (C := C) X d point source := by
  classical
  let := P.metricSpace
  let U := P.sourceUnfoldingOfNonextreme (H source) outside
  let R := U.frame
  let injective := U.coordinate_injective
  let A := R.coordinateHomeomorph injective
  let project := R.projection injective
  let fold : R.domain → X := fun z => H.symm (project z)
  have Hfold (z : R.domain) : H (fold z) = project z := H.apply_symm_apply _
  have coordinate (z : R.domain) : R.coordinate (A.symm z).path (A.symm z).geodesic = z.val :=
    congrArg Subtype.val (A.apply_symm_apply z)
  have radial (z : R.domain) (t : unitInterval) : (t : ℝ) • z.val ∈ R.domain :=
    R.starConvex_domain.smul_mem z.property t.property.1 t.property.2
  have tracks (z : R.domain) (t : unitInterval) :
      project ⟨(t : ℝ) • z.val, radial z t⟩ = (A.symm z).path t := by
    have equal : A ((A.symm z).initial t) = ⟨(t : ℝ) • z.val, radial z t⟩ := by
      apply Subtype.ext
      exact (R.coordinate_initial (A.symm z) t).trans (congrArg (fun x => (t : ℝ) • x)
        (coordinate z))
    rw [← equal]
    exact R.projection_coordinateHomeomorph injective ((A.symm z).initial t)
  have radius (z : R.domain) : d source (fold z) = ENNReal.ofReal ‖z.val‖ := by
    rw [distance, Hfold, edist_dist, ← R.norm_eq_projection_distance injective z]
  have zero : (0 : Plane) ∈ interior R.domain := by
    simpa only [Set.Icc.coe_zero, zero_smul] using
      P.sourceDomain_radial_interior R R.zero_mem_domain 0 zero_lt_one
  have cut := cutLocus_eq_preimage d H distance source
  refine
    { region := R.domain
      zero_interior := zero
      disk := ⟨P.sourceDomainDiskHomeomorph R⟩
      fold := fold
      continuous_fold := H.symm.continuous.comp (R.continuous_projection injective)
      surjective_fold := H.symm.surjective.comp (R.projection_surjective injective
        (P.sourcePath_target_surjective (H source)))
      radial := radial
      source_image := ?_
      pieces := ?_
      polygonal_boundary := ?_
      cut_complement := ?_
      local_isometry := ?_
      boundary_projection := ?_
      source_distance := radius
      radial_geodesic := ?_
      all_shortest_paths := ?_ }
  · apply H.injective
    apply (edist_eq_zero.mp ?_).symm
    rw [← distance, radius]
    simp
  · let := U.finite_pieces
    let e := Fintype.equivFin U.Piece
    refine ⟨Fintype.card U.Piece, fun i => U.layout.region (e.symm i),
      fun i => layout_polygon U.layout (e.symm i), ?_, ?_,
      fun i => U.layout.face (e.symm i), fun i => U.layout.foldPlacement (e.symm i), ?_⟩
    · intro i j different
      exact U.nonoverlapping (fun same => different (e.symm.injective same))
    · rw [← U.footprint]
      ext x
      constructor
      · intro member
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
        exact Set.mem_iUnion.mpr ⟨e.symm i, hi⟩
      · intro member
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
        exact Set.mem_iUnion.mpr ⟨e i, (e.symm_apply_apply i).symm ▸ hi⟩
    · intro i x
      let j := e.symm i
      have in_face := U.layout.in_face j x.val x.property
      obtain ⟨z, equal, image⟩ := U.folding j x
      refine ⟨in_face, equal ▸ z.property, ?_⟩
      apply H.injective
      rw [Hfold, point_eq]
      change project _ = U.layout.fold Set.univ j x
      exact (congrArg project (Subtype.ext equal.symm)).trans image
  · let := U.finite_boundary_edges.fintype
    let e := Fintype.equivFin U.boundary_edges
    refine ⟨Fintype.card U.boundary_edges, fun i => (e.symm i).val.1,
      fun i => (e.symm i).val.2, ?_⟩
    rw [U.boundary_segments]
    ext x
    constructor
    · intro member
      obtain ⟨edge, member, hx⟩ := Set.mem_iUnion₂.mp member
      exact Set.mem_iUnion.mpr ⟨e ⟨edge, member⟩, by
        simpa only [e.symm_apply_apply] using hx⟩
    · intro member
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp member
      exact Set.mem_iUnion₂.mpr ⟨(e.symm i).val, (e.symm i).property, hi⟩
  · let B := H.subtype (p := fun x => x ∉ cutLocus d source)
      (q := fun x => x ∉ sourceCutLocus (H source)) (by intro x; rw [cut]; rfl)
    let V := U.cutComplement.trans (PolygonalPoint.openHomeomorph isOpen_interior)
    refine ⟨V.symm.trans B.symm, ?_⟩
    intro z
    apply H.injective
    have inverse := congrArg Subtype.val (B.apply_symm_apply (V.symm z))
    change H (B.symm (V.symm z)).val = (V.symm z).val at inverse
    change H (B.symm (V.symm z)).val = H (fold _)
    rw [inverse, Hfold]
    exact (U.interior_projection
      ((PolygonalPoint.openHomeomorph isOpen_interior).symm z)).symm
  · intro x
    obtain ⟨T, open_T, member, isometric⟩ := P.sourceInterior_inverse_local_isometry R x
    refine ⟨T, open_T, member, ?_⟩
    intro y z
    rw [distance, Hfold, Hfold]
    exact isometric y z
  · rw [cut]
    ext x
    constructor
    · rintro ⟨z, boundary, equal⟩
      have member : project z ∈ sourceCutLocus (H source) := by
        rw [← U.boundary_projection]
        exact ⟨PolygonalPoint.ofSubtype z, boundary, rfl⟩
      change H x ∈ sourceCutLocus (H source)
      rwa [← equal, Hfold]
    · intro member
      obtain ⟨z, boundary, equal⟩ := U.boundary_projection.symm ▸ member
      refine ⟨PolygonalPoint.toSubtype z, boundary, ?_⟩
      apply H.injective
      exact (Hfold _).trans equal
  · intro z s t
    rw [distance, Hfold, Hfold, tracks z s, tracks z t, (A.symm z).geodesic s t]
    rw [edist_dist, ← R.norm_coordinate (A.symm z).path (A.symm z).geodesic, coordinate z]
  · intro x p shortest
    let q := pathEquiv H source x p
    have geodesic := (shortest_iff d H distance p).mp shortest
    let path : SourcePath (H source) := ⟨H x, q, geodesic⟩
    refine ⟨A path, ?_, ?_⟩
    · intro t
      apply H.injective
      rw [Hfold, tracks]
      exact congrArg (fun p : SourcePath (H source) => p.path t) (A.symm_apply_apply path)
    · intro z same
      have paths : A.symm z = path := by
        apply SourcePath.ext
        intro t
        exact (tracks z t).symm.trans ((Hfold _).symm.trans (congrArg H (same t)))
      exact (A.apply_symm_apply z).symm.trans (congrArg A paths)

/-- The same face-bound characterization, on a quotient whose relation is supplied explicitly. -/
def intrinsicDistance (R : C.Total → C.Total → Prop) (x y : Quot R) : ENNReal :=
  ⨆ d : Quot R → Quot R → ENNReal,
    ⨆ (_ : (∀ a, d a a = 0) ∧ (∀ a b, d a b = d b a) ∧
      (∀ a b c, d a c ≤ d a b + d b c) ∧
      (∀ f (a b : C.Cell f), d (Quot.mk R ⟨f, a⟩) (Quot.mk R ⟨f, b⟩) ≤ edist a b)),
    d x y

/-- Raw embedding and convex-hull boundary data suffice; no unfolding data are input. -/
def geometric_source_net (F : SpatialFolding C) (R : C.Total → C.Total → Prop)
    (relation : R = fun p q => ∃ s x, p = C.edgePoint (C.left s) x ∧
      q = C.edgePoint (C.right s) (C.identify s x))
    (embedded : ∀ p q : C.Total, F.place p.1 p.2.val = F.place q.1 q.2.val →
      Relation.EqvGen R p q)
    (interior_nonempty : (interior F.vertexHull).Nonempty)
    (boundary : F.surface = frontier F.vertexHull) (source : C.Total)
    (nonextreme : F.place source.1 source.2.val ∉ F.vertexHull.extremePoints ℝ) :
    NetData (C := C) (Quot R) (intrinsicDistance R)
      (fun f x => Quot.mk R ⟨f, x⟩) (Quot.mk R source) := by
  have glue : R = C.glue Set.univ := by
    rw [relation]
    funext p q
    apply propext
    simp only [TriangleComplex.glue, Set.mem_univ, true_and]
    rfl
  let H := (quotientHomeomorph glue).trans (C.realizationHomeomorph Set.univ)
  have point_eq (f : Face) (x : C.Cell f) :
      H (Quot.mk R ⟨f, x⟩) = C.faceMap Set.univ f x := by
    change C.realizationHomeomorph Set.univ (quotientHomeomorph glue (Quot.mk R ⟨f, x⟩)) = _
    rw [quotientHomeomorph_mk]
    rfl
  have distance (x y : Quot R) : intrinsicDistance R x y = edist (H x) (H y) :=
    maximal_edist_of_glue_eq R glue x y
  have P : F.ConvexBoundary :=
    { embedded := F.isEmbedded_iff.mpr (by
        intro p q same
        rw [← glue]
        exact embedded p q same)
      interior_nonempty := interior_nonempty
      boundary := boundary }
  have outside : F.toSpace Set.univ (H (Quot.mk R source)) ∉ F.vertexHull.extremePoints ℝ := by
    obtain ⟨f, x⟩ := source
    rw [point_eq]
    exact nonextreme
  exact source_net F P (intrinsicDistance R) H distance
    (fun f x => Quot.mk R ⟨f, x⟩) point_eq (Quot.mk R source) outside

/-- Expanded ordinary net validity, independent of the source construction. -/
def NetOf (F : SpatialFolding C) (region : Set Plane) (fold : region → Space) : Prop :=
  Nonempty (region ≃ₜ Metric.closedBall (0 : Plane) 1) ∧
  Continuous fold ∧ Set.range fold = F.surface ∧
  Set.InjOn fold {z : region | z.val ∈ interior region} ∧
  (∃ n : ℕ, ∃ piece : Fin n → Set Plane,
    (∀ i, Polygon (piece i)) ∧
    Pairwise (fun i j => Disjoint (interior (piece i)) (interior (piece j))) ∧
    (⋃ i, piece i) = region ∧
    ∃ motion : Fin n → Plane →ᵃⁱ[ℝ] Space,
      ∀ i (x : piece i), ∃ hz : x.val ∈ region, fold ⟨x.val, hz⟩ = motion i x.val) ∧
  ∃ n : ℕ, ∃ a b : Fin n → Plane, frontier region = ⋃ i, segment ℝ (a i) (b i)

/-- Expanded source properties; the abstract supplies the independent public predicate. -/
def SourceUnfolding (F : SpatialFolding C) (R : C.Total → C.Total → Prop)
    (source : C.Total) (region : Set Plane) (fold : region → Space) : Prop :=
  NetOf F region fold ∧ ∃ project : region → Quot R,
    Continuous project ∧ Function.Surjective project ∧
    (∀ z p, project z = Quot.mk R p → fold z = F.place p.1 p.2.val) ∧
    (0 : Plane) ∈ interior region ∧
    (∀ (z : region) (t : unitInterval), (t : ℝ) • z.val ∈ region) ∧
    (∀ h : (0 : Plane) ∈ region, project ⟨0, h⟩ = Quot.mk R source) ∧
    (∃ H : interior region ≃ₜ ↥((cutLocus (intrinsicDistance R) (Quot.mk R source))ᶜ),
      ∀ z, (H z).val = project ⟨z.val, interior_subset z.property⟩) ∧
    (∀ x : interior region, ∃ T : Set (interior region), IsOpen T ∧ x ∈ T ∧
      ∀ y z : T, intrinsicDistance R
        (project ⟨y.val.val, interior_subset y.val.property⟩)
        (project ⟨z.val.val, interior_subset z.val.property⟩) = edist y.val.val z.val.val) ∧
    project '' {z : region | z.val ∈ frontier region} =
      cutLocus (intrinsicDistance R) (Quot.mk R source) ∧
    (∀ z : region, intrinsicDistance R (Quot.mk R source) (project z) =
      ENNReal.ofReal ‖z.val‖) ∧
    (∀ (z : region) (s t : unitInterval)
      (hs : (s : ℝ) • z.val ∈ region) (ht : (t : ℝ) • z.val ∈ region),
      intrinsicDistance R (project ⟨(s : ℝ) • z.val, hs⟩) (project ⟨(t : ℝ) • z.val, ht⟩) =
        ENNReal.ofReal ‖z.val‖ * edist s t) ∧
    ∀ x (p : Path (Quot.mk R source) x), Shortest (intrinsicDistance R) p →
      ∃! z : region, ∀ t : unitInterval, ∃ hz : (t : ℝ) • z.val ∈ region,
        project ⟨(t : ℝ) • z.val, hz⟩ = p t

/-- Compose the intrinsic projection with the actual spatial embedding. The result
covers precisely the polyhedron and has no duplicated interior surface points. -/
theorem NetData.folds_to_polyhedron (F : SpatialFolding C) (P : F.ConvexBoundary)
    {R : C.Total → C.Total → Prop} (equal : R = C.glue Set.univ) (source : C.Total)
    (D : NetData (C := C) (Quot R) (intrinsicDistance R)
      (fun f x => Quot.mk R ⟨f, x⟩) (Quot.mk R source)) :
    ∃ fold : D.region → Space, NetOf F D.region fold ∧
      ∀ z p, D.fold z = Quot.mk R p → fold z = F.place p.1 p.2.val := by
  let H := (quotientHomeomorph equal).trans (C.realizationHomeomorph Set.univ)
  let spatial : Quot R → Space := F.toSpace Set.univ ∘ H
  have spatial_point (p : C.Total) : spatial (Quot.mk R p) = F.place p.1 p.2.val := by
    change F.toSpace Set.univ
      (C.realizationHomeomorph Set.univ (quotientHomeomorph equal (Quot.mk R p))) = _
    rw [quotientHomeomorph_mk]
    rfl
  let fold := spatial ∘ D.fold
  have agrees (z) (p : C.Total) (same : D.fold z = Quot.mk R p) :
      fold z = F.place p.1 p.2.val := by
    change spatial (D.fold z) = _
    rw [same, spatial_point]
  refine ⟨fold, ⟨D.disk, ?_, ?_, ?_, ?_, D.polygonal_boundary⟩, agrees⟩
  · exact ((F.toSpace_lipschitz Set.univ).continuous.comp H.continuous).comp D.continuous_fold
  · ext x
    rw [← F.range_toSpace Set.univ]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨H (D.fold z), rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := D.surjective_fold (H.symm y)
      refine ⟨z, ?_⟩
      change F.toSpace Set.univ (H (D.fold z)) = F.toSpace Set.univ y
      rw [hz, H.apply_symm_apply]
  · intro z hz w hw same
    have physical : D.fold z = D.fold w :=
      H.injective (P.embedded same)
    obtain ⟨V, projected⟩ := D.cut_complement
    have cut : V ⟨z.val, hz⟩ = V ⟨w.val, hw⟩ := by
      apply Subtype.ext
      rw [projected, projected]
      exact physical
    have planar : z.val = w.val :=
      congrArg (fun v : interior D.region => v.val) (V.injective cut)
    exact Subtype.ext planar
  · obtain ⟨n, piece, polygons, disjoint, cover, face, motion, charts⟩ := D.pieces
    refine ⟨n, piece, polygons, disjoint, cover,
      fun i => (F.place (face i)).comp (motion i).toAffineIsometry, ?_⟩
    intro i x
    obtain ⟨inside, hz, same⟩ := charts i x
    exact ⟨hz, agrees _ _ same⟩

/-- Coordinate equations express the same edge identifications without public subtype proofs. -/
theorem edgePoint_eq_coordinates (p : C.Total) (e : EdgeRef Face)
    (x : (C.triangle e.face).Edge e.edge) :
    p = C.edgePoint e x ↔ p.1 = e.face ∧ p.2.val = x.val := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · obtain ⟨f, p⟩ := p
    rintro ⟨same, coordinate⟩
    change f = e.face at same
    subst f
    apply congrArg (Sigma.mk e.face)
    exact Subtype.ext coordinate

/-- The complete abstract statement, with all construction and validity proofs in the bridge. -/
theorem valid_source_unfolding (F : SpatialFolding C) (R : C.Total → C.Total → Prop)
    (relation : R = fun p q => ∃ s, ∃ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
      p.1 = (C.left s).face ∧ p.2.val = x.val ∧
      q.1 = (C.right s).face ∧ q.2.val = (C.identify s x).val)
    (embedded : ∀ p q : C.Total, F.place p.1 p.2.val = F.place q.1 q.2.val →
      Relation.EqvGen R p q)
    (interior_nonempty : (interior F.vertexHull).Nonempty)
    (boundary : F.surface = frontier F.vertexHull) (source : C.Total)
    (nonextreme : F.place source.1 source.2.val ∉ F.vertexHull.extremePoints ℝ) :
    ∃ region : Set Plane, ∃ fold : region → Space, SourceUnfolding F R source region fold := by
  classical
  have edges : R = fun p q => ∃ s x, p = C.edgePoint (C.left s) x ∧
      q = C.edgePoint (C.right s) (C.identify s x) := by
    rw [relation]
    funext p q
    apply propext
    simp only [edgePoint_eq_coordinates, and_assoc]
  have equal : R = C.glue Set.univ := by
    rw [edges]
    funext p q
    apply propext
    simp only [TriangleComplex.glue, Set.mem_univ, true_and]
    rfl
  have P : F.ConvexBoundary :=
    { embedded := F.isEmbedded_iff.mpr (by
        intro p q same
        rw [← equal]
        exact embedded p q same)
      interior_nonempty := interior_nonempty
      boundary := boundary }
  let D := geometric_source_net F R edges embedded interior_nonempty boundary source nonextreme
  obtain ⟨fold, net, agrees⟩ := D.folds_to_polyhedron F P equal source
  refine ⟨D.region, fold, net, D.fold, D.continuous_fold, D.surjective_fold, agrees,
    D.zero_interior, D.radial, (fun _ => D.source_image), D.cut_complement,
    D.local_isometry, D.boundary_projection, D.source_distance,
    (fun z s t _ _ => D.radial_geodesic z s t), ?_⟩
  intro x p shortest
  obtain ⟨z, tracks, unique⟩ := D.all_shortest_paths x p shortest
  refine ⟨z, fun t => ⟨D.radial z t, tracks t⟩, ?_⟩
  intro w same
  apply unique w
  intro t
  obtain ⟨_, equal⟩ := same t
  exact equal

/-- Assemble all implementation inputs here, so the abstract theorem only invokes this bridge. -/
theorem abstract_source_unfolding {Face Seam : Type} [Fintype Face] [Fintype Seam]
    (vertex : Face → Fin 3 → Plane)
    (nondegenerate : ∀ f, orient (vertex f 0) (vertex f 1) (vertex f 2) ≠ 0)
    (first last : Seam → Face × Fin 3) (distinct : ∀ s, first s ≠ last s)
    (identify : ∀ s,
      (Triangle.mk (vertex (first s).1) (nondegenerate (first s).1)).Edge (first s).2 ≃ᵢ
      (Triangle.mk (vertex (last s).1) (nondegenerate (last s).1)).Edge (last s).2)
    (unique : ∀ s t, first s = first t ∨ first s = last t ∨
      last s = first t ∨ last s = last t → s = t)
    (place : Face → Plane →ᵃⁱ[ℝ] Space)
    (joined : ∀ s x, place (first s).1 x.val = place (last s).1 (identify s x).val)
    (embedded : ∀ p q : (f : Face) × convexHull ℝ (Set.range (vertex f)),
      place p.1 p.2.val = place q.1 q.2.val →
        Relation.EqvGen (fun p q => ∃ s,
          ∃ x : (Triangle.mk (vertex (first s).1) (nondegenerate (first s).1)).Edge (first s).2,
            p.1 = (first s).1 ∧ p.2.val = x.val ∧
            q.1 = (last s).1 ∧ q.2.val = (identify s x).val) p q)
    (interior_nonempty : (interior (convexHull ℝ (Set.range
      (fun p : Face × Fin 3 => place p.1 (vertex p.1 p.2))))).Nonempty)
    (boundary : (⋃ f, place f '' convexHull ℝ (Set.range (vertex f))) =
      frontier (convexHull ℝ (Set.range
        (fun p : Face × Fin 3 => place p.1 (vertex p.1 p.2)))))
    (source : (f : Face) × convexHull ℝ (Set.range (vertex f)))
    (nonextreme : place source.1 source.2.val ∉ (convexHull ℝ (Set.range
      (fun p : Face × Fin 3 => place p.1 (vertex p.1 p.2)))).extremePoints ℝ) :
    let C := CapAbstractBridge.meshComplex vertex nondegenerate first last distinct identify unique
    let F : SpatialFolding C := ⟨place, joined⟩
    let R : C.Total → C.Total → Prop := fun p q => ∃ s,
      ∃ x : (C.triangle (C.left s).face).Edge (C.left s).edge,
        p.1 = (C.left s).face ∧ p.2.val = x.val ∧
        q.1 = (C.right s).face ∧ q.2.val = (C.identify s x).val
    ∃ region : Set Plane, ∃ fold : region → Space, SourceUnfolding F R source region fold := by
  let C := CapAbstractBridge.meshComplex vertex nondegenerate first last distinct identify unique
  let F : SpatialFolding C := ⟨place, joined⟩
  exact valid_source_unfolding (C := C) F _ rfl embedded
    interior_nonempty boundary source nonextreme

end Unfoldings.SourceAbstractBridge
