module

public import Unfoldings.Roof.SharpStraightLink
public import Unfoldings.Topology.PairedInvolutionExtension
public import Unfoldings.Topology.FinitePrefixSum
public import Unfoldings.Geometry.ClosedRayChain
public import Unfoldings.Complex.LinkCornerWeights
public import Unfoldings.Polyhedron.RestrictedBoundaryTurns

/-! The sharp connector estimate on the actual boundary fans of a selected roof region. -/

@[expose] public section

noncomputable section

namespace Unfoldings.ConvexRoof

open InnerProductGeometry Real

universe u v

variable {Face : Type u} [Fintype Face] {C : TriangleComplex.{u, v} Face} (K : ConvexRoof C)

section PartialLink

variable {v : C.Vertex Set.univ} {n : ℕ} (c : (C.linkSystem Set.univ v).Chain n)

/-- The selected and complementary projected angles bound the same actual endpoint angle. -/
theorem projected_partial_link_angle_bounds (internal : ¬ C.IsBoundaryVertex Set.univ v) :
    let angle := InnerProductGeometry.angle (K.projectedGermRay c.first)
      (K.projectedGermRay (C.linkTurn Set.univ v c.last))
    let selected := ∑ i : Fin (n + 1),
      (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2
    angle ≤ selected ∧ angle ≤ K.projectedTotalAngle Set.univ v - selected := by
  have partial_first : K.projectedIntervalRay c 0 = K.projectedGermRay c.first := by
    change K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc = _
    rw [K.projectedIntervalRay_castSucc]
    rfl
  have direct := angle_endpoint_le_sum (K.projectedIntervalRay c)
    (K.projectedIntervalRay_ne_zero c 0)
  rw [partial_first, K.projectedIntervalRay_last] at direct
  simp only [K.projectedIntervalRay_castSucc, K.projectedIntervalRay_succ,
    K.projectedGermRay_angle] at direct
  refine ⟨direct, ?_⟩
  have free (p : C.LinkGerm Set.univ v) : C.linkMate Set.univ v p ≠ p := fun fixed =>
    internal ((C.isBoundaryVertex_iff_linkMate_fixed Set.univ v).mpr ⟨p, fixed⟩)
  obtain ⟨m, d, longer, kept, closed, covers⟩ := (C.linkSystem Set.univ v).exists_cycle_extension
    (C.linkSystem_connected Set.univ v) free c
  let weight (p : C.LinkGerm Set.univ v) := (K.projectedTriangle p.val.1.1).cornerAngle p.val.1.2
  let big (i : Fin (m + 1)) := weight (d.point i)
  let small (i : Fin (n + 1)) := weight (c.point i)
  let ray := K.projectedIntervalRay d
  have origin : ray 0 = K.projectedGermRay d.first := by
    change K.projectedIntervalRay d (0 : Fin (m + 1)).castSucc = _
    rw [K.projectedIntervalRay_castSucc]
    rfl
  have same_origin : ray 0 = K.projectedGermRay c.first := by
    rw [origin]
    exact congrArg K.projectedGermRay (kept 0)
  have closes : ray (Fin.last (m + 1)) = ray 0 := by
    rw [show ray (Fin.last (m + 1)) = K.projectedGermRay (C.linkTurn Set.univ v d.last) from
      K.projectedIntervalRay_last d, origin]
    have equal := congrArg K.projectedGermRay closed
    change K.projectedGermRay (C.linkMate Set.univ v (C.linkTurn Set.univ v d.last)) =
      K.projectedGermRay d.first at equal
    simpa only [K.projectedGermRay_mate] using equal
  have angles (i : Fin (m + 1)) :
      InnerProductGeometry.angle (ray i.castSucc) (ray i.succ) = big i := by
    calc
      _ = InnerProductGeometry.angle (K.projectedGermRay (d.point i))
          (K.projectedGermRay (C.linkTurn Set.univ v (d.point i))) :=
        congrArg₂ InnerProductGeometry.angle (K.projectedIntervalRay_castSucc d i)
          (K.projectedIntervalRay_succ d i)
      _ = big i := K.projectedGermRay_angle (d.point i)
  have total : (∑ i, big i) = K.projectedTotalAngle Set.univ v :=
    K.projectedLinkFan_totalAngle d covers
  have prefix_sum : Fin.partialSum big ⟨n + 1, by omega⟩ = ∑ i, small i := by
    apply fin_partialSum_prefix (by omega : n + 1 ≤ m + 1) big small
    intro i
    exact congrArg weight (kept i)
  let endpoint : Fin (m + 2) := ⟨n + 1, by omega⟩
  let last_corner : Fin (m + 1) := ⟨n, by omega⟩
  have terminal : ray endpoint = K.projectedGermRay (C.linkTurn Set.univ v c.last) := by
    rw [show endpoint = last_corner.succ from Fin.ext rfl]
    exact (K.projectedIntervalRay_succ d last_corner).trans
      (congrArg (fun p : C.LinkGerm Set.univ v => K.projectedGermRay (C.linkTurn Set.univ v p))
        (kept (Fin.last n)))
  have estimate := angle_le_remaining_closed_ray_sum ray
    (K.projectedIntervalRay_ne_zero d 0) closes endpoint
  simp only [angles] at estimate
  rw [total, prefix_sum, terminal, same_origin, InnerProductGeometry.angle_comm] at estimate
  exact estimate

end PartialLink

open Classical in
/-- A straight boundary vertex has precisely a halfplane as its selected projected fan. -/
theorem restricted_projected_angle_eq_pi (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (straight : InnerProductGeometry.angle
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val))
      (Cap.horizontal ((K.folding.restrictFaces U).germDirection
        ((C.restrictFaces U).boundaryMate Set.univ p).val)) = Real.pi) :
    (C.restrictFaces U).regionalCornerSum Set.univ
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
      ((C.restrictFaces U).boundaryEndVertex Set.univ p) = Real.pi := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  obtain ⟨n, c, first, last, covers⟩ := R.exists_boundary_link Set.univ p
  let d := C.includeRestrictedLinkChain U c
  have projected_ray (g : R.LinkGerm Set.univ w) :
      K.projectedGermRay (C.includeRestrictedLinkGerm U g) =
        Cap.horizontal ((K.folding.restrictFaces U).germDirection g.val) :=
    (K.horizontal_germDirection (C.includeRestrictedLinkGerm U g)).symm
  have first_ray : K.projectedGermRay d.first =
      Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) := by
    have same := projected_ray c.first
    rw [first] at same
    exact same
  have last_ray : K.projectedGermRay
      (C.linkTurn Set.univ (C.includeRestrictedVertexUniv U w) d.last) =
        Cap.horizontal ((K.folding.restrictFaces U).germDirection
          (R.boundaryMate Set.univ p).val) := by
    have same := projected_ray (R.linkTurn Set.univ w c.last)
    rw [last] at same
    exact same
  have selected : (∑ i : Fin (n + 1),
      (K.projectedTriangle (d.point i).val.1.1).cornerAngle (d.point i).val.1.2) =
      R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w :=
    R.sum_linkCornerWeight w c covers
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
  obtain ⟨lower, upper⟩ := K.projected_partial_link_angle_bounds d internal
  rw [first_ray, last_ray, straight, selected] at lower upper
  rw [K.projectedTotalAngle_eq_two_pi _ internal] at upper
  exact le_antisymm (by linarith) lower

open Classical in
/-- Actual intrinsic exterior fan turn minus its actual projected exterior fan turn. -/
def restrictedBoundaryTurnError (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) : ℝ :=
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  (Real.pi - R.totalAngle Set.univ w) -
    (Real.pi - R.regionalCornerSum Set.univ
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w)

open Classical in
/-- The restricted fan has exactly its signed hinge turn, with the actual
intermediate crease germ of a selected face. -/
theorem restrictedBoundaryTurnError_eq_hinge_difference (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (d s₁ s₂ : Plane)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) =
      C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) →
      K.normalSlope f = s₁ ∨ K.normalSlope f = s₂)
    (transverse : s₁ = s₂ ∨ inner ℝ (s₁ - s₂) d ≠ 0)
    {a b : ℝ} (a_pos : 0 < a) (b_pos : 0 < b)
    (first : Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) = a • d)
    (last : Cap.horizontal ((K.folding.restrictFaces U).germDirection
      ((C.restrictFaces U).boundaryMate Set.univ p).val) = b • (-d)) :
    let w := C.includeRestrictedVertexUniv U
      ((C.restrictFaces U).boundaryEndVertex Set.univ p)
    let l := p.val.1.1.val
    let r := ((C.restrictFaces U).boundaryMate Set.univ p).val.1.1.val
    (K.normalSlope l = K.normalSlope r ∧ K.restrictedBoundaryTurnError U p = 0) ∨
      ∃ g : C.LinkGerm Set.univ w, g.val.1.1 ∈ U ∧
        let join := K.projectedGermRay g
        inner ℝ (K.normalSlope l - K.normalSlope r) join = 0 ∧ orient 0 join d ≠ 0 ∧
          K.restrictedBoundaryTurnError U p =
            angle (K.sectionDirection l join) (K.sectionDirection r d) -
              angle (K.sectionDirection l join) (K.sectionDirection l d) := by
  let R := C.restrictFaces U
  let w := R.boundaryEndVertex Set.univ p
  let F := K.folding.restrictFaces U
  let q := R.boundaryMate Set.univ p
  obtain ⟨n, chain, first_chain, last_chain, covers⟩ := R.exists_boundary_link Set.univ p
  let c := C.includeRestrictedLinkChain U chain
  have head : K.projectedIntervalRay c 0 = a • d := by
    change K.projectedIntervalRay c (0 : Fin (n + 1)).castSucc = _
    rw [K.projectedIntervalRay_castSucc]
    have h := (K.horizontal_germDirection (C.includeRestrictedLinkGerm U chain.first)).symm
    change K.projectedGermRay (C.includeRestrictedLinkGerm U chain.first) =
      Cap.horizontal (F.germDirection chain.first.val) at h
    rw [first_chain] at h
    exact h.trans first
  have tail : K.projectedIntervalRay c (Fin.last (n + 1)) = b • (-d) := by
    rw [K.projectedIntervalRay_last]
    have h := (K.horizontal_germDirection
      (C.includeRestrictedLinkGerm U (R.linkTurn Set.univ w chain.last))).symm
    change K.projectedGermRay (C.includeRestrictedLinkGerm U (R.linkTurn Set.univ w chain.last)) =
      Cap.horizontal (F.germDirection (R.linkTurn Set.univ w chain.last).val) at h
    rw [last_chain] at h
    exact h.trans last
  have genuine : d ≠ 0 := by
    intro zero
    exact K.projectedIntervalRay_ne_zero c 0 (by rw [head, zero, smul_zero])
  have straight : angle (Cap.horizontal (F.germDirection p.val))
      (Cap.horizontal (F.germDirection q.val)) = π := by
    rw [first, last, angle_smul_left_of_pos _ _ a_pos,
      angle_smul_right_of_pos _ _ b_pos, angle_neg_right, angle_self genuine, sub_zero]
  have projected : (∑ i : Fin (n + 1),
      (K.projectedTriangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2) w :=
    R.sum_linkCornerWeight w chain covers
      (fun c => (K.projectedTriangle c.1.val).cornerAngle c.2)
  have flat := K.restricted_projected_angle_eq_pi U p internal straight
  have intrinsic : (∑ i : Fin (n + 1),
      (C.triangle (c.point i).val.1.1).cornerAngle (c.point i).val.1.2) =
      R.totalAngle Set.univ w := R.sum_linkCornerAngle Set.univ w chain covers
  have faces (i : Fin (n + 1)) : K.normalSlope (c.point i).val.1.1 = s₁ ∨
      K.normalSlope (c.point i).val.1.1 = s₂ :=
    slopes (c.point i).val.1.1 (c.point i).val.1.2 (c.point i).property
  have a_face : c.first.val.1.1 = p.val.1.1.val := by
    exact congrArg (fun g : R.Germ => g.1.1.val) first_chain
  have b_face : c.last.val.1.1 = q.val.1.1.val := by
    change (R.linkTurn Set.univ w chain.last).val.1.1.val = q.val.1.1.val
    exact congrArg (fun g : R.Germ => g.1.1.val) last_chain
  have turn : K.restrictedBoundaryTurnError U p = π - R.totalAngle Set.univ w := by
    change (π - R.totalAngle Set.univ w) -
      (π - R.regionalCornerSum Set.univ (fun c => (K.projectedTriangle c.1.val).cornerAngle
        c.2) w) = π - R.totalAngle Set.univ w
    rw [flat, sub_self, sub_zero]
  have exact := K.straight_link_turn_eq_hinge_difference c d s₁ s₂ faces transverse
    a_pos b_pos head tail (projected.trans flat)
  rcases exact with ⟨same, zero⟩ | ⟨i, tie, nonzero, equal⟩
  · rw [a_face, b_face] at same
    rw [turn, ← intrinsic]
    exact Or.inl ⟨same, zero⟩
  · let g := C.includeRestrictedLinkGerm U (chain.point i.succ)
    have member : g.val.1.1 ∈ U := (chain.point i.succ).val.1.1.property
    have eq : K.projectedIntervalRay c i.castSucc.succ = K.projectedGermRay g := by
      rw [Fin.succ_castSucc, K.projectedIntervalRay_castSucc]
      rfl
    rw [a_face, b_face, eq] at tie equal
    rw [eq] at nonzero
    exact Or.inr ⟨g, member, tie, nonzero, by rwa [turn, ← intrinsic]⟩

open Classical in
/-- A regular straight contact pays only the sine-scaled change of the two
actual support inclinations. The selected link and its boundary directions
come from the given restricted complex. -/
theorem abs_restrictedBoundaryTurnError_le_sin_mul_active_angle {φ : ℝ}
    (nonnegative : 0 ≤ φ) (small : φ < π / 2) (tilt : K.TiltBound φ) (U : Set Face)
    (p : (C.restrictFaces U).BoundaryEnd Set.univ) (d s₁ s₂ : Plane)
    (internal : ¬ C.IsBoundaryVertex Set.univ
      (C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p)))
    (slopes : ∀ f i, C.vertexOfCorner Set.univ (f, i) =
      C.includeRestrictedVertexUniv U ((C.restrictFaces U).boundaryEndVertex Set.univ p) →
      K.normalSlope f = s₁ ∨ K.normalSlope f = s₂)
    (transverse : s₁ = s₂ ∨ inner ℝ (s₁ - s₂) d ≠ 0)
    {a b : ℝ} (a_pos : 0 < a) (b_pos : 0 < b)
    (first : Cap.horizontal ((K.folding.restrictFaces U).germDirection p.val) = a • d)
    (last : Cap.horizontal ((K.folding.restrictFaces U).germDirection
      ((C.restrictFaces U).boundaryMate Set.univ p).val) = b • (-d)) :
    |K.restrictedBoundaryTurnError U p| ≤ sin φ *
      angle (K.sectionDirection p.val.1.1.val d)
        (K.sectionDirection ((C.restrictFaces U).boundaryMate Set.univ p).val.1.1.val d) := by
  rcases K.restrictedBoundaryTurnError_eq_hinge_difference U p d s₁ s₂ internal slopes
      transverse a_pos b_pos first last with flat | ⟨g, _, tie, cross, eq⟩
  · rw [flat.2, abs_zero]
    exact mul_nonneg (sin_nonneg_of_nonneg_of_le_pi nonnegative (by linarith only [small, pi_pos]))
      (angle_nonneg _ _)
  · let l := p.val.1.1.val
    let r := ((C.restrictFaces U).boundaryMate Set.univ p).val.1.1.val
    let join := K.projectedGermRay g
    have shared : K.sectionDirection l join = K.sectionDirection r join := by
      change inner ℝ (K.normalSlope l - K.normalSlope r) join = 0 at tie
      rw [inner_sub_left, sub_eq_zero] at tie
      simp only [sectionDirection, tie]
    have sharp := K.abs_sectionDirection_common_angle_sub_le_sin_tilt
      nonnegative small tilt l r join d shared cross
    rw [eq, abs_sub_comm]
    exact sharp

end Unfoldings.ConvexRoof
