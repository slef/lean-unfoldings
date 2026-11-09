module

public import Unfoldings.Topology.BoundaryQuotient
public import Unfoldings.Topology.PuncturedSphere
public import Unfoldings.Topology.GraphAcyclic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Boundary quotients of closed balls and the spherical tree obstruction

Normalizing nonzero vectors retracts a punctured closed ball onto its sphere.
For a quotient with identifications only on that sphere, this retraction
descends to the punctured target. If the target is homeomorphic to a sphere,
the boundary image is contractible. Every finite embedded graph representing
that image is consequently simple and a tree.

These are necessary conditions on a disk presentation. They do not construct
a disk by cutting along an arbitrary embedded tree.
-/

@[expose] public section

noncomputable section

namespace Unfoldings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def closedBallOrigin : Metric.closedBall (0 : E) 1 := ⟨0, Metric.mem_closedBall_self zero_le_one⟩

def closedBallBoundary : Set (Metric.closedBall (0 : E) 1) := {x | ‖x.val‖ = 1}

omit [NormedSpace ℝ E] in
theorem closedBallOrigin_not_mem_boundary :
    (closedBallOrigin (E := E)) ∉ closedBallBoundary := by
  change ‖(0 : E)‖ ≠ 1
  simp

def closedBallBoundaryRetraction :
    C(↥(({closedBallOrigin (E := E)} : Set (Metric.closedBall (0 : E) 1))ᶜ),
      closedBallBoundary (E := E)) := by
  have nonzero (x : ↥(({closedBallOrigin (E := E)} :
      Set (Metric.closedBall (0 : E) 1))ᶜ)) : x.val.val ≠ 0 := by
    intro equal
    exact x.property (Subtype.ext equal)
  have normalized (x : ↥(({closedBallOrigin (E := E)} :
      Set (Metric.closedBall (0 : E) 1))ᶜ)) : ‖‖x.val.val‖⁻¹ • x.val.val‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (nonzero x))]
  have inside (x : ↥(({closedBallOrigin (E := E)} :
      Set (Metric.closedBall (0 : E) 1))ᶜ)) :
      ‖x.val.val‖⁻¹ • x.val.val ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, normalized]
  have continuous_normalize : Continuous (fun x : ↥(({closedBallOrigin (E := E)} :
      Set (Metric.closedBall (0 : E) 1))ᶜ) => ‖x.val.val‖⁻¹ • x.val.val) :=
    (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
      (fun x => norm_ne_zero_iff.mpr (nonzero x))).smul
        (continuous_subtype_val.comp continuous_subtype_val))
  exact ⟨fun x => ⟨⟨‖x.val.val‖⁻¹ • x.val.val, inside x⟩, normalized x⟩,
    (continuous_normalize.subtype_mk inside).subtype_mk normalized⟩

theorem closedBallBoundaryRetraction_boundary (b : closedBallBoundary (E := E))
    (h : b.val ≠ closedBallOrigin) : closedBallBoundaryRetraction ⟨b.val, h⟩ = b := by
  apply Subtype.ext
  apply Subtype.ext
  change ‖b.val.val‖⁻¹ • b.val.val = b.val.val
  rw [b.property, inv_one, one_smul]

omit [NormedSpace ℝ E] in
theorem isClosed_closedBallBoundary : IsClosed (closedBallBoundary (E := E)) :=
  isClosed_eq continuous_subtype_val.norm continuous_const

def closedBallInteriorHomeomorph : ↥((closedBallBoundary (E := E))ᶜ) ≃ₜ
    Metric.ball (0 : E) 1 := by
  have inside (x : ↥((closedBallBoundary (E := E))ᶜ)) : x.val.val ∈ Metric.ball (0 : E) 1 := by
    have bound : ‖x.val.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.val.property
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_ne bound x.property
  have outside (x : Metric.ball (0 : E) 1) :
      (⟨x.val, Metric.ball_subset_closedBall x.property⟩ : Metric.closedBall (0 : E) 1) ∉
        closedBallBoundary := by
    have bound : ‖x.val‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using x.property
    exact ne_of_lt bound
  exact
    { toFun := fun x => ⟨x.val.val, inside x⟩
      invFun := fun x => ⟨⟨x.val, Metric.ball_subset_closedBall x.property⟩, outside x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk inside
      continuous_invFun :=
        (continuous_subtype_val.subtype_mk
          (fun x => Metric.ball_subset_closedBall x.property)).subtype_mk outside }

namespace BoundaryQuotient

variable {X : Type*} [TopologicalSpace X] [T1Space X]
  (Q : BoundaryQuotient (Metric.closedBall (0 : E) 1) X)

def ballComplementHomeomorph (boundary : Q.boundary = closedBallBoundary) :
    Metric.ball (0 : E) 1 ≃ₜ ↥(Q.boundaryImageᶜ) := by
  have closed : IsClosed Q.boundary := boundary ▸ isClosed_closedBallBoundary
  exact closedBallInteriorHomeomorph.symm.trans
    ((Homeomorph.setCongr (congrArg Set.compl boundary.symm)).trans
      (Q.complementHomeomorph closed))

omit [NormedSpace ℝ E] [T1Space X] in
@[simp] theorem ballComplementHomeomorph_apply (boundary : Q.boundary = closedBallBoundary)
    (x : Metric.ball (0 : E) 1) :
    (Q.ballComplementHomeomorph boundary x).val =
      Q.projection ⟨x.val, Metric.ball_subset_closedBall x.property⟩ := rfl

omit [T1Space X] in
theorem ball_complement_contractible (boundary : Q.boundary = closedBallBoundary) :
    ContractibleSpace ↥(Q.boundaryImageᶜ) := by
  let := (convex_ball (0 : E) 1).contractibleSpace
    ⟨0, Metric.mem_ball_self zero_lt_one⟩
  exact (Q.ballComplementHomeomorph boundary).symm.contractibleSpace

/-- A closed-ball presentation gives an actual retraction onto the boundary image. -/
theorem exists_ball_boundary_retraction (boundary : Q.boundary = closedBallBoundary) :
    ∃ R : C(↥(({Q.projection closedBallOrigin} : Set X)ᶜ), Q.boundaryImage),
      ∀ b : Q.boundaryImage, ∀ h : b.val ≠ Q.projection closedBallOrigin,
        R ⟨b.val, h⟩ = b := by
  have outside : closedBallOrigin ∉ Q.boundary := by
    rw [boundary]
    exact closedBallOrigin_not_mem_boundary
  let H := Homeomorph.setCongr boundary.symm
  let retract := (⟨H, H.continuous⟩ : C(closedBallBoundary, Q.boundary)).comp
    closedBallBoundaryRetraction
  have fixed (b : Q.boundary) (h : b.val ≠ closedBallOrigin) : retract ⟨b.val, h⟩ = b := by
    apply Subtype.ext
    have equal := congrArg (fun x : closedBallBoundary => x.val)
      (closedBallBoundaryRetraction_boundary (H.symm b) h)
    exact equal
  obtain ⟨R, fixed⟩ := Q.exists_boundary_retraction closedBallOrigin outside retract fixed
  exact ⟨R, fun b _ => fixed b⟩

theorem ball_boundaryImage_contractible_of_sphere
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    (sphere : X ≃ₜ Metric.sphere (0 : S) 1)
    (boundary : Q.boundary = closedBallBoundary) : ContractibleSpace Q.boundaryImage := by
  let pole := sphere (Q.projection closedBallOrigin)
  let punctured : ↥(({Q.projection closedBallOrigin} : Set X)ᶜ) ≃ₜ
      ↥(({pole} : Set (Metric.sphere (0 : S) 1))ᶜ) := sphere.subtype (by
    intro x
    change x ≠ Q.projection closedBallOrigin ↔ sphere x ≠ sphere (Q.projection closedBallOrigin)
    exact not_congr sphere.injective.eq_iff.symm)
  let := contractible_punctured_unit_sphere pole
  let := punctured.contractibleSpace
  obtain ⟨R, fixed⟩ := Q.exists_ball_boundary_retraction boundary
  have outside : closedBallOrigin ∉ Q.boundary := by
    rw [boundary]
    exact closedBallOrigin_not_mem_boundary
  exact contractible_of_retraction (Q.boundaryImageInclusion closedBallOrigin outside) R
    (fun b => fixed b _)

theorem ball_boundary_graph_tree_of_sphere [T2Space X]
    {S : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
    (sphere : X ≃ₜ Metric.sphere (0 : S) 1)
    (boundary : Q.boundary = closedBallBoundary)
    {Vertex Edge : Type*} (G : FiniteEmbeddedGraph Vertex Edge X)
    (carrier : G.carrier = Q.boundaryImage) : G.graph.Simple ∧ G.adjacencyGraph.IsTree := by
  have contractible : ContractibleSpace G.carrier := by
    rw [carrier]
    exact Q.ball_boundaryImage_contractible_of_sphere sphere boundary
  let := contractible
  exact ⟨G.graph_simple_of_contractible, G.adjacencyGraph_tree_of_contractible⟩

end BoundaryQuotient
end Unfoldings
