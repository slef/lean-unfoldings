module

public import Unfoldings.Geometry.Edge

/-! The endpoint permutation induced by an arbitrary full-edge isometry. -/

@[expose] public section

noncomputable section

namespace Unfoldings.Triangle

theorem vertex_injective (T : Triangle) : Function.Injective T.vertex := by
  intro i j equal
  rcases corner_cases i j with rfl | rfl | rfl
  · rfl
  · exact (T.edge_endpoints_ne i equal).elim
  · have cycle : next (next (next i)) = i := by fin_cases i <;> rfl
    exact (T.edge_endpoints_ne (next (next i)) (by rw [cycle]; exact equal.symm)).elim

/-- False is the initial endpoint of a local edge; true is its terminal endpoint. -/
def endpoint (T : Triangle) (e : Fin 3) : Bool → T.Edge e
  | false => ⟨T.vertex e, left_mem_segment ℝ _ _⟩
  | true => ⟨T.vertex (next e), right_mem_segment ℝ _ _⟩

theorem endpoint_injective (T : Triangle) (e : Fin 3) : Function.Injective (T.endpoint e) := by
  intro b c equal
  cases b <;> cases c
  · rfl
  · exact (T.edge_endpoints_ne e (congrArg Subtype.val equal)).elim
  · exact (T.edge_endpoints_ne e (congrArg Subtype.val equal).symm).elim
  · rfl

theorem isVertex_endpoint (T : Triangle) (e : Fin 3) (b : Bool) :
    T.IsVertex (T.endpoint e b) := by
  cases b
  · exact ⟨e, rfl⟩
  · exact ⟨next e, rfl⟩

theorem exists_endpoint (T : Triangle) (e : Fin 3) (x : T.Edge e) (vertex : T.IsVertex x) :
    ∃ b, T.endpoint e b = x := by
  rcases (T.edge_vertex_iff e x).mp vertex with left | right
  · exact ⟨false, Subtype.ext left.symm⟩
  · exact ⟨true, Subtype.ext right.symm⟩

theorem exists_endpoint_image (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f)
    (b : Bool) : ∃ c, U.endpoint f c = identify (T.endpoint e b) :=
  U.exists_endpoint f _ ((T.edge_isometry_isVertex_iff U e f identify _).mpr
    (T.isVertex_endpoint e b))

/-- The actual endpoint map, chosen after preservation of endpoints has been proved. -/
def endpointMap (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f)
    (b : Bool) : Bool :=
  Classical.choose (T.exists_endpoint_image U e f identify b)

theorem endpoint_endpointMap (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f)
    (b : Bool) : U.endpoint f (T.endpointMap U e f identify b) = identify (T.endpoint e b) :=
  Classical.choose_spec (T.exists_endpoint_image U e f identify b)

theorem endpointMap_bijective (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) :
    Function.Bijective (T.endpointMap U e f identify) := by
  constructor
  · intro b c equal
    apply T.endpoint_injective e
    apply identify.injective
    rw [← T.endpoint_endpointMap U e f identify b, ← T.endpoint_endpointMap U e f identify c, equal]
  · intro c
    obtain ⟨b, hb⟩ := U.exists_endpoint_image T f e identify.symm c
    refine ⟨b, U.endpoint_injective f ?_⟩
    rw [T.endpoint_endpointMap, hb, identify.apply_symm_apply]

/-- Full-edge isometries act by permutations of the two endpoints. -/
def endpointEquiv (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) : Bool ≃ Bool :=
  Equiv.ofBijective (T.endpointMap U e f identify) (T.endpointMap_bijective U e f identify)

theorem endpoint_endpointEquiv (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f)
    (b : Bool) : U.endpoint f (T.endpointEquiv U e f identify b) = identify (T.endpoint e b) :=
  T.endpoint_endpointMap U e f identify b

theorem endpointEquiv_symm (T U : Triangle) (e f : Fin 3) (identify : T.Edge e ≃ᵢ U.Edge f) :
    U.endpointEquiv T f e identify.symm = (T.endpointEquiv U e f identify).symm := by
  ext b
  apply T.endpoint_injective e
  apply identify.injective
  rw [U.endpoint_endpointEquiv, identify.apply_symm_apply,
    ← T.endpoint_endpointEquiv, Equiv.apply_symm_apply]

end Unfoldings.Triangle
